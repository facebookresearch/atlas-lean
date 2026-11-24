/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

/-!
# Strassen's circuit bound

For blocks of side `2 ^ k`, Strassen's recursion uses seven recursive products and eighteen
entrywise block additions or subtractions. Zero padding extends the circuit construction to every
dimension, giving the exponent bound `strassen1969Upper` over every field.
-/

namespace Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted

universe u
variable {F : Type u} [Field F] {I : Type}

-- A wire is described by its value on all input assignments at once.
private abbrev Value (I : Type) (F : Type u) := (I → F) → F

-- Each gate has a single description that works for every input assignment.
private structure Tape (I : Type) (F : Type u) [Field F] where
  size : ℕ
  value : ℕ → Value I F
  valid (i : ℕ) (hi : i < size) : ∃ g : ArithmeticGate F I i,
    ∀ x, g.evaluate x (fun j => value j x) = value i x

private def wires (p : Tape I F) : Set (Value I F) :=
  {f | ∃ a : ArithmeticOperand F I p.size, ∀ x, a.evaluate x (fun j => p.value j x) = f x}

private theorem wires_node (p : Tape I F) {i : ℕ} (hi : i < p.size) :
    p.value i ∈ wires p := ⟨.node ⟨i, hi⟩, fun _ => rfl⟩

private theorem wires_const (p : Tape I F) (a : F) : (fun _ => a) ∈ wires p :=
  ⟨.constant a, fun _ => rfl⟩

private theorem wires_input (p : Tape I F) (i : I) : (fun x => x i) ∈ wires p :=
  ⟨.input i, fun _ => rfl⟩

private theorem append_gate (p : Tape I F) (g : ArithmeticGate F I p.size) (f : Value I F)
    (hg : ∀ x, g.evaluate x (fun j => p.value j x) = f x) :
    ∃ q : Tape I F, q.size = p.size + 1 ∧ wires p ⊆ wires q ∧ f ∈ wires q := by
  let v (i : ℕ) := if i = p.size then f else p.value i
  have old {i : ℕ} (hi : i < p.size) : v i = p.value i := by simp [v, hi.ne]
  have last : v p.size = f := by simp [v]
  let q : Tape I F := {
    size := p.size + 1
    value := v
    valid := by
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
      · obtain ⟨a, ha⟩ := p.valid i h
        exact ⟨a, fun x => by simpa only [old h, old (Nat.lt_trans (Fin.isLt _) h)] using ha x⟩
      · exact ⟨g, fun x => by simpa only [old (Fin.isLt _), last] using hg x⟩ }
  refine ⟨q, rfl, ?_, ?_⟩
  · rintro _ ⟨a, ha⟩
    cases a with
    | constant c => exact ⟨.constant c, ha⟩
    | input i => exact ⟨.input i, ha⟩
    | node i =>
      refine ⟨.node ⟨i, Nat.lt_succ_of_lt i.isLt⟩, fun x => ?_⟩
      exact (congrFun (old i.isLt) x).trans (ha x)
  · simpa only [q, last] using wires_node q (i := p.size) (Nat.lt_succ_self _)

-- Starting with all wires in s, append at most n gates to make all wires in t available.
private def Builds (s : Set (Value I F)) (n : ℕ) (t : Set (Value I F)) : Prop :=
  ∀ p : Tape I F, s ⊆ wires p → ∃ q : Tape I F,
    q.size ≤ p.size + n ∧ wires p ⊆ wires q ∧ t ⊆ wires q

private theorem free {s t : Set (Value I F)} (h : t ⊆ s) : Builds s 0 t :=
  fun p hp => ⟨p, by simp, Set.Subset.rfl, h.trans hp⟩

private theorem weaken {s t t' : Set (Value I F)} {n m : ℕ}
    (h : Builds s n t) (hn : n ≤ m) (ht : t' ⊆ t) : Builds s m t' := by
  intro p hp
  obtain ⟨q, hq, hkeep, htq⟩ := h p hp
  exact ⟨q, by omega, hkeep, ht.trans htq⟩

private theorem seq {s t v : Set (Value I F)} {n m : ℕ}
    (a : Builds s n t) (b : Builds t m v) : Builds s (n + m) v := by
  intro p hp
  obtain ⟨q, hq, hpq, ht⟩ := a p hp
  obtain ⟨r, hr, hqr, hv⟩ := b q ht
  exact ⟨r, by omega, hpq.trans hqr, hv⟩

private theorem both {s t v : Set (Value I F)} {n m : ℕ}
    (a : Builds s n t) (b : Builds s m v) : Builds s (n + m) (t ∪ v) := by
  intro p hp
  obtain ⟨q, hq, hpq, ht⟩ := a p hp
  obtain ⟨r, hr, hqr, hv⟩ := b q (hp.trans hpq)
  exact ⟨r, by omega, hpq.trans hqr, Set.union_subset (ht.trans hqr) hv⟩

private theorem family {J : Type} [Fintype J] {s : Set (Value I F)}
    {t : J → Set (Value I F)} {n : J → ℕ} (h : ∀ j, Builds s (n j) (t j)) :
    Builds s (∑ j, n j) (⋃ j, t j) := by
  classical
  suffices ∀ a : Finset J, Builds s (∑ j ∈ a, n j) (⋃ j ∈ a, t j) by
    simpa using this Finset.univ
  intro a
  induction a using Finset.induction_on with
  | empty => simpa using (free (s := s) (Set.empty_subset s))
  | @insert j a hj ih =>
    simpa [hj] using both (h j) ih

private inductive Op | add | sub | mul

private def Op.act (op : Op) (a b : Value I F) : Value I F :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

private theorem one_gate {s : Set (Value I F)} (op : Op) {a b : Value I F}
    (ha : a ∈ s) (hb : b ∈ s) : Builds s 1 {op.act a b} := by
  intro p hp
  obtain ⟨v, hv⟩ := hp ha
  obtain ⟨w, hw⟩ := hp hb
  let g : ArithmeticGate F I p.size := match op with
    | .add => .add v w
    | .sub => .sub v w
    | .mul => .mul v w
  have hg (x) : g.evaluate x (fun j => p.value j x) = op.act a b x := by
    cases op <;> simp [g, ArithmeticGate.evaluate, Op.act, hv, hw]
  obtain ⟨q, hq, hkeep, hout⟩ := append_gate p g _ hg
  exact ⟨q, hq.le, hkeep, Set.singleton_subset_iff.mpr hout⟩

private def entries {J : Type} (M : Matrix J J (Value I F)) : Set (Value I F) :=
  Set.range fun ij : J × J => M ij.1 ij.2

omit [Field F] in
private theorem entry {J : Type} (M : Matrix J J (Value I F)) (i j : J) :
    M i j ∈ entries M := ⟨(i, j), rfl⟩

private theorem pointwise {J : Type} [Fintype J] {s : Set (Value I F)}
    {A B : Matrix J J (Value I F)} {a b : ℕ}
    (ha : Builds s a (entries A)) (hb : Builds s b (entries B)) (op : Op) :
    Builds s (a + b + Fintype.card J ^ 2) (entries (.of fun i j => op.act (A i j) (B i j))) := by
  apply seq (both ha hb)
  have h (ij : J × J) :=
    one_gate op (Set.mem_union_left (entries B) (entry A ij.1 ij.2))
      (Set.mem_union_right (entries A) (entry B ij.1 ij.2))
  simpa [entries, Set.iUnion_singleton_eq_range, sq] using family h

private theorem add_blocks {J : Type} [Fintype J] {s : Set (Value I F)}
    {A B : Matrix J J (Value I F)} {a b : ℕ}
    (ha : Builds s a (entries A)) (hb : Builds s b (entries B)) :
    Builds s (a + b + Fintype.card J ^ 2) (entries (A + B)) := pointwise ha hb .add

private theorem sub_blocks {J : Type} [Fintype J] {s : Set (Value I F)}
    {A B : Matrix J J (Value I F)} {a b : ℕ}
    (ha : Builds s a (entries A)) (hb : Builds s b (entries B)) :
    Builds s (a + b + Fintype.card J ^ 2) (entries (A - B)) := pointwise ha hb .sub

private def cost : ℕ → ℕ
  | 0 => 1
  | k + 1 => 7 * cost k + 18 * 4 ^ k

private def Index : ℕ → Type
  | 0 => Unit
  | k + 1 => Index k ⊕ Index k

private instance indexFintype : (k : ℕ) → Fintype (Index k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => @instFintypeSum _ _ (indexFintype k) (indexFintype k)

private theorem index_card (k : ℕ) : Fintype.card (Index k) = 2 ^ k := by
  induction k with
  | zero => exact Fintype.card_unit
  | succ k ih =>
    change Fintype.card (Index k ⊕ Index k) = _
    rw [Fintype.card_sum, ih, pow_succ]
    omega

omit [Field F] in
private theorem entries_fromBlocks {J : Type} (a b c d : Matrix J J (Value I F))
    {s : Set (Value I F)} (ha : entries a ⊆ s) (hb : entries b ⊆ s)
    (hc : entries c ⊆ s) (hd : entries d ⊆ s) :
    entries (Matrix.fromBlocks a b c d) ⊆ s := by
  rintro _ ⟨⟨i, j⟩, rfl⟩
  cases i <;> cases j
  · exact ha (entry a _ _)
  · exact hb (entry b _ _)
  · exact hc (entry c _ _)
  · exact hd (entry d _ _)

private theorem builds_dyadic_product (k : ℕ) (A B : Matrix (Index k) (Index k) (Value I F)) :
    Builds (entries A ∪ entries B) (cost k) (entries (A * B)) := by
  classical
  induction k with
  | zero =>
    let u : Index 0 := ()
    have h := one_gate .mul (Set.mem_union_left (entries B) (entry A u u))
      (Set.mem_union_right (entries A) (entry B u u))
    apply weaken h (by rfl)
    rintro _ ⟨⟨⟨⟩, ⟨⟩⟩, rfl⟩
    change (∑ i : Unit, A () i * B i ()) = A () () * B () ()
    simp
  | succ k ih =>
    change Matrix (Index k ⊕ Index k) (Index k ⊕ Index k) (Value I F) at A B
    let a := A.toBlocks₁₁
    let b := A.toBlocks₁₂
    let c := A.toBlocks₂₁
    let d := A.toBlocks₂₂
    let e := B.toBlocks₁₁
    let f := B.toBlocks₁₂
    let g := B.toBlocks₂₁
    let h := B.toBlocks₂₂
    let s := entries A ∪ entries B
    have left (r t : Index k → Index (k + 1)) :
        Builds s 0 (entries (A.submatrix r t)) := by
      apply free
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact Or.inl (entry A (r i) (t j))
    have right (r t : Index k → Index (k + 1)) :
        Builds s 0 (entries (B.submatrix r t)) := by
      apply free
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact Or.inr (entry B (r i) (t j))
    have ha : Builds s 0 (entries a) := left Sum.inl Sum.inl
    have hb : Builds s 0 (entries b) := left Sum.inl Sum.inr
    have hc : Builds s 0 (entries c) := left Sum.inr Sum.inl
    have hd : Builds s 0 (entries d) := left Sum.inr Sum.inr
    have he : Builds s 0 (entries e) := right Sum.inl Sum.inl
    have hf : Builds s 0 (entries f) := right Sum.inl Sum.inr
    have hg : Builds s 0 (entries g) := right Sum.inr Sum.inl
    have hh : Builds s 0 (entries h) := right Sum.inr Sum.inr
    let P : Fin 7 → Matrix (Index k) (Index k) (Value I F) :=
      ![(a + d) * (e + h), (c + d) * e, a * (f - h), d * (g - e), (a + b) * h,
        (c - a) * (e + f), (b - d) * (g + h)]
    have area : Fintype.card (Index k) ^ 2 = 4 ^ k := by
      rw [sq, index_card, ← mul_pow]
      rfl
    -- Ten block operations prepare the inputs to the seven products.
    let prep : Fin 7 → ℕ := ![2, 1, 1, 1, 1, 2, 2]
    have product {X Y : Matrix (Index k) (Index k) (Value I F)} {x y t : ℕ}
        (hx : Builds s x (entries X)) (hy : Builds s y (entries Y))
        (hxy : x + y ≤ t) :
        Builds s (t + cost k) (entries (X * Y)) :=
      weaken (seq (both hx hy) (ih X Y)) (by omega) Set.Subset.rfl
    have products (i : Fin 7) : Builds s (prep i * 4 ^ k + cost k) (entries (P i)) := by
      fin_cases i <;> dsimp [prep]
      · exact product (add_blocks ha hd) (add_blocks he hh) (by omega)
      · exact product (add_blocks hc hd) he (by omega)
      · exact product ha (sub_blocks hf hh) (by omega)
      · exact product hd (sub_blocks hg he) (by omega)
      · exact product (add_blocks ha hb) hh (by omega)
      · exact product (sub_blocks hc ha) (add_blocks he hf) (by omega)
      · exact product (sub_blocks hb hd) (add_blocks hg hh) (by omega)
    -- Eight more block operations assemble the quadrants from the seven stored products.
    have readP (i : Fin 7) : Builds (⋃ j, entries (P j)) 0 (entries (P i)) :=
      free (Set.subset_iUnion (fun j => entries (P j)) i)
    have q₁₁ := add_blocks (sub_blocks (add_blocks (readP 0) (readP 3)) (readP 4)) (readP 6)
    have q₁₂ := add_blocks (readP 2) (readP 4)
    have q₂₁ := add_blocks (readP 1) (readP 3)
    have q₂₂ := add_blocks (add_blocks (sub_blocks (readP 0) (readP 1)) (readP 2)) (readP 5)
    apply weaken (seq (family products) (both q₁₁ (both q₁₂ (both q₂₁ q₂₂))))
    · simp [Fin.sum_univ_succ, prep, area, cost]
      omega
    · have mulBlocks : A * B = Matrix.fromBlocks
          (P 0 + P 3 - P 4 + P 6) (P 2 + P 4) (P 1 + P 3) (P 0 - P 1 + P 2 + P 5) := by
        conv_lhs => rw [← Matrix.fromBlocks_toBlocks A, ← Matrix.fromBlocks_toBlocks B,
          Matrix.fromBlocks_multiply]
        congr 1 <;> dsimp [P, a, b, c, d, e, f, g, h] <;> noncomm_ring
      change entries (A * B) ⊆ _
      rw [mulBlocks]
      apply entries_fromBlocks <;> intro z hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr (Or.inl hz))
      · exact Or.inr (Or.inr (Or.inr hz))

omit [Field F] in
private theorem entries_reindex {J K : Type} (A : Matrix J J (Value I F)) (e : K ≃ J) :
    entries (A.submatrix e e) = entries A := by
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    exact entry A (e i) (e j)
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    exact ⟨(e.symm i, e.symm j), by simp⟩

private theorem builds_product_of_card {J : Type} [Fintype J] (k : ℕ) (h : Fintype.card J = 2 ^ k)
    (A B : Matrix J J (Value I F)) : Builds (entries A ∪ entries B) (cost k) (entries (A * B)) := by
  let e : Index k ≃ J := Fintype.equivOfCardEq ((index_card k).trans h.symm)
  simpa only [Matrix.submatrix_mul_equiv, entries_reindex] using
    builds_dyadic_product k (A.submatrix e e) (B.submatrix e e)

-- Choose the witnessing gate at each position and verify the circuit's recursive evaluator.
private theorem to_circuit {O : Type} (p : Tape I F) (out : O → Value I F)
    (hout : ∀ o, out o ∈ wires p) :
    ∃ c : ArithmeticCircuit F I O, c.size = p.size ∧ ∀ x o, c.evaluate x o = out o x := by
  choose gates hg using p.valid
  choose outputs ho using hout
  let c : ArithmeticCircuit F I O := ⟨p.size, fun i => gates i i.isLt, outputs⟩
  refine ⟨c, rfl, fun x o => ?_⟩
  have node (i : ℕ) (hi : i < p.size) : c.evaluateNode x ⟨i, hi⟩ = p.value i x := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      rw [ArithmeticCircuit.evaluateNode]
      exact (congrArg ((gates i hi).evaluate x)
        (funext fun j => ih j j.isLt (j.isLt.trans hi))).trans (hg i hi x)
  exact (congrArg ((outputs o).evaluate x) (funext fun j => node j j.isLt)).trans (ho o x)

private def padded {n : ℕ} (m : ℕ) (A : Matrix (Fin n) (Fin n) (Value I F)) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) (Value I F) := Matrix.fromBlocks A 0 0 0

private theorem padded_wires {n : ℕ} (m : ℕ) (p : Tape I F) (A : Matrix (Fin n) (Fin n) (Value I F))
    (ha : ∀ i j, A i j ∈ wires p) : entries (padded m A) ⊆ wires p := by
  rintro _ ⟨⟨i, j⟩, rfl⟩
  cases i <;> cases j
  · exact ha _ _
  all_goals exact wires_const p 0

private theorem padded_circuit (F : Type u) [Field F] (n k : ℕ) (hn : n ≤ 2 ^ k) :
    ∃ c : MatrixArithmeticCircuit F n n n, IsMatrixMultiplication c ∧ c.size ≤ cost k := by
  let I := (Fin n × Fin n) ⊕ (Fin n × Fin n)
  let L : Matrix (Fin n) (Fin n) (Value I F) := .of fun i j x => x (.inl (i, j))
  let R : Matrix (Fin n) (Fin n) (Value I F) := .of fun i j x => x (.inr (i, j))
  let m := 2 ^ k - n
  have hd : Fintype.card (Fin n ⊕ Fin m) = 2 ^ k := by simp [m, hn]
  let empty : Tape I F := ⟨0, 0, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  have start := Set.union_subset
    (padded_wires m empty L fun i j => wires_input empty (.inl (i, j)))
    (padded_wires m empty R fun i j => wires_input empty (.inr (i, j)))
  obtain ⟨p, hp, _, hout⟩ := builds_product_of_card k hd (padded m L) (padded m R) empty start
  have out (ij : Fin n × Fin n) : (L * R) ij.1 ij.2 ∈ wires p := by
    have h := hout (entry (padded m L * padded m R) (.inl ij.1) (.inl ij.2))
    simpa [padded, Matrix.fromBlocks_multiply] using h
  obtain ⟨c, hs, hc⟩ := to_circuit p _ out
  refine ⟨c, ?_, hs.le.trans (by simpa [empty] using hp)⟩
  intro A B i j
  simpa [L, R, Matrix.mul_apply, Finset.sum_apply, matrixInput] using hc (matrixInput A B) (i, j)

private theorem cost_bound (k : ℕ) : cost k ≤ 7 * 7 ^ k := by
  suffices cost k + 6 * 4 ^ k ≤ 7 * 7 ^ k by omega
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [cost, pow_succ]
    omega

/-- **Strassen's 1969 bound on the matrix multiplication exponent.** For every field $F$, the
square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le \log_2 7$.

Source: C15a [S1969], Strassen's `log₂ 7` bound. -/
public theorem strassen1969Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (Real.log 7 / Real.log 2) := by
  intro F _
  let w := Real.logb 2 7
  have hw : 0 ≤ w := div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))
  apply rectangularCircuitExponent_le_of_admissible
  refine ⟨by norm_num, hw, fun ε hε => ⟨49, by norm_num, 1, by norm_num, ?_⟩⟩
  intro n hn
  rw [MatrixMultiplicationExponent.rectangularInnerDimension_one]
  let k := Nat.log 2 n
  obtain ⟨c, hc, hs⟩ := padded_circuit F n (k + 1) (Nat.lt_pow_succ_log_self (by decide) n).le
  refine ⟨c, hc, ?_⟩
  have hn' : (2 : ℝ) ^ k ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hpow : (2 : ℝ) ^ w = 7 := Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have hseven : (7 : ℝ) ^ k ≤ (n : ℝ) ^ w := calc
    (7 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ w := by
      rw [← hpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    _ ≤ (n : ℝ) ^ w := Real.rpow_le_rpow (by positivity) hn' hw
  have hsize : (c.size : ℝ) ≤ 7 * (7 : ℝ) ^ (k + 1) := by
    exact_mod_cast hs.trans (cost_bound _)
  have hε' : (n : ℝ) ^ w ≤ (n : ℝ) ^ (w + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  rw [pow_succ] at hsize
  change (c.size : ℝ) ≤ 49 * (n : ℝ) ^ (w + ε)
  linarith [hseven.trans hε']

end Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted
