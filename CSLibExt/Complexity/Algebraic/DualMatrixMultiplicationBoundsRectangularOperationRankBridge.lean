/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

set_option autoImplicit false

universe u v w

namespace Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted

open Cslib.Complexity.Algebraic MatrixMultiplicationExponent Filter

private noncomputable def operandPolynomial {F : Type u} [Field F] {A : Type v} {n : ℕ}
    (nodes : Fin n → MvPolynomial A F) : ArithmeticOperand F A n → MvPolynomial A F
  | .constant x => MvPolynomial.C x
  | .input a => MvPolynomial.X a
  | .node i => nodes i

private noncomputable def gatePolynomial {F : Type u} [Field F] {A : Type v} {n : ℕ}
    (nodes : Fin n → MvPolynomial A F) : ArithmeticGate F A n → MvPolynomial A F
  | .add a b => operandPolynomial nodes a + operandPolynomial nodes b
  | .sub a b => operandPolynomial nodes a - operandPolynomial nodes b
  | .mul a b => operandPolynomial nodes a * operandPolynomial nodes b

private noncomputable def nodePolynomial {F : Type u} [Field F] {A : Type v} {B : Type w}
    (c : ArithmeticCircuit F A B) (i : Fin c.size) : MvPolynomial A F :=
  gatePolynomial (fun j => nodePolynomial c ⟨j.val, j.isLt.trans i.isLt⟩) (c.gate i)
termination_by i.val
decreasing_by exact j.isLt

private noncomputable def outputPolynomial {F : Type u} [Field F] {A : Type v} {B : Type w}
    (c : ArithmeticCircuit F A B) (b : B) : MvPolynomial A F :=
  operandPolynomial (nodePolynomial c) (c.output b)

private theorem eval_operandPolynomial {F : Type u} [Field F] {A : Type v} {n : ℕ}
    (nodes : Fin n → MvPolynomial A F) (x : A → F) (o : ArithmeticOperand F A n) :
    MvPolynomial.eval x (operandPolynomial nodes o) =
      o.evaluate x (fun i => MvPolynomial.eval x (nodes i)) := by
  cases o <;> simp [operandPolynomial, ArithmeticOperand.evaluate]

private theorem eval_gatePolynomial {F : Type u} [Field F] {A : Type v} {n : ℕ}
    (nodes : Fin n → MvPolynomial A F) (x : A → F) (g : ArithmeticGate F A n) :
    MvPolynomial.eval x (gatePolynomial nodes g) =
      g.evaluate x (fun i => MvPolynomial.eval x (nodes i)) := by
  cases g <;> simp [gatePolynomial, ArithmeticGate.evaluate, eval_operandPolynomial]

private theorem eval_nodePolynomial {F : Type u} [Field F] {A : Type v} {B : Type w}
    (c : ArithmeticCircuit F A B) (x : A → F) (i : Fin c.size) :
    MvPolynomial.eval x (nodePolynomial c i) = c.evaluateNode x i := by
  rw [nodePolynomial, eval_gatePolynomial, ArithmeticCircuit.evaluateNode.eq_1]
  apply congrArg (fun vals => (c.gate i).evaluate x vals)
  funext j
  exact eval_nodePolynomial c x ⟨j.val, j.isLt.trans i.isLt⟩
termination_by i.val
decreasing_by exact j.isLt

private theorem eval_outputPolynomial {F : Type u} [Field F] {A : Type v} {B : Type w}
    (c : ArithmeticCircuit F A B) (x : A → F) (b : B) :
    MvPolynomial.eval x (outputPolynomial c b) = c.evaluate x b := by
  simp [outputPolynomial, eval_operandPolynomial, eval_nodePolynomial,
    ArithmeticCircuit.evaluate]

private theorem outputPolynomial_eq_mul {F : Type u} [Field F] [Infinite F]
    {m r n : ℕ} {c : MatrixArithmeticCircuit F m r n} (hc : IsMatrixMultiplication c)
    (i : Fin m) (l : Fin n) :
    outputPolynomial c (i, l) =
      ∑ j : Fin r, MvPolynomial.X (.inl (i, j)) * MvPolynomial.X (.inr (j, l)) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_outputPolynomial]
  let A : Matrix (Fin m) (Fin r) F := fun i j => x (.inl (i, j))
  let B : Matrix (Fin r) (Fin n) F := fun j l => x (.inr (j, l))
  have hx : matrixInput A B = x := by
    funext a
    cases a <;> rfl
  rw [← hx, hc A B]
  rw [Matrix.mul_apply]
  simp [A, B, matrixInput]

private noncomputable def derivativeAtZero {F : Type u} [Field F] {A : Type v}
    (a : A) (p : MvPolynomial A F) : F :=
  MvPolynomial.eval (fun _ => 0) (MvPolynomial.pderiv a p)

private noncomputable def mixedAtZero {F : Type u} [Field F] {A : Type v}
    (a b : A) (p : MvPolynomial A F) : F :=
  derivativeAtZero b (MvPolynomial.pderiv a p)

private theorem mixedAtZero_mul {F : Type u} [Field F] {A : Type v}
    (a b : A) (p q : MvPolynomial A F) :
    mixedAtZero a b (p * q) =
      mixedAtZero a b p * MvPolynomial.eval (fun _ => 0) q +
      derivativeAtZero a p * derivativeAtZero b q +
      derivativeAtZero b p * derivativeAtZero a q +
      MvPolynomial.eval (fun _ => 0) p * mixedAtZero a b q := by
  simp [mixedAtZero, derivativeAtZero]
  ring

private theorem mixedAtZero_output {F : Type u} [Field F] [Infinite F]
    {m r n : ℕ} {c : MatrixArithmeticCircuit F m r n} (hc : IsMatrixMultiplication c)
    (a : Fin m × Fin r) (b : Fin r × Fin n) (d : Fin n × Fin m) :
    mixedAtZero (.inl a) (.inr b) (outputPolynomial c (d.2, d.1)) =
      matrixMultiplicationTensor F m r n a b d := by
  classical
  rw [outputPolynomial_eq_mul hc]
  by_cases h : d.2 = a.1 <;>
    simp [mixedAtZero, derivativeAtZero, MvPolynomial.pderiv_X,
      matrixMultiplicationTensor, Pi.single_apply, Prod.ext_iff, apply_ite, h, eq_comm]
  simp_all [eq_comm]

private noncomputable def mixedMatrix {F : Type u} [Field F] {A B : Type v}
    (p : MvPolynomial (A ⊕ B) F) : A → B → F :=
  fun a b => mixedAtZero (.inl a) (.inr b) p

private theorem mixedMatrix_add {F : Type u} [Field F] {A B : Type v}
    (p q : MvPolynomial (A ⊕ B) F) : mixedMatrix (p + q) = mixedMatrix p + mixedMatrix q := by
  funext a b
  simp [mixedMatrix, mixedAtZero, derivativeAtZero]

private theorem mixedMatrix_sub {F : Type u} [Field F] {A B : Type v}
    (p q : MvPolynomial (A ⊕ B) F) : mixedMatrix (p - q) = mixedMatrix p - mixedMatrix q := by
  funext a b
  simp [mixedMatrix, mixedAtZero, derivativeAtZero]

private theorem mixedMatrix_mul {F : Type u} [Field F] {A B : Type v}
    (p q : MvPolynomial (A ⊕ B) F) :
    mixedMatrix (p * q) =
      MvPolynomial.eval (fun _ => 0) q • mixedMatrix p +
      MvPolynomial.eval (fun _ => 0) p • mixedMatrix q +
      (fun a b => derivativeAtZero (.inl a) p * derivativeAtZero (.inr b) q) +
      (fun a b => derivativeAtZero (.inl a) q * derivativeAtZero (.inr b) p) := by
  funext a b
  simp only [mixedMatrix, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mixedAtZero_mul]
  ring

private theorem mixedMatrix_C {F : Type u} [Field F] {A B : Type v} (x : F) :
    mixedMatrix (A := A) (B := B) (MvPolynomial.C x) = 0 := by
  funext a b
  simp [mixedMatrix, mixedAtZero, derivativeAtZero]

private theorem mixedMatrix_X {F : Type u} [Field F] {A B : Type v} (x : A ⊕ B) :
    mixedMatrix (MvPolynomial.X x : MvPolynomial (A ⊕ B) F) = 0 := by
  classical
  funext a b
  simp [mixedMatrix, mixedAtZero, derivativeAtZero, MvPolynomial.pderiv_X,
    Pi.single_apply, apply_ite]

private noncomputable def sourceFactors {F : Type u} [Field F] {A B : Type v} {C : Type w}
    (c : ArithmeticCircuit F (A ⊕ B) C) (t : Fin c.size × Bool) :
    (A → F) × (B → F) :=
  match c.gate t.1 with
  | .mul p q =>
    let nodes := fun j => nodePolynomial c ⟨j.val, j.isLt.trans t.1.isLt⟩
    let pp := operandPolynomial nodes p
    let qq := operandPolynomial nodes q
    if t.2 then
      (fun a => derivativeAtZero (.inl a) qq, fun b => derivativeAtZero (.inr b) pp)
    else
      (fun a => derivativeAtZero (.inl a) pp, fun b => derivativeAtZero (.inr b) qq)
  | _ => (0, 0)

private noncomputable def sourceMatrix {F : Type u} [Field F] {A B : Type v} {C : Type w}
    (c : ArithmeticCircuit F (A ⊕ B) C) (t : Fin c.size × Bool) : A → B → F :=
  fun a b => (sourceFactors c t).1 a * (sourceFactors c t).2 b

private theorem operand_mixed_mem {F : Type u} [Field F] {A B : Type v} {n : ℕ}
    (nodes : Fin n → MvPolynomial (A ⊕ B) F) (S : Submodule F (A → B → F))
    (hn : ∀ i, mixedMatrix (nodes i) ∈ S) (o : ArithmeticOperand F (A ⊕ B) n) :
    mixedMatrix (operandPolynomial nodes o) ∈ S := by
  cases o with
  | constant x => simpa only [operandPolynomial, mixedMatrix_C] using S.zero_mem
  | input a => simpa only [operandPolynomial, mixedMatrix_X] using S.zero_mem
  | node i => exact hn i

private theorem node_mixed_mem {F : Type u} [Field F] {A B : Type v} {C : Type w}
    (c : ArithmeticCircuit F (A ⊕ B) C) (i : Fin c.size) :
    mixedMatrix (nodePolynomial c i) ∈ Submodule.span F (Set.range (sourceMatrix c)) := by
  let S := Submodule.span F (Set.range (sourceMatrix c))
  let nodes := fun j : Fin i.val => nodePolynomial c ⟨j.val, j.isLt.trans i.isLt⟩
  have hn : ∀ j, mixedMatrix (nodes j) ∈ S :=
    fun j => node_mixed_mem c ⟨j.val, j.isLt.trans i.isLt⟩
  have ho := operand_mixed_mem nodes S hn
  rw [nodePolynomial]
  change mixedMatrix (gatePolynomial nodes (c.gate i)) ∈ S
  cases hg : c.gate i with
  | add p q =>
    rw [gatePolynomial, mixedMatrix_add]
    exact S.add_mem (ho p) (ho q)
  | sub p q =>
    rw [gatePolynomial, mixedMatrix_sub]
    exact S.sub_mem (ho p) (ho q)
  | mul p q =>
    have hfalse : sourceMatrix c (i, false) ∈ S :=
      Submodule.subset_span (Set.mem_range_self (i, false))
    have htrue : sourceMatrix c (i, true) ∈ S :=
      Submodule.subset_span (Set.mem_range_self (i, true))
    unfold sourceMatrix sourceFactors at hfalse htrue
    simp only [hg, Bool.false_eq_true, ↓reduceIte] at hfalse htrue
    rw [gatePolynomial, mixedMatrix_mul]
    exact S.add_mem (S.add_mem
      (S.add_mem (S.smul_mem _ (ho p)) (S.smul_mem _ (ho q))) hfalse) htrue
termination_by i.val

private theorem output_mixed_mem {F : Type u} [Field F] {A B : Type v} {C : Type w}
    (c : ArithmeticCircuit F (A ⊕ B) C) (d : C) :
    mixedMatrix (outputPolynomial c d) ∈ Submodule.span F (Set.range (sourceMatrix c)) :=
  operand_mixed_mem (nodePolynomial c) _ (node_mixed_mem c) (c.output d)

private theorem rank_le_card_of_span {F : Type u} [Field F] {A B : Type v} {C : Type w}
    {S : Type v} [Fintype S] (left : S → A → F) (middle : S → B → F)
    (T : A → B → C → F)
    (h : ∀ d, (fun a b => T a b d) ∈
      Submodule.span F (Set.range (fun s a b => left s a * middle s b))) :
    HasTrilinearRankAtMost T (Fintype.card S) := by
  classical
  have hex : ∀ d, ∃ coefficients : S → F,
      ∑ s, coefficients s • (fun a b => left s a * middle s b) = (fun a b => T a b d) :=
    fun d => (Submodule.mem_span_range_iff_exists_fun F).mp (h d)
  choose coefficients hcoeff using hex
  let terms : S → RankOneTrilinearTerm F A B C :=
    fun s => ⟨left s, middle s, fun d => coefficients d s⟩
  refine ⟨List.ofFn (fun i => terms ((Fintype.equivFin S).symm i)), by simp, ?_⟩
  intro a b d
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [Equiv.sum_comp (Fintype.equivFin S).symm (fun s => (terms s).eval a b d)]
  have he := congrArg (fun M => M a b) (hcoeff d)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro s _
  simp only [terms, RankOneTrilinearTerm.eval]
  ring

private theorem circuit_rank_le_twice_size {F : Type u} [Field F] [Infinite F]
    {m r n : ℕ} {c : MatrixArithmeticCircuit F m r n} (hc : IsMatrixMultiplication c) :
    HasTrilinearRankAtMost (matrixMultiplicationTensor F m r n) (2 * c.size) := by
  have h := rank_le_card_of_span
    (fun t => (sourceFactors c t).1) (fun t => (sourceFactors c t).2)
    (matrixMultiplicationTensor F m r n) (fun d => ?_)
  · simpa [Fintype.card_prod, Nat.mul_comm] using h
  · have hd := output_mixed_mem c (d.2, d.1)
    have he : (fun a b => matrixMultiplicationTensor F m r n a b d) =
        mixedMatrix (outputPolynomial c (d.2, d.1)) := by
      funext a b
      exact (mixedAtZero_output hc a b d).symm
    rw [he]
    exact hd

private theorem circuit_admissible_rank {F : Type u} [Field F] [Infinite F]
    {k w : ℝ} (h : HasRectangularCircuitExponent F k w) :
    HasRectangularMatrixMultiplicationRankExponent F k w := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro ε hε
  obtain ⟨C, hC, N, hN, hb⟩ := h.2.2 ε hε
  refine ⟨2 * C, by positivity, N, hN, ?_⟩
  intro n hn
  obtain ⟨c, hc, hs⟩ := hb n hn
  refine ⟨2 * c.size, circuit_rank_le_twice_size hc, ?_⟩
  change (c.size : ℝ) ≤ C * Real.rpow (n : ℝ) (w + ε) at hs
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
    mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 2 by norm_num)

private theorem rank_exponent_le_circuit {F : Type u} [Field F] [Infinite F] (k : ℝ) :
    rectangularMatrixMultiplicationExponent F k ≤ rectangularCircuitExponent F k := by
  apply le_rectangularCircuitExponent F
  intro w hw
  exact sInf_le ⟨w, rfl, circuit_admissible_rank hw⟩

private theorem indexed_rank {F : Type u} [Field F] {m r n R : ℕ}
    (h : HasTrilinearRankAtMost (matrixMultiplicationTensor F m r n) R) :
    ∃ L : ℕ, L ≤ R ∧ ∃ terms : Fin L →
      RankOneTrilinearTerm F (Fin m × Fin r) (Fin r × Fin n) (Fin n × Fin m),
      ∀ a b d, matrixMultiplicationTensor F m r n a b d =
        ∑ s, (terms s).eval a b d := by
  obtain ⟨terms, hlen, he⟩ := h
  refine ⟨terms.length, hlen, terms.get, ?_⟩
  intro a b d
  rw [he]
  conv_lhs => rw [← List.ofFn_get terms]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]

private theorem decomposition_mul {F : Type u} [Field F] {m r n L : ℕ}
    (terms : Fin L →
      RankOneTrilinearTerm F (Fin m × Fin r) (Fin r × Fin n) (Fin n × Fin m))
    (ht : ∀ a b d, matrixMultiplicationTensor F m r n a b d =
      ∑ s, (terms s).eval a b d)
    (A : Matrix (Fin m) (Fin r) F) (B : Matrix (Fin r) (Fin n) F)
    (i : Fin m) (l : Fin n) :
    ∑ s, (∑ a, (terms s).left a * A a.1 a.2) *
      (∑ b, (terms s).middle b * B b.1 b.2) * (terms s).right (l, i) =
        (A * B) i l := by
  rw [← matrixMultiplicationTensorContraction_eq_mul F A B i l]
  unfold matrixMultiplicationTensorContraction
  simp_rw [ht, RankOneTrilinearTerm.eval, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem decomposition_input_lower {F : Type u} [Field F] {m r n L : ℕ}
    (terms : Fin L →
      RankOneTrilinearTerm F (Fin m × Fin r) (Fin r × Fin n) (Fin n × Fin m))
    (ht : ∀ a b d, matrixMultiplicationTensor F m r n a b d =
      ∑ s, (terms s).eval a b d) (l : Fin n) : m * r ≤ L := by
  classical
  let U : Matrix (Fin m × Fin r) (Fin L) F := fun a s => (terms s).left a
  let V : Matrix (Fin L) (Fin m × Fin r) F :=
    fun s a => (terms s).middle (a.2, l) * (terms s).right (l, a.1)
  have he : U * V = 1 := by
    ext a b
    rw [Matrix.mul_apply]
    have hh := ht a (b.2, l) (l, b.1)
    simp only [RankOneTrilinearTerm.eval, mul_assoc] at hh
    rw [← hh]
    simp [matrixMultiplicationTensor, Matrix.one_apply, Prod.ext_iff, eq_comm, and_comm]
  have hr := (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)
  rw [he, Matrix.rank_one] at hr
  simpa using hr

private theorem decomposition_output_lower {F : Type u} [Field F] {m r n L : ℕ}
    (terms : Fin L →
      RankOneTrilinearTerm F (Fin m × Fin r) (Fin r × Fin n) (Fin n × Fin m))
    (ht : ∀ a b d, matrixMultiplicationTensor F m r n a b d =
      ∑ s, (terms s).eval a b d) (j : Fin r) : m * n ≤ L := by
  classical
  let U : Matrix (Fin m × Fin n) (Fin L) F := fun a s => (terms s).right (a.2, a.1)
  let V : Matrix (Fin L) (Fin m × Fin n) F :=
    fun s a => (terms s).left (a.1, j) * (terms s).middle (j, a.2)
  have he : U * V = 1 := by
    ext a b
    rw [Matrix.mul_apply]
    have hh := ht (b.1, j) (j, b.2) (a.2, a.1)
    have heq : (∑ s, (terms s).right (a.2, a.1) *
        ((terms s).left (b.1, j) * (terms s).middle (j, b.2))) =
        matrixMultiplicationTensor F m r n (b.1, j) (j, b.2) (a.2, a.1) := by
      rw [hh]
      apply Finset.sum_congr rfl
      intro s _
      simp only [RankOneTrilinearTerm.eval]
      ring
    change (∑ s, (terms s).right (a.2, a.1) *
      ((terms s).left (b.1, j) * (terms s).middle (j, b.2))) = _
    rw [heq]
    simp [matrixMultiplicationTensor, Matrix.one_apply, Prod.ext_iff, eq_comm, and_comm]
  have hr := (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)
  rw [he, Matrix.rank_one] at hr
  simpa using hr

private abbrev Value (I : Type) (F : Type u) := (I → F) → F

private structure Tape (I : Type) (F : Type u) [Field F] where
  size : ℕ
  value : ℕ → Value I F
  valid (i : ℕ) (hi : i < size) : ∃ g : ArithmeticGate F I i,
    ∀ x, g.evaluate x (fun j => value j x) = value i x

private def wires {F : Type u} [Field F] {I : Type} (p : Tape I F) : Set (Value I F) :=
  {f | ∃ a : ArithmeticOperand F I p.size, ∀ x, a.evaluate x (fun j => p.value j x) = f x}

private theorem wires_node {F : Type u} [Field F] {I : Type} (p : Tape I F) {i : ℕ}
    (hi : i < p.size) :
    p.value i ∈ wires p := ⟨.node ⟨i, hi⟩, fun _ => rfl⟩

private theorem wires_const {F : Type u} [Field F] {I : Type} (p : Tape I F) (a : F) :
    (fun _ => a) ∈ wires p :=
  ⟨.constant a, fun _ => rfl⟩

private theorem wires_input {F : Type u} [Field F] {I : Type} (p : Tape I F) (i : I) :
    (fun x => x i) ∈ wires p :=
  ⟨.input i, fun _ => rfl⟩

private theorem append_gate {F : Type u} [Field F] {I : Type} (p : Tape I F)
    (g : ArithmeticGate F I p.size) (f : Value I F)
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

private def Builds {F : Type u} [Field F] {I : Type} (s : Set (Value I F)) (n : ℕ)
    (t : Set (Value I F)) : Prop :=
  ∀ p : Tape I F, s ⊆ wires p → ∃ q : Tape I F,
    q.size ≤ p.size + n ∧ wires p ⊆ wires q ∧ t ⊆ wires q

private theorem free {F : Type u} [Field F] {I : Type} {s t : Set (Value I F)}
    (h : t ⊆ s) : Builds s 0 t :=
  fun p hp => ⟨p, by simp, Set.Subset.rfl, h.trans hp⟩

private theorem weaken {F : Type u} [Field F] {I : Type} {s t t' : Set (Value I F)} {n m : ℕ}
    (h : Builds s n t) (hn : n ≤ m) (ht : t' ⊆ t) : Builds s m t' := by
  intro p hp
  obtain ⟨q, hq, hkeep, htq⟩ := h p hp
  exact ⟨q, by omega, hkeep, ht.trans htq⟩

private theorem seq {F : Type u} [Field F] {I : Type} {s t v : Set (Value I F)} {n m : ℕ}
    (a : Builds s n t) (b : Builds t m v) : Builds s (n + m) v := by
  intro p hp
  obtain ⟨q, hq, hpq, ht⟩ := a p hp
  obtain ⟨r, hr, hqr, hv⟩ := b q ht
  exact ⟨r, by omega, hpq.trans hqr, hv⟩

private theorem both {F : Type u} [Field F] {I : Type} {s t v : Set (Value I F)} {n m : ℕ}
    (a : Builds s n t) (b : Builds s m v) : Builds s (n + m) (t ∪ v) := by
  intro p hp
  obtain ⟨q, hq, hpq, ht⟩ := a p hp
  obtain ⟨r, hr, hqr, hv⟩ := b q (hp.trans hpq)
  exact ⟨r, by omega, hpq.trans hqr, Set.union_subset (ht.trans hqr) hv⟩

private theorem family {F : Type u} [Field F] {I : Type} {J : Type} [Fintype J]
    {s : Set (Value I F)}
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

private def Op.act {F : Type u} [Field F] {I : Type} (op : Op) (a b : Value I F) : Value I F :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

private theorem one_gate {F : Type u} [Field F] {I : Type} {s : Set (Value I F)} (op : Op)
    {a b : Value I F}
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


private theorem mono_source {F : Type u} [Field F] {I : Type}
    {s s' t : Set (Value I F)} {n : ℕ} (h : Builds s n t) (hs : s ⊆ s') :
    Builds s' n t := fun p hp => h p (hs.trans hp)

private theorem builds_constant {F : Type u} [Field F] {I : Type}
    (s : Set (Value I F)) (r : F) : Builds s 0 {fun _ => r} := by
  intro p _
  exact ⟨p, by simp, Set.Subset.rfl, Set.singleton_subset_iff.mpr (wires_const p r)⟩

private theorem builds_scale {F : Type u} [Field F] {I : Type}
    {s : Set (Value I F)} (r : F) (a : Value I F) (ha : a ∈ s) :
    Builds s 1 {r • a} := by
  intro p hp
  obtain ⟨v, hv⟩ := hp ha
  let g : ArithmeticGate F I p.size := .mul (.constant r) v
  have hg (x) : g.evaluate x (fun j => p.value j x) = (r • a) x := by
    change r * v.evaluate x (fun j => p.value j x) = r * a x
    rw [hv x]
  obtain ⟨q, hq, hkeep, hout⟩ := append_gate p g _ hg
  exact ⟨q, hq.le, hkeep, Set.singleton_subset_iff.mpr hout⟩

private theorem builds_linear {F : Type u} [Field F] {I J : Type} [Fintype J]
    {s : Set (Value I F)} (coeff : J → F) (a : J → Value I F) (ha : ∀ j, a j ∈ s) :
    Builds s (2 * Fintype.card J) {∑ j, coeff j • a j} := by
  classical
  suffices ∀ t : Finset J, Builds s (2 * t.card) {∑ j ∈ t, coeff j • a j} by
    simpa using this Finset.univ
  intro t
  induction t using Finset.induction_on with
  | empty =>
    change Builds s 0 {fun _ => (0 : F)}
    exact builds_constant s 0
  | @insert j t hj ih =>
    have hc := builds_scale (coeff j) (a j) (ha j)
    have hboth := both hc ih
    have hout := one_gate .add
      (Set.mem_union_left {∑ k ∈ t, coeff k • a k} (Set.mem_singleton (coeff j • a j)))
      (Set.mem_union_right {coeff j • a j} (Set.mem_singleton (∑ k ∈ t, coeff k • a k)))
    have hseq := seq hboth hout
    convert hseq using 1 <;> simp [Finset.sum_insert, hj, Op.act]
    omega

private def entries {F : Type u} {I J K : Type}
    (M : Matrix J K (Value I F)) : Set (Value I F) :=
  Set.range fun ij : J × K => M ij.1 ij.2

private theorem entry {F : Type u} {I J K : Type}
    (M : Matrix J K (Value I F)) (i : J) (j : K) : M i j ∈ entries M :=
  ⟨(i, j), rfl⟩

private theorem builds_linear_entries {F : Type u} [Field F] {I J K S : Type}
    [Fintype J] [Fintype K] [Fintype S] {s : Set (Value I F)}
    (coeff : J → K → S → F) (a : J → K → S → Value I F)
    (ha : ∀ j k t, a j k t ∈ s) :
    Builds s (Fintype.card J * Fintype.card K * (2 * Fintype.card S))
      (entries (fun j k => ∑ t, coeff j k t • a j k t)) := by
  have h (jk : J × K) := builds_linear (coeff jk.1 jk.2) (a jk.1 jk.2) (ha jk.1 jk.2)
  simpa [entries, Set.iUnion_singleton_eq_range, Fintype.card_prod] using family h

private def Index (q : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => Fin q × Index q t

private instance indexFintype (q : ℕ) : (t : ℕ) → Fintype (Index q t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t + 1 => @instFintypeProd _ _ (inferInstanceAs (Fintype (Fin q))) (indexFintype q t)

private theorem index_card (q t : ℕ) : Fintype.card (Index q t) = q ^ t := by
  induction t with
  | zero => exact Fintype.card_unit
  | succ t ih =>
    change Fintype.card (Fin q × Index q t) = _
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    exact Nat.mul_comm _ _

private def recursiveCost (b r R : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => R * recursiveCost b r R t +
      4 * R * (b * r) * (b * r) ^ t + 2 * R * (b * b) * (b * b) ^ t

private noncomputable def encodeLeft {F : Type u} [Field F] {I X Y : Type} {b r R : ℕ}
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (A : Matrix (Fin b × X) (Fin r × Y) (Value I F)) (s : Fin R) :
    Matrix X Y (Value I F) :=
  fun x y => ∑ a, (terms s).left a • A (a.1, x) (a.2, y)

private noncomputable def encodeRight {F : Type u} [Field F] {I X Y : Type} {b r R : ℕ}
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (B : Matrix (Fin r × Y) (Fin b × X) (Value I F)) (s : Fin R) :
    Matrix Y X (Value I F) :=
  fun y x => ∑ a, (terms s).middle a • B (a.1, y) (a.2, x)

private noncomputable def decode {F : Type u} [Field F] {I X : Type} {b r R : ℕ}
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (P : Fin R → Matrix X X (Value I F)) : Matrix (Fin b × X) (Fin b × X) (Value I F) :=
  fun ix lz => ∑ s, (terms s).right (lz.1, ix.1) • P s ix.2 lz.2

private theorem decoded_product_eq {F : Type u} [Field F] {I X Y : Type} [Fintype Y]
    {b r R : ℕ}
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (ht : ∀ a c d, matrixMultiplicationTensor F b r b a c d = ∑ s, (terms s).eval a c d)
    (A : Matrix (Fin b × X) (Fin r × Y) (Value I F))
    (B : Matrix (Fin r × Y) (Fin b × X) (Value I F)) :
    decode terms (fun s => encodeLeft terms A s * encodeRight terms B s) = A * B := by
  classical
  funext ix lz input
  simp only [decode, Matrix.mul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  let AA : Matrix (Fin b) (Fin r) F := fun i j => A (i, ix.2) (j, y) input
  let BB : Matrix (Fin r) (Fin b) F := fun j l => B (j, y) (l, lz.2) input
  have hh := decomposition_mul terms ht AA BB ix.1 lz.1
  rw [Matrix.mul_apply] at hh
  simp only [AA, BB] at hh
  simp only [encodeLeft, encodeRight, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hh]
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem builds_encode_left {F : Type u} [Field F] {I X Y : Type}
    [Fintype X] [Fintype Y] {b r R : ℕ}
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (A : Matrix (Fin b × X) (Fin r × Y) (Value I F)) (s : Fin R) :
    Builds (entries A) (Fintype.card X * Fintype.card Y * (2 * (b * r)))
      (entries (encodeLeft terms A s)) := by
  have h := builds_linear_entries (F := F) (I := I)
    (fun (_ : X) (_ : Y) a => (terms s).left a)
    (fun x y a => A (a.1, x) (a.2, y))
    (fun x y a => entry A (a.1, x) (a.2, y))
  unfold encodeLeft
  simpa only [Fintype.card_prod, Fintype.card_fin] using h

private theorem builds_encode_right {F : Type u} [Field F] {I X Y : Type}
    [Fintype X] [Fintype Y] {b r R : ℕ}
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (B : Matrix (Fin r × Y) (Fin b × X) (Value I F)) (s : Fin R) :
    Builds (entries B) (Fintype.card X * Fintype.card Y * (2 * (b * r)))
      (entries (encodeRight terms B s)) := by
  have h := builds_linear_entries (F := F) (I := I)
    (fun (_ : Y) (_ : X) a => (terms s).middle a)
    (fun y x a => B (a.1, y) (a.2, x))
    (fun y x a => entry B (a.1, y) (a.2, x))
  unfold encodeRight
  convert h using 1
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

private theorem builds_decode {F : Type u} [Field F] {I X : Type} [Fintype X]
    {b r R : ℕ}
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (P : Fin R → Matrix X X (Value I F)) :
    Builds (⋃ s, entries (P s)) (2 * R * (b * b) * Fintype.card X ^ 2)
      (entries (decode terms P)) := by
  have h := builds_linear_entries (F := F) (I := I)
    (fun (ix : Fin b × X) (lz : Fin b × X) s => (terms s).right (lz.1, ix.1))
    (fun ix lz s => P s ix.2 lz.2)
    (fun ix lz s => Set.mem_iUnion.mpr ⟨s, entry (P s) ix.2 lz.2⟩)
  unfold decode
  convert h using 1
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

private theorem builds_block_step {F : Type u} [Field F] {I X Y : Type}
    [Fintype X] [Fintype Y] {b r R cost : ℕ}
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (ht : ∀ a c d, matrixMultiplicationTensor F b r b a c d = ∑ s, (terms s).eval a c d)
    (ih : ∀ (L : Matrix X Y (Value I F)) (M : Matrix Y X (Value I F)),
      Builds (entries L ∪ entries M) cost (entries (L * M)))
    (A : Matrix (Fin b × X) (Fin r × Y) (Value I F))
    (B : Matrix (Fin r × Y) (Fin b × X) (Value I F)) :
    Builds (entries A ∪ entries B)
      (R * cost + 4 * R * (b * r) * (Fintype.card X * Fintype.card Y) +
        2 * R * (b * b) * Fintype.card X ^ 2) (entries (A * B)) := by
  classical
  let L := encodeLeft terms A
  let M := encodeRight terms B
  let P := fun s => L s * M s
  let start := entries A ∪ entries B
  let enc := (⋃ s, entries (L s)) ∪ (⋃ s, entries (M s))
  have hL (s : Fin R) : Builds start _ (entries (L s)) :=
    mono_source (builds_encode_left terms A s) Set.subset_union_left
  have hM (s : Fin R) : Builds start _ (entries (M s)) :=
    mono_source (builds_encode_right terms B s) Set.subset_union_right
  have he := both (family hL) (family hM)
  have hr (s : Fin R) : Builds enc cost (entries (P s)) := by
    apply mono_source (ih (L s) (M s))
    rintro f (hf | hf)
    · exact Or.inl (Set.mem_iUnion.mpr ⟨s, hf⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨s, hf⟩)
  have hd := builds_decode terms P
  have hall := seq he (seq (family hr) hd)
  change Builds start _ (entries (decode terms P)) at hall
  rw [show decode terms P = A * B from decoded_product_eq terms ht A B] at hall
  convert hall using 1
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ]
  ring

private theorem builds_recursive_product {F : Type u} [Field F] {I : Type}
    (b r R : ℕ)
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (ht : ∀ a c d, matrixMultiplicationTensor F b r b a c d = ∑ s, (terms s).eval a c d)
    (t : ℕ) (A : Matrix (Index b t) (Index r t) (Value I F))
    (B : Matrix (Index r t) (Index b t) (Value I F)) :
    Builds (entries A ∪ entries B) (recursiveCost b r R t) (entries (A * B)) := by
  classical
  induction t with
  | zero =>
    have h := one_gate .mul (Set.mem_union_left (entries B) (entry A () ()))
      (Set.mem_union_right (entries A) (entry B () ()))
    apply weaken h (by rfl)
    rintro _ ⟨⟨⟨⟩, ⟨⟩⟩, rfl⟩
    change (∑ j : Unit, A () j * B j ()) = A () () * B () ()
    simp
  | succ t ih =>
    have h := builds_block_step terms ht ih A B
    convert h using 1
    · rfl
    · simp only [recursiveCost, index_card, Nat.mul_pow]
      ring
    · rfl

private theorem entries_reindex {F : Type u} {I J K J' K' : Type}
    (A : Matrix J K (Value I F)) (e : J' ≃ J) (f : K' ≃ K) :
    entries (A.submatrix e f) = entries A := by
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    exact entry A (e i) (f j)
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    exact ⟨(e.symm i, f.symm j), by simp⟩

private theorem builds_product_of_card {F : Type u} [Field F] {I J K : Type}
    [Fintype J] [Fintype K] (b r R t : ℕ)
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (ht : ∀ a c d, matrixMultiplicationTensor F b r b a c d = ∑ s, (terms s).eval a c d)
    (hJ : Fintype.card J = b ^ t) (hK : Fintype.card K = r ^ t)
    (A : Matrix J K (Value I F)) (B : Matrix K J (Value I F)) :
    Builds (entries A ∪ entries B) (recursiveCost b r R t) (entries (A * B)) := by
  let e : Index b t ≃ J := Fintype.equivOfCardEq ((index_card b t).trans hJ.symm)
  let f : Index r t ≃ K := Fintype.equivOfCardEq ((index_card r t).trans hK.symm)
  simpa only [Matrix.submatrix_mul_equiv, entries_reindex] using
    builds_recursive_product b r R terms ht t (A.submatrix e f) (B.submatrix f e)

private theorem to_circuit {F : Type u} [Field F] {I O : Type}
    (p : Tape I F) (out : O → Value I F) (hout : ∀ o, out o ∈ wires p) :
    ∃ c : ArithmeticCircuit F I O, c.size = p.size ∧ ∀ x o, c.evaluate x o = out o x := by
  choose gates hg using p.valid
  choose outputs ho using hout
  let c : ArithmeticCircuit F I O := ⟨p.size, fun i => gates i i.isLt, outputs⟩
  refine ⟨c, rfl, fun x o => ?_⟩
  have node (i : ℕ) (hi : i < p.size) : c.evaluateNode x ⟨i, hi⟩ = p.value i x := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      rw [ArithmeticCircuit.evaluateNode.eq_1]
      exact (congrArg ((gates i hi).evaluate x)
        (funext fun j => ih j j.isLt (j.isLt.trans hi))).trans (hg i hi x)
  exact (congrArg ((outputs o).evaluate x) (funext fun j => node j j.isLt)).trans (ho o x)

private theorem padded_wires {F : Type u} [Field F] {I J K J' K' : Type}
    (p : Tape I F) (A : Matrix J K (Value I F)) (ha : ∀ i j, A i j ∈ wires p) :
    entries (Matrix.fromBlocks A (0 : Matrix J K' _) (0 : Matrix J' K _) 0) ⊆ wires p := by
  rintro _ ⟨⟨i, j⟩, rfl⟩
  cases i <;> cases j
  · exact ha _ _
  all_goals exact wires_const p 0

private theorem padded_circuit {F : Type u} [Field F] (b r R t n q : ℕ)
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (ht : ∀ a c d, matrixMultiplicationTensor F b r b a c d = ∑ s, (terms s).eval a c d)
    (hn : n ≤ b ^ t) (hq : q ≤ r ^ t) :
    ∃ c : MatrixArithmeticCircuit F n q n, IsMatrixMultiplication c ∧
      c.size ≤ recursiveCost b r R t := by
  let I := (Fin n × Fin q) ⊕ (Fin q × Fin n)
  let L : Matrix (Fin n) (Fin q) (Value I F) := fun i j x => x (.inl (i, j))
  let M : Matrix (Fin q) (Fin n) (Value I F) := fun j l x => x (.inr (j, l))
  let a := b ^ t - n
  let d := r ^ t - q
  let LL : Matrix (Fin n ⊕ Fin a) (Fin q ⊕ Fin d) (Value I F) := Matrix.fromBlocks L 0 0 0
  let MM : Matrix (Fin q ⊕ Fin d) (Fin n ⊕ Fin a) (Value I F) := Matrix.fromBlocks M 0 0 0
  have hJ : Fintype.card (Fin n ⊕ Fin a) = b ^ t := by simp [a, hn]
  have hK : Fintype.card (Fin q ⊕ Fin d) = r ^ t := by simp [d, hq]
  let empty : Tape I F := ⟨0, 0, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  have start : entries LL ∪ entries MM ⊆ wires empty := Set.union_subset
    (padded_wires empty L fun i j => wires_input empty (.inl (i, j)))
    (padded_wires empty M fun j l => wires_input empty (.inr (j, l)))
  obtain ⟨p, hp, _, hout⟩ := builds_product_of_card b r R t terms ht hJ hK LL MM empty start
  have out (ij : Fin n × Fin n) : (L * M) ij.1 ij.2 ∈ wires p := by
    have h := hout (entry (LL * MM) (.inl ij.1) (.inl ij.2))
    simpa [LL, MM, Matrix.fromBlocks_multiply] using h
  obtain ⟨c, hs, hc⟩ := to_circuit p _ out
  refine ⟨c, ?_, hs.le.trans (by simpa [empty] using hp)⟩
  intro A B i j
  have hh := hc (matrixInput A B) (i, j)
  rw [Matrix.mul_apply] at hh ⊢
  simpa [L, M, Finset.sum_apply, matrixInput] using hh

private theorem recursiveCost_bound (b r R t : ℕ) (hbr : b * r ≤ R) (hbb : b * b ≤ R) :
    recursiveCost b r R t ≤ (1 + 6 * R) * (t + 1) * R ^ t := by
  induction t with
  | zero => simp [recursiveCost]
  | succ t ih =>
    have hbrp : (b * r) ^ t ≤ R ^ t := Nat.pow_le_pow_left hbr t
    have hbbp : (b * b) ^ t ≤ R ^ t := Nat.pow_le_pow_left hbb t
    calc
      recursiveCost b r R (t + 1) ≤ R * ((1 + 6 * R) * (t + 1) * R ^ t) +
          4 * R * R * R ^ t + 2 * R * R * R ^ t := by
        simp only [recursiveCost]
        gcongr
      _ ≤ (1 + 6 * R) * ((t + 1) + 1) * R ^ (t + 1) := by
        calc
          _ ≤ R * ((1 + 6 * R) * (t + 1) * R ^ t) +
              4 * R * R * R ^ t + 2 * R * R * R ^ t + R * R ^ t := Nat.le_add_right _ _
          _ = _ := by rw [pow_succ]; ring

private theorem pow_rpow_comm (x p : ℝ) (d : ℕ) (hx : 0 ≤ x) :
    (x ^ p) ^ d = (x ^ d) ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm,
    Real.rpow_mul hx, Real.rpow_natCast]

private theorem inner_dimension_le_power (b r n t : ℕ) (k : ℝ) (hk : 0 ≤ k)
    (hn : n ≤ b ^ t) (hr : (b : ℝ) ^ k ≤ r) : rectangularInnerDimension n k ≤ r ^ t := by
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ k ≤ ((b ^ t : ℕ) : ℝ) ^ k :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hk
    _ = ((b : ℝ) ^ k) ^ t := by
      rw [Nat.cast_pow, pow_rpow_comm _ _ _ (Nat.cast_nonneg b)]
    _ ≤ ((r ^ t : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
      exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg b) k) hr t

private theorem linear_le_geometric (a : ℝ) (ha : 1 < a) (t : ℕ) :
    (t : ℝ) + 1 ≤ (1 + 1 / (a - 1)) * a ^ t := by
  have hd : 0 < a - 1 := by linarith
  have hp : 1 ≤ a ^ t := one_le_pow₀ ha.le
  have h := one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ a) t
  have ht : (t : ℝ) ≤ a ^ t / (a - 1) := (le_div_iff₀ hd).mpr (by linarith)
  calc
    (t : ℝ) + 1 ≤ a ^ t / (a - 1) + a ^ t := add_le_add ht hp
    _ = (1 + 1 / (a - 1)) * a ^ t := by ring

private theorem bound_from_decomposition {F : Type u} [Field F]
    (b r R : ℕ) (k p δ : ℝ) (hk : 0 ≤ k) (hp : 0 ≤ p) (hδ : 0 < δ)
    (hb : 2 ≤ b) (hbr : b * r ≤ R) (hbb : b * b ≤ R)
    (hr : (b : ℝ) ^ k ≤ r) (hR : (R : ℝ) ≤ (b : ℝ) ^ p)
    (terms : Fin R → RankOneTrilinearTerm F (Fin b × Fin r) (Fin r × Fin b) (Fin b × Fin b))
    (ht : ∀ a c d, matrixMultiplicationTensor F b r b a c d = ∑ s, (terms s).eval a c d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ c : MatrixArithmeticCircuit F n (rectangularInnerDimension n k) n,
        IsMatrixMultiplication c ∧ (c.size : ℝ) ≤ C * (n : ℝ) ^ (p + δ) := by
  let a : ℝ := (b : ℝ) ^ δ
  have ha : 1 < a := Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < b)) hδ
  let D : ℝ := 1 + 1 / (a - 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hRpos : 0 < (R : ℝ) := by
    have h : 0 < R := lt_of_lt_of_le (by nlinarith : 0 < b * b) hbb
    exact_mod_cast h
  let C : ℝ := (1 + 6 * R) * D * a * R
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn
  let d := Nat.log b n
  let t := d + 1
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnb : n ≤ b ^ t := (Nat.lt_pow_succ_log_self (by omega) n).le
  have hnr := inner_dimension_le_power b r n t k hk hnb hr
  obtain ⟨c, hc, hs⟩ := padded_circuit b r R t n (rectangularInnerDimension n k) terms ht hnb hnr
  refine ⟨c, hc, ?_⟩
  have hcost : (c.size : ℝ) ≤ (1 + 6 * (R : ℝ)) * ((t : ℝ) + 1) * (R : ℝ) ^ t := by
    exact_mod_cast hs.trans (recursiveCost_bound b r R t hbr hbb)
  have hbpow : (b : ℝ) ^ d ≤ n := by exact_mod_cast Nat.pow_log_le_self b (by omega : n ≠ 0)
  have hRp : (R : ℝ) ^ d ≤ (n : ℝ) ^ p := calc
    _ ≤ ((b : ℝ) ^ p) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg R) hR d
    _ = ((b : ℝ) ^ d) ^ p := pow_rpow_comm _ _ _ (Nat.cast_nonneg b)
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hbpow hp
  have hap : a ^ d ≤ (n : ℝ) ^ δ := calc
    _ = ((b : ℝ) ^ d) ^ δ := pow_rpow_comm _ _ _ (Nat.cast_nonneg b)
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hbpow hδ.le
  have hgeo : (t : ℝ) + 1 ≤ D * a ^ t := linear_le_geometric a ha t
  calc
    (c.size : ℝ) ≤ (1 + 6 * (R : ℝ)) * ((t : ℝ) + 1) * (R : ℝ) ^ t := hcost
    _ ≤ (1 + 6 * (R : ℝ)) * (D * a ^ t) * (R : ℝ) ^ t := by gcongr
    _ = C * ((R : ℝ) ^ d * a ^ d) := by dsimp [C, t]; rw [pow_succ, pow_succ]; ring
    _ ≤ C * ((n : ℝ) ^ p * (n : ℝ) ^ δ) := by gcongr
    _ = C * (n : ℝ) ^ (p + δ) := by rw [Real.rpow_add hnreal]

private theorem rank_admissible_circuit {F : Type u} [Field F] {k w : ℝ}
    (h : HasRectangularMatrixMultiplicationRankExponent F k w) :
    HasRectangularCircuitExponent F k w := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro ε hε
  have he : 0 < ε / 4 := by linarith
  obtain ⟨C, hC, N, hN, hbnd⟩ := h.2.2 (ε / 4) he
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (ε / 4)) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  obtain ⟨b, hbC, hbN⟩ :=
    ((htend.eventually (eventually_gt_atTop C)).and (eventually_ge_atTop (max N 2))).exists
  have hb : 2 ≤ b := (le_max_right N 2).trans hbN
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  let r := rectangularInnerDimension b k
  obtain ⟨S, hS, hSb⟩ := hbnd b ((le_max_left N 2).trans hbN)
  obtain ⟨R, hRS, terms, ht⟩ := indexed_rank hS
  have hRbound : (R : ℝ) ≤ (b : ℝ) ^ (w + ε / 2) := calc
    _ ≤ (S : ℝ) := by exact_mod_cast hRS
    _ ≤ C * (b : ℝ) ^ (w + ε / 4) := hSb
    _ ≤ (b : ℝ) ^ (ε / 4) * (b : ℝ) ^ (w + ε / 4) :=
      mul_le_mul_of_nonneg_right hbC.le (Real.rpow_nonneg hbpos.le _)
    _ = (b : ℝ) ^ (w + ε / 2) := by rw [← Real.rpow_add hbpos]; congr 1; ring
  have hbr : b * r ≤ R := decomposition_input_lower terms ht ⟨0, by omega⟩
  have hbb : b * b ≤ R := decomposition_output_lower terms ht
    ⟨0, rectangularInnerDimension_pos (by omega) k⟩
  obtain ⟨D, hD, hd⟩ := bound_from_decomposition b r R k (w + ε / 2) (ε / 2)
    h.1 (by linarith [h.2.1]) (by linarith) hb hbr hbb (Nat.le_ceil _) hRbound terms ht
  refine ⟨D, hD, 1, by norm_num, ?_⟩
  intro n hn
  have heq : (w + ε / 2) + ε / 2 = w + ε := by ring
  simpa only [heq] using hd n hn

/-- **Circuit size and tensor rank give the same rectangular exponent.** For every infinite field
$F$ and every real $k \ge 0$, the rectangular matrix multiplication exponent at aspect $k$ defined
by arithmetic-circuit size equals the one defined by tensor rank.

Source: LG2012 exact bilinear-rank characterization. -/
public theorem rectangularOperationRankBridge :
    ∀ (F : Type u) [Field F] [Infinite F] (k : ℝ), 0 ≤ k →
      rectangularCircuitExponent F k =
        MatrixMultiplicationExponent.rectangularMatrixMultiplicationExponent F k := by
  intro F _ _ k _
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨w, rfl, hw⟩
    exact rectangularCircuitExponent_le_of_admissible F (rank_admissible_circuit hw)
  · exact rank_exponent_le_circuit k

end Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted
