/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.ACGateBridge
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith

/-!
# Yao's XOR lemma

`yao_xor_lemma` bounds the agreement of a Boolean circuit with the XOR of independent copies
of a mildly hard function. The proof gives the gate-count exponent `c = 12`.

The proof approximates the signed target by a function on a finite grid in `[-1, 1]`.
Whenever a small circuit detects an error, its output moves the approximation one grid step,
decreasing the mean squared error. A circuit stores the current grid value with one wire per
level. At termination, hardness bounds the mean absolute value of the approximation, and
conditioning on one input block at a time bounds the XOR correlation.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.YaoXOR

open Cslib.Complexity.Classes

/-- **Encoded gates.** An encoded gate is a pair $(k, r)$ of a natural number $k$ (the gate kind)
and a list $r$ of natural numbers (its references), the shared (kind, references) encoding of
gates of flat Boolean circuits. -/
abbrev XORGate := ℕ × List ℕ

/-- **Gate values of an encoded circuit.** For a list $C$ of encoded gates and a list $x$ of
Booleans of length $\ell$, the gate values of $C$ on $x$ are obtained by decoding each pair of $C$
to a gate of a flat Boolean circuit on $\ell$ inputs and evaluating the decoded circuit with the
assignment that gives input $i$ the value $x_i$; the result lists the values of all gates in
order. A pair referring to an input index $i \ge \ell$ decodes to the constant false. -/
def xorCircuitEval (C : List XORGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- **Flattening blocks of bits.** For $n > 0$ and $k$ blocks $x_0, \dots, x_{k-1}$ of $n$ bits
each, the flattened string has $nk$ bits, and its bit $i$ is bit $i \bmod n$ of the block
$x_{\lfloor i/n \rfloor}$. -/
def xorFlat {n k : ℕ} (hn : 0 < n) (xs : Fin k → Fin n → Bool) : Fin (n * k) → Bool :=
  fun i => xs ⟨i.val / n, by
      rw [Nat.div_lt_iff_lt_mul hn]
      calc i.val < n * k := i.isLt
        _ = k * n := by rw [Nat.mul_comm]⟩
    ⟨i.val % n, Nat.mod_lt _ hn⟩

/-- **XOR of finitely many bits.** For $k$ bits $b_0, \dots, b_{k-1}$, their XOR is true if and
only if an odd number of the $b_i$ are true. -/
def xorFold {k : ℕ} (b : Fin k → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => b i)).card % 2 = 1)

/-- **XOR of independent copies of a function.** For natural numbers $n$ and $k$ and a Boolean
function $f$ on $n$ bits, the function $f^{\oplus k}$ takes $k$ blocks $x_0, \dots, x_{k-1}$
of $n$ bits each to $f(x_0) \oplus \cdots \oplus f(x_{k-1})$, which is true if and only if an
odd number of the values $f(x_i)$ are true. -/
def xorOf {n k : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin k → Fin n → Bool) : Bool :=
  xorFold (fun i => f (xs i))

/-- **Agreement of a circuit with a Boolean function.** Let $\alpha$ be a nonempty finite type, let
$C$ be a circuit given as a list of encoded gates, let $g$ assign a Boolean to each
$a \in \alpha$, and let $\mathrm{enc}$ encode each $a \in \alpha$ as a list of Booleans. The
agreement of $C$ with $g$ is the rational number $N / |\alpha|$, where $N$ is the number of
$a \in \alpha$ such that $C$ has at least one gate and the value of its last gate, when $C$ is
evaluated on the input list $\mathrm{enc}(a)$, equals $g(a)$. -/
noncomputable def agreement {α : Type*} [Fintype α] [Nonempty α]
    (C : List XORGate) (g : α → Bool) (enc : α → List Bool) : ℚ :=
  (Set.ncard {a | (xorCircuitEval C (enc a)).getLast? = some (g a)} : ℚ) /
    (Fintype.card α : ℚ)

private abbrev Bits (n : ℕ) := Fin n → Bool
private abbrev Program := List XORGate

private def values {n : ℕ} (P : Program) (x : Bits n) :=
  circuitEval (P.map (acGateOfPair (n := n))) x

private lemma eval_ofFn {n : ℕ} (P : Program) (x : Bits n) :
    xorCircuitEval P (List.ofFn x) = values P x := by
  unfold xorCircuitEval
  generalize h : (List.ofFn x).length = l
  have hl : l = n := h.symm.trans (List.length_ofFn (f := x))
  clear h
  subst l
  congr 1
  funext i
  simp [List.getD_eq_getElem?_getD, i.isLt]

@[local simp] private lemma values_length {n} (P : Program) (x : Bits n) :
    (values P x).length = P.length := by simp [values]

private lemma values_snoc {n} (P : Program) (g : XORGate) (x : Bits n) :
    values (P ++ [g]) x =
      values P x ++ [gateValue (values P x) x (acGateOfPair g)] := by
  simp [values, circuitEval_append_singleton]

private lemma values_prefix {n} {P Q : Program} (h : P <+: Q) (x : Bits n) :
    values P x <+: values Q x := by
  obtain ⟨T, rfl⟩ := h
  induction T using List.reverseRecOn with
  | nil => simp
  | append_singleton T g ih =>
    rw [← List.append_assoc, values_snoc]
    exact ih.trans (List.prefix_append ..)

private def Wire {n} (P : Program) (f : Bits n → Bool) : Prop :=
  ∃ i, i < P.length ∧ ∀ x, (values P x).getD i false = f x

private lemma Wire.mono {n} {P Q : Program} {f : Bits n → Bool} (h : Wire P f)
    (hPQ : P <+: Q) : Wire Q f := by
  obtain ⟨i, hi, hw⟩ := h
  refine ⟨i, lt_of_lt_of_le hi hPQ.length_le, fun x => ?_⟩
  obtain ⟨T, hT⟩ := values_prefix hPQ x
  rw [← hT, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
  exact hw x

-- The postcondition can use any earlier wire, so updates share the existing circuit.
private def Build (P : Program) (cost : ℕ) (post : Program → Prop) : Prop :=
  ∃ Q, P <+: Q ∧ Q.length ≤ P.length + cost ∧ post Q

private lemma Build.weaken {P : Program} {c d : ℕ} {A B : Program → Prop}
    (h : Build P c A) (hc : c ≤ d) (hAB : ∀ Q, P <+: Q → A Q → B Q) : Build P d B := by
  obtain ⟨Q, hp, hq, ha⟩ := h
  exact ⟨Q, hp, by omega, hAB Q hp ha⟩

private lemma Build.bind {P : Program} {c d : ℕ} {A B : Program → Prop}
    (h : Build P c A) (next : ∀ Q, P <+: Q → A Q → Build Q d B) : Build P (c + d) B := by
  obtain ⟨Q, hp, hq, ha⟩ := h
  obtain ⟨R, hr, hs, hb⟩ := next Q hp ha
  exact ⟨R, hp.trans hr, by omega, hb⟩

private abbrev Emit {n} (P : Program) (cost : ℕ) (f : Bits n → Bool) :=
  Build P cost (fun Q => Wire Q f)

private lemma emit_gate {n} (P : Program) (g : XORGate) (f : Bits n → Bool)
    (hg : ∀ x, gateValue (values P x) x (acGateOfPair g) = f x) : Emit P 1 f := by
  refine ⟨P ++ [g], List.prefix_append .., by simp, P.length, by simp, fun x => ?_⟩
  rw [values_snoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simpa using hg x

private lemma emit_const {n} (P : Program) (b : Bool) : Emit (n := n) P 1 (fun _ => b) := by
  cases b
  · exact emit_gate P (1, [0]) _ (fun _ => rfl)
  · exact emit_gate P (1, [1]) _ (fun _ => rfl)

private lemma emit_not {n} {P : Program} {f : Bits n → Bool} (h : Wire P f) :
    Emit P 1 (fun x => !(f x)) := by
  obtain ⟨i, _, hi⟩ := h
  apply emit_gate P (2, [i])
  simp [-List.getD_eq_getElem?_getD, acGateOfPair, gateValue, hi]

private lemma emit_and {n} {P : Program} {f g : Bits n → Bool} (hf : Wire P f) (hg : Wire P g) :
    Emit P 1 (fun x => f x && g x) := by
  obtain ⟨i, _, hi⟩ := hf
  obtain ⟨j, _, hj⟩ := hg
  apply emit_gate P (3, [i, j])
  simp [-List.getD_eq_getElem?_getD, acGateOfPair, gateValue, hi, hj]

private lemma emit_any {n} {P : Program} {ι : Type*} (L : List ι) {f : ι → Bits n → Bool}
    (h : ∀ j, Wire P (f j)) : Emit P 1 (fun x => L.any (fun j => f j x)) := by
  classical
  choose idx _ hv using h
  apply emit_gate P (4, L.map idx)
  simp [-List.getD_eq_getElem?_getD, acGateOfPair, gateValue, List.any_map, Function.comp_def, hv]

private lemma build_all {n} {ι : Type*} (P : Program) (d : ℕ) (L : List ι)
    (f : ι → Bits n → Bool)
    (build : ∀ Q, P <+: Q → ∀ i, Emit Q d (f i)) :
    Build P (L.length * d) (fun Q => ∀ i ∈ L, Wire Q (f i)) := by
  induction L with
  | nil => exact ⟨P, List.prefix_rfl, by simp, by simp⟩
  | cons i L ih =>
    simpa only [List.length_cons, Nat.succ_mul] using
      ih.bind (B := fun Q => ∀ j ∈ i :: L, Wire Q (f j)) (d := d) (fun Q hp hw =>
        (build Q hp i).weaken le_rfl (fun R hr hi j hj => by
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hi
          · exact (hw _ hj).mono hr))

private lemma emit_or {n} {P : Program} {f g : Bits n → Bool} (hf : Wire P f) (hg : Wire P g) :
    Emit P 1 (fun x => f x || g x) := by
  obtain ⟨i, _, hi⟩ := hf
  obtain ⟨j, _, hj⟩ := hg
  apply emit_gate P (4, [i, j])
  simp [-List.getD_eq_getElem?_getD, acGateOfPair, gateValue, hi, hj]

-- A unary encoding lets a single disjunction test membership in any set of states.
private def Readable {n N} (P : Program) (u : Bits n → Fin N) : Prop :=
  ∀ Q, P <+: Q → ∀ p : Fin N → Bool, Emit Q 1 (fun x => p (u x))

private lemma readable_of_indicators {n N} {P : Program} {u : Bits n → Fin N}
    (h : ∀ i, Wire P (fun x => decide (u x = i))) : Readable P u := by
  intro Q hp p
  let L := (List.finRange N).filter p
  have eqv (x : Bits n) : L.any (fun i => decide (u x = i)) = p (u x) := by
    apply Bool.eq_iff_iff.mpr
    simp [L]
  simpa only [eqv] using emit_any L (fun i => (h i).mono hp)

private lemma build_transition {n N} {P : Program} {u : Bits n → Fin N} (hu : Readable P u)
    {b : Bits n → Bool} (hb : Wire P b) (step : Fin N → Bool → Fin N) :
    Build P (1 + N * 5) (fun Q => Readable Q (fun x => step (u x) (b x))) := by
  apply (emit_not hb).bind
  intro R hPR hnb
  let p (i : Fin N) (x : Bits n) := decide (step (u x) (b x) = i)
  have build (Q : Program) (hr : R <+: Q) (i : Fin N) : Emit Q 5 (p i) := by
    apply (hu Q (hPR.trans hr) (fun j => decide (step j true = i))).bind (d := 4)
    intro A ha ht
    apply (hu A (hPR.trans (hr.trans ha)) (fun j => decide (step j false = i))).bind (d := 3)
    intro B hab hf
    let hQB := ha.trans hab
    apply (emit_and (hb.mono (hPR.trans (hr.trans hQB))) (ht.mono hab)).bind (d := 2)
    intro C hbc h1
    apply (emit_and (hnb.mono (hr.trans (hQB.trans hbc))) (hf.mono hbc)).bind (d := 1)
    intro D hcd h0
    have eqv (x : Bits n) :
        ((b x && decide (step (u x) true = i)) ||
          (!(b x) && decide (step (u x) false = i))) = p i x := by
      cases hx : b x <;> simp [p, hx]
    simpa only [eqv] using emit_or (h1.mono hcd) h0
  apply (build_all R 5 (List.finRange N) p build).weaken (by simp)
  intro Q _ h
  exact readable_of_indicators (fun i => h i (by simp))

-- Replace each input by a constant or an input of the new circuit. Gate indices are shifted
-- past the prefix, including forward references, which must continue to evaluate to false.
private def renameGate {m n} (r : Fin m → Bool ⊕ Fin n) (off : ℕ) : ACGate m → XORGate
  | .var i => match r i with
    | .inl b => (1, [if b then 1 else 0])
    | .inr j => (0, [j.val])
  | .const b => (1, [if b then 1 else 0])
  | .notGate i => (2, [off + i])
  | .andGate l => (3, l.map (off + ·))
  | .orGate l => (4, l.map (off + ·))
  | .modGate _ _ => (1, [0])

private lemma getD_shift (u v : List Bool) (i : ℕ) :
    (u ++ v).getD (u.length + i) false = v.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

private lemma eval_renameGate {m n} (r : Fin m → Bool ⊕ Fin n) (a : Bits n) (u v : List Bool)
    (g : ACGate m) (hg : ∀ d l, g ≠ .modGate d l) :
    gateValue (u ++ v) a (acGateOfPair (renameGate r u.length g)) =
      gateValue v (fun i => (r i).elim id a) g := by
  cases g with
  | var i =>
    cases h : r i with
    | inl b => cases b <;> simp [renameGate, h, acGateOfPair, gateValue]
    | inr j => simp [renameGate, h, acGateOfPair, gateValue, j.isLt]
  | const b => cases b <;> rfl
  | notGate i => simp [-List.getD_eq_getElem?_getD, renameGate, acGateOfPair, gateValue, getD_shift]
  | andGate l =>
    simp [-List.getD_eq_getElem?_getD, renameGate, acGateOfPair, gateValue, List.all_map,
      Function.comp_def, getD_shift]
  | orGate l =>
    simp [-List.getD_eq_getElem?_getD, renameGate, acGateOfPair, gateValue, List.any_map,
      Function.comp_def, getD_shift]
  | modGate d l => exact (hg d l rfl).elim

private lemma decode_ne_mod {m} (g : XORGate) (d : ℕ) (l : List ℕ) :
    acGateOfPair (n := m) g ≠ .modGate d l := by
  fun_cases acGateOfPair (n := m) g <;> simp_all

private lemma eval_rename {m n} (P C : Program) (r : Fin m → Bool ⊕ Fin n) (a : Bits n) :
    values (P ++ C.map (fun g => renameGate r P.length (acGateOfPair g))) a =
      values P a ++ values C (fun i => (r i).elim id a) := by
  induction C using List.reverseRecOn with
  | nil => simp [values, circuitEval]
  | append_singleton C g ih =>
    simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc, values_snoc, ih]
    rw [← values_length P a, eval_renameGate _ _ _ _ _ (decode_ne_mod _)]

private def prediction {n} (C : Program) (x : Bits n) := (values C x).getLastD false

private lemma emit_restriction {m n} (P C : Program) (hC : C ≠ []) (r : Fin m → Bool ⊕ Fin n) :
    Emit P C.length (fun a => prediction C (fun i => (r i).elim id a)) := by
  let D := C.map (fun g => renameGate r P.length (acGateOfPair g))
  have hpos : 0 < C.length := List.length_pos_iff.mpr hC
  refine ⟨P ++ D, List.prefix_append .., by simp [D], P.length + (C.length - 1), by
    simp [D]; omega, fun a => ?_⟩
  change (values (P ++ C.map _) a).getD _ false = _
  rw [eval_rename, ← values_length P a, getD_shift]
  simp [prediction, List.getLast?_eq_getElem?, values_length]

open scoped BigOperators
open Finset

private def bitSign (b : Bool) : ℚ := if b then -1 else 1

private lemma abs_bitSign (b : Bool) : |bitSign b| = 1 := by cases b <;> decide

private lemma expect_cons {α : Type*} [Fintype α] {k : ℕ} (F : (Fin (k + 1) → α) → ℚ) :
    (𝔼 xs, F xs) = 𝔼 x, 𝔼 ys, F (Fin.cons x ys) := by
  let e := (Fin.consEquiv (fun _ : Fin (k + 1) => α)).symm
  exact (Fintype.expect_equiv e F (fun p => F (Fin.cons p.1 p.2))
    (fun xs => congrArg F (e.symm_apply_apply xs).symm)).trans (by
      rw [← Finset.expect_product', Finset.univ_product_univ])

-- Peel off the first block. Replacing its sign by the model costs at most ε on each
-- section. Its mean absolute value then multiplies the remaining correlation.
private lemma correlation_bound {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ℚ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1)
    {β ε : ℚ} (hb : 0 ≤ β) (hb' : β ≤ 1) (he : 0 ≤ ε)
    (hmean : (𝔼 x, |g x|) ≤ β + ε) (k : ℕ) (D : (Fin k → α) → ℚ)
    (hD : ∀ xs, |D xs| ≤ 1)
    (hsec : ∀ (i : Fin k) (xs : Fin k → α),
      |𝔼 x, (f x - g x) * D (Function.update xs i x)| ≤ ε) :
    |𝔼 xs, D xs * ∏ i, f (xs i)| ≤ β ^ k + 2 * k * ε := by
  induction k with
  | zero =>
    simpa using (Finset.abs_expect_le univ D).trans
      ((Finset.expect_le_expect (fun xs _ => hD xs)).trans_eq (Fintype.expect_const 1))
  | succ k ih =>
    let tailProd (ys : Fin k → α) := ∏ i, f (ys i)
    have ht (ys : Fin k → α) : |tailProd ys| ≤ 1 := by
      simp only [tailProd, abs_prod]
      exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => hf _)
    have herr (ys : Fin k → α) :
        |𝔼 x, (f x - g x) * D (Fin.cons x ys)| ≤ ε := by
      obtain ⟨a⟩ := ‹Nonempty α›
      simpa [Fin.update_cons_zero] using hsec 0 (Fin.cons a ys)
    have hrest (x : α) :
        |𝔼 ys, D (Fin.cons x ys) * tailProd ys| ≤ β ^ k + 2 * k * ε := by
      apply ih _ (fun ys => hD _)
      intro i ys
      simpa [← Fin.cons_update] using hsec i.succ (Fin.cons x ys)
    let A := 𝔼 x, 𝔼 ys, ((f x - g x) * D (Fin.cons x ys)) * tailProd ys
    let B := 𝔼 x, g x * (𝔼 ys, D (Fin.cons x ys) * tailProd ys)
    have hsplit : (𝔼 xs, D xs * ∏ i, f (xs i)) = A + B := by
      rw [expect_cons]
      simp only [A, B, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.mul_expect,
        ← Finset.expect_add_distrib, tailProd]
      congr 1
      funext x
      congr 1
      funext ys
      ring
    have ha : |A| ≤ ε := by
      dsimp only [A]
      rw [Finset.expect_comm]
      simp only [← Finset.expect_mul]
      apply (abs_expect_le _ _).trans
      apply (Finset.expect_le_expect (g := fun _ => ε) _).trans_eq (Fintype.expect_const ε)
      intro ys _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (ht ys) |>.trans (herr ys)
    have hbnd : |B| ≤ (𝔼 x, |g x|) * (β ^ k + 2 * k * ε) := by
      apply (abs_expect_le _ _).trans
      rw [Finset.expect_mul]
      exact expect_le_expect fun x _ => (abs_mul _ _).le.trans
        (mul_le_mul_of_nonneg_left (hrest x) (abs_nonneg _))
    have hm1 : (𝔼 x, |g x|) ≤ 1 :=
      (expect_le_expect (fun x _ => hg x)).trans_eq (Fintype.expect_const 1)
    rw [hsplit]
    apply (abs_add_le _ _).trans
    have h1 := mul_le_mul_of_nonneg_right hmean (pow_nonneg hb k)
    have h2 := mul_le_mul_of_nonneg_right hm1 (show 0 ≤ 2 * (k : ℚ) * ε by positivity)
    have h3 := mul_le_mul_of_nonneg_right (pow_le_one₀ (n := k) hb hb') he
    rw [pow_succ]
    push_cast
    nlinarith

-- Integer scores from 0 to 2M represent the grid from -1 to 1.
private abbrev Level (M : ℕ) := Fin (2 * M + 1)

private def advance {M : ℕ} (j : Level M) (b : Bool) : Level M :=
  if b then ⟨j.val - 1, by have := j.isLt; omega⟩
  else ⟨min (j.val + 1) (2 * M), by omega⟩

private def residual {M : ℕ} (target : Bool) (j : Level M) : ℚ :=
  M * bitSign target - (j.val - (M : ℚ))

private lemma loss_step {M : ℕ} (target b : Bool) (j : Level M) :
    (residual target (advance j b)) ^ 2 ≤
      (residual target j) ^ 2 - 2 * (residual target j * bitSign b) + 1 := by
  have hj : j.val ≤ 2 * M := by have := j.isLt; omega
  cases b
  · by_cases h : j.val < 2 * M
    · simp [advance, min_eq_left (by omega : j.val + 1 ≤ 2 * M), residual, bitSign]
      ring_nf
      rfl
    · have h' : j.val = 2 * M := by omega
      cases target <;> simp [advance, h', residual, bitSign] <;> nlinarith
  · by_cases h : 1 ≤ j.val
    · simp [advance, residual, bitSign, Nat.cast_sub h]
      ring_nf
      rfl
    · have h' : j.val = 0 := by omega
      cases target <;> simp [advance, h', residual, bitSign]
      nlinarith

private def loopCost (M d : ℕ) := d + (1 + (2 * M + 1) * 5)

-- A failed test decreases the squared error by at least one. The starting error is M².
private lemma exists_model {n} (M d : ℕ) (f : Bits n → Bool) :
    ∃ (P : Program) (u : Bits n → Level M),
      P.length ≤ M ^ 2 * loopCost M d ∧ Readable P u ∧
      ∀ h : Bits n → Bool, Emit P d h →
        (𝔼 x, residual (f x) (u x) * bitSign (h x)) ≤ 1 := by
  classical
  by_contra! hbad
  let B := loopCost M d
  have iterate (t : ℕ) (ht : t ≤ M ^ 2 + 1) :
      ∃ (P : Program) (u : Bits n → Level M),
        P.length ≤ t * B ∧ Readable P u ∧
          (𝔼 x, (residual (f x) (u x)) ^ 2) ≤ (M : ℚ) ^ 2 - t := by
    induction t with
    | zero =>
      let j : Level M := ⟨M, by omega⟩
      refine ⟨[], fun _ => j, by simp, fun Q _ p => emit_const Q (p j), ?_⟩
      have h (x : Bits n) : residual (f x) j ^ 2 = (M : ℚ) ^ 2 := by
        cases hx : f x <;> simp [j, residual, bitSign]
      simp [h]
    | succ t ih =>
      obtain ⟨P, u, hP, hu, hpot⟩ := ih (by omega)
      obtain ⟨h, hem, hcorr⟩ := hbad P u (hP.trans (Nat.mul_le_mul_right _ (by omega))) hu
      obtain ⟨Q, hp, hQ, hw⟩ := hem
      obtain ⟨R, _, hR, hur⟩ := build_transition
        (P := Q) (fun S hqs => hu S (hp.trans hqs)) hw advance
      refine ⟨R, _, ?_, hur, ?_⟩
      · rw [Nat.succ_mul]
        dsimp [B, loopCost] at *
        omega
      · have he := expect_le_expect (s := univ) (fun x _ => loss_step (f x) (h x) (u x))
        simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
          Fintype.expect_const] at he
        push_cast
        linarith
  obtain ⟨P, u, _, _, hu⟩ := iterate (M ^ 2 + 1) le_rfl
  have hnonneg := expect_nonneg (s := univ) (fun x _ => sq_nonneg (residual (f x) (u x)))
  push_cast at hu
  linarith

private lemma agreement_le_one {α : Type*} [Fintype α] [Nonempty α] (C : Program)
    (f : α → Bool) (enc : α → List Bool) : agreement C f enc ≤ 1 := by
  unfold agreement
  apply (div_le_one (by exact_mod_cast Fintype.card_pos)).2
  exact_mod_cast (Set.ncard_le_card _).trans_eq Nat.card_eq_fintype_card

private lemma corr_eq_agreement {α : Type*} [Fintype α] [Nonempty α] (C : Program)
    (f h : α → Bool) (enc : α → List Bool)
    (hh : ∀ x, (xorCircuitEval C (enc x)).getLast? = some (h x)) :
    (𝔼 x, bitSign (f x) * bitSign (h x)) = 2 * agreement C f enc - 1 := by
  classical
  have eqv (x : α) :
      bitSign (f x) * bitSign (h x) = 2 * (if h x = f x then 1 else 0) - 1 := by
    cases f x <;> cases h x <;> norm_num [bitSign]
  let S := univ.filter (fun x => h x = f x)
  have hs : {x | (xorCircuitEval C (enc x)).getLast? = some (f x)} = (S : Set α) := by
    ext x
    simp [S, hh]
  simp only [eqv, expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
  simp only [agreement, hs, Set.ncard_coe_finset, Finset.expect_eq_sum_div_card, sum_boole,
    card_univ, S]

private lemma hard_wire {n s} {δ : ℚ} {f h : Bits n → Bool}
    (hard : ∀ C : Program, C.length ≤ s → agreement C f List.ofFn ≤ 1 - δ)
    {P : Program} (hs : P.length + 1 ≤ s) (hw : Wire P h) :
    (𝔼 x, bitSign (f x) * bitSign (h x)) ≤ 1 - 2 * δ := by
  obtain ⟨i, _, hi⟩ := hw
  let Q := P ++ [(4, [i])]
  have hv (x : Bits n) : (xorCircuitEval Q (List.ofFn x)).getLast? = some (h x) := by
    simp [-List.getD_eq_getElem?_getD, Q, eval_ofFn, values_snoc, acGateOfPair, gateValue, hi]
  rw [corr_eq_agreement Q f h _ hv]
  linarith [hard Q (by simpa [Q] using hs)]

private lemma bitSign_xorOf {n k} (f : Bits n → Bool) (xs : Fin k → Bits n) :
    bitSign (xorOf f xs) = ∏ i, bitSign (f (xs i)) := by
  classical
  simp only [bitSign, xorOf, xorFold, decide_eq_true_eq, Finset.prod_ite, prod_const,
    one_pow, mul_one]
  rw [neg_one_pow_eq_pow_mod_two]
  have hm := Nat.mod_lt (univ.filter (fun i => f (xs i) = true)).card (by decide : 0 < 2)
  split <;> rename_i h
  · rw [h]; norm_num
  · rw [show (univ.filter (fun i => f (xs i) = true)).card % 2 = 0 by omega]; norm_num

private lemma emit_section {n k} (hn : 0 < n) (P C : Program) (hc : C ≠ [])
    (xs : Fin k → Bits n) (i : Fin k) :
    Emit P C.length (fun a => prediction C (xorFlat hn (Function.update xs i a))) := by
  let block (v : Fin (n * k)) : Fin k :=
    ⟨v.val / n, (Nat.div_lt_iff_lt_mul hn).2 (by simp [Nat.mul_comm])⟩
  let pos (v : Fin (n * k)) : Fin n := ⟨v.val % n, Nat.mod_lt _ hn⟩
  let r (v : Fin (n * k)) : Bool ⊕ Fin n :=
    if block v = i then .inr (pos v) else .inl (xs (block v) (pos v))
  have eqv (a : Bits n) : (fun v => (r v).elim id a) = xorFlat hn (Function.update xs i a) := by
    funext v
    change (r v).elim id a = Function.update xs i a (block v) (pos v)
    by_cases heq : block v = i <;> simp [r, heq, Function.update_of_ne]
  simpa only [eqv] using emit_restriction P C hc r

private def gridValue {M : ℕ} (j : Level M) : ℚ := (j.val - (M : ℚ)) / M

private lemma grid_abs_le_one {M : ℕ} (hM : 0 < M) (j : Level M) :
    |gridValue j| ≤ 1 := by
  have hpos : (0 : ℚ) < M := by exact_mod_cast hM
  have hj : j.val ≤ 2 * M := by have := j.isLt; omega
  have hj' : (j.val : ℚ) ≤ 2 * M := by exact_mod_cast hj
  rw [gridValue, abs_le]
  constructor
  · rw [le_div_iff₀ hpos]; linarith [Nat.cast_nonneg (α := ℚ) j.val]
  · rw [div_le_iff₀ hpos]; linarith

private lemma model_error {n M d} {P : Program} {f : Bits n → Bool} {u : Bits n → Level M}
    (hM : 0 < M) (hg : ∀ h : Bits n → Bool, Emit P d h →
      (𝔼 x, residual (f x) (u x) * bitSign (h x)) ≤ 1)
    {h : Bits n → Bool} (he : Emit P d h) :
    (𝔼 x, (bitSign (f x) - gridValue (u x)) * bitSign (h x)) ≤ 1 / M := by
  have hpos : (0 : ℚ) < M := by exact_mod_cast hM
  rw [le_div_iff₀ hpos, Finset.expect_mul]
  convert hg h he using 2
  dsimp [gridValue, residual]
  field_simp

-- The sign of the grid value is a one-gate lookup. Hardness bounds its correlation with
-- the target, and the model error controls the difference from the mean absolute grid value.
private lemma model_mean {n M d s} {δ : ℚ} {f : Bits n → Bool} {P : Program}
    {u : Bits n → Level M} (hM : 0 < M) (hd : 1 ≤ d) (hP : P.length + 2 ≤ s)
    (hu : Readable P u)
    (hg : ∀ h : Bits n → Bool, Emit P d h →
      (𝔼 x, residual (f x) (u x) * bitSign (h x)) ≤ 1)
    (hard : ∀ C : Program, C.length ≤ s → agreement C f List.ofFn ≤ 1 - δ) :
    (𝔼 x, |gridValue (u x)|) ≤ (1 - 2 * δ) + 1 / M := by
  classical
  let p (j : Level M) := decide (gridValue j < 0)
  have hh := hu P List.prefix_rfl p
  obtain ⟨Q, _, hQ, hw⟩ := hh
  have hc := hard_wire hard (by omega : Q.length + 1 ≤ s) hw
  have he := model_error hM hg ((hu P List.prefix_rfl (fun j => !(p j))).weaken hd
    (fun _ _ h => h))
  have iden (x : Bits n) :
      (bitSign (f x) - gridValue (u x)) * bitSign (!(p (u x))) =
        |gridValue (u x)| - bitSign (f x) * bitSign (p (u x)) := by
    by_cases h : gridValue (u x) < 0
    · simp [p, bitSign, h, abs_of_neg h]; ring
    · simp [p, bitSign, h, abs_of_nonneg (le_of_not_gt h)]
  simp only [iden, expect_sub_distrib] at he
  linarith

private lemma size_budget (a t : ℕ) (ha : 1 ≤ a) (ht : 2 ≤ t) :
    (t ^ 2) ^ 2 * loopCost (t ^ 2) (a + 1) + 2 ≤ a * t ^ 12 := by
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ (by omega)
  have ht6 : 64 ≤ t ^ 6 := by simpa using Nat.pow_le_pow_left ht 6
  have hB : loopCost (t ^ 2) (a + 1) ≤ 18 * (a * t ^ 2) := by
    dsimp [loopCost]
    nlinarith [Nat.mul_le_mul_right a ht2, Nat.mul_le_mul_right (t ^ 2) ha]
  calc
    _ ≤ (t ^ 2) ^ 2 * (18 * (a * t ^ 2)) + 2 := by gcongr
    _ = 18 * (a * t ^ 6) + 2 := by ring
    _ ≤ (a * t ^ 6) * t ^ 6 := by nlinarith [Nat.mul_le_mul_left (a * t ^ 6) ht6]
    _ = _ := by ring

/-- **Yao's XOR lemma: hardness amplification by XOR.** There is a natural number $c$ such that
the following holds for all natural numbers $n \ge 1$ and $k$, every rational $\delta$ with
$0 < \delta \le 1/2$, every Boolean function $f$ on $n$ bits and every natural number $s$.
Suppose every circuit given as a list of at most $s$ encoded gates has agreement at most
$1 - \delta$ with $f$, where an input $x \in \{0,1\}^n$ is given to the circuit as its $n$ bits.
Then every circuit $C$ given as a list of encoded gates, whose number of gates $|C|$ satisfies
$|C| \cdot (k + 1)^c \le s$, has agreement at most $1/2 + (1 - 2\delta)^k / 2 + 1/(k + 1)$ with
the XOR $f^{\oplus k}$ of $k$ independent copies of $f$, where a $k$-tuple of $n$-bit blocks is
given to the circuit as its $nk$-bit flattening.

Attributed to A. C. Yao, "Theory and applications of trapdoor functions" (FOCS 1982, 80-91); by O.
Goldreich, N. Nisan and A. Wigderson, "On Yao's XOR-Lemma" (ECCC TR95-050, revision 2, Section 1),
the lemma was presented in Yao's talks rather than in that paper, with a first published proof by L.
Levin (1987). Compare Goldreich-Nisan-Wigderson, Lemma 2, and S. Arora and B. Barak, *Computational
Complexity*, web draft of 2007-01-08, Theorem 17.2. -/
public theorem yao_xor_lemma :
    ∃ c : ℕ, ∀ (n k : ℕ) (hn : 1 ≤ n), ∀ (δ : ℚ), 0 < δ → δ ≤ 1 / 2 →
      ∀ f : (Fin n → Bool) → Bool, ∀ s : ℕ,
      (∀ C : List XORGate, C.length ≤ s →
        agreement C f List.ofFn ≤ 1 - δ) →
      ∀ C : List XORGate, C.length * (k + 1) ^ c ≤ s →
        agreement C (xorOf (k := k) f)
          (fun xs : Fin k → Fin n → Bool => List.ofFn (xorFlat (k := k) hn xs)) ≤
          1 / 2 + (1 - 2 * δ) ^ k / 2 + 1 / (k + 1 : ℚ) := by
  classical
  refine ⟨12, ?_⟩
  intro n k hn δ hδ hhalf f s hard C hsize
  have hβ : 0 ≤ 1 - 2 * δ := by linarith
  by_cases hempty : C = []
  · subst C
    have hz : agreement [] (xorOf (k := k) f) (fun xs => List.ofFn (xorFlat hn xs)) = 0 := by
      simp [agreement, xorCircuitEval, circuitEval]
    rw [hz]
    positivity
  by_cases hk : k = 0
  · subst k
    exact (agreement_le_one _ _ _).trans (by norm_num)
  -- With this grid spacing the accumulated agreement error is at most 1 / (k + 1).
  let M := (k + 1) ^ 2
  let d := C.length + 1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨P, u, hlen, hu, hg⟩ := exists_model M d f
  have hbudget := size_budget C.length (k + 1) (List.length_pos_iff.mpr hempty) (by omega)
  have hs : P.length + 2 ≤ s := by dsimp [M, d] at hlen; omega
  let pred (xs : Fin k → Bits n) := prediction C (xorFlat hn xs)
  -- Restrict to one block and test both polarities of the output.
  have hsec (i : Fin k) (xs : Fin k → Bits n) :
      |𝔼 x, (bitSign (f x) - gridValue (u x)) * bitSign (pred (Function.update xs i x))| ≤
        1 / M := by
    let h (x : Bits n) := pred (Function.update xs i x)
    have he : Emit P C.length h := emit_section hn P C hempty xs i
    have hpos := model_error hM hg (he.weaken (by dsimp [d]; omega) (fun _ _ hw => hw))
    have hneg := model_error hM hg (he.bind (d := 1) (fun _ _ hw => emit_not hw))
    have neg (b : Bool) : bitSign (!b) = -bitSign b := by cases b <;> decide
    simp only [neg, mul_neg, expect_neg_distrib] at hneg
    exact abs_le.mpr ⟨by dsimp [h] at hneg; linarith, hpos⟩
  have hcorr := correlation_bound (fun x => bitSign (f x)) (fun x => gridValue (u x))
    (fun _ => (abs_bitSign _).le) (fun _ => grid_abs_le_one hM _) hβ (by linarith)
    (by positivity : (0 : ℚ) ≤ 1 / M) (model_mean hM (by dsimp [d]; omega) hs hu hg hard) k
    (fun xs => bitSign (pred xs)) (fun _ => (abs_bitSign _).le) hsec
  have hv (xs : Fin k → Bits n) :
      (xorCircuitEval C (List.ofFn (xorFlat hn xs))).getLast? = some (pred xs) := by
    rw [eval_ofFn]
    have hne : values C (xorFlat hn xs) ≠ [] := by
      apply List.length_pos_iff.mp
      simpa using List.length_pos_iff.mpr hempty
    simp [pred, prediction, List.getLast?_eq_some_getLast hne]
  have ha := corr_eq_agreement C (xorOf f) pred (fun xs => List.ofFn (xorFlat hn xs)) hv
  simp only [bitSign_xorOf, mul_comm (∏ _, _)] at ha
  have hupp := (le_abs_self _).trans hcorr
  have herr : (k : ℚ) * (1 / M) ≤ 1 / (k + 1) := by
    dsimp [M]
    push_cast
    field_simp
    linarith
  linarith

end MetaMathlibExt.Complexity.KeyTheorems.YaoXOR
