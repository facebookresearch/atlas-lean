/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Observation-likelihood normalization for hidden Markov models

For finite state and observation sets, normalized parameters (a nonnegative
initial distribution with row-stochastic transition and emission matrices,
zeros allowed) connect the Atlas HMM path weights
(`Cslib.MachineLearning.Sequence.HiddenMarkov`) to the induced joint law on
paths and observation strings.

Jurafsky and Martin, *Speech and Language Processing*, 3rd ed. draft (2026),
Appendix A, Section A.2, eqs. (A.8) and (A.10): `pathProb h x t z` is the
joint weight P(O, Q) of (A.8) and `likelihood h x t` the marginal P(O) of
(A.10), both over observations `x 0, …, x t`. Since the Atlas observation
argument is a stream `ℕ → O`, the bridge fixes length `t + 1` through an
explicit extension `extend` of `Fin (t + 1) → O`.

Main results:

* `sum_joint_eq_one`: the joint law over paths and length-`t + 1`
  observation strings sums to one.
* `sum_likelihood_eq_one`: the observation likelihood sums to one over all
  observation strings of length `t + 1`.
* `sum_forward_eq_one`: the forward form, reusing
  `likelihood_eq_sum_forward`.

These hold only under `Normalized`. Arbitrary semiring weights (for example
all weights equal to `2`) do not satisfy them; see the boundary tests in
`CSLibExtTest`.
-/

@[expose] public section

namespace Cslib.MachineLearning.Sequence.HiddenMarkovLaw

open Cslib.MachineLearning.Sequence.HiddenMarkov

/-- Normalized HMM parameters over the reals: a nonnegative initial
distribution with row-stochastic transition and emission matrices. Zeros
are allowed, unlike `BaumWelch.Valid` which requires positivity. -/
structure Normalized {S O : Type*} [Fintype S] [Fintype O]
    (h : HMM S O ℝ) : Prop where
  /-- Initial weights are nonnegative. -/
  init_nonneg : ∀ s, 0 ≤ h.init s
  /-- The initial weights sum to one. -/
  init_sum : ∑ s, h.init s = 1
  /-- Transition weights are nonnegative. -/
  trans_nonneg : ∀ s s', 0 ≤ h.trans s s'
  /-- Every transition row sums to one. -/
  trans_sum : ∀ s, ∑ s', h.trans s s' = 1
  /-- Emission weights are nonnegative. -/
  emit_nonneg : ∀ s o, 0 ≤ h.emit s o
  /-- Every emission row sums to one. -/
  emit_sum : ∀ s, ∑ o, h.emit s o = 1

/-- A normalized HMM has nonnegative weights. -/
theorem toNonneg (S O : Type*) [Fintype S] [Fintype O]
    (h : HMM S O ℝ) (hN : Normalized h) : h.Nonneg :=
  ⟨hN.init_nonneg, hN.trans_nonneg, hN.emit_nonneg⟩

/-- Extend a length-`t + 1` observation string to a full stream. Only
the values at `0, …, t` are ever read by `pathProb` and `likelihood`. -/
def extend (t : ℕ) {O : Type*} (v : Fin (t + 1) → O) : ℕ → O :=
  fun i => if h : i ≤ t then v ⟨i, Nat.lt_succ_of_le h⟩
    else v ⟨0, Nat.zero_lt_succ t⟩

/-- Path weights under a normalized HMM are nonnegative. -/
theorem pathProb_nonneg_extend (S O : Type*) [Fintype S] [Fintype O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ)
    (v : Fin (t + 1) → O) (z : Fin (t + 1) → S) :
    0 ≤ pathProb h (extend t v) t z :=
  pathProb_nonneg (extend t v) (toNonneg S O h hN) t z

/-- A sum over length-`t + 2` tuples splits on the last entry
(applied to both observation strings and state paths). -/
theorem sum_snoc_obs {O : Type*} [Fintype O] {M : Type*}
    [AddCommMonoid M] {t : ℕ} (f : (Fin (t + 1 + 1) → O) → M) :
    ∑ v, f v = ∑ v : Fin (t + 1) → O, ∑ o, f (Fin.snoc v o) := by
  rw [← (Fin.snocEquiv fun _ => O).sum_comp, Fintype.sum_prod_type_right]
  rfl

/-- The extension of a snoc'd string agrees with the prefix extension
on `0, …, t`. -/
theorem extend_snoc_apply (t : ℕ) {O : Type*} (x : Fin (t + 1) → O)
    (o : O) (i : ℕ) (hi : i ≤ t) :
    extend (t + 1) (Fin.snoc x o) i = extend t x i := by
  have hi' : i ≤ t + 1 := Nat.le_succ_of_le hi
  simp only [extend, dite_eq_left hi, dite_eq_left hi']
  have heq : (⟨i, Nat.lt_succ_of_le hi'⟩ : Fin (t + 1 + 1)) =
      Fin.castSucc ⟨i, Nat.lt_succ_of_le hi⟩ := by
    apply Fin.ext
    rfl
  rw [heq, Fin.snoc_castSucc]

/-- `pathProb` at length `t` depends only on observations `0, …, t`. -/
theorem pathProb_congr (S O : Type*) (h : HMM S O ℝ)
    (x₁ x₂ : ℕ → O) :
    ∀ (t : ℕ) (_ : ∀ i, i ≤ t → x₁ i = x₂ i)
      (z : Fin (t + 1) → S),
      pathProb h x₁ t z = pathProb h x₂ t z := by
  intro t
  induction t with
  | zero =>
    intro heq z
    have h0 : x₁ 0 = x₂ 0 := heq 0 (Nat.zero_le 0)
    simp only [pathProb, h0]
  | succ t ih =>
    intro heq z
    show pathProb h x₁ (t + 1) z = pathProb h x₂ (t + 1) z
    have hle : ∀ i, i ≤ t → x₁ i = x₂ i :=
      fun i hi => heq i (Nat.le_succ_of_le hi)
    have hlast : x₁ (t + 1) = x₂ (t + 1) := heq (t + 1) (Nat.le_refl _)
    have hdecomp : z = Fin.snoc (Fin.init z) (z (Fin.last (t + 1))) :=
      (Fin.snoc_init_self z).symm
    rw [hdecomp, pathProb_snoc, pathProb_snoc, ih hle (Fin.init z), hlast]

/-- The extension of a snoc'd string reads the new symbol at `t + 1`. -/
theorem extend_snoc_last (t : ℕ) {O : Type*} (x : Fin (t + 1) → O)
    (o : O) : extend (t + 1) (Fin.snoc x o) (t + 1) = o := by
  have hle : t + 1 ≤ t + 1 := Nat.le_refl _
  simp only [extend, dite_eq_left hle]
  have heq : (⟨t + 1, Nat.lt_succ_of_le hle⟩ : Fin (t + 1 + 1)) =
      Fin.last (t + 1) := by
    apply Fin.ext
    rfl
  rw [heq, Fin.snoc_last]

/-- The joint law over paths and length-`t + 1` observation strings
sums to one: with nonnegativity, this is the finite-PMF law. -/
theorem sum_joint_eq_one (S O : Type*) [Fintype S] [Fintype O]
    (h : HMM S O ℝ) (hN : Normalized h) :
    ∀ t : ℕ, ∑ x : Fin (t + 1) → O, ∑ z : Fin (t + 1) → S,
      pathProb h (extend t x) t z = 1 := by
  intro t
  induction t with
  | zero =>
    change ∑ x : Fin 1 → O, ∑ z : Fin 1 → S,
      pathProb h (extend 0 x) 0 z = 1
    simp only [← (Equiv.funUnique (Fin 1) O).symm.sum_comp,
      ← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
    have hsymmO : ∀ o : O,
        (Equiv.funUnique (Fin 1) O).symm o = fun _ => o := fun _ => rfl
    have hsymmS : ∀ s : S,
        (Equiv.funUnique (Fin 1) S).symm s = fun _ => s := fun _ => rfl
    have hext : ∀ o : O, extend 0 (fun _ => o) 0 = o := by
      intro o
      simp only [extend, dite_eq_left (Nat.zero_le 0)]
    simp only [hsymmO, hsymmS, pathProb, hext]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hN.emit_sum, mul_one]
    exact hN.init_sum
  | succ t ih =>
    have key : ∀ (v : Fin (t + 1) → O),
        (∑ _o : O, ∑ z : Fin (t + 1) → S, ∑ _s : S,
          pathProb h (extend (t + 1) (Fin.snoc v _o)) (t + 1)
            (Fin.snoc z _s)) =
        ∑ z : Fin (t + 1) → S, pathProb h (extend t v) t z := by
      intro v
      rw [Finset.sum_comm]
      have pz : ∀ (z : Fin (t + 1) → S),
          (∑ _o : O, ∑ _s : S,
            pathProb h (extend (t + 1) (Fin.snoc v _o)) (t + 1)
              (Fin.snoc z _s)) =
          pathProb h (extend t v) t z := by
        intro z
        have step : ∀ (o : O) (s : S),
            pathProb h (extend (t + 1) (Fin.snoc v o)) (t + 1)
                (Fin.snoc z s) =
              pathProb h (extend t v) t z *
                h.trans (z (Fin.last t)) s * h.emit s o := by
          intro o s
          rw [pathProb_snoc, extend_snoc_last]
          have hpp : pathProb h (extend (t + 1) (Fin.snoc v o)) t z =
              pathProb h (extend t v) t z := by
            apply pathProb_congr
            intro i hi
            exact extend_snoc_apply t v o i hi
          rw [hpp]
        simp only [step]
        rw [Finset.sum_comm]
        have inner : ∀ s : S, (∑ _o : O,
            pathProb h (extend t v) t z * h.trans (z (Fin.last t)) s *
              h.emit s _o) =
            pathProb h (extend t v) t z * h.trans (z (Fin.last t)) s := by
          intro s
          rw [← Finset.mul_sum, hN.emit_sum, mul_one]
        simp only [inner]
        rw [← Finset.mul_sum, hN.trans_sum, mul_one]
      simp only [pz]
    change ∑ x : Fin (t + 1 + 1) → O, ∑ z : Fin (t + 1 + 1) → S,
      pathProb h (extend (t + 1) x) (t + 1) z = 1
    simp only [sum_snoc_obs (t := t), key]
    exact ih

/-- The observation likelihood at fixed length sums to one over all
observation strings: the marginal law is normalized. -/
theorem sum_likelihood_eq_one (S O : Type*) [Fintype S] [Fintype O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    ∑ x : Fin (t + 1) → O, likelihood h (extend t x) t = 1 := by
  simp only [likelihood]
  exact sum_joint_eq_one S O h hN t

/-- The forward algorithm computes a normalized law: the forward form,
reusing `likelihood_eq_sum_forward`. -/
theorem sum_forward_eq_one (S O : Type*) [Fintype S] [Fintype O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    ∑ x : Fin (t + 1) → O, ∑ s : S, forward h (extend t x) t s = 1 := by
  simp only [← likelihood_eq_sum_forward]
  exact sum_likelihood_eq_one S O h hN t

/-- The joint law on paths and observation strings (Jurafsky and Martin
eq. (A.8)): the path weight at the observed string. -/
def jointProb (S O : Type*) [Fintype S] [Fintype O]
    (h : HMM S O ℝ) (t : ℕ)
    (zx : (Fin (t + 1) → S) × (Fin (t + 1) → O)) : ℝ :=
  pathProb h (extend t zx.2) t zx.1

/-- The joint law is a finite PMF: nonnegative and summing to one. -/
theorem sum_jointProb_eq_one (S O : Type*) [Fintype S] [Fintype O]
    (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    ∑ zx : (Fin (t + 1) → S) × (Fin (t + 1) → O),
      jointProb S O h t zx = 1 := by
  simp only [jointProb]
  rw [Fintype.sum_prod_type_right]
  exact sum_joint_eq_one S O h hN t

/-- The likelihood is the marginal of the joint law (Jurafsky and Martin
eq. (A.10)): summing paths out recovers `likelihood`. -/
theorem likelihood_eq_sum_jointProb (S O : Type*) [Fintype S]
    [Fintype O] (h : HMM S O ℝ) (t : ℕ)
    (x : Fin (t + 1) → O) :
    likelihood h (extend t x) t =
      ∑ z : Fin (t + 1) → S, jointProb S O h t (z, x) := by
  simp only [likelihood, jointProb]

end Cslib.MachineLearning.Sequence.HiddenMarkovLaw
