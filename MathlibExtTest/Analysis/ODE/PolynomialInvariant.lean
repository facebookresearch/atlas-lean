/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Analysis.ODE.PolynomialInvariant
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MvPolynomial Set

private theorem circle_regular (x : Fin 2 → ℝ)
    (hx : eval x (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) ℝ) = 0) :
    ∃ i, eval x (pderiv i (X 0 ^ 2 + X 1 ^ 2 - 1)) ≠ 0 := by
  simp only [map_sub, eval_add, eval_pow, eval_X, map_one] at hx
  by_cases h : x 0 = 0
  · refine ⟨1, ?_⟩
    simp
    intro hz
    simp [h, hz] at hx
  · exact ⟨0, by simpa using h⟩

private theorem rotation_velocity (t : ℝ) :
    HasDerivAt (fun r => (![Real.cos r, Real.sin r] : Fin 2 → ℝ))
      (fun i => eval ![Real.cos t, Real.sin t] (![-X 1, X 0] i)) t := by
  apply hasDerivAt_pi.mpr
  intro i; fin_cases i
  · simpa using! Real.hasDerivAt_cos t
  · simpa using! Real.hasDerivAt_sin t

-- A concrete nonconstant trajectory uses the invariant-set theorem, not an
-- assumed scalar derivative or a curve assumed to remain in the disk.
example (T : ℝ) : MapsTo (fun t => (![Real.cos t, Real.sin t] : Fin 2 → ℝ))
    (Icc 0 T) {x | x 0 ^ 2 + x 1 ^ 2 ≤ 1} := by
  have h := mapsTo_sublevel_of_mkDerivation_nonpos ![-X 1, X 0]
    (X 0 ^ 2 + X 1 ^ 2 - 1) circle_regular
    (by intro x hx; simp [mkDerivation_eq_sum_pderiv, Fin.sum_univ_two]; nlinarith)
    (a := 0) (b := T) (fun t _ => (rotation_velocity t).hasDerivWithinAt)
    (by norm_num)
  simpa [sub_nonpos] using h

example : (![Real.cos 0, Real.sin 0] : Fin 2 → ℝ) ≠
    ![Real.cos (Real.pi / 2), Real.sin (Real.pi / 2)] := by
  intro h
  have := congrFun h 0
  norm_num at this

private theorem interval_regular (x : Fin 1 → ℝ)
    (hx : eval x (X 0 ^ 2 - 1 : MvPolynomial (Fin 1) ℝ) = 0) :
    ∃ i, eval x (pderiv i (X 0 ^ 2 - 1)) ≠ 0 := by
  refine ⟨0, ?_⟩
  simp at hx ⊢
  intro hz
  simp [hz] at hx

-- The inward field is nonzero. Its explicit solution starts on the boundary.
example (T : ℝ) : MapsTo (fun t => (![Real.exp (-t)] : Fin 1 → ℝ))
    (Icc 0 T) {x | x 0 ^ 2 ≤ 1} := by
  have hu (t : ℝ) : HasDerivAt (fun r => (![Real.exp (-r)] : Fin 1 → ℝ))
      (fun i => eval ![Real.exp (-t)] ((fun _ => -X 0) i)) t := by
    apply hasDerivAt_pi.mpr
    intro i; fin_cases i
    simpa using! ((hasDerivAt_id t).neg.exp)
  have h := mapsTo_sublevel_of_mkDerivation_nonpos (fun _ => -X 0)
    (X 0 ^ 2 - 1) interval_regular
    (by intro x hx; simp [mkDerivation_eq_sum_pderiv]; nlinarith [sq_nonneg (x 0)])
    (a := 0) (b := T) (fun t _ => (hu t).hasDerivWithinAt) (by norm_num)
  simpa [sub_nonpos] using h

-- This regular sublevel is compact; global existence is not a premise or
-- conclusion of the invariance theorem.
example : IsCompact {x : Fin 1 → ℝ | eval x (X 0 ^ 2 - 1) ≤ 0} := by
  have he : {x : Fin 1 → ℝ | eval x (X 0 ^ 2 - 1) ≤ 0} =
      Icc (fun _ => -1) (fun _ => 1) := by
    ext x
    simp only [mem_ofPred_eq, map_sub, eval_pow, eval_X, map_one, mem_Icc,
      Pi.le_def]
    constructor
    · intro h
      constructor <;> intro i
      · have hi : i = 0 := Subsingleton.elim _ _
        subst i
        nlinarith [sq_nonneg (x 0 + 1)]
      · have hi : i = 0 := Subsingleton.elim _ _
        subst i
        nlinarith [sq_nonneg (x 0 - 1)]
    · rintro ⟨hl, hu⟩
      have := hl 0
      have := hu 0
      nlinarith
  rw [he]
  exact isCompact_Icc

-- Independently invariant constraints can be intersected, with each boundary
-- hypothesis imposed on its entire zero set.
example {σ : Type*} [Fintype σ] (F : σ → MvPolynomial σ ℝ)
    (p q : MvPolynomial σ ℝ)
    (hp : ∀ x, eval x p = 0 → ∃ i, eval x (pderiv i p) ≠ 0)
    (hq : ∀ x, eval x q = 0 → ∃ i, eval x (pderiv i q) ≠ 0)
    (hFp : ∀ x, eval x p = 0 → eval x (mkDerivation ℝ F p) ≤ 0)
    (hFq : ∀ x, eval x q = 0 → eval x (mkDerivation ℝ F q) ≤ 0)
    {a b : ℝ} {u : ℝ → σ → ℝ}
    (hu : ∀ t ∈ Icc a b,
      HasDerivWithinAt u (fun i => eval (u t) (F i)) (Icc a b) t)
    (h₀ : eval (u a) p ≤ 0 ∧ eval (u a) q ≤ 0) :
    MapsTo u (Icc a b) ({x | eval x p ≤ 0} ∩ {x | eval x q ≤ 0}) := by
  exact (mapsTo_sublevel_of_mkDerivation_nonpos F p hp hFp hu h₀.1).inter
    (mapsTo_sublevel_of_mkDerivation_nonpos F q hq hFq hu h₀.2)

-- A singleton time interval has no unique derivative; the API still accepts
-- the supplied velocity of the constant curve on this interval.
example : MapsTo (fun _ : ℝ => (![1] : Fin 1 → ℝ)) (Icc 0 0)
    {x | eval x (X 0 ^ 2 - 1) ≤ 0} := by
  apply mapsTo_sublevel_of_mkDerivation_nonpos (fun _ => -X 0)
    (X 0 ^ 2 - 1) interval_regular
    (by intro x hx; simp [mkDerivation_eq_sum_pderiv]; nlinarith [sq_nonneg (x 0)])
  · intro t ht
    have ht' : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simpa only [Icc_self] using! (HasFDerivWithinAt.singleton :
      HasDerivWithinAt (fun _ : ℝ => (![1] : Fin 1 → ℝ))
        (fun i => eval ![1] ((fun _ => -X 0) i)) {0} 0)
  · norm_num

-- The tempting singular-boundary rule is false: h(x)=x³ and x'=1 have
-- zero Lie derivative on h=0, yet the solution from zero immediately escapes.
example (x : Fin 1 → ℝ) (hx : eval x (X 0 ^ 3 : MvPolynomial (Fin 1) ℝ) = 0) :
    eval x (mkDerivation ℝ (fun _ : Fin 1 => (1 : MvPolynomial (Fin 1) ℝ)) (X 0 ^ 3)) ≤ 0 := by
  have hz : x 0 = 0 := by simpa using hx
  simp [hz]

example : ¬ ∃ i : Fin 1,
    eval (fun _ => (0 : ℝ)) (pderiv i (X 0 ^ 3 : MvPolynomial (Fin 1) ℝ)) ≠ 0 := by
  simp

example (t : ℝ) : HasDerivAt (fun r => (![r] : Fin 1 → ℝ))
    (fun i => eval ![t] ((fun _ => (1 : MvPolynomial (Fin 1) ℝ)) i)) t := by
  apply hasDerivAt_pi.mpr
  intro i; fin_cases i
  simpa using! hasDerivAt_id t

example : eval (![0] : Fin 1 → ℝ) (X 0 ^ 3 : MvPolynomial (Fin 1) ℝ) ≤ 0 := by
  norm_num

example (t : ℝ) (ht : 0 < t) :
    ¬ eval (![t] : Fin 1 → ℝ) (X 0 ^ 3 : MvPolynomial (Fin 1) ℝ) ≤ 0 := by
  simpa using pow_pos ht 3

-- The analytic layer also works without a polynomial presentation.
example {a b : ℝ} {u : ℝ → ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivWithinAt u (-u t) (Icc a b) t)
    (h₀ : u a ≤ 0) : MapsTo u (Icc a b) (Iic 0) := by
  apply Nagumo.mapsTo_sublevel_of_fderiv_nonpos
    ((contDiff_id.neg : ContDiff ℝ 1 (fun x : ℝ => -x)).locallyLipschitz)
    differentiable_id _ _ hu h₀
  · intro x hx hz
    have he := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hz
    norm_num at he
  · intro x hx
    change x = 0 at hx
    subst x
    simp

-- No nonempty variable type is required. A strictly negative constant has
-- empty zero level, so regularity and inwardness hold vacuously.
example (F : Empty → MvPolynomial Empty ℝ) {a b : ℝ} {u : ℝ → Empty → ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivWithinAt u (fun i => eval (u t) (F i)) (Icc a b) t) :
    MapsTo u (Icc a b) {x | eval x (C (-1) : MvPolynomial Empty ℝ) ≤ 0} := by
  exact mapsTo_sublevel_of_mkDerivation_nonpos F (C (-1))
    (by intro x hx; norm_num at hx) (by intro x hx; norm_num at hx) hu (by norm_num)
