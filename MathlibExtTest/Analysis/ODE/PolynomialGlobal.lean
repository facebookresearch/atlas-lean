/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Analysis.ODE.PolynomialGlobal
import MathlibExt.Analysis.ODE.RegularSublevelGlobal
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set MvPolynomial MathlibExt.Analysis.ODE

-- The compact-set interface accepts a singleton and a shifted initial time.
-- Its finite-interval invariance premise is proved for arbitrary solutions.
example (a c : ℝ) : ∃ x : ℝ → ℝ, x a = c ∧
    (∀ t ∈ Ici a, x t ∈ ({c} : Set ℝ)) ∧
    ∀ t ∈ Ici a, HasDerivAt x 0 t := by
  apply exists_forward_solution_of_compact_invariant
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ))).locallyLipschitz)
    isCompact_singleton a c
  intro b hab x hx hd t ht
  have hn := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (C := 0) (by intro s hs; simp) (convex_Icc a b) ⟨le_rfl, hab⟩ ht
  have he : x t = x a := sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm (by simpa using hn) (norm_nonneg _)))
  simp [he, hx]

private theorem interval_compact :
    IsCompact {x : Fin 1 → ℝ | eval x (X 0 ^ 2 - 1) ≤ 0} := by
  have he : {x : Fin 1 → ℝ | eval x (X 0 ^ 2 - 1) ≤ 0} =
      Icc (fun _ => -1) (fun _ => 1) := by
    ext x
    simp only [mem_ofPred_eq, map_sub, eval_pow, eval_X, map_one, mem_Icc, Pi.le_def]
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

private theorem interval_regular (x : Fin 1 → ℝ)
    (hx : eval x (X 0 ^ 2 - 1 : MvPolynomial (Fin 1) ℝ) = 0) :
    ∃ i, eval x (pderiv i (X 0 ^ 2 - 1)) ≠ 0 := by
  refine ⟨0, ?_⟩
  simp at hx ⊢
  intro hz
  simp [hz] at hx

private theorem cubic_boundary (x : Fin 1 → ℝ)
    (hx : eval x (X 0 ^ 2 - 1 : MvPolynomial (Fin 1) ℝ) = 0) :
    eval x (mkDerivation ℝ (fun _ : Fin 1 => X 0 - X 0 ^ 3) (X 0 ^ 2 - 1)) ≤ 0 := by
  have hx2 : x 0 ^ 2 = 1 := by simpa [sub_eq_zero] using hx
  have hx3 : x 0 ^ 3 = x 0 := by
    calc
      x 0 ^ 3 = x 0 * x 0 ^ 2 := by ring
      _ = x 0 := by rw [hx2, mul_one]
  simp [mkDerivation_eq_sum_pderiv, hx3]

private theorem cubic_solution (a : ℝ) {z : Fin 1 → ℝ} (hz : z 0 ^ 2 ≤ 1) :
    ∃ x : ℝ → Fin 1 → ℝ, x a = z ∧ (∀ t ∈ Ici a, x t 0 ^ 2 ≤ 1) ∧
      ∀ t ∈ Ici a, HasDerivAt x (fun i => x t i - x t i ^ 3) t := by
  have h := MvPolynomial.exists_forward_solution_of_compact_sublevel
    (fun _ : Fin 1 => X 0 - X 0 ^ 3) (X 0 ^ 2 - 1)
    interval_compact interval_regular cubic_boundary a (x₀ := z) (by simpa using hz)
  obtain ⟨x, hx, hbound, hd⟩ := h
  refine ⟨x, hx, by simpa using hbound, ?_⟩
  intro t ht
  convert! hd t ht using 1
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp

-- The cubic field is only required to be locally Lipschitz. All points of the
-- initial interval receive actual global forward solutions.
example (a : ℝ) (z : Fin 1 → ℝ) (hz : z ∈ Icc (fun _ => -1) (fun _ => 1)) :
    ∃ x : ℝ → Fin 1 → ℝ, x a = z ∧ (∀ t ∈ Ici a, x t 0 ^ 2 ≤ 1) ∧
      ∀ t ∈ Ici a, HasDerivAt x (fun i => x t i - x t i ^ 3) t := by
  apply cubic_solution a
  have := hz.1 0
  have := hz.2 0
  nlinarith

-- Inwardness is weak on the entire boundary, while the Lie derivative is
-- strictly positive at this interior point. Existing strict/global-sign
-- sublevel criteria do not supply this boundary-only argument.
example : eval (fun _ : Fin 1 => (1 / 2 : ℝ))
    (mkDerivation ℝ (fun _ : Fin 1 => X 0 - X 0 ^ 3) (X 0 ^ 2 - 1)) = 3 / 8 := by
  norm_num

example (x : Fin 1 → ℝ) (hx : eval x (X 0 ^ 2 - 1 : MvPolynomial (Fin 1) ℝ) = 0) :
    eval x (mkDerivation ℝ (fun _ : Fin 1 => X 0 - X 0 ^ 3) (X 0 ^ 2 - 1)) = 0 := by
  have hx2 : x 0 ^ 2 = 1 := by simpa [sub_eq_zero] using hx
  have hx3 : x 0 ^ 3 = x 0 := by
    calc
      x 0 ^ 3 = x 0 * x 0 ^ 2 := by ring
      _ = x 0 := by rw [hx2, mul_one]
  simp [mkDerivation_eq_sum_pderiv, hx3]

-- Unpack the returned trajectory at a shifted initial time; its actual initial
-- derivative is nonzero, ruling out a constant witness for the existence claim.
example : ∃ x : ℝ → Fin 1 → ℝ, x 7 = (fun _ => 1 / 2) ∧
    (∀ t ∈ Ici 7, x t 0 ^ 2 ≤ 1) ∧
    HasDerivAt x (fun _ => 3 / 8) 7 ∧ (fun _ : Fin 1 => (3 / 8 : ℝ)) ≠ 0 := by
  obtain ⟨x, hx, hbound, hd⟩ := cubic_solution 7 (z := fun _ => 1 / 2) (by norm_num)
  refine ⟨x, hx, hbound, ?_, ?_⟩
  · have h := hd 7 (by simp)
    norm_num [hx] at h
    exact h
  · intro h
    have := congrFun h 0
    norm_num at this


-- The generic analytic theorem is independently usable for a scalar field,
-- without representing the level function or velocity by MvPolynomial.
example (a : ℝ) : ∃ x : ℝ → ℝ, x a = 1 / 2 ∧
    (∀ t ∈ Ici a, x t ^ 2 - 1 ≤ 0) ∧
      ∀ t ∈ Ici a, HasDerivAt x (x t - x t ^ 3) t := by
  have hK : IsCompact {x : ℝ | x ^ 2 - 1 ≤ 0} := by
    have he : {x : ℝ | x ^ 2 - 1 ≤ 0} = Icc (-1) 1 := by
      ext x
      simp only [mem_ofPred_eq, mem_Icc]
      constructor
      · intro h
        constructor <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
      · rintro ⟨hl, hu⟩
        nlinarith
    rw [he]
    exact isCompact_Icc
  have hF : ContDiff ℝ 1 (fun x : ℝ => x - x ^ 3) := by fun_prop
  apply Nagumo.exists_forward_solution_of_compact_regular_sublevel hF.locallyLipschitz
    (h := fun x : ℝ => x ^ 2 - 1) (by fun_prop) hK _ _ a (by norm_num)
  · intro x hx hz
    have he := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hz
    rw [((hasDerivAt_pow 2 x).sub_const 1).hasFDerivAt.fderiv] at he
    norm_num at he
    simp [he] at hx
  · intro x hx
    have hx2 : x ^ 2 = 1 := sub_eq_zero.mp hx
    have hx3 : x ^ 3 = x := by
      calc
        x ^ 3 = x * x ^ 2 := by ring
        _ = x := by rw [hx2, mul_one]
    rw [hx3, sub_self]
    simp


-- The generic premise has real content even on a singleton time interval:
-- it entails initial membership without a separate assumption.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {K : Set E} {a : ℝ} {x₀ : E}
    (hinv : ∀ b, a ≤ b → ∀ x : ℝ → E, x a = x₀ →
      (∀ t ∈ Icc a b, HasDerivWithinAt x (F (x t)) (Icc a b) t) →
      MapsTo x (Icc a b) K) : x₀ ∈ K := by
  apply hinv a le_rfl (fun _ => x₀) rfl _ (show a ∈ Icc a a by simp)
  intro t ht
  have he : t = a := le_antisymm ht.2 ht.1
  subst t
  simpa only [Icc_self] using! (HasFDerivWithinAt.singleton :
    HasDerivWithinAt (fun _ : ℝ => x₀) (F x₀) {a} a)
