/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The function `1 / r` is harmonic in three dimensions away from `r = 0`

The flat Laplacian `Δ` of `y ↦ ‖y‖⁻¹` vanishes at every nonzero point of
`EuclideanSpace ℝ (Fin 3)`.

## i. Overview

Write `‖y‖⁻¹ = (‖y‖ ^ 2) ^ (-1 / 2)` as `g ∘ h` with `g s = s ^ (-1 / 2)`
and `h y = ‖y‖ ^ 2`. Expanding `Δ` over the standard orthonormal basis and
computing each second directional derivative by Faà di Bruno along the line
`t ↦ x + t • v` gives, for each basis vector `v`,
`(r * (r - 1) * (h x) ^ (r - 2)) * (2 * ⟪x, v⟫) ^ 2
+ (r * (h x) ^ (r - 1)) * (2 * ⟪v, v⟫)` with `r = -1 / 2`. Summing over
the basis with `∑ v, ⟪x, v⟫ ^ 2 = ‖x‖ ^ 2` leaves
`(4 * r * (r - 1) + 6 * r) * (h x) ^ (r - 1) = 0`.

## ii. Key results

- `MathlibExt.Analysis.laplacian_inv_norm_eq_zero`: `1 / r` is harmonic in
  three dimensions away from `r = 0`.

## iii. References

- `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`,
  `iteratedDeriv_vcomp_two`, `iteratedDeriv_comp_two` (Mathlib).
-/

@[expose] public section

open Laplacian
open scoped RealInnerProductSpace

namespace MathlibExt.Analysis

/-- The function `1 / r` is harmonic in three dimensions away from `r = 0`:
its (flat) Laplacian vanishes at every nonzero point of
`EuclideanSpace ℝ (Fin 3)`. -/
theorem laplacian_inv_norm_eq_zero {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    Δ (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖⁻¹) x = 0 := by
  set r : ℝ := -1 / 2 with hr
  set h : EuclideanSpace ℝ (Fin 3) → ℝ := fun y => ‖y‖ ^ 2 with hh_def
  set g : ℝ → ℝ := fun s => s ^ r with hg_def
  set F : EuclideanSpace ℝ (Fin 3) → ℝ := g ∘ h
  set e := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 3))
  have hr0 : r ≠ 0 := by rw [hr]; norm_num
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx2 : h x ≠ 0 := by
    have h1 : (‖x‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hxpos)
    simpa [hh_def] using h1
  have hx2pos : 0 < h x := by
    have h1 : (0 : ℝ) < (‖x‖ : ℝ) ^ 2 := by positivity
    simpa [hh_def] using h1
  have hfg : (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖⁻¹) = F := by
    funext y
    by_cases hy : y = 0
    · subst hy
      change (‖(0 : EuclideanSpace ℝ (Fin 3))‖ : ℝ)⁻¹ = g (h 0)
      rw [norm_zero]
      have e2 : h (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by simp [hh_def]
      rw [e2]
      have e3 : g (0 : ℝ) = 0 := by
        simp only [hg_def]
        exact Real.zero_rpow hr0
      rw [e3, inv_zero]
    · have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have h2 : ((2 : ℕ) : ℝ) * r = -1 := by rw [hr]; norm_num
      change (‖y‖ : ℝ)⁻¹ = ((‖y‖ ^ 2 : ℝ)) ^ r
      rw [← Real.rpow_natCast ‖y‖ 2, ← Real.rpow_mul (le_of_lt hpos), h2,
        Real.rpow_neg_one]
  have hΔ := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (E := EuclideanSpace ℝ (Fin 3)) (F := ℝ) F e
  have hΔx : Δ F x = ∑ i, iteratedFDeriv ℝ 2 F x ![e i, e i] := congrFun hΔ x
  rw [hfg, hΔx]
  have hterm : ∀ v : EuclideanSpace ℝ (Fin 3),
      iteratedFDeriv ℝ 2 F x (fun _ : Fin 2 => v) =
        (r * (r - 1) * (h x) ^ (r - 2)) * (2 * ⟪x, v⟫) ^ 2 +
        (r * (h x) ^ (r - 1)) * (2 * ⟪v, v⟫) := by
    intro v
    have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
      have h0 := HasDerivAt.add (hasDerivAt_const t x)
        (HasDerivAt.smul_const (hasDerivAt_id t) v)
      have hval : (0 : EuclideanSpace ℝ (Fin 3)) + (1 : ℝ) • v = v := by simp
      rw [hval] at h0
      exact HasDerivAt.congr_of_eventuallyEq h0
        (Filter.Eventually.of_forall fun s => rfl)
    have hγ0 : (fun s : ℝ => x + s • v) 0 = x := by simp
    have hγ0' : x + (0 : ℝ) • v = x := hγ0
    have hderivγ : deriv (fun s : ℝ => x + s • v) 0 = v :=
      HasDerivAt.deriv (hγ 0)
    have hiterγ : iteratedDeriv 2 (fun s : ℝ => x + s • v) 0 = 0 := by
      have h1 : iteratedDeriv 1 (fun s : ℝ => x + s • v)
          = deriv (fun s : ℝ => x + s • v) := iteratedDeriv_one
      have h2 : iteratedDeriv 2 (fun s : ℝ => x + s • v)
          = deriv (deriv (fun s : ℝ => x + s • v)) := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, h1]
      have h3 : deriv (fun s : ℝ => x + s • v) = fun _ => v :=
        funext fun t => HasDerivAt.deriv (hγ t)
      rw [h2, h3]
      simp
    have hγ2 : ∀ t : ℝ, ContDiffAt ℝ 2 (fun s : ℝ => x + s • v) t :=
      fun t => by fun_prop
    have hF2 : ContDiffAt ℝ 2 F ((fun s : ℝ => x + s • v) 0) := by
      rw [hγ0]
      have hg : ContDiffAt ℝ 2 g (h x) := Real.contDiffAt_rpow_const_of_ne hx2
      have hh : ContDiffAt ℝ 2 h x := (contDiff_norm_sq ℝ).contDiffAt
      exact ContDiffAt.comp x hg hh
    have hhi0 : (h ∘ (fun s : ℝ => x + s • v)) 0 = h x := by
      change h ((fun s : ℝ => x + s • v) 0) = h x
      rw [hγ0]
    have hcg : ContDiffAt ℝ 2 g ((h ∘ (fun s : ℝ => x + s • v)) 0) := by
      rw [hhi0]
      exact Real.contDiffAt_rpow_const_of_ne hx2
    have hch : ContDiffAt ℝ 2 (h ∘ (fun s : ℝ => x + s • v)) 0 :=
      ContDiffAt.comp 0 (contDiff_norm_sq ℝ).contDiffAt (hγ2 0)
    have hderivg : deriv g (h x) = r * (h x) ^ (r - 1) := by
      have h0 := Real.hasDerivAt_rpow_const (x := h x) (p := r) (Or.inl hx2)
      exact HasDerivAt.deriv h0
    have hiter2g : iteratedDeriv 2 g (h x) = r * (r - 1) * (h x) ^ (r - 2) := by
      have hpoch : (descPochhammer ℝ 2).eval r = r * (r - 1) := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, descPochhammer_succ_right,
          descPochhammer_one]
        simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_one]
      have hiter : iteratedDeriv 2 g (h x)
          = (descPochhammer ℝ 2).eval r * (h x) ^ (r - 2) := by
        rw [iteratedDeriv_eq_iterate]
        exact Real.iter_deriv_rpow_const r (h x) 2
      rw [hiter, hpoch]
    have hderivhi : deriv (h ∘ (fun s : ℝ => x + s • v)) 0 = 2 * ⟪x, v⟫ := by
      have h0 : ∀ t : ℝ, deriv (h ∘ (fun s : ℝ => x + s • v)) t
          = 2 * ⟪x + t • v, v⟫ :=
        fun t => HasDerivAt.deriv (HasDerivAt.norm_sq (hγ t))
      have h00 := h0 0
      simp only [zero_smul, add_zero] at h00
      exact h00
    have hiter2hi : iteratedDeriv 2 (h ∘ (fun s : ℝ => x + s • v)) 0
        = 2 * ⟪v, v⟫ := by
      have h1 : iteratedDeriv 1 (h ∘ (fun s : ℝ => x + s • v))
          = deriv (h ∘ (fun s : ℝ => x + s • v)) := iteratedDeriv_one
      have h2 : iteratedDeriv 2 (h ∘ (fun s : ℝ => x + s • v))
          = deriv (deriv (h ∘ (fun s : ℝ => x + s • v))) := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, h1]
      have hder : ∀ t : ℝ, deriv (h ∘ (fun s : ℝ => x + s • v)) t
          = 2 * ⟪x + t • v, v⟫ :=
        fun t => HasDerivAt.deriv (HasDerivAt.norm_sq (hγ t))
      have hfun : deriv (h ∘ (fun s : ℝ => x + s • v))
          = fun t : ℝ => 2 * ⟪x + t • v, v⟫ := funext hder
      have hexp : (fun t : ℝ => 2 * ⟪x + t • v, v⟫)
          = fun t : ℝ => 2 * (⟪x, v⟫ + t * ⟪v, v⟫) := by
        funext t
        show (2 : ℝ) * ⟪x + t • v, v⟫ = 2 * (⟪x, v⟫ + t * ⟪v, v⟫)
        rw [inner_add_left, real_inner_smul_left]
      have hlin : HasDerivAt (fun t : ℝ => 2 * (⟪x, v⟫ + t * ⟪v, v⟫))
          (2 * ⟪v, v⟫) 0 := by
        have h0 := HasDerivAt.const_mul 2
          (HasDerivAt.add (hasDerivAt_const 0 ⟪x, v⟫)
            (HasDerivAt.mul_const (hasDerivAt_id 0) ⟪v, v⟫))
        have hval : (2 : ℝ) * (0 + 1 * ⟪v, v⟫) = 2 * ⟪v, v⟫ := by ring
        rw [hval] at h0
        exact HasDerivAt.congr_of_eventuallyEq h0
          (Filter.Eventually.of_forall fun s => rfl)
      rw [h2, hfun, hexp]
      exact HasDerivAt.deriv hlin
    have hvcomp := iteratedDeriv_vcomp_two hF2 (hγ2 0)
    rw [hγ0'] at hvcomp
    have hFγ : F ∘ (fun s : ℝ => x + s • v)
        = g ∘ (h ∘ (fun s : ℝ => x + s • v)) := rfl
    rw [hFγ] at hvcomp
    have hcomp := iteratedDeriv_comp_two hcg hch
    rw [hcomp, hhi0, hderivγ, hiterγ, hderivg, hiter2g, hderivhi,
      hiter2hi] at hvcomp
    simp only [map_zero, add_zero] at hvcomp
    exact hvcomp.symm
  have hcons : ∀ v : EuclideanSpace ℝ (Fin 3), ![v, v] = (fun _ : Fin 2 => v) := by
    intro v
    funext j
    fin_cases j <;> simp
  simp_rw [hcons, hterm, OrthonormalBasis.inner_eq_one e]
  have hreshape : ∀ c : ℝ, (r * (r - 1) * (h x) ^ (r - 2)) * (2 * c) ^ 2
      + (r * (h x) ^ (r - 1)) * (2 * 1)
      = (4 * (r * (r - 1) * (h x) ^ (r - 2))) * c ^ 2
        + 2 * (r * (h x) ^ (r - 1)) := by
    intro c; ring
  simp_rw [hreshape]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, OrthonormalBasis.sum_sq_inner_left,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, finrank_euclideanSpace_fin]
  have hpow : (h x) ^ (r - 2) * (h x) = (h x) ^ (r - 1) := by
    have h1 : (h x) ^ (r - 2) * (h x) ^ (1 : ℝ) = (h x) ^ (r - 1) := by
      rw [← Real.rpow_add hx2pos]
      congr 1
      ring
    simpa [Real.rpow_one] using h1
  have hcoeff : (4 : ℝ) * r * (r - 1) + 3 * (2 * r) = 0 := by rw [hr]; norm_num
  have hhx : (‖x‖ : ℝ) ^ 2 = h x := rfl
  rw [hhx]
  linear_combination (4 * r * (r - 1)) * hpow + hcoeff * ((h x) ^ (r - 1))


end MathlibExt.Analysis
