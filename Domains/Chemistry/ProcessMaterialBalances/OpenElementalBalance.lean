/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PhyslibExt.Chemistry.Stoichiometry.Balance

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Open elemental balance

Projecting an open species balance along constant composition rows removes the reaction term
if each stoichiometric column is balanced. Unlike conservation under a prescribed change in
reaction extents, this result is a derivative identity with inlet and outlet streams.

## References

* J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*,
  2nd ed., seventh printing, Exercise 2.8, equation (2.67) (balance in the transposed
  convention), and §4.3, equation (4.36) (species accumulation).
-/

public section

namespace MathlibExt.Chemistry.ProcessMaterialBalances.OpenElementalBalance

open Matrix

/-- Let `A` be a constant real composition matrix, with rows for elements or charge,
and `N` a stoichiometric matrix whose columns are balanced for `A`. Then `A * N = 0`,
so the projected reaction term `A *ᵥ (N *ᵥ q)` is zero for every rate vector `q`.

On the interval `I`, if species amounts `n` have within derivative
`F_in - F_out + N *ᵥ w`, the within derivative of `A *ᵥ n` is just `A *ᵥ (F_in - F_out)`.
This gives a within derivative without asserting uniqueness on a singleton interval.
Likewise a constant row `ℓ` with `ℓ ᵥ* N = 0` projects the species derivative to
`ℓ ⬝ᵥ (F_in - F_out)`. If both streams vanish on `I`, the projected amounts `A *ᵥ n`
are constant there. At a time when the modeled species rate is zero, the projected inlet
and outlet flows agree. -/
theorem open_elemental_balance {β ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (A : Matrix β ι ℝ) (N : Matrix ι ρ ℝ) (I : Set ℝ) (hI : Convex ℝ I)
    (n F_in F_out : ℝ → ι → ℝ) (w : ℝ → ρ → ℝ)
    (hbalanced : ∀ r, _root_.Chemistry.Stoichiometry.IsBalanced A (N.col r))
    (hspecies : ∀ t ∈ I, HasDerivWithinAt n (F_in t - F_out t + N *ᵥ w t) I t) :
    A * N = 0 ∧
    (∀ q, A *ᵥ (N *ᵥ q) = 0) ∧
    (∀ t ∈ I, HasDerivWithinAt (fun u ↦ A *ᵥ n u) (A *ᵥ (F_in t - F_out t)) I t) ∧
    (∀ ℓ : ι → ℝ, ℓ ᵥ* N = 0 → ∀ t ∈ I,
      HasDerivWithinAt (fun u ↦ ℓ ⬝ᵥ n u) (ℓ ⬝ᵥ (F_in t - F_out t)) I t) ∧
    ((∀ t ∈ I, F_in t = 0 ∧ F_out t = 0) → ∀ x ∈ I, ∀ y ∈ I, A *ᵥ n x = A *ᵥ n y) ∧
    (∀ t ∈ I, F_in t - F_out t + N *ᵥ w t = 0 → A *ᵥ F_in t = A *ᵥ F_out t) := by
  have hAN : A * N = 0 := by
    ext b r
    exact congrFun (hbalanced r : A *ᵥ N.col r = 0) b
  have hcancel (q : ρ → ℝ) : A *ᵥ (N *ᵥ q) = 0 := by
    rw [Matrix.mulVec_mulVec, hAN, Matrix.zero_mulVec]
  have hproject (t : ℝ) :
      A *ᵥ (F_in t - F_out t + N *ᵥ w t) = A *ᵥ (F_in t - F_out t) := by
    rw [Matrix.mulVec_add, hcancel, add_zero]
  have hrow (ℓ : ι → ℝ) (hℓ : ℓ ᵥ* N = 0) (t : ℝ) (ht : t ∈ I) :
      HasDerivWithinAt (fun u ↦ ℓ ⬝ᵥ n u) (ℓ ⬝ᵥ (F_in t - F_out t)) I t := by
    have h := (dotProductBilin ℝ ℝ ℓ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t
      (hspecies t ht)
    change HasDerivWithinAt (fun u ↦ ℓ ⬝ᵥ n u)
      (ℓ ⬝ᵥ (F_in t - F_out t + N *ᵥ w t)) I t at h
    simpa only [dotProduct_add, dotProduct_mulVec, hℓ, zero_dotProduct, add_zero] using h
  have hArow (b : β) : A b ᵥ* N = 0 := by
    rw [← Matrix.mul_apply_eq_vecMul, hAN]
    rfl
  refine ⟨hAN, hcancel, ?_, hrow, ?_, ?_⟩
  · intro t ht
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    apply hasFDerivWithinAt_pi''
    intro b
    exact (hrow (A b) (hArow b) t ht).hasFDerivWithinAt
  · intro hclosed x hx y hy
    funext b
    have hzero (t : ℝ) (ht : t ∈ I) : HasDerivWithinAt (fun u ↦ A b ⬝ᵥ n u) 0 I t := by
      obtain ⟨hin, hout⟩ := hclosed t ht
      simpa only [hin, hout, sub_self, dotProduct_zero] using hrow (A b) (hArow b) t ht
    have hle := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := fun _ ↦ 0) hzero (C := 0) (fun _ _ ↦ by simp) hx hy
    change A b ⬝ᵥ n x = A b ⬝ᵥ n y
    symm
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hle
  · intro t _ hsteady
    apply sub_eq_zero.mp
    rw [← Matrix.mulVec_sub, ← hproject t, hsteady, Matrix.mulVec_zero]

end MathlibExt.Chemistry.ProcessMaterialBalances.OpenElementalBalance
