/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.Ring

/-!
# The genuine finite positive-weight C-star estimate

Use the stock finite WithCStarModule Pi carrier with its actual C-star-module
norm and inner(x,y)=y*star(x). The sqrt and sqrt-times-coefficient columns
turn the weighted sum into the stock Cauchy-Schwarz pairing. The conjugation
order bound supplies the coefficient norm estimate.

This generic estimate accepts an arbitrary nonunital C-star algebra with its
original order and norm. The column functions are private proof constructions;
no alternate norm or comparison certificate is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace CStarAlgebra

noncomputable section

universe uA uI

variable (A : Type uA) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {I : Type uI} [Fintype I]

/-- The actual sqrt column in the stock finite C-star-module Pi carrier. -/
private def sqrtColumn (c : I → A) : WithCStarModule A (I → A) :=
  (WithCStarModule.equiv A (I → A)).symm fun i => CFC.sqrt (c i)

/-- The actual sqrt-times-coefficient column, with the same stock C-star-module norm. -/
private def productColumn (c d : I → A) : WithCStarModule A (I → A) :=
  (WithCStarModule.equiv A (I → A)).symm fun i => CFC.sqrt (c i) * d i

/-- **Norm bound for a finite positive sandwich sum.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order, let `I` be finite, and let `c,d : I → A`. If each `cᵢ ≥ 0`, `M ≥ 0`,
and `‖dᵢ‖ ≤ M` for all `i`, then `‖∑ i, √cᵢ dᵢ √cᵢ‖ ≤ ‖∑ i, cᵢ‖ M`, where square roots are defined
by continuous functional calculus. -/
theorem norm_sum_sqrt_sandwich_le (c d : I → A) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, ‖d i‖ ≤ M) :
    ‖∑ i, CFC.sqrt (c i) * d i * CFC.sqrt (c i)‖ ≤ ‖∑ i, c i‖ * M := by
  classical
  let V := WithCStarModule A (I → A)
  let x : V := sqrtColumn A c
  let y : V := productColumn A c d
  have hs (i : I) : star (CFC.sqrt (c i)) = CFC.sqrt (c i) :=
    (CFC.sqrt_nonneg (c i)).isSelfAdjoint.star_eq
  have hxx : ‖x‖ ^ 2 = ‖∑ i, c i‖ := by
    rw [WithCStarModule.pi_norm_sq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change CFC.sqrt (c i) * star (CFC.sqrt (c i)) = c i
    rw [hs, CFC.sqrt_mul_sqrt_self (c i) (hc i)]
  have hterm (i : I) :
      (CFC.sqrt (c i) * d i) * star (CFC.sqrt (c i) * d i) ≤ (M ^ 2 : ℝ) • c i := by
    calc
      _ = CFC.sqrt (c i) * (d i * star (d i)) * star (CFC.sqrt (c i)) := by
        simp only [star_mul, mul_assoc]
      _ ≤ ‖d i * star (d i)‖ •
          (CFC.sqrt (c i) * star (CFC.sqrt (c i))) :=
        CStarAlgebra.star_right_conjugate_le_norm_smul (CFC.sqrt (c i)) (d i * star (d i))
      _ = (‖d i‖ ^ 2 : ℝ) • c i := by
        rw [CStarRing.norm_self_mul_star, hs, CFC.sqrt_mul_sqrt_self (c i) (hc i), pow_two]
      _ ≤ (M ^ 2 : ℝ) • c i :=
        smul_le_smul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd i) 2) (hc i)
  have hyy : ‖y‖ ^ 2 ≤ M ^ 2 * ‖∑ i, c i‖ := by
    calc
      _ = ‖∑ i, (CFC.sqrt (c i) * d i) * star (CFC.sqrt (c i) * d i)‖ := by
        rw [WithCStarModule.pi_norm_sq]
        congr 1
      _ ≤ ‖(M ^ 2 : ℝ) • ∑ i, c i‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg
          (by simpa only [Finset.smul_sum] using Finset.sum_le_sum fun i _ => hterm i)
          (Finset.sum_nonneg fun i _ => mul_star_self_nonneg _)
      _ = M ^ 2 * ‖∑ i, c i‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg M)]
  have hinner : inner A x y = ∑ i, CFC.sqrt (c i) * d i * CFC.sqrt (c i) := by
    rw [WithCStarModule.pi_inner]
    apply Finset.sum_congr rfl
    intro i _
    change (CFC.sqrt (c i) * d i) * star (CFC.sqrt (c i)) = _
    rw [hs]
  have hcs : ‖∑ i, CFC.sqrt (c i) * d i * CFC.sqrt (c i)‖ ≤ ‖x‖ * ‖y‖ := by
    rw [← hinner]
    exact CStarModule.norm_inner_le (A := A) (E := V) (x := x) (y := y)
  have hsq : ‖∑ i, CFC.sqrt (c i) * d i * CFC.sqrt (c i)‖ ^ 2 ≤ (‖∑ i, c i‖ * M) ^ 2 := by
    calc
      _ ≤ (‖x‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcs 2
      _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := mul_pow _ _ 2
      _ ≤ ‖∑ i, c i‖ * (M ^ 2 * ‖∑ i, c i‖) := by
        rw [hxx]
        exact mul_le_mul_of_nonneg_left hyy (norm_nonneg _)
      _ = (‖∑ i, c i‖ * M) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hM) (by decide)).mp hsq

/-- **Norm bound for commuting positive weights.** Let `A` be a nonunital complex C*-algebra with a
star-compatible partial order and let `c,d : I → A` be indexed by a finite type. If `cᵢ ≥ 0`, `M ≥
0`, `‖dᵢ‖ ≤ M`, and `cᵢ dᵢ = dᵢ cᵢ` for every `i`, then `‖∑ i, cᵢ dᵢ‖ ≤ ‖∑ i, cᵢ‖ M`. -/
theorem norm_sum_commuting_positive_mul_le (c d : I → A) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, ‖d i‖ ≤ M) (hcomm : ∀ i, Commute (c i) (d i)) :
    ‖∑ i, c i * d i‖ ≤ ‖∑ i, c i‖ * M := by
  have heq (i : I) : c i * d i = CFC.sqrt (c i) * d i * CFC.sqrt (c i) := by
    have hsqrt : Commute (CFC.sqrt (c i)) (d i) := by
      simpa only [CFC.sqrt] using (hcomm i).cfcₙ_nnreal NNReal.sqrt
    calc
      _ = (CFC.sqrt (c i) * CFC.sqrt (c i)) * d i := by
        rw [CFC.sqrt_mul_sqrt_self (c i) (hc i)]
      _ = CFC.sqrt (c i) * (CFC.sqrt (c i) * d i) := mul_assoc _ _ _
      _ = CFC.sqrt (c i) * (d i * CFC.sqrt (c i)) :=
        congrArg (fun b => CFC.sqrt (c i) * b) hsqrt.eq
      _ = _ := (mul_assoc _ _ _).symm
  calc
    _ = ‖∑ i, CFC.sqrt (c i) * d i * CFC.sqrt (c i)‖ := by simp only [heq]
    _ ≤ ‖∑ i, c i‖ * M := norm_sum_sqrt_sandwich_le A c d M hM hc hd

end

end CStarAlgebra
