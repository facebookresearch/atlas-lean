/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.Foundations.ProductMeasure
import Code.Inequalities.FKG

open scoped NNReal

namespace StatMech

open bernoulliProductMeasure

variable {E : Type*}

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in




theorem harris_inequality [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B
      ≤ (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) := by
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  
  
  have hw0 : (0 : ConfigSpace E → ℝ) ≤ fun ω => μ.real {ω} :=
    fun ω => real_singleton_nonneg ω
  have hwsum : ∑ ω, μ.real {ω} = 1 := sum_real_singleton
  have hwlatt : FKGLatticeCondition (fun ω => μ.real {ω}) :=
    FKGLatticeCondition.of_logModular (fun a b => real_singleton_logModular a b)
  
  have hfkg := fkg_inequality_events (π := fun ω => μ.real {ω}) hw0 hwsum hwlatt hA hB
  
  have hbridge : ∀ S : Set (ConfigSpace E),
      μ.real S = ∑ ω, μ.real {ω} * S.indicator (fun _ => (1 : ℝ)) ω := by
    intro S
    rw [real_eq_sum]
    exact Finset.sum_congr rfl (fun ω _ => mul_comm _ _)
  rw [hbridge A, hbridge B, hbridge (A ∩ B)]
  exact hfkg

end StatMech
