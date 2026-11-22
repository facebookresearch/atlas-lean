/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.ProductMeasure
public import MathlibExt.Probability.CorrelationInequalities.FKG

@[expose] public section

/-!
# Harris inequality for product Bernoulli measures

For a finite set `E` and `p ∈ [0, 1]`, two increasing events are positively correlated under the
product Bernoulli measure `bernoulliProductMeasure p` on `ConfigSpace E = E → Bool`.

## Main results

* `StatMech.harris_inequality`: the **Harris inequality** (also called the Harris–FKG or
  Harris–Kleitman inequality): `P_p(A) * P_p(B) ≤ P_p(A ∩ B)` for increasing `A, B`.

The proof checks that the product Bernoulli weight is log-modular and applies
`StatMech.fkg_inequality_events`. Mathlib's `IsUpperSet.le_card_inter_finset` is the counting
(uniform, `p = 1/2`) form of the same inequality, stated for families of finsets.

## References

* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Cambridge Philos. Soc. 56 (1960).
* D. J. Kleitman, *Families of non-disjoint subsets*, J. Combin. Theory 1 (1966).
-/

open scoped NNReal

namespace StatMech

open bernoulliProductMeasure

variable {E : Type*}

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The **Harris inequality** (Harris 1960): under the product Bernoulli(`p`) measure on a finite
configuration space, increasing events are positively correlated,
`P_p(A) * P_p(B) ≤ P_p(A ∩ B)`. No measurability hypothesis is needed since `E` is finite.
See also `IsUpperSet.le_card_inter_finset` (Harris–Kleitman, counting form). -/
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
