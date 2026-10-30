/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.ConfigSpace

@[expose] public section

/-!
# Increasing events and the FKG lattice condition

This file sets up the order-theoretic vocabulary for correlation inequalities on the
configuration space `ConfigSpace E = E → Bool`, ordered coordinatewise (`false < true`).

An event is *increasing* if it is an upper set: whenever a configuration lies in the event, so
does every configuration obtained by opening further coordinates. A weight function
`π : ConfigSpace E → ℝ` satisfies the *FKG lattice condition* if
`π ω * π ω' ≤ π (ω ⊔ ω') * π (ω ⊓ ω')` for all `ω ω'`.

## Main definitions

* `StatMech.IsIncreasing`, `StatMech.IsDecreasing`: increasing (upper) and decreasing (lower)
  events; these are `IsUpperSet` and `IsLowerSet` on `ConfigSpace E`.
* `StatMech.FKGLatticeCondition`: the FKG lattice condition (log-supermodularity) of a weight.

## Main results

* `StatMech.isIncreasing_iff_indicator_monotone`: an event is increasing iff its real-valued
  indicator function is monotone.
* `StatMech.FKGLatticeCondition.of_logModular`: a log-modular weight (for example a product
  Bernoulli weight) satisfies the FKG lattice condition.

## References

* C. M. Fortuin, P. W. Kasteleyn, J. Ginibre, *Correlation inequalities on some partially ordered
  sets*, Comm. Math. Phys. 22 (1971).
-/

namespace StatMech

open ConfigSpace

variable {E : Type*}

/-- An event `A ⊆ ConfigSpace E` is *increasing* if it is an upper set for the coordinatewise
order: `ω ∈ A` and `ω ≤ ω'` imply `ω' ∈ A`. This is `IsUpperSet A`. -/
def IsIncreasing (A : Set (ConfigSpace E)) : Prop := IsUpperSet A

/-- An event `A ⊆ ConfigSpace E` is *decreasing* if it is a lower set for the coordinatewise
order. This is `IsLowerSet A`. -/
def IsDecreasing (A : Set (ConfigSpace E)) : Prop := IsLowerSet A

/-- The complement of an increasing event is decreasing (`IsUpperSet.compl`). -/
lemma IsIncreasing.compl {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    IsDecreasing Aᶜ := IsUpperSet.compl hA

/-- The complement of a decreasing event is increasing (`IsLowerSet.compl`). -/
lemma IsDecreasing.compl {A : Set (ConfigSpace E)} (hA : IsDecreasing A) :
    IsIncreasing Aᶜ := IsLowerSet.compl hA

/-- The intersection of two increasing events is increasing (`IsUpperSet.inter`). -/
lemma IsIncreasing.inter {A B : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) : IsIncreasing (A ∩ B) :=
  IsUpperSet.inter hA hB

/-- The union of two increasing events is increasing (`IsUpperSet.union`). -/
lemma IsIncreasing.union {A B : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) : IsIncreasing (A ∪ B) :=
  IsUpperSet.union hA hB

/-- An intersection of increasing events is increasing (`isUpperSet_iInter`). -/
lemma isIncreasing_iInter {ι : Sort*} {A : ι → Set (ConfigSpace E)}
    (hA : ∀ i, IsIncreasing (A i)) : IsIncreasing (⋂ i, A i) :=
  isUpperSet_iInter hA

/-- The real indicator function of an increasing event is monotone. -/
lemma IsIncreasing.indicator_monotone {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    Monotone (A.indicator (fun _ => (1 : ℝ))) := by
  intro x y hxy
  simp only [Set.indicator]
  split_ifs with hxA hyA
  · exact le_refl _
  · exact absurd (hA hxy hxA) hyA
  · exact zero_le_one
  · exact le_refl _

/-- An event is increasing iff its real indicator function is monotone. See also
`Set.monotone_mem`, the analogous statement for the `Prop`-valued membership predicate. -/
theorem isIncreasing_iff_indicator_monotone {A : Set (ConfigSpace E)} :
    IsIncreasing A ↔ Monotone (A.indicator (fun _ => (1 : ℝ))) := by
  refine ⟨IsIncreasing.indicator_monotone, fun h x y hxy hx => ?_⟩
  have h1 : A.indicator (fun _ => (1 : ℝ)) x = 1 := by rw [Set.indicator_of_mem hx]
  have hle := h hxy
  rw [h1] at hle
  by_contra hy
  rw [Set.indicator_of_notMem hy] at hle
  linarith

/-- The *FKG lattice condition* on a weight `π : ConfigSpace E → ℝ`:
`π ω * π ω' ≤ π (ω ⊔ ω') * π (ω ⊓ ω')` for all configurations `ω ω'`. For a positive weight this
is log-supermodularity. Mathlib's `fkg` and `holley` state it in the form
`π a * π b ≤ π (a ⊓ b) * π (a ⊔ b)`. -/
def FKGLatticeCondition (π : ConfigSpace E → ℝ) : Prop :=
  ∀ ω ω', π ω * π ω' ≤ π (ω ⊔ ω') * π (ω ⊓ ω')

/-- A log-modular weight, `π ω * π ω' = π (ω ⊔ ω') * π (ω ⊓ ω')`, satisfies the FKG lattice
condition. -/
lemma FKGLatticeCondition.of_logModular {π : ConfigSpace E → ℝ}
    (h : ∀ ω ω', π ω * π ω' = π (ω ⊔ ω') * π (ω ⊓ ω')) : FKGLatticeCondition π :=
  fun ω ω' => le_of_eq (h ω ω')

end StatMech
