/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Preference.OrdinalInvariance

@[expose] public section

/-!
# Ordinal utility on the attained range

An ordinal utility records comparisons, not the sizes of utility differences. Two utilities for
one preference therefore determine the same ordered scale up to an order isomorphism of their
attained ranges. A strictly increasing extension to all of `ℝ` need not exist.

L. Blume, *Ordinal Representations* (September 1, 2006), §1, defines representation using strict
preference (Definition 1, p. 1) and gives invariance under a strictly increasing real transformation
(Definition 2, p. 2). The attained-range isomorphism below is derived from the weak comparisons in
`Preference.Represents`.
-/

namespace MathlibExt.Economics.Preference.Represents

variable {X : Type*} {P : Preference X} {u v : X → ℝ}

/-- If `u` and `v` both represent the weak preference `P` on `X`, there is an order isomorphism
from the attained values of `u` onto those of `v` sending `u x` to `v x` for every `x : X`. -/
theorem exists_rangeOrderIso (hu : P.Represents u) (hv : P.Represents v) :
    ∃ e : Set.range u ≃o Set.range v,
      ∀ x, e (Set.rangeFactorization u x) = Set.rangeFactorization v x := by
  have hle (x y : X) : v x ≤ v y ↔ u x ≤ u y := (hv y x).symm.trans (hu y x)
  have hties : v.FactorsThrough u := fun {x y} h =>
    le_antisymm ((hle x y).2 h.le) ((hle y x).2 h.ge)
  let f := Set.rangeFactorization v ∘ Set.rangeSplitting u
  have hmap (x : X) : f (Set.rangeFactorization u x) = Set.rangeFactorization v x :=
    Subtype.ext (hties (Set.apply_rangeSplitting u (Set.rangeFactorization u x)))
  have hf (a b : Set.range u) : f a ≤ f b ↔ a ≤ b := by
    change v (Set.rangeSplitting u a) ≤ v (Set.rangeSplitting u b) ↔ (a : ℝ) ≤ b
    rw [hle, Set.apply_rangeSplitting u a, Set.apply_rangeSplitting u b]
  refine ⟨OrderIso.ofSurjective (OrderEmbedding.ofMapLEIff f hf) ?_, hmap⟩
  rintro ⟨_, x, rfl⟩
  exact ⟨_, hmap x⟩

/-- If `u` represents the weak preference `P` and `f` is strictly increasing from the range of
`u` to `ℝ`, then the utility sending `x` to `f` of the attained value `u x` also represents `P`. -/
theorem comp_rangeFactorization (hu : P.Represents u) {f : Set.range u → ℝ}
    (hf : StrictMono f) : P.Represents (f ∘ Set.rangeFactorization u) :=
  fun x y => (hu x y).trans (hf.le_iff_le (a := Set.rangeFactorization u y)
    (b := Set.rangeFactorization u x)).symm

end MathlibExt.Economics.Preference.Represents
