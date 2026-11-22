/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import MathlibExt.RingTheory.DedekindDomain.DiscriminantTower

/-!
# The discriminant ideal of a number field

For a number field `K`, the discriminant ideal of `𝓞 K / ℤ` has absolute
norm equal to the absolute discriminant of `K`. This connects the
ideal-theoretic discriminant of `Ideal.discriminantIdeal` with the
integer `NumberField.discr`.

## Main results

* `Ideal.absNorm_discriminantIdeal`: the absolute norm of the discriminant
  ideal of `𝓞 K / ℤ` is `(discr K).natAbs`.
-/

@[expose] public section

namespace Ideal

/-- The absolute norm of the discriminant ideal of `𝓞 K / ℤ` is the absolute
discriminant of `K`. -/
theorem absNorm_discriminantIdeal (K : Type*) [Field K] [NumberField K] :
    Ideal.absNorm (discriminantIdeal ℤ (NumberField.RingOfIntegers K)) =
      (NumberField.discr K).natAbs := by
  rw [discriminantIdeal_eq_spanNorm, Ideal.spanNorm_eq, Ideal.absNorm_relNorm]
  exact NumberField.absNorm_differentIdeal K (NumberField.RingOfIntegers K)

end Ideal
