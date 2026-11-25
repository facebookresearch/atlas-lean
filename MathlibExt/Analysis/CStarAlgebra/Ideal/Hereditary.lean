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

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Hereditary nonunital star subalgebras

The predicate records only downward closure among positive elements in the
canonical spectral order. Closedness and fullness are separate properties.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace NonUnitalStarSubalgebra

universe uA

/-- **Hereditary star subalgebra.** For a nonunital complex C*-algebra `A`, a nonunital star subalgebra
`S ⊆ A` is hereditary when `0 ≤ a ≤ b` and `b ∈ S` imply `a ∈ S`, with inequalities in spectral
order. This condition concerns positive elements and does not itself require `S` to be topologically
closed. -/
def IsHereditary
    {A : Type uA} [NonUnitalCStarAlgebra A]
    (S : NonUnitalStarSubalgebra ℂ A) : Prop :=
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  ∀ {x y : A}, 0 ≤ x → 0 ≤ y → y ∈ S → x ≤ y → x ∈ S

end NonUnitalStarSubalgebra
