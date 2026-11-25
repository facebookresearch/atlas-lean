/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Extension.Basic
public import Mathlib.Topology.Bases

import MathlibExt.Topology.Maps.Separable
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Separability of C-star quotients and extensions

A quotient of a separable nonunital C-star algebra by a closed two-sided star ideal is separable
for the quotient norm topology. For an extension `0 → B → E → A → 0`, separability of `A` and
`B` implies separability of `E`: the quotient map is open and its kernel is identified with `B`.
-/

@[expose] public section

open TopologicalSpace
open scoped CStarAlgebra

universe uA uB uM

namespace ClosedStarIdeal

/-- **Separability of a closed-ideal quotient.** If the nonunital C-star algebra `A` is separable
and `I` is a closed two-sided star ideal, the normed quotient `A/I` is separable. -/
theorem separable_quotient {A : Type uA} [NonUnitalCStarAlgebra A] [SeparableSpace A]
    (I : ClosedStarIdeal A) :
    letI : I.carrier.IsTwoSided := I.isTwoSided;
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra;
    SeparableSpace I.Quotient := by
  let : I.carrier.IsTwoSided := I.isTwoSided
  let : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  exact I.quotientMap_surjective.denseRange.separableSpace (map_continuous I.quotientMap)

end ClosedStarIdeal

namespace CStarExtension

/-- **Separability of an extension algebra.** For a C-star extension `0 → B → X.Middle → A → 0`,
separability of the nonunital endpoint algebras `A,B` implies `SeparableSpace X.Middle`. -/
theorem separable_middle {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [SeparableSpace A] [SeparableSpace B]
    (X : CStarExtension.{uA, uB, uM} A B) : SeparableSpace X.Middle := by
  let qAdd : X.Middle →+ A :=
    { toFun := X.quotient
      map_zero' := map_zero X.quotient
      map_add' := map_add X.quotient }
  let qL : X.Middle →L[ℂ] A :=
    { toLinearMap := LinearMap.ofClass X.quotient
      cont := map_continuous X.quotient }
  have hOpen : IsOpenMap qAdd := qL.isOpenMap X.quotient_surjective
  let j : B → qAdd.ker := fun b ↦
    ⟨X.inclusion b, (AddMonoidHom.mem_ker).2 (X.exact.apply_apply_eq_zero b)⟩
  have hjContinuous : Continuous j := (map_continuous X.inclusion).subtype_mk _
  have hjSurjective : Function.Surjective j := by
    intro z
    obtain ⟨b, hb⟩ := (X.exact z.val).1 ((AddMonoidHom.mem_ker).1 z.property)
    exact ⟨b, Subtype.ext hb⟩
  let : SeparableSpace qAdd.ker :=
    hjSurjective.denseRange.separableSpace hjContinuous
  exact IsOpenMap.separableSpace_of_separable_ker qAdd hOpen

end CStarExtension
