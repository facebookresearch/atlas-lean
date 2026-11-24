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
# Separability of actual C-star quotients and extensions

The quotient uses the existing canonical normed-module quotient. For an
extension, the actual quotient is open by Banach open mapping and its
kernel is the continuous image of the actual ideal coefficient. No
splitting, nuclearity, or separable-middle result field is assumed.
-/

@[expose] public section

open TopologicalSpace
open scoped CStarAlgebra

universe uA uB uM

namespace ClosedStarIdeal

/-- The actual quotient of a separable C-star algebra by a closed star ideal
is separable, with the existing scoped quotient dictionary. -/
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

/-- In a genuine normalized extension, separable endpoints imply that its
actual middle algebra is separable. There is no section hypothesis. -/
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
