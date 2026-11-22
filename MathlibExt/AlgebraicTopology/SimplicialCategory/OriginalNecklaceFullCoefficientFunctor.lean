/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceJointPreimages
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceJointCoefficients
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceCoefficientFunctor

/-!
# The entire original joint-coefficient functor

Every full native necklace map acts on every original joint-containing
flag by its actual direct-image operator. The target joint preimages
prove the same complete image is again a full coefficient. No restriction
to flanked flags or surjective maps is imposed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace

/-- Every original full coefficient retains all actual target joints under the SAME native map. -/
theorem coefficientMap_joint_property {T U : Data} (f : T ⟶ U) {q : SimplexCategoryᵒᵖ}
    (p : (fullCoefficient.{u} T).obj q) :
    ∀ j ∈ U.joints, ULift.up.{u} j ∈
      (((OriginalFlaggedNecklace.coefficientFunctor.{u}.map f).app q p.val).obj 0).I := by
  intro j hj
  obtain ⟨i, hi, he⟩ := target_joint_preimage f j hj
  exact ⟨ULift.up.{u} i, p.property i hi, ULift.ext he⟩

/-- The SAME actual full original coefficient map in every scalar degree. -/
def fullCoefficientMap {T U : Data} (f : T ⟶ U) : fullCoefficient.{u} T ⟶ fullCoefficient U where
  app q := ↾fun p => ⟨(OriginalFlaggedNecklace.coefficientFunctor.map f).app q p.val,
    coefficientMap_joint_property f p⟩
  naturality _q _r θ := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((OriginalFlaggedNecklace.coefficientFunctor.map f).naturality θ) p.val

/-- The SAME entire original joint-coefficient diagram on the full native necklace category. -/
def fullCoefficientFunctor : Data ⥤ SSet.{u} where
  obj := fullCoefficient
  map f := fullCoefficientMap f
  map_id T := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (congr_app (OriginalFlaggedNecklace.coefficientFunctor.map_id T) q) p.val
  map_comp f g := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (congr_app (OriginalFlaggedNecklace.coefficientFunctor.map_comp f g) q) p.val

/-- Every SAME full coefficient map retains the entire original direct-image coefficient. -/
theorem fullCoefficientMap_val {T U : Data} (f : T ⟶ U) {q : SimplexCategoryᵒᵖ}
    (p : (fullCoefficient.{u} T).obj q) :
    ((fullCoefficientMap f).app q p).val = (OriginalFlaggedNecklace.coefficientFunctor.map f).app q p.val := rfl

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
