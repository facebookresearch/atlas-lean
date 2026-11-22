/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedRawHomIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceFullCoefficientFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceAllMaps

/-!
# The SAME native raw Hom is the entire original joint coefficient

The actual native ambient map is a mono. Every original raw Hom value
has a full flagged representative by the proved original inverse, and
every native input map hits all target joints from original source
joints. Its complete ambient image is therefore precisely the original
joint-coefficient complex, with both full inverse maps retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace
open OriginalFlaggedNecklace

/-- EVERY SAME native raw Hom has its full ambient flag containing all original target joints. -/
theorem ambientHomMap_joint_property (T : Data) {q : SimplexCategoryᵒᵖ}
    (a : (hom T.object.{u} (sourceVertex T) (targetVertex T)).obj q) :
    ∀ j ∈ T.joints, ULift.up.{u} j ∈ (((ambientHomMap T).app q a).obj 0).I := by
  have H : ∀ c : CategoryTheory.ConnectedComponents
      (Object T.object.{u} (sourceVertex T) (targetVertex T) q),
      ∀ j ∈ T.joints, ULift.up.{u} j ∈
        (((ambientHomMap T).app q
          (Components.rawEvaluation T.object (sourceVertex T) (targetVertex T) q c)).obj 0).I := by
    intro c
    induction c using _root_.Quotient.inductionOn' with
    | h U =>
      let f := Morphism.ofMap U.input (SSet.yonedaEquiv.injective U.source_eq)
        (SSet.yonedaEquiv.injective U.target_eq)
      have hI : nativeHomMap.{u} f = inputHomMap U :=
        pointedHomMap_eq (Morphism.ofMap_map U.input (SSet.yonedaEquiv.injective U.source_eq)
          (SSet.yonedaEquiv.injective U.target_eq)) (nativeMap_source f) (nativeMap_target f)
          (input_source U) (input_target U)
      have hs := ConcreteCategory.congr_hom (congr_app (ambientHomMap_native.{u} f) q)
        (coefficientLift U.necklace (jointCoefficient U))
      have he : (ambientHomMap T).app q (OriginalFlaggedNecklace.evaluation U) =
          (OriginalFlaggedNecklace.coefficientFunctor.{u}.map f).app q U.coefficient :=
        (congrArg (fun m => (ambientHomMap T).app q (m.app q
          (coefficientLift U.necklace (jointCoefficient U)))) hI).symm.trans
            (hs.trans (congrArg ((OriginalFlaggedNecklace.coefficientFunctor.map f).app q)
              (coefficientLift_ambient U.necklace (jointCoefficient U))))
      exact he.symm ▸ coefficientMap_joint_property f (jointCoefficient U)
  have ha := ConcreteCategory.congr_hom
    (congr_app (Components.rawHomMap_rawEvaluationMap T.object (sourceVertex T) (targetVertex T)) q) a
  change Components.rawEvaluation T.object (sourceVertex T) (targetVertex T) q
    ((Components.rawHomMap T.object (sourceVertex T) (targetVertex T)).app q a) = a at ha
  exact ha ▸ H ((Components.rawHomMap T.object (sourceVertex T) (targetVertex T)).app q a)

/-- The SAME entire native ambient Hom map lands in the exact original joint-coefficient complex. -/
def fullAmbientHomMap (T : Data) : hom T.object.{u} (sourceVertex T) (targetVertex T) ⟶ fullCoefficient.{u} T where
  app q := ↾fun a => ⟨(ambientHomMap T).app q a, ambientHomMap_joint_property T a⟩
  naturality _q _r θ := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((ambientHomMap T).naturality θ) a

/-- Both full original inverse maps identify the SAME native raw Hom with its entire joint coefficient. -/
def rawCoefficientIso (T : Data) : hom T.object.{u} (sourceVertex T) (targetVertex T) ≅ fullCoefficient.{u} T where
  hom := fullAmbientHomMap T
  inv := coefficientLiftMap T
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro a
    symm
    exact coefficientLift_unique T ⟨(ambientHomMap T).app q a, ambientHomMap_joint_property T a⟩ a rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact coefficientLift_ambient T p

/-- Every SAME original native map retains both full raw and joint-coefficient maps. -/
theorem rawCoefficientIso_natural {T U : Data} (f : T ⟶ U) :
    nativeHomMap.{u} f ≫ (rawCoefficientIso U).hom = (rawCoefficientIso T).hom ≫ fullCoefficientMap f := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (congr_app (ambientHomMap_native.{u} f) q) a

/-- The native raw coefficient isomorphism retains its SAME entire ambient Hom map. -/
theorem rawCoefficientIso_hom_val (T : Data) {q : SimplexCategoryᵒᵖ}
    (a : (hom T.object.{u} (sourceVertex T) (targetVertex T)).obj q) :
    ((rawCoefficientIso T).hom.app q a).val = (ambientHomMap T).app q a := rfl

/-- The native raw coefficient inverse retains its SAME uniquely determined complete original lift. -/
theorem rawCoefficientIso_inv_app (T : Data) {q : SimplexCategoryᵒᵖ}
    (p : (fullCoefficient.{u} T).obj q) : (rawCoefficientIso T).inv.app q p = coefficientLift T p := rfl

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
