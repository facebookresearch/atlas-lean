/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentProperFaceDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeFaceRangeIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCosimplicial

/-!
# The actual original proper-face right-cube boundary cocone

Every original proper injection lands in the genuine proper-support
boundary. All original structured-arrow maps retain that same inclusion.
The cocone is on the actual opposite matching diagram, not an assumed
latching presentation. Its colimit property is a separate proof.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeLatchingDiagram
open RightCubeSupport RightCubeSupportOperators RightCubeSupportBoundary RightCubeFaceRangeIso

/-- The actual whole original proper-injection quotient-cube diagram. -/
def diagram (n : ℕ) : (SimplicialObject.matchingIndex n)ᵒᵖ ⥤ SSet.{u} :=
  ProperFaceIndex.diagram n ⋙ RightCubeCosimplicial.diagram

/-- A proper original injection omits an individual original target label. -/
theorem proper_range {n : ℕ} (a : SimplicialObject.matchingIndex n) :
    ∃ j : Fin (n + 1), j ∉ Set.range a.obj.hom.unop.toOrderHom := by
  classical
  exact not_forall.mp (ProperFaceIndex.not_surjective a)

/-- The actual original quotient proper-face map with values in its whole proper-support boundary. -/
def inclusion {n : ℕ} (a : SimplicialObject.matchingIndex n) :
    RightCubeRelations.object.{u} a.obj.right.unop.len ⟶ boundary.{u} n where
  app q := ↾fun b => ⟨(RightCubeCosimplicialMaps.map a.obj.hom.unop).app q b, by
    change ∃ j : Fin (n + 1), j ∉ quotientSupport ((RightCubeCosimplicialMaps.map a.obj.hom.unop).app q b)
    obtain ⟨j, hj⟩ := proper_range a
    refine ⟨j, ?_⟩
    intro h
    have himage := quotientSupport_image a.obj.hom.unop b
    have h' : j ∈ a.obj.hom.unop.toOrderHom '' quotientSupport b := Eq.mp (congrArg (fun S => j ∈ S) himage) h
    obtain ⟨k, _, hk⟩ := h'
    exact hj ⟨k, hk⟩⟩
  naturality q r η := by
    ext b
    apply Subtype.ext
    exact congr($((RightCubeCosimplicialMaps.map a.obj.hom.unop).naturality η) b)

/-- The entire original proper-face boundary map retains exactly the original quotient operator after its
  actual ambient inclusion. -/
theorem inclusion_ι {n : ℕ} (a : SimplicialObject.matchingIndex n) :
    inclusion.{u} a ≫ (boundary n).ι = RightCubeCosimplicialMaps.map a.obj.hom.unop := by ext q b; rfl

/-- All original proper-injection morphisms retain the same whole actual boundary inclusion. -/
theorem inclusion_naturality {n : ℕ} {a b : SimplicialObject.matchingIndex n} (g : a ⟶ b) :
    RightCubeCosimplicialMaps.map.{u} g.hom.right.unop ≫ inclusion a = inclusion b := by
  apply (cancel_mono (boundary.{u} n).ι).1
  have hcomp : RightCubeCosimplicialMaps.map.{u} g.hom.right.unop ≫ RightCubeCosimplicialMaps.map a.obj.hom.unop =
      RightCubeCosimplicialMaps.map (g.hom.right.unop ≫ a.obj.hom.unop) :=
    (RightCubeCosimplicial.diagram.map_comp _ _).symm
  exact (Category.assoc (RightCubeCosimplicialMaps.map g.hom.right.unop) (inclusion a) (boundary n).ι).trans
    ((congrArg (fun f => RightCubeCosimplicialMaps.map g.hom.right.unop ≫ f) (inclusion_ι a)).trans
      (hcomp.trans ((congrArg (fun θ => RightCubeCosimplicialMaps.map.{u} θ)
        (congrArg Quiver.Hom.unop (StructuredArrow.w g.hom))).trans (inclusion_ι b).symm)))

/-- The genuine entire boundary cocone on the original opposite matching-index diagram. -/
def cocone (n : ℕ) : Cocone (diagram.{u} n) where
  pt := boundary n
  ι := {
    app := fun a => inclusion a.unop
    naturality := by
      intro a b g
      change RightCubeCosimplicialMaps.map g.unop.hom.right.unop ≫ inclusion b.unop = inclusion a.unop ≫ 𝟙 _
      rw [Category.comp_id]
      exact inclusion_naturality g.unop }

/-- The actual original coface leg into the proper-support boundary is the genuine omitted-support inclusion
  after its whole cube isomorphism. -/
theorem inclusion_face (n : ℕ) (i : Fin (n + 2)) :
    inclusion.{u} (ProperFaceIndex.face n i) =
      (cofaceIso i).hom ≫ SSet.Subcomplex.homOfLE (missing_le_boundary (n + 1) i) := by
  apply (cancel_mono (boundary.{u} (n + 1)).ι).1
  exact (inclusion_ι (ProperFaceIndex.face n i)).trans
    (((cofaceIso_inclusion i).symm.trans
      (congrArg (fun f => (cofaceIso.{u} i).hom ≫ f) (SSet.Subcomplex.homOfLE_ι (missing_le_boundary (n + 1)
        i)).symm)).trans
        (Category.assoc (cofaceIso i).hom (SSet.Subcomplex.homOfLE (missing_le_boundary (n + 1) i))
          (boundary (n + 1)).ι).symm)

end CategoryTheory.CoherentRealization.RightCubeLatchingDiagram
