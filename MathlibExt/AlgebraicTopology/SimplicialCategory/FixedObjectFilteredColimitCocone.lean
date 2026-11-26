/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectDiagramEnrichment
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps
import MathlibExt.AlgebraicTopology.SimplicialSet.FilteredColimitMonoidal

/-!
# The actual filtered fixed-object colimit object and cocone

The pointwise Hom diagram is transported through the genuinely monoidal
scalar filtered colimit. Its original object labels remain unchanged.
The canonical cocone is constructed from the actual scalar injections
and their proved identity and composition equations.
-/

noncomputable section
universe u v w
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FilteredColimit

variable {O : Type u} {J : Type v} [Category.{w} J] [IsFiltered J] [Small.{u} J]
  (F : J ⥤ FixedObjects O)

/-- The actual enrichment on the same original labels, with scalar filtered-colimit Homs. -/
def object : FixedObjects O := by
  letI := diagramEnrichment F
  let X := TransportEnrichment (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) O
  exact ⟨SimplicialEnrichment.of X, rfl⟩

/-- Its whole original Hom object is the actual scalar filtered colimit. -/
theorem object_hom (x y : O) : hom (object F) x y = colimit (homDiagram F x y) := rfl

/-- The actual identity is the colimit monoidal unit followed by the original diagram identity. -/
theorem object_identity (x : O) : identityMap (object F) x =
    Functor.LaxMonoidal.ε (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) ≫
      colim.map (diagramIdentity F x) := rfl

/-- The actual composition is the colimit tensorator followed by the original diagram composition. -/
theorem object_composition (x y z : O) : compositionMap (object F) x y z =
    Functor.LaxMonoidal.μ (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u})
      (homDiagram F x y) (homDiagram F y z) ≫ colim.map (diagramComposition F x y z) := rfl

/-- The whole original scalar injection at the supplied indexing object and two endpoint labels. -/
def injectionHom (j : J) (x y : O) : hom (F.obj j) x y ⟶ hom (object F) x y :=
  colimit.ι (homDiagram F x y) j

private theorem injection_identity (j : J) (x : O) :
    identityMap (F.obj j) x ≫ injectionHom F j x x = identityMap (object F) x := by
  have h := (SSet.FilteredColimit.injection.{u, v, w} J j).naturality (diagramIdentity F x)
  change identityMap (F.obj j) x ≫ colimit.ι (homDiagram F x x) j =
    colimit.ι (𝟙_ (J ⥤ SSet.{u})) j ≫ colim.map (diagramIdentity F x) at h
  rw [SSet.FilteredColimit.injection_unit] at h
  exact h

private theorem injection_composition (j : J) (x y z : O) :
    compositionMap (F.obj j) x y z ≫ injectionHom F j x z =
      (injectionHom F j x y ⊗ₘ injectionHom F j y z) ≫ compositionMap (object F) x y z := by
  have h := (SSet.FilteredColimit.injection.{u, v, w} J j).naturality (diagramComposition F x y z)
  change compositionMap (F.obj j) x y z ≫ colimit.ι (homDiagram F x z) j =
    colimit.ι (homDiagram F x y ⊗ homDiagram F y z) j ≫ colim.map (diagramComposition F x y z) at h
  exact h.trans
    ((congrArg (fun k => k ≫ colim.map (diagramComposition F x y z))
      (SSet.FilteredColimit.injection_tensor J j (homDiagram F x y) (homDiagram F y z)).symm).trans
        (Category.assoc _ _ _))

/-- The actual whole enriched cocone leg, preserving every original object label and Hom injection. -/
def injection (j : J) : F.obj j ⟶ object F :=
  ofHomMaps (injectionHom F j) (injection_identity F j) (injection_composition F j)

/-- The constructed cocone leg acts by the same whole original scalar Hom injection. -/
@[simp]
theorem homMap_injection (j : J) (x y : O) :
    homMap (injection F j) x y = colimit.ι (homDiagram F x y) j :=
  homMap_ofHomMaps _ _ _ x y

/-- The cocone leg carries the exact supplied individual original object label. -/
@[simp]
theorem injection_obj (j : J) (a : (F.obj j).val) :
    (injection F j).val.obj a = vertex (object F) (label (F.obj j) a) := rfl

/-- The genuine cocone over the original fixed-object diagram. -/
def cocone : Cocone F where
  pt := object F
  ι := {
    app := injection F
    naturality j k f := by
      change F.map f ≫ injection F k = injection F j ≫ 𝟙 (object F)
      apply homMaps_ext
      intro x y
      rw [homMap_comp, homMap_comp, homMap_id, Category.comp_id,
        homMap_injection, homMap_injection]
      exact colimit.w (homDiagram F x y) f }

end CategoryTheory.SimplicialEnrichment.FixedObjects.FilteredColimit
