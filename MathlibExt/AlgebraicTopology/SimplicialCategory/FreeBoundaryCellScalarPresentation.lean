/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeIndexedMonoPushoutScalarPresentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFamilies
import MathlibExt.AlgebraicTopology.SimplicialCategory.SingleHomQuiverMaps
import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

/-!
# Full original free scalar presentations of actual boundary-cell attachments

All original boundary cells are read from their actual family-membership
witnesses. Their whole original coproduct cocones and actual pushout map
are retained through exact single-Hom quiver coordinates. The full scalar
free presentation is then constructed by the genuine indexed monic
attachment theorem, including zero-dimensional and loop cells.
-/

noncomputable section
universe u v w
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeBoundaryCells
open RelativeWords

private def cofanIsColimitOfPointwiseIso {D : Type v} [Category.{w} D]
    {I : Type u} {X Y : I → D} (e : ∀ i, X i ≅ Y i)
    (c : Cofan Y) (hc : IsColimit c) :
    IsColimit (Cofan.mk c.pt (fun i => (e i).hom ≫ c.inj i)) := by
  let d : Discrete.functor X ≅ Discrete.functor Y := Discrete.natIso (fun i => e i.as)
  exact (IsColimit.precomposeHomEquiv d c).symm hc

variable {O : Type u}

/-- The actual original boundary-cell labels, with all original endpoint pairs. -/
abbrev Index (O : Type u) := O × O × ℕ

/-- The SAME original boundary-domain generating quiver. -/
abbrev domainQuiver (i : Index O) : SimplicialQuiver.Data O :=
  SimplicialQuiver.SingleHom.quiver i.1 i.2.1 (∂Δ[i.2.2] : SSet.{u})

/-- The SAME original simplex-target generating quiver. -/
abbrev targetQuiver (i : Index O) : SimplicialQuiver.Data O :=
  SimplicialQuiver.SingleHom.quiver i.1 i.2.1 (Δ[i.2.2] : SSet.{u})

/-- The SAME original boundary map at its supplied ordered pair. -/
def quiverMap (i : Index O) : ∀ a b : O, (domainQuiver i).Hom a b ⟶ (targetQuiver i).Hom a b :=
  SimplicialQuiver.SingleHom.quiverMap i.1 i.2.1 (∂Δ[i.2.2]).ι

/-- Every actual original boundary quiver map is genuinely monic. -/
theorem quiverMap_mono (i : Index O) (a b : O) : Mono (quiverMap i a b) := by
  classical
  by_cases h : a = i.1 ∧ b = i.2.1
  · rcases h with ⟨rfl, rfl⟩
    rw [quiverMap, SimplicialQuiver.SingleHom.quiverMap_at]
    infer_instance
  · rw [quiverMap, SimplicialQuiver.SingleHom.quiverMap_other _ _ _ a b h]
    infer_instance

/-- Literal original family membership selects the SAME entire canonical boundary arrow. -/
def index (i : (boundaryFamily O).toSet) : Index O :=
  ((MorphismProperty.ofHoms_iff
    (fun i : Index O => (FreeSingleHom.functor i.1 i.2.1).map (∂Δ[i.2.2]).ι)
    i.val.hom).mp i.property).choose

/-- The selected actual cell is the SAME original free quiver arrow, as a full arrow equality. -/
theorem index_spec (i : (boundaryFamily O).toSet) :
    i.val = Arrow.mk (FreeQuiver.map (quiverMap (index i))) := by
  have h := ((MorphismProperty.ofHoms_iff
    (fun i : Index O => (FreeSingleHom.functor i.1 i.2.1).map (∂Δ[i.2.2]).ι)
    i.val.hom).mp i.property).choose_spec
  have hi : i.val = Arrow.mk i.val.hom := by
    cases i with | mk i hi => cases i; rfl
  exact hi.trans
    (h.trans (congrArg Arrow.mk
      (SimplicialQuiver.SingleHom.free_quiverMap (index i).1 (index i).2.1
        (∂Δ[(index i).2.2]).ι)).symm)

variable {C D : FixedObjects O} {f : C ⟶ D}
  (a : AttachCells.{u} (boundaryFamily O).homFamily f)

/-- The genuine original cell inclusion is represented by its canonical boundary quiver arrow. -/
def cellArrowIso (i : a.ι) :
    Arrow.mk (FreeQuiver.map (quiverMap (index (a.π i)))) ≅ Arrow.mk ((boundaryFamily O).homFamily (a.π i)) :=
  eqToIso (index_spec (a.π i)).symm

/-- The full original boundary-domain coproduct cocone with its SAME actual source maps. -/
def domainCofan : Cofan (fun i : a.ι => FreeQuiver.object (domainQuiver (index (a.π i)))) :=
  Cofan.mk a.cofan₁.pt (fun i => (Arrow.leftFunc.mapIso (cellArrowIso a i)).hom ≫ a.cofan₁.inj i)

/-- The full original simplex-target coproduct cocone with its SAME actual target maps. -/
def targetCofan : Cofan (fun i : a.ι => FreeQuiver.object (targetQuiver (index (a.π i)))) :=
  Cofan.mk a.cofan₂.pt (fun i => (Arrow.rightFunc.mapIso (cellArrowIso a i)).hom ≫ a.cofan₂.inj i)

/-- The actual domain coproduct universal property is retained by the exact original cell coordinates. -/
def domainIsColimit : IsColimit (domainCofan a) :=
  cofanIsColimitOfPointwiseIso
    (fun i : a.ι => Arrow.leftFunc.mapIso (cellArrowIso a i)) a.cofan₁ a.isColimit₁

/-- The actual target coproduct universal property is retained by the exact original cell coordinates. -/
def targetIsColimit : IsColimit (targetCofan a) :=
  cofanIsColimitOfPointwiseIso
    (fun i : a.ι => Arrow.rightFunc.mapIso (cellArrowIso a i)) a.cofan₂ a.isColimit₂

/-- Every original cell square is the SAME full coproduct map square under its coordinates. -/
theorem coproductMap (i : a.ι) :
    (domainCofan a).inj i ≫ a.m =
      FreeQuiver.map (quiverMap (index (a.π i))) ≫ (targetCofan a).inj i := by
  have hw := (cellArrowIso a i).hom.w
  change (_ ≫ a.cofan₁.inj i) ≫ a.m = _ ≫ _ ≫ a.cofan₂.inj i
  rw [Category.assoc, a.hm, ← Category.assoc]
  exact (congrArg (fun e => e ≫ a.cofan₂.inj i) hw).trans (Category.assoc _ _ _)

/-- Construct the actual full scalar free presentation of the SAME original boundary attachment. -/
def scalarPresentation (q : SimplexCategoryᵒᵖ)
    (P : FreePresentation.{u,u,u} (scalarCategory C q)) :
    FreePresentation.{u,u,u} (scalarCategory D q) :=
  FreeIndexedMonoPushout.scalarPresentation (fun i => quiverMap (index (a.π i)))
    (fun i => quiverMap_mono (index (a.π i)))
    (domainCofan a) (targetCofan a) (domainIsColimit a) (targetIsColimit a)
    a.m (coproductMap a) a.g₁ f a.g₂ a.isPushout q P

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeBoundaryCells
