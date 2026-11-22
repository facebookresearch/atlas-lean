/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.Products
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Positive homotopy groups of products with small original labels

The existing native product theorem is transported through an equivalence
of the original label type with its carrier-universe shrink. The chosen
product and every original projection remain fixed. In particular finite
labels need no equality between their universe and the point universe.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits

namespace PointedCGWH.SmallHomotopyProductGeometry

private def groupPiReindex {α : Type v} {β : Type w} (P : β → Type v)
    [∀ b, Group (P b)] (e : α ≃ β) : (∀ a, P (e a)) ≃* ∀ b, P b where
  toEquiv := Equiv.piCongrLeft P e
  map_mul' a b := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact (Equiv.piCongrLeft_apply_apply P e (a * b) j).trans
      (congrArg₂ (fun x y => x * y)
        (Equiv.piCongrLeft_apply_apply P e a j)
        (Equiv.piCongrLeft_apply_apply P e b j)).symm

private theorem groupPiReindex_apply {α : Type v} {β : Type w} (P : β → Type v)
    [∀ b, Group (P b)] (e : α ≃ β) (z : ∀ a, P (e a)) (a : α) :
    groupPiReindex P e z (e a) = z a :=
  Equiv.piCongrLeft_apply_apply P e z a

variable {ι : Type w} [Small.{v} ι] (X : ι → PointedCGWH.{u, v}) [HasProduct X]

/-- The exact original label equivalence into its carrier-sized shrink. -/
def labels : Shrink.{v} ι ≃ ι := (equivShrink ι).symm

/-- The same original family at carrier-sized labels. -/
def family : Shrink.{v} ι → PointedCGWH.{u, v} := fun i => X (labels (ι := ι) i)

private instance familyHasProduct : HasProduct (family X) :=
  ⟨⟨Fan.mk (∏ᶜ X) (fun i => Pi.π X (labels (ι := ι) i)),
    (Fan.isLimitEquivOfEquiv (labels (ι := ι)) (limit.cone (Discrete.functor X)))
      (limit.isLimit _)⟩⟩

/-- The chosen original product is retained under the actual label reindexing Iso. -/
def sourceIso : (∏ᶜ X) ≅ ∏ᶜ family X :=
  (Pi.reindex (labels (ι := ι)) X).symm

/-- Every shrunk coordinate keeps the same actual original pointed projection. -/
theorem sourceIso_projection (i : Shrink.{v} ι) :
    (sourceIso X).hom ≫ Pi.π (family X) i = Pi.π X (labels (ι := ι) i) :=
  Pi.reindex_inv_π (labels (ι := ι)) X i

/-- Reindexing the coordinate group family retains its original coordinate functions. -/
def coordinateEquiv (k : ℕ) :
    (∀ i : Shrink.{v} ι, PointedCGWH.piN (k + 1) (family X i)) ≃*
      ∀ i : ι, PointedCGWH.piN (k + 1) (X i) :=
  groupPiReindex (fun i => PointedCGWH.piN (k + 1) (X i)) (labels (ι := ι))

/-- The actual original product has the complete positive homotopy coordinate equivalence. -/
def equiv (k : ℕ) :
    PointedCGWH.piN (k + 1) (∏ᶜ X) ≃* ∀ i, PointedCGWH.piN (k + 1) (X i) :=
  (((PointedCGWH.piNPositiveFunctor k).mapIso (sourceIso X)).groupIsoToMulEquiv).trans
    ((PointedCGWH.HomotopyProductGeometry.selectedEquiv (family X) k).trans (coordinateEquiv X k))

/-- The whole small-label product equivalence retains every original positive projection map. -/
theorem equiv_projection (k : ℕ) (z : PointedCGWH.piN (k + 1) (∏ᶜ X)) (i : ι) :
    equiv X k z i = ((PointedCGWH.piNPositiveFunctor k).map (Pi.π X i)).hom z := by
  obtain ⟨j, rfl⟩ := (labels (ι := ι)).surjective i
  let a : PointedCGWH.piN (k + 1) (∏ᶜ family X) :=
    ((PointedCGWH.piNPositiveFunctor k).map (sourceIso X).hom).hom z
  have h := PointedCGWH.HomotopyProductGeometry.selectedEquiv_projection (family X) k a j
  have hm := ConcreteCategory.congr_hom
    ((PointedCGWH.piNPositiveFunctor k).map_comp (sourceIso X).hom (Pi.π (family X) j)) z
  have hp := ConcreteCategory.congr_hom
    ((PointedCGWH.piNPositiveFunctor k).congr_map (sourceIso_projection X j)) z
  have hc : equiv X k z (labels (ι := ι) j) =
      PointedCGWH.HomotopyProductGeometry.selectedEquiv (family X) k a j := by
    exact groupPiReindex_apply
      (fun i => PointedCGWH.piN (k + 1) (X i)) (labels (ι := ι)) _ j
  exact hc.trans (h.trans (hm.symm.trans hp))

end PointedCGWH.SmallHomotopyProductGeometry

namespace PointedCGWH.SmallHomotopyProductGeometry

variable {ι : Type} (X : ι → PointedCGWH.{u, v}) [HasProduct X]

/-- The full small-label comparison is the actual original family of positive projection maps. -/
def comparison (k : ℕ) : (PointedCGWH.piNPositiveFunctor k).obj (∏ᶜ X) ⟶
    GrpCat.of (∀ i, (PointedCGWH.piNPositiveFunctor k).obj (X i)) :=
  GrpCat.ofHom {
    toFun := fun z i => ((PointedCGWH.piNPositiveFunctor k).map (Pi.π X i)).hom z
    map_one' := by funext i; exact map_one _
    map_mul' := by intro a b; funext i; exact map_mul _ _ _ }

/-- The same original small-label projection comparison is a genuine group Iso. -/
def comparisonIso (k : ℕ) : (PointedCGWH.piNPositiveFunctor k).obj (∏ᶜ X) ≅
    GrpCat.of (∀ i, (PointedCGWH.piNPositiveFunctor k).obj (X i)) := (equiv X k).toGrpIso

/-- Its entire forward map is the unchanged positive homotopy map of every original projection. -/
theorem comparisonIso_hom (k : ℕ) : (comparisonIso X k).hom = comparison X k := by
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro z
  funext i
  exact equiv_projection X k z i

end PointedCGWH.SmallHomotopyProductGeometry
