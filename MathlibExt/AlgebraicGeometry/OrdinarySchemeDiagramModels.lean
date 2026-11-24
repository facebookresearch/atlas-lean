/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels
public import MathlibExt.AlgebraicGeometry.GeneralArcHypercoverModels

/-!
# Native coherent categorical limits of ordinary scheme-module diagrams

The indexing category is the actual Grothendieck category of every
ordinary affine family in the prescribed scheme diagram. An arrow
records its original diagram arrow, ring map and commuting Spec square.
The full categorical limit is the native cocartesian module-section
object over this whole category, restricted by the actual finite-cell
perfect-module tests. Its comparison is literal source reindexing by
the original augmentation. No supplied homotopy-limit callback appears.

Sources: HTT Section3.3.3; Bhatt--Mathew1807.04725v4,
Theorems5.13/5.16; native DG module/section operators retain their exact
source revisions and copyright/license notices in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinarySchemeDiagramModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open GeneralArcCoverModels OrdinarySchemeModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

variable {J : Type} [Category.{0} J] {X : QcqsScheme} (H : J ⥤ Over X)

/-- Every original diagram object retains all of its actual ordinary affine families. -/
structure DiagramFamily where
  index : J
  family : Family (H.obj index).left

/-- The actual Grothendieck arrow, with its complete original affine test square. -/
structure DiagramFamilyHom (A B : DiagramFamily H) where
  index : A.index ⟶ B.index
  algebra : A.family.algebra ⟶ B.family.algebra
  square : Spec.map (ordinaryRings.map algebra) ≫ A.family.map ≫ (H.map index).left = B.family.map

@[ext]
theorem DiagramFamilyHom.ext {A B : DiagramFamily H} {f g : DiagramFamilyHom H A B}
    (hi : f.index = g.index) (ha : f.algebra = g.algebra) : f = g := by
  cases f; cases g; cases hi; cases ha; rfl

instance diagramFamilyCategory : Category.{0} (DiagramFamily H) where
  Hom := DiagramFamilyHom H
  id A := ⟨𝟙 A.index, 𝟙 A.family.algebra, by
    rw [ordinaryRings.map_id, Spec.map_id, H.map_id]
    change (𝟙 (Spec (ordinaryRings.obj A.family.algebra))) ≫ A.family.map ≫
      (𝟙 (H.obj A.index).left.scheme) = A.family.map
    simp⟩
  comp {A B C} f g := ⟨f.index ≫ g.index, f.algebra ≫ g.algebra, by
    rw [Functor.map_comp, Spec.map_comp, H.map_comp]
    change (Spec.map (ordinaryRings.map g.algebra) ≫ Spec.map (ordinaryRings.map f.algebra)) ≫
      _ ≫ ((H.map f.index).left ≫ (H.map g.index).left) = _
    calc
      _ = Spec.map (ordinaryRings.map g.algebra) ≫
          (Spec.map (ordinaryRings.map f.algebra) ≫ A.family.map ≫ (H.map f.index).left) ≫
          (H.map g.index).left := by simp only [Category.assoc]
      _ = Spec.map (ordinaryRings.map g.algebra) ≫ B.family.map ≫ (H.map g.index).left := by
          rw [f.square]
      _ = C.family.map := g.square⟩
  id_comp f := by apply DiagramFamilyHom.ext <;> simp
  comp_id f := by apply DiagramFamilyHom.ext <;> simp
  assoc f g h := by apply DiagramFamilyHom.ext <;> simp

/-- The projection keeps every actual original ring map. -/
def ringProjection : DiagramFamily H ⥤ OrdinaryAlgebras where
  obj A := A.family.algebra
  map f := f.algebra
  map_id _ := rfl
  map_comp _ _ := rfl

/-- All diagram coefficients are the literal constant original rings. -/
def coefficientProjection : DiagramFamily H ⥤ SimplicialAlgebraGeometry.SAlg ℤ :=
  ringProjection H ⋙ constantCoefficients

/-- The actual source augmentation sends each affine family to its original composite Spec map. -/
def augmentation : DiagramFamily H ⥤ Family X where
  obj A := ⟨A.family.algebra, A.family.map ≫ (H.obj A.index).hom⟩
  map {A B} f := ⟨f.algebra, by
    change Spec.map (ordinaryRings.map f.algebra) ≫
      (A.family.map ≫ (H.obj A.index).hom) = B.family.map ≫ (H.obj B.index).hom
    calc
      _ = Spec.map (ordinaryRings.map f.algebra) ≫
          (A.family.map ≫ (H.map f.index).left ≫ (H.obj B.index).hom) := by
          exact congrArg (fun k : (H.obj A.index).left ⟶ X =>
            Spec.map (ordinaryRings.map f.algebra) ≫ A.family.map ≫ k) (Over.w (H.map f.index)).symm
      _ = (Spec.map (ordinaryRings.map f.algebra) ≫ A.family.map ≫
          (H.map f.index).left) ≫ (H.obj B.index).hom := by simp only [Category.assoc]
      _ = B.family.map ≫ (H.obj B.index).hom := by rw [f.square]⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The entire augmented coefficient functor is the same original constant-ring projection. -/
theorem augmentation_coefficients :
    augmentation H ⋙ OrdinarySchemeModuleFamilies.coefficientProjection X = coefficientProjection H := by
  refine _root_.CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro A B f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

variable {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N} (M : AffineModuleFibration N S)

/-- The full categorical module limit uses native cocartesian sections over all actual diagram families. -/
def qcohLimit : SSet.{1} :=
  sectionsOver M.projection (nerveMap (coefficientProjection H))

/-- Native source reindexing fixes the whole categorical comparison on every parameter simplex. -/
def qcohComparison : OrdinarySchemeModuleFamilies.qcoh M X ⟶ qcohLimit H M :=
  sectionsOverMap M.projection (nerveMap (OrdinarySchemeModuleFamilies.coefficientProjection X))
    (nerveMap (coefficientProjection H)) (nerveMap (augmentation H)) (by
      ext n a
      change (a ⋙ augmentation H) ⋙ OrdinarySchemeModuleFamilies.coefficientProjection X =
        a ⋙ coefficientProjection H
      rw [Functor.assoc, augmentation_coefficients H])

def evaluateSection (a : (qcohLimit H M) _⦋0⦌) (j : DiagramFamily H) : M.total _⦋0⦌ :=
  (a.val.app (op ⦋0⦌) (𝟙 (op ⦋0⦌))) (ComposableArrows.mk₀ j)

/-- Perfectness uses all actual finite-cell/retract tests, at every original diagram family. -/
def IsPerfectDiagram (a : (qcohLimit H M) _⦋0⦌) : Prop :=
  ∀ j : DiagramFamily H, IsPerfectAt M ((coefficientProjection H).obj j) (evaluateSection H M a j)

theorem perfect_comparison (a : (OrdinarySchemeModuleFamilies.qcoh M X) _⦋0⦌)
    (ha : OrdinarySchemeModuleFamilies.IsPerfectGlobal M X a) :
    IsPerfectDiagram H M ((qcohComparison H M).app (op ⦋0⦌) a) := by
  intro j
  have hj := ha ((augmentation H).obj j)
  change IsPerfectAt M ((coefficientProjection H).obj j)
    ((a.val.app (op ⦋0⦌) (𝟙 (op ⦋0⦌)))
      ((nerveMap (augmentation H)).app (op ⦋0⦌) (ComposableArrows.mk₀ j)))
  rw [nerveMap_app_mk₀]
  exact hj

/-- The full categorical perfect limit retains every native noninvertible parameter map. -/
def perfLimit : SSet.{1} :=
  ((qcohLimit H M).fullEnhancedSubcategory (IsPerfectDiagram H M)).toSSet

/-- Its actual comparison is the full native source reindexing, restricted by the original perfect tests. -/
def perfComparison : OrdinarySchemeModuleFamilies.perf M X ⟶ perfLimit H M :=
  SSet.Subcomplex.lift
    (((OrdinarySchemeModuleFamilies.qcoh M X).fullEnhancedSubcategory
      (OrdinarySchemeModuleFamilies.IsPerfectGlobal M X)).ι ≫ qcohComparison H M)
    (by
      rw [SSet.range_le_fullEnhancedSubcategory_iff]
      intro a
      exact perfect_comparison H M a.val
        ((SSet.mem_fullEnhancedSubcategory_obj_zero_iff
          (OrdinarySchemeModuleFamilies.IsPerfectGlobal M X) a.val).mp a.property))

end MathlibExt.AlgebraicGeometry.OrdinarySchemeDiagramModels
