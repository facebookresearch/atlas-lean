/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralArcTopology
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Actual relative Čech diagrams and arc matching hypercovers

The simplicial object lives over the original qcqs scheme. Čech levels
are the native products of its actual cover arrow, and every simplicial
map is fixed on each original projection. Relative matching objects are
native limits over all maps from lower-degree simplices to the specified
simplex. Degree zero has the empty relative diagram and hence the base.
An arc hypercover tests the actual matching map at every degree.

Source: Bhatt--Mathew1807.04725v4, Theorems5.13/5.16; the standard
relative coskeleton/hypercover definition. Native structured arrows,
products, limits and with-terminal augmentation are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralArcHypercoverModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open GeneralArcCoverModels
open scoped Simplicial

variable {X : QcqsScheme}

/-- The actual relative cover object in the native over-category. -/
def coverObject {Y : QcqsScheme} (f : Y ⟶ X) : Over X := Over.mk f

/-- The same cover at every finite product coordinate. -/
def cechProduct {Y : QcqsScheme} (f : Y ⟶ X) (n : ℕ) : Fin (n + 1) → Over X :=
  fun _ => coverObject f

/-- Every level and map is normalized to the original native relative product projections. -/
structure CechSource {Y : QcqsScheme} (f : Y ⟶ X) [HasFiniteProducts (Over X)] where
  simplicial : SimplicialObject (Over X)
  comparison : ∀ n : SimplexCategoryᵒᵖ,
    simplicial.obj n ≅ _root_.CategoryTheory.Limits.piObj (cechProduct f n.unop.len)
  maps : ∀ {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m) (i : Fin (m.unop.len + 1)),
    simplicial.map a ≫ (comparison m).hom ≫ Pi.π (cechProduct f m.unop.len) i =
      (comparison n).hom ≫ Pi.π (cechProduct f n.unop.len) (a.unop.toOrderHom i)

/-- The actual strict lower-degree subcategory used by the relative coskeleton. -/
def lowerDegree (n : ℕ) : ObjectProperty SimplexCategoryᵒᵖ := fun d => d.unop.len < n

/-- All lower-degree simplex maps into the original n-simplex, including their native relations. -/
abbrev MatchingIndex (n : ℕ) := StructuredArrow (op ⦋n⦌) (lowerDegree n).ι

/-- The actual relative matching diagram on the given simplicial over-object. -/
def matchingDiagram (H : SimplicialObject (Over X)) (n : ℕ) : MatchingIndex n ⥤ Over X :=
  StructuredArrow.proj (op ⦋n⦌) (lowerDegree n).ι ⋙ (lowerDegree n).ι ⋙ H

/-- Its canonical cone is given by every original simplicial structure map. -/
def matchingCone (H : SimplicialObject (Over X)) (n : ℕ) : Cone (matchingDiagram H n) where
  pt := H.obj (op ⦋n⦌)
  π :=
    { app a := H.map a.hom
      naturality a b f := by
        simp only [Functor.const_obj_map]
        change H.map b.hom = H.map a.hom ≫ H.map ((lowerDegree n).ι.map f.right)
        rw [← H.map_comp]
        exact congrArg H.map (StructuredArrow.w f).symm }

/-- Relative matching means the native limit of the whole lower-degree diagram. -/
def matchingObject (H : SimplicialObject (Over X)) (n : ℕ) [HasLimit (matchingDiagram H n)] : Over X :=
  limit (matchingDiagram H n)

/-- The actual relative matching map is the native limit lift of its original structure-map cone. -/
def matchingMap (H : SimplicialObject (Over X)) (n : ℕ) [HasLimit (matchingDiagram H n)] :
    H.obj (op ⦋n⦌) ⟶ matchingObject H n := limit.lift (matchingDiagram H n) (matchingCone H n)

/-- Every matching degree is tested on its actual underlying qcqs scheme map. -/
def IsArcHypercover (H : SimplicialObject (Over X))
    [∀ n : ℕ, HasLimit (matchingDiagram H n)] : Prop :=
  ∀ n : ℕ, IsArcCover (matchingMap H n).left

/-- Forget only the original over-structure, retaining every actual simplicial map. -/
def underlyingDiagram (H : SimplicialObject (Over X)) : SimplexCategoryᵒᵖ ⥤ QcqsScheme :=
  H ⋙ Over.forget X

/-- The whole native augmentation is the original map of every over-object to X. -/
def augmentedDiagram (H : SimplicialObject (Over X)) : WithTerminal SimplexCategoryᵒᵖ ⥤ QcqsScheme :=
  WithTerminal.lift (Z := X) (underlyingDiagram H)
    (fun i => (H.obj i).hom) (by
      intro i j f
      exact Over.w (H.map f))

/-- The augmentation restricts to the original full simplicial source. -/
theorem augmentation_restriction (H : SimplicialObject (Over X)) :
    WithTerminal.incl ⋙ augmentedDiagram H = underlyingDiagram H := by
  apply _root_.CategoryTheory.Functor.ext (fun _ => rfl)

end MathlibExt.AlgebraicGeometry.GeneralArcHypercoverModels
