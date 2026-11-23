/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionElementsContraction
public import MathlibExt.KTheory.Exact.Quillen.Nerve
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridLift

/-!
# Simplicial nerves of Quillen Stage-grid lifts

The degreewise category of Quillen Stage-grid lifts and the discrete category
of retained Quillen simplices both reindex contravariantly in the outer
simplex.  Taking their levelwise nerves gives simplicial objects in simplicial
sets.  The retained-Q projection is a natural transformation between them,
and hence induces a map of their simplicial diagonals.

The diagonal of the discrete target is canonically isomorphic to the ordinary
Quillen Q-nerve.  Its component uses `SSet.nerveDiscreteObjEquiv`, rather than
identifying a chain in a discrete category by definitional equality.

This file constructs only simplicial carriers, their projection, and the
discrete-diagonal isomorphism.  It makes no finality, contractibility, bar,
realization, weak-equivalence, basepoint, or Q/S comparison claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.ExactCategory
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Levelwise nerve of the category of Quillen Stage-grid lifts. -/
noncomputable def quillenStageGridNerve
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    SimplicialObject SSet.{max u v} where
  obj a := CategoryTheory.nerve (QuillenStageGridLift C a.unop)
  map f := CategoryTheory.nerveMap
    (reindexQuillenStageGridLift (C := C) f.unop)
  map_id a := by
    simp only [unop_id, reindexQuillenStageGridLift_id]
    rfl
  map_comp f g := by
    simp only [unop_comp, reindexQuillenStageGridLift_comp]
    rfl

/-- Outer-degree computation for the Stage-grid nerve. -/
@[simp]
theorem quillenStageGridNerve_obj (a : SimplexCategoryᵒᵖ) :
    (quillenStageGridNerve C).obj a =
      CategoryTheory.nerve (QuillenStageGridLift C a.unop) :=
  rfl

/-- Outer-map computation for the Stage-grid nerve. -/
@[simp]
theorem quillenStageGridNerve_map {a b : SimplexCategoryᵒᵖ}
    (f : a ⟶ b) :
    (quillenStageGridNerve C).map f =
      CategoryTheory.nerveMap
        (reindexQuillenStageGridLift (C := C) f.unop) :=
  rfl

/-- Levelwise nerve of the discrete category of retained Quillen simplices. -/
noncomputable def quillenQSimplexDiscreteNerve
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    SimplicialObject SSet.{max u v} where
  obj a := CategoryTheory.nerve (Discrete (QuillenQSimplex C a.unop))
  map f := CategoryTheory.nerveMap
    (quillenQSimplexDiscreteReindex (C := C) f.unop)
  map_id a := by
    simp only [unop_id, quillenQSimplexDiscreteReindex_id]
    rfl
  map_comp f g := by
    simp only [unop_comp, quillenQSimplexDiscreteReindex_comp]
    rfl

/-- Outer-degree computation for the retained-Q discrete nerve. -/
@[simp]
theorem quillenQSimplexDiscreteNerve_obj (a : SimplexCategoryᵒᵖ) :
    (quillenQSimplexDiscreteNerve C).obj a =
      CategoryTheory.nerve (Discrete (QuillenQSimplex C a.unop)) :=
  rfl

/-- Outer-map computation for the retained-Q discrete nerve. -/
@[simp]
theorem quillenQSimplexDiscreteNerve_map
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (quillenQSimplexDiscreteNerve C).map f =
      CategoryTheory.nerveMap
        (quillenQSimplexDiscreteReindex (C := C) f.unop) :=
  rfl

/-- Levelwise nerve of the retained-Q projection.  Naturality is exactly the
strict landed reindex/projection law. -/
noncomputable def quillenStageGridQProjectionNerve :
    quillenStageGridNerve C ⟶ quillenQSimplexDiscreteNerve C where
  app a := CategoryTheory.nerveMap
    (quillenStageGridQProjection C a.unop)
  naturality {a b} f := by
    change CategoryTheory.nerveMap
          (reindexQuillenStageGridLift (C := C) f.unop) ≫
        CategoryTheory.nerveMap
          (quillenStageGridQProjection C b.unop) =
      CategoryTheory.nerveMap
          (quillenStageGridQProjection C a.unop) ≫
        CategoryTheory.nerveMap
          (quillenQSimplexDiscreteReindex (C := C) f.unop)
    rw [CategoryTheory.nerveMap_comp, CategoryTheory.nerveMap_comp,
      reindexQuillenStageGridLift_comp_qProjection]

/-- Component computation for the levelwise retained-Q projection. -/
@[simp]
theorem quillenStageGridQProjectionNerve_app
    (a : SimplexCategoryᵒᵖ) :
    (quillenStageGridQProjectionNerve (C := C)).app a =
      CategoryTheory.nerveMap
        (quillenStageGridQProjection C a.unop) :=
  rfl

/-- Simplicial diagonal of the levelwise Stage-grid nerve. -/
noncomputable abbrev quillenStageGridDiagonal
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    SSet.{max u v} :=
  SSet.simplicialDiagonalFunctor.obj (quillenStageGridNerve C)

/-- Simplicial diagonal of the retained-Q discrete nerve. -/
noncomputable abbrev quillenQSimplexDiscreteDiagonal
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    SSet.{max u v} :=
  SSet.simplicialDiagonalFunctor.obj
    (quillenQSimplexDiscreteNerve C)

/-- Diagonal map induced by the retained-Q projection. -/
noncomputable def quillenStageGridQProjectionDiagonal :
    quillenStageGridDiagonal C ⟶
      quillenQSimplexDiscreteDiagonal C :=
  SSet.simplicialDiagonalFunctor.map
    (quillenStageGridQProjectionNerve (C := C))

/-- Degreewise component of the diagonal retained-Q projection. -/
@[simp]
theorem quillenStageGridQProjectionDiagonal_app
    (a : SimplexCategoryᵒᵖ) :
    (quillenStageGridQProjectionDiagonal (C := C)).app a =
      (CategoryTheory.nerveMap
        (quillenStageGridQProjection C a.unop)).app a :=
  rfl

/-- The diagonal of the retained-Q discrete nerve is canonically the ordinary
Quillen Q-nerve. -/
noncomputable def quillenQSimplexDiscreteDiagonalIso :
    quillenQSimplexDiscreteDiagonal C ≅ NQ C :=
  NatIso.ofComponents
    (fun a =>
      (SSet.nerveDiscreteObjEquiv
        (QuillenQSimplex C a.unop) a).toIso)
    (by
      intro a b f
      apply ConcreteCategory.hom_ext
      intro X
      let h :
          (X.obj (f.unop.toOrderHom 0)).as = (X.obj 0).as :=
        (Discrete.eq_of_hom
          (X.map (homOfLE
            (Fin.zero_le (f.unop.toOrderHom 0))))).symm
      exact congrArg
        (fun q : QuillenQSimplex C a.unop =>
          (edgewiseQuillenSimplexReindex
            (C := C) f.unop).obj q) h)

/-- The discrete-diagonal comparison evaluates a chain at vertex zero using
the landed nerve-discrete equivalence. -/
@[simp]
theorem quillenQSimplexDiscreteDiagonalIso_hom_app
    (a : SimplexCategoryᵒᵖ)
    (x : (quillenQSimplexDiscreteDiagonal C).obj a) :
    (quillenQSimplexDiscreteDiagonalIso (C := C)).hom.app a x =
      (SSet.nerveDiscreteObjEquiv
        (QuillenQSimplex C a.unop) a) x :=
  rfl

end AlgebraicKTheory

end
