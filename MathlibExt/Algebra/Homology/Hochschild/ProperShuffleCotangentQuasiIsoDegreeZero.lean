/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleCotangentMap
public import MathlibExt.Algebra.Homology.ChainComplex.ToSingleHomologyZero
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Degree-zero proper-shuffle cotangent comparison

The coefficient cotangent cokernel comparison identifies
the degree-zero homology map of the proper-shuffle
augmentation. The augmentation is a quasi-isomorphism
in degree zero without rationality or flatness assumptions.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [SMulCommClass k A M]

/-- The original chain augmentation has the scalar augmentation as its component zero. -/
theorem properShuffleCotangentMap_f_zero :
    (properShuffleCotangentMap k A M).f 0 = properCotangentScalarAugmentation k A M := by
  rw [properShuffleCotangentMap_eq, HomologicalComplex.comp_f,
    properCotangentAugmentation_f_zero, ChainComplex.single₀_map_f_zero]
  rfl

/-- Native degree-zero homology of the original chain augmentation is the same coefficient cotangent map. -/
@[reassoc]
theorem properShuffleCotangentMap_homology_zero :
    HomologicalComplex.homologyMap (properShuffleCotangentMap k A M) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0
        (coefficientCotangentModule k A M)).hom = properCotangentHomologyZeroMap k A M := by
  apply Cofork.IsColimit.hom_ext
    (ChainComplex.homologyZeroCoforkIsColimit (properCotangentComplex k A M))
  change ChainComplex.homologyZeroClass (properCotangentComplex k A M) ≫
      (HomologicalComplex.homologyMap (properShuffleCotangentMap k A M) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0
          (coefficientCotangentModule k A M)).hom) =
    ChainComplex.homologyZeroClass (properCotangentComplex k A M) ≫ properCotangentHomologyZeroMap k A M
  exact (ChainComplex.homologyZeroClass_toSingle (properShuffleCotangentMap k A M)).trans
    ((properShuffleCotangentMap_f_zero k A M).trans (properCotangentHomologyZeroMap_class k A M).symm)

/-- The arbitrary-coefficient H0 isomorphism gives degree-zero quasi-isomorphism of the chain map. -/
instance properShuffleCotangentMap_quasiIsoAt_zero :
    _root_.QuasiIsoAt (properShuffleCotangentMap k A M) 0 := by
  apply (_root_.quasiIsoAt_iff_isIso_homologyMap _ _).mpr
  let e := HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0
    (coefficientCotangentModule k A M)
  have h : HomologicalComplex.homologyMap (properShuffleCotangentMap k A M) 0 =
      (properCotangentHomologyZeroIso k A M).hom ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    calc
      _ = properCotangentHomologyZeroMap k A M := properShuffleCotangentMap_homology_zero k A M
      _ = (properCotangentHomologyZeroIso k A M).hom := (properCotangentHomologyZeroIso_hom k A M).symm
      _ = _ := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [h]
  infer_instance

end ModuleCat.Algebra.Hochschild.Symmetric
