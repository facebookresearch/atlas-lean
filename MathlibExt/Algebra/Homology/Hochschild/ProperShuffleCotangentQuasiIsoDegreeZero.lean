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

For a commutative ring k, a commutative k-algebra A and a compatible symmetric coefficient
module M, the proper-shuffle cotangent chain map Ccot → (M ⊗_AΩ¹_{A/k})[0] has the scalar
cotangent augmentation as its degree-zero component. After identifying the degree-zero homology
of the single-object target with that target module, its homology map equals the induced
Leibniz-cokernel comparison.

The cokernel comparison is an isomorphism, so the chain map is a quasi-isomorphism in degree
zero. This degree-zero result needs neither a rationality nor a coefficient-flatness hypothesis;
it does not assert vanishing of higher cotangent homology for a general algebra.
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Let Ccot be the proper quotient restricted along n ↦ n+1 and T the
canonically lifted coefficient cotangent module M ⊗_AΩ¹_{A/k}. The degree-zero component of
properShuffleCotangentMap k A M : Ccot → T[0] equals properCotangentScalarAugmentation k A M :
Ccot₀ → T. -/
theorem properShuffleCotangentMap_f_zero :
    (properShuffleCotangentMap k A M).f 0 = properCotangentScalarAugmentation k A M := by
  rw [properShuffleCotangentMap_eq, HomologicalComplex.comp_f,
    properCotangentAugmentation_f_zero, ChainComplex.single₀_map_f_zero]
  rfl

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Let Ccot be the proper quotient restricted along n ↦ n+1 and T the
canonically lifted coefficient cotangent module M ⊗_AΩ¹_{A/k}. Let q : Ccot → T[0] be
properShuffleCotangentMap and e : H₀(T[0]) ≅ T the single-object homology isomorphism. Then
H₀(q) ≫ e.hom = properCotangentHomologyZeroMap k A M, the map induced by the scalar augmentation
through the incoming-boundary cokernel. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. Let Ccot be the proper quotient restricted along n ↦ n+1 and T the
canonically lifted coefficient cotangent module M ⊗_AΩ¹_{A/k}. The map properShuffleCotangentMap
k A M : Ccot → T[0] induces an isomorphism on degree-zero homology. Under H₀(T[0]) ≅ T, its
homology map is the coefficient cotangent cokernel isomorphism H₀(Ccot) ≅ T. -/
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
