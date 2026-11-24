/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# alternating-face homology in degree zero

The differential in degree one is `δ₀ - δ₁`. Native opcycles
and the preadditive cofork/cokernel conversion show that the degree-zero
class map is a coequalizer of these faces. The resulting comparison with the
native coequalizer is characterized by its projection and is natural.

Only preadditivity, the individual degree-zero homology and the indicated
coequalizer are required. No alternative simplicial/complex model is defined.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace AlgebraicTopology.AlternatingFaceMapComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The degree-one differential is the difference of the
two degree-one faces. -/
theorem degreeOneDifferential_eq_sub (X : SimplicialObject C) :
    (obj X).d 1 0 = X.δ (0 : Fin 2) - X.δ (1 : Fin 2) := by
  rw [obj_d_eq, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_one_smul, sub_eq_add_neg]

section Homology

variable (X : SimplicialObject C) [(obj X).HasHomology 0]

/-- The class map from degree-zero chains to homology. -/
def homologyZeroClass : X _⦋0⦌ ⟶ (obj X).homology 0 :=
  ChainComplex.homologyZeroClass (obj X)

/-- The native class map coequalizes the first two faces. -/
theorem homologyZeroClass_balance :
    X.δ (0 : Fin 2) ≫ homologyZeroClass X =
      X.δ (1 : Fin 2) ≫ homologyZeroClass X := by
  have h : (X.δ (0 : Fin 2) - X.δ (1 : Fin 2)) ≫ homologyZeroClass X = 0 := by
    rw [← degreeOneDifferential_eq_sub X]
    exact ChainComplex.d_comp_homologyZeroClass (obj X)
  exact sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using h)

/-- The homology class map as a cofork of the degree-one faces. -/
def homologyZeroCofork : Cofork (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) :=
  Cofork.ofπ (homologyZeroClass X) (homologyZeroClass_balance X)

@[simp]
theorem homologyZeroCofork_π : (homologyZeroCofork X).π = homologyZeroClass X :=
  rfl

/-- The native degree-zero class map earns the coequalizer universal property. -/
def homologyZeroCoforkIsColimit : IsColimit (homologyZeroCofork X) := by
  let c : CokernelCofork (X.δ (0 : Fin 2) - X.δ (1 : Fin 2)) :=
    CokernelCofork.ofπ (homologyZeroClass X) (by
      rw [← degreeOneDifferential_eq_sub X]
      exact ChainComplex.d_comp_homologyZeroClass (obj X))
  have hc : IsColimit c := by
    have h := CokernelCofork.isColimitOfIsColimitOfIff'
      (ChainComplex.homologyZeroCoforkIsColimit (obj X))
      (X.δ (0 : Fin 2) - X.δ (1 : Fin 2))
      (fun {W} φ => by rw [degreeOneDifferential_eq_sub X])
    exact h
  exact Preadditive.isColimitCoforkOfCokernelCofork hc

variable [HasCoequalizer (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2))]

/-- Actual degree-zero alternating-face homology is the native coequalizer
of the two degree-one faces. -/
def homologyZeroIsoCoequalizer : (obj X).homology 0 ≅
    coequalizer (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) :=
  IsColimit.coconePointUniqueUpToIso
    (s := homologyZeroCofork X)
    (t := Cofork.ofπ (coequalizer.π (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)))
      (coequalizer.condition (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2))))
    (homologyZeroCoforkIsColimit X)
    (coequalizerIsCoequalizer (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)))

@[reassoc (attr := simp)]
theorem homologyZeroIsoCoequalizer_class :
    homologyZeroClass X ≫ (homologyZeroIsoCoequalizer X).hom =
      coequalizer.π (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (s := homologyZeroCofork X)
    (t := Cofork.ofπ (coequalizer.π (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)))
      (coequalizer.condition (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2))))
    (homologyZeroCoforkIsColimit X)
    (coequalizerIsCoequalizer (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)))
    WalkingParallelPair.one

end Homology

section Naturality

variable {X Y : SimplicialObject C} [(obj X).HasHomology 0] [(obj Y).HasHomology 0]

/-- Genuine simplicial maps preserve the degree-zero class maps. -/
@[reassoc]
theorem homologyZeroClass_naturality (α : X ⟶ Y) :
    homologyZeroClass X ≫
        HomologicalComplex.homologyMap (AlgebraicTopology.AlternatingFaceMapComplex.map α) 0 =
      α.app (Opposite.op (SimplexCategory.mk 0)) ≫ homologyZeroClass Y := by
  let φ : obj X ⟶ obj Y := AlgebraicTopology.AlternatingFaceMapComplex.map α
  have h : homologyZeroClass X ≫ HomologicalComplex.homologyMap φ 0 =
      φ.f 0 ≫ homologyZeroClass Y :=
    ChainComplex.homologyZeroClass_naturality φ
  have hf : φ.f 0 = α.app (Opposite.op (SimplexCategory.mk 0)) :=
    AlgebraicTopology.AlternatingFaceMapComplex.map_f α 0
  exact h.trans (congrArg (fun f : X _⦋0⦌ ⟶ Y _⦋0⦌ =>
    f ≫ homologyZeroClass Y) hf)

variable [HasCoequalizer (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2))]
  [HasCoequalizer (Y.δ (0 : Fin 2)) (Y.δ (1 : Fin 2))]

/-- Compatibility with any ordinary morphism obeying the native
coequalizer projection equation. The comparison itself is canonically earned. -/
theorem homologyZeroIsoCoequalizer_naturality_of_π (α : X ⟶ Y)
    (u : coequalizer (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) ⟶
      coequalizer (Y.δ (0 : Fin 2)) (Y.δ (1 : Fin 2)))
    (hu : coequalizer.π (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) ≫ u =
      α.app (Opposite.op (SimplexCategory.mk 0)) ≫
        coequalizer.π (Y.δ (0 : Fin 2)) (Y.δ (1 : Fin 2))) :
    HomologicalComplex.homologyMap (AlgebraicTopology.AlternatingFaceMapComplex.map α) 0 ≫
        (homologyZeroIsoCoequalizer Y).hom =
      (homologyZeroIsoCoequalizer X).hom ≫ u := by
  apply Cofork.IsColimit.hom_ext (homologyZeroCoforkIsColimit X)
  change homologyZeroClass X ≫
      (HomologicalComplex.homologyMap (AlgebraicTopology.AlternatingFaceMapComplex.map α) 0 ≫
        (homologyZeroIsoCoequalizer Y).hom) =
    homologyZeroClass X ≫ ((homologyZeroIsoCoequalizer X).hom ≫ u)
  calc
    _ = (homologyZeroClass X ≫
        HomologicalComplex.homologyMap (AlgebraicTopology.AlternatingFaceMapComplex.map α) 0) ≫
          (homologyZeroIsoCoequalizer Y).hom := (Category.assoc _ _ _).symm
    _ = (α.app (Opposite.op (SimplexCategory.mk 0)) ≫ homologyZeroClass Y) ≫
        (homologyZeroIsoCoequalizer Y).hom :=
      congrArg (fun f : X _⦋0⦌ ⟶ (obj Y).homology 0 =>
        f ≫ (homologyZeroIsoCoequalizer Y).hom) (homologyZeroClass_naturality α)
    _ = α.app (Opposite.op (SimplexCategory.mk 0)) ≫
        coequalizer.π (Y.δ (0 : Fin 2)) (Y.δ (1 : Fin 2)) := by
      rw [Category.assoc, homologyZeroIsoCoequalizer_class]
    _ = coequalizer.π (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) ≫ u := hu.symm
    _ = _ := by rw [← Category.assoc, homologyZeroIsoCoequalizer_class]

end Naturality

section CoequalizerMaps

variable {X Y : SimplicialObject C}
  [HasCoequalizer (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2))]
  [HasCoequalizer (Y.δ (0 : Fin 2)) (Y.δ (1 : Fin 2))]

/-- The colimit map of the degree-one parallel-pair diagram. -/
def degreeZeroCoequalizerMap (α : X ⟶ Y) :
    coequalizer (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) ⟶
      coequalizer (Y.δ (0 : Fin 2)) (Y.δ (1 : Fin 2)) :=
  colimMap (parallelPairHom (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2))
    (Y.δ (0 : Fin 2)) (Y.δ (1 : Fin 2))
    (α.app (Opposite.op (SimplexCategory.mk 1)))
    (α.app (Opposite.op (SimplexCategory.mk 0)))
    (α.naturality (SimplexCategory.δ (0 : Fin 2)).op)
    (α.naturality (SimplexCategory.δ (1 : Fin 2)).op))

omit [Preadditive C] in
@[reassoc (attr := simp)]
theorem degreeZeroCoequalizerMap_π (α : X ⟶ Y) :
    coequalizer.π (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) ≫ degreeZeroCoequalizerMap α =
      α.app (Opposite.op (SimplexCategory.mk 0)) ≫
        coequalizer.π (Y.δ (0 : Fin 2)) (Y.δ (1 : Fin 2)) := by
  let η : parallelPair (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) ⟶
      parallelPair (Y.δ (0 : Fin 2)) (Y.δ (1 : Fin 2)) :=
    parallelPairHom (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2))
      (Y.δ (0 : Fin 2)) (Y.δ (1 : Fin 2))
      (α.app (Opposite.op (SimplexCategory.mk 1)))
      (α.app (Opposite.op (SimplexCategory.mk 0)))
      (α.naturality (SimplexCategory.δ (0 : Fin 2)).op)
      (α.naturality (SimplexCategory.δ (1 : Fin 2)).op)
  exact ι_colimMap η WalkingParallelPair.one

variable [(obj X).HasHomology 0] [(obj Y).HasHomology 0]

/-- The homology/coequalizer comparison is natural for simplicial maps and the native parallel-pair colimit maps. -/
@[reassoc]
theorem homologyZeroIsoCoequalizer_naturality (α : X ⟶ Y) :
    HomologicalComplex.homologyMap (AlgebraicTopology.AlternatingFaceMapComplex.map α) 0 ≫
        (homologyZeroIsoCoequalizer Y).hom =
      (homologyZeroIsoCoequalizer X).hom ≫ degreeZeroCoequalizerMap α :=
  homologyZeroIsoCoequalizer_naturality_of_π α (degreeZeroCoequalizerMap α)
    (degreeZeroCoequalizerMap_π α)

end CoequalizerMaps

end AlgebraicTopology.AlternatingFaceMapComplex
