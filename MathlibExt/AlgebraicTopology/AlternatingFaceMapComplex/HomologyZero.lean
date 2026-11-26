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
# Degree-zero homology as a coequalizer of faces

For a simplicial object X in a preadditive category, the alternating-face differential X₁ → X₀
is δ₀ − δ₁. When degree-zero homology exists, its class map c_X : X₀ → H₀(X) is a coequalizer
of these two faces. If their chosen coequalizer Q_X exists, there is a canonical isomorphism
H₀(X) ≅ Q_X carrying c_X to its projection.

A simplicial map α induces both a homology map and a map between these coequalizers. The
isomorphisms commute with these maps. More generally, the same square holds for any map Q_X →
Q_Y satisfying the projection equation with α₀.

See Weibel, *An Introduction to Homological Algebra*, Chapter 8, for alternating-face
complexes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace AlgebraicTopology.AlternatingFaceMapComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- For a simplicial object X in a preadditive category C, the degree-one differential of its
alternating-face chain complex is d₁₀ = X.δ 0 − X.δ 1 : X₁ ⟶ X₀. This is the alternating sum
with the δ₀ term positive and the δ₁ term negative. -/
theorem degreeOneDifferential_eq_sub (X : SimplicialObject C) :
    (obj X).d 1 0 = X.δ (0 : Fin 2) - X.δ (1 : Fin 2) := by
  rw [obj_d_eq, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_one_smul, sub_eq_add_neg]

section Homology

variable (X : SimplicialObject C) [(obj X).HasHomology 0]

/-- In a preadditive category C, let X be a simplicial object whose alternating-face chain complex
K_X has homology in degree 0. Define c_X : X₀ ⟶ K_X.homology 0 to be the degree-zero chain
class map. It is the cokernel projection of the boundary K_X.d 1 0 = δ₀ − δ₁. -/
def homologyZeroClass : X _⦋0⦌ ⟶ (obj X).homology 0 :=
  ChainComplex.homologyZeroClass (obj X)

/-- In a preadditive category C, let X be a simplicial object whose alternating-face chain complex
K_X has homology in degree 0. The class map c_X satisfies X.δ 0 ≫ c_X = X.δ 1 ≫ c_X as
morphisms X₁ ⟶ H₀(K_X). -/
theorem homologyZeroClass_balance :
    X.δ (0 : Fin 2) ≫ homologyZeroClass X =
      X.δ (1 : Fin 2) ≫ homologyZeroClass X := by
  have h : (X.δ (0 : Fin 2) - X.δ (1 : Fin 2)) ≫ homologyZeroClass X = 0 := by
    rw [← degreeOneDifferential_eq_sub X]
    exact ChainComplex.d_comp_homologyZeroClass (obj X)
  exact sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using h)

/-- In a preadditive category C, let X be a simplicial object whose alternating-face chain complex
K_X has homology in degree 0. The class map c_X : X₀ ⟶ H₀(K_X), together with δ₀ ≫ c_X = δ₁ ≫
c_X, defines a cofork of the parallel faces δ₀, δ₁ : X₁ ⟶ X₀. -/
def homologyZeroCofork : Cofork (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) :=
  Cofork.ofπ (homologyZeroClass X) (homologyZeroClass_balance X)

@[simp]
theorem homologyZeroCofork_π : (homologyZeroCofork X).π = homologyZeroClass X :=
  rfl

/-- In a preadditive category C, let X be a simplicial object whose alternating-face chain complex
K_X has homology in degree 0. The cofork with projection c_X is a colimit: every morphism f :
X₀ ⟶ W satisfying δ₀ ≫ f = δ₁ ≫ f factors uniquely as c_X ≫ g for a morphism g : H₀(K_X) ⟶ W. -/
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

/-- In a preadditive category C, let X be a simplicial object whose alternating-face chain complex
K_X has homology in degree 0. Assume also that Q_X = coequalizer (X.δ 0) (X.δ 1) exists. The
colimit universal properties give an isomorphism e_X : H₀(K_X) ≅ Q_X, uniquely characterized
by c_X ≫ e_X.hom = coequalizer.π (X.δ 0) (X.δ 1). -/
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

/-- In a preadditive category C, let α : X ⟶ Y be a simplicial map and assume that the
alternating-face complexes K_X and K_Y have homology in degree 0. Writing c_X and c_Y for
their class maps, one has c_X ≫ H₀(map α) = α₀ ≫ c_Y, where map α is the induced
alternating-face chain map and α₀ is the component at the zero simplex. -/
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

/-- In a preadditive category C, let α : X ⟶ Y be a simplicial map and assume that the
alternating-face complexes K_X and K_Y have homology in degree 0. Assume the face coequalizers
Q_X and Q_Y exist, with projections π_X and π_Y, and let u : Q_X ⟶ Q_Y satisfy π_X ≫ u = α₀ ≫
π_Y. Then H₀(map α) ≫ e_Y.hom = e_X.hom ≫ u, where e_X and e_Y are the canonical
homology-to-coequalizer isomorphisms. -/
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

/-- For simplicial objects X and Y in a category C, assume that the coequalizers Q_X and Q_Y of
their two faces X₁ ⇉ X₀ and Y₁ ⇉ Y₀ exist. A simplicial map α : X ⟶ Y induces the colimit map
Q_X ⟶ Q_Y from its components α₁ and α₀. It satisfies π_X ≫ degreeZeroCoequalizerMap α = α₀ ≫
π_Y. -/
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

/-- In a preadditive category C, let α : X ⟶ Y be a simplicial map and assume that the
alternating-face complexes K_X and K_Y have homology in degree 0. If the coequalizers Q_X and
Q_Y of the degree-one faces exist, the canonical comparison isomorphisms satisfy H₀(map α) ≫
e_Y.hom = e_X.hom ≫ degreeZeroCoequalizerMap α. The map on the right is induced by α₁ and α₀
on the parallel-pair diagrams. -/
@[reassoc]
theorem homologyZeroIsoCoequalizer_naturality (α : X ⟶ Y) :
    HomologicalComplex.homologyMap (AlgebraicTopology.AlternatingFaceMapComplex.map α) 0 ≫
        (homologyZeroIsoCoequalizer Y).hom =
      (homologyZeroIsoCoequalizer X).hom ≫ degreeZeroCoequalizerMap α :=
  homologyZeroIsoCoequalizer_naturality_of_π α (degreeZeroCoequalizerMap α)
    (degreeZeroCoequalizerMap_π α)

end CoequalizerMaps

end AlgebraicTopology.AlternatingFaceMapComplex
