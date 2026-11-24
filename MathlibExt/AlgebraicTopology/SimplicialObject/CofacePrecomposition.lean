/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.CofaceComparison
public import Mathlib.Algebra.Homology.Additive

/-!
# alternating-complex precomposition of coface isomorphisms
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u₁ u₂ u₃ v₁ v₂ v₃
open CategoryTheory AlgebraicTopology
namespace AlgebraicTopology.CosimplicialCup
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E]

set_option backward.isDefEq.respectTransparency.types false in
private theorem alternatingFunctorDifferential (F : C ⥤ D) [F.Additive]
    (A : CosimplicialObject C) (n : ℕ) :
    F.map (AlternatingCofaceMapComplex.objD A n) =
      AlternatingCofaceMapComplex.objD (A ⋙ F) n := by
  let a := fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val • A.δ i
  have h := _root_.map_sum (F.mapAddHom : (A.obj (SimplexCategory.mk n) ⟶
      A.obj (SimplexCategory.mk (n + 1))) →+ (F.obj (A.obj (SimplexCategory.mk n)) ⟶
        F.obj (A.obj (SimplexCategory.mk (n + 1))))) a Finset.univ
  have h' : F.map (∑ i, a i) = ∑ i, F.map (a i) := h
  change F.map (∑ i, a i) = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • F.map (A.δ i)
  rw [h']
  apply Finset.sum_congr rfl
  intro i _
  exact F.map_zsmul

set_option backward.isDefEq.respectTransparency.types false in
/-- The literal identity components commute with the alternating differentials. -/
theorem alternatingFunctorComm (F : C ⥤ D) [F.Additive]
    (A : CosimplicialObject C) (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (Iso.refl ((AlternatingCofaceMapComplex.obj (A ⋙ F)).X i)).hom ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlternatingCofaceMapComplex.obj A)).d i j =
      (AlternatingCofaceMapComplex.obj (A ⋙ F)).d i j ≫
        (Iso.refl ((AlternatingCofaceMapComplex.obj (A ⋙ F)).X j)).hom := by
  obtain rfl : i + 1 = j := hij
  dsimp only [AlternatingCofaceMapComplex.obj, Functor.mapHomologicalComplex_obj_d, Iso.refl_hom]
  rw [CochainComplex.of_d, CochainComplex.of_d, Category.id_comp, Category.comp_id]
  exact alternatingFunctorDifferential F A i

/-- The additive alternating-complex comparison has literal identity components. -/
def alternatingFunctorIso (F : C ⥤ D) [F.Additive] (A : CosimplicialObject C) :
    AlternatingCofaceMapComplex.obj (A ⋙ F) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlternatingCofaceMapComplex.obj A)) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro i j hij
  exact alternatingFunctorComm F A i j hij

/-- A functor isomorphism gives its original complex precomposition isomorphism. -/
def complexPrecompositionIso (J : C ⥤ D) [J.Additive] (P : C ⥤ E) [P.Additive]
    (Q : D ⥤ E) [Q.Additive] (α : P ≅ J ⋙ Q) (K : CochainComplex C ℕ) :
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≅
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((J.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) :=
  (NatIso.mapHomologicalComplex α (ComplexShape.up ℕ)).app K ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ Q)) (ComplexShape.up ℕ)).app K).symm

/-- The mapped coefficient coface comparison in the original coefficient complexes. -/
def mappedCofaceComplexIso (A : CosimplicialObject C) (B : CosimplicialObject D)
    (J : C ⥤ D) [J.Additive] (e : CofaceIso (A ⋙ J) B) :
    ((J.mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlternatingCofaceMapComplex.obj A)) ≅
      AlternatingCofaceMapComplex.obj B :=
  (alternatingFunctorIso J A).symm ≪≫ e.alternatingIso

set_option backward.isDefEq.respectTransparency.types false in
/-- The original coface-precomposition complex map equals the coefficient-complex precomposition map. -/
theorem coface_precomposition_complexIso (A : CosimplicialObject C) (B : CosimplicialObject D)
    (J : C ⥤ D) [J.Additive] (P : C ⥤ E) [P.Additive]
    (Q : D ⥤ E) [Q.Additive] (α : P ≅ J ⋙ Q) (e : CofaceIso (A ⋙ J) B) :
    (alternatingFunctorIso P A).symm ≪≫
        (cofaceIsoWhiskerNatIso A B J P Q α e).alternatingIso ≪≫ alternatingFunctorIso Q B =
      complexPrecompositionIso J P Q α (AlternatingCofaceMapComplex.obj A) ≪≫
        (Q.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso (mappedCofaceComplexIso A B J e) := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [complexPrecompositionIso, mappedCofaceComplexIso, Iso.trans_hom,
    Functor.mapIso_hom, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change 𝟙 _ ≫ ((α.hom.app (A.obj (SimplexCategory.mk n)) ≫ Q.map (e.app n).hom) ≫ 𝟙 _) =
    (α.hom.app (A.obj (SimplexCategory.mk n)) ≫ 𝟙 _) ≫ Q.map (𝟙 _ ≫ (e.app n).hom)
  simp only [Category.id_comp, Category.comp_id]

end AlgebraicTopology.CosimplicialCup
