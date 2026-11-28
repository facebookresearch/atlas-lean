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
# Alternating complexes and additive functor transport

An additive functor F between preadditive categories commutes with the alternating coface
differential ∑_i(−1)^iδ_i. The identity degree components therefore identify Alt(F(A)) with
F(Alt(A)). Coface-compatible coefficient isomorphisms and natural isomorphisms between additive
functors transport through these comparisons; the two resulting isomorphisms from P(Alt(A)) to
Q(Alt(B)) agree.
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
/-- Let C,D be preadditive, F : C → D additive and A a cosimplicial C-object. For i,j ∈ ℕ with
j=i+1, the identity maps on F(A^i) and F(A^j) commute with the differentials of Alt(F(A)) and
F(Alt(A)). Equivalently F(∑_r(−1)^rδ_r^A) = ∑_r(−1)^rF(δ_r^A) in each degree. -/
theorem alternatingFunctorComm (F : C ⥤ D) [F.Additive]
    (A : CosimplicialObject C) (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (Iso.refl ((AlternatingCofaceMapComplex.obj (A ⋙ F)).X i)).hom ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (AlternatingCofaceMapComplex.obj A)).d i j =
      (AlternatingCofaceMapComplex.obj (A ⋙ F)).d i j ≫
        (Iso.refl ((AlternatingCofaceMapComplex.obj (A ⋙ F)).X j)).hom := by
  obtain rfl : i + 1 = j := hij
  dsimp only [AlternatingCofaceMapComplex.obj, Functor.mapHomologicalComplex_obj_d, Iso.refl_hom]
  rw [CochainComplex.of_d, CochainComplex.of_d, Category.id_comp, Category.comp_id]
  exact alternatingFunctorDifferential F A i

/-- Let C,D be preadditive, F : C → D additive, and A a cosimplicial C-object. The identity degree
components define the canonical isomorphism β_F,A : Alt(F(A)) ≅ F(Alt(A)) of nonnegative cochain
complexes. -/
def alternatingFunctorIso (F : C ⥤ D) [F.Additive] (A : CosimplicialObject C) :
    AlternatingCofaceMapComplex.obj (A ⋙ F) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlternatingCofaceMapComplex.obj A)) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro i j hij
  exact alternatingFunctorComm F A i j hij

/-- Let C,D,E be preadditive, J : C → D, P : C → E and Q : D → E additive functors, and α : P ≅ QJ a
natural isomorphism. For a nonnegative cochain complex K in C, complexPrecompositionIso gives
P(K) ≅ Q(J(K)), with degree-n component α_{K^n}. -/
def complexPrecompositionIso (J : C ⥤ D) [J.Additive] (P : C ⥤ E) [P.Additive]
    (Q : D ⥤ E) [Q.Additive] (α : P ≅ J ⋙ Q) (K : CochainComplex C ℕ) :
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≅
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((J.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) :=
  (NatIso.mapHomologicalComplex α (ComplexShape.up ℕ)).app K ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ Q)) (ComplexShape.up ℕ)).app K).symm

/-- Let C,D be preadditive, J : C → D additive, A and B cosimplicial objects in C and D, and e :
J(A) ≅ B a coface-compatible degreewise isomorphism. The canonical isomorphism J(Alt(A)) ≅
Alt(B) is β_J,A⁻¹ followed by the alternating-complex isomorphism induced by e. -/
def mappedCofaceComplexIso (A : CosimplicialObject C) (B : CosimplicialObject D)
    (J : C ⥤ D) [J.Additive] (e : CofaceIso (A ⋙ J) B) :
    ((J.mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlternatingCofaceMapComplex.obj A)) ≅
      AlternatingCofaceMapComplex.obj B :=
  (alternatingFunctorIso J A).symm ≪≫ e.alternatingIso

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C,D,E be preadditive, A and B cosimplicial objects in C,D, J : C → D, P : C → E, Q : D → E
additive, α : P ≅ QJ natural, and e : J(A) ≅ B coface compatible. Write β_F,A : Alt(F(A)) ≅
F(Alt(A)), a : P(A) ≅ Q(B) for the coface isomorphism induced by α and e, and φ : P(Alt(A)) ≅
Q(J(Alt(A))) for complexPrecompositionIso. Then β_P,A⁻¹ ≪≫ Alt(a) ≪≫ β_Q,B = φ ≪≫ Q(β_J,A⁻¹ ≪≫
Alt(e)), as isomorphisms P(Alt(A)) ≅ Q(Alt(B)). -/
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
