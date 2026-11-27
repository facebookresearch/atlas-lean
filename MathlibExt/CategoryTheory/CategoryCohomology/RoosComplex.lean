/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryCohomology.RoosCosimplicial
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import MathlibExt.CategoryTheory.CategoryHomology.BarLinear
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Roos cochains and their differential

The alternating-coface construction applied to the Roos cosimplicial object
gives a cochain complex functor. Its differential uses the covariant
coefficient action at the first coface and deletion of vertices at the other
cofaces, with alternating signs. In a preadditive coefficient category with
sized products, the coefficient functor is additive.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped BigOperators

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryCohomology

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Preadditive A]
  [HasProducts.{max u₁ v₁} A]

/-- The Roos coefficient functor inherits additivity from the coefficient bar. -/
instance roosCosimplicialFunctor_additive :
    (roosCosimplicialFunctor (I := I) (A := A)).Additive where
  map_add {M N f g} := by
    have hop : NatTrans.op (f + g) = NatTrans.op f + NatTrans.op g := by
      apply NatTrans.ext
      funext i
      exact CategoryTheory.op_add A (f.app i.unop) (g.app i.unop)
    change NatTrans.unop
        ((coefficientBarSimplicialFunctor (C := Iᵒᵖ) (A := Aᵒᵖ)).map
          (NatTrans.op (f + g))) =
      NatTrans.unop
        ((coefficientBarSimplicialFunctor (C := Iᵒᵖ) (A := Aᵒᵖ)).map (NatTrans.op f)) +
      NatTrans.unop
        ((coefficientBarSimplicialFunctor (C := Iᵒᵖ) (A := Aᵒᵖ)).map (NatTrans.op g))
    rw [hop, Functor.map_add]
    apply NatTrans.ext
    funext Δ
    dsimp only [NatTrans.unop]
    exact CategoryTheory.unop_add A
      (((coefficientBarSimplicialFunctor (C := Iᵒᵖ) (A := Aᵒᵖ)).map
        (NatTrans.op f)).app (op Δ))
      (((coefficientBarSimplicialFunctor (C := Iᵒᵖ) (A := Aᵒᵖ)).map
        (NatTrans.op g)).app (op Δ))

/-- The full Roos cochain complex is the alternating-coface complex. -/
abbrev roosComplex (M : I ⥤ A) : CochainComplex A ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (roosCosimplicial M)

/-- The Roos cochain maps, functorial in the coefficient diagram. -/
abbrev roosComplexFunctor : (I ⥤ A) ⥤ CochainComplex A ℕ :=
  roosCosimplicialFunctor ⋙ AlgebraicTopology.alternatingCofaceMapComplex A

/-- Additivity of the cochain-valued Roos functor. -/
instance roosComplexFunctor_additive :
    (roosComplexFunctor (I := I) (A := A)).Additive where
  map_add {M N f g} := by
    apply HomologicalComplex.hom_ext
    intro n
    change ((roosCosimplicialFunctor (I := I) (A := A)).map (f + g)).app
        (SimplexCategory.mk n) =
      ((roosCosimplicialFunctor (I := I) (A := A)).map f).app
          (SimplexCategory.mk n) +
        ((roosCosimplicialFunctor (I := I) (A := A)).map g).app
          (SimplexCategory.mk n)
    rw [Functor.map_add]
    rfl

/-- The Roos complex functor assigns the Roos cochain complex to a coefficient diagram. -/
theorem roosComplexFunctor_obj (M : I ⥤ A) :
    (roosComplexFunctor (I := I) (A := A)).obj M = roosComplex M := rfl

/-- The degree-n term of the Roos complex is the degree-n value of the Roos cosimplicial object. -/
@[simp]
theorem roosComplex_X (M : I ⥤ A) (n : ℕ) :
    (roosComplex M).X n = (roosCosimplicial M).obj (SimplexCategory.mk n) := rfl

/-- Every cochain-map component is the coefficient map. -/
theorem roosComplexFunctor_map_f {M N : I ⥤ A} (α : M ⟶ N) (n : ℕ) :
    ((roosComplexFunctor (I := I) (A := A)).map α).f n =
      (roosMap α).app (SimplexCategory.mk n) := rfl

/-- Projecting an cochain-map component gives the covariant coefficient map. -/
@[reassoc]
theorem roosComplexFunctor_map_f_π {M N : I ⥤ A} (α : M ⟶ N) {n : ℕ}
    (F : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n))) :
    ((roosComplexFunctor (I := I) (A := A)).map α).f n ≫ roosπ N F =
      roosπ M F ≫ α.app (F.left.unop) := by
  have h := congrArg
    (fun (k : (roosCosimplicial M).obj (SimplexCategory.mk n) ⟶
      (roosCosimplicial N).obj (SimplexCategory.mk n)) ↦ k ≫ roosπ N F)
    (roosComplexFunctor_map_f α n)
  exact h.trans (roosMap_app_π α F)

/-- The differential is the alternating sum of the cofaces. -/
theorem roosComplex_d (M : I ⥤ A) (n : ℕ) :
    (roosComplex M).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (roosCosimplicial M).map (SimplexCategory.δ i) := by
  dsimp only [roosComplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  rfl

/-- The signed differential on a weak-chain product projection. -/
@[reassoc]
theorem roosComplex_d_π (M : I ⥤ A) {n : ℕ}
    (F : ComposableArrows Iᵒᵖ (n + 1)) :
    (roosComplex M).d n (n + 1) ≫ roosπ M F =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (roosπ M ((nerve Iᵒᵖ).δ i F) ≫ M.map ((faceLeftHom i F).unop)) := by
  dsimp only [roosComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [CosimplicialObject.δ, Preadditive.zsmul_comp] using congrArg
    (fun (f : (roosCosimplicial M).obj (SimplexCategory.mk n) ⟶
      M.obj (F.left.unop)) ↦ (-1 : ℤ) ^ i.val • f) (roos_coface_π M i F)

/-- Degree zero compares the diagram action with the terminal projection. -/
@[reassoc]
theorem roosComplex_d_zero_π (M : I ⥤ A)
    (F : ComposableArrows Iᵒᵖ 1) :
    (roosComplex M).d 0 1 ≫ roosπ M F =
      roosπ M ((nerve Iᵒᵖ).δ 0 F) ≫ M.map ((F.map' 0 1).unop) -
        roosπ M ((nerve Iᵒᵖ).δ 1 F) ≫
          M.map ((faceLeftHom (1 : Fin 2) F).unop) := by
  rw [roosComplex_d_π, Fin.sum_univ_two]
  rw [faceLeftHom_zero]
  simp [sub_eq_add_neg]
  rfl

end CategoryTheory.CategoryCohomology

end
