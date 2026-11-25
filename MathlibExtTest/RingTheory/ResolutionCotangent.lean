/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.ResolutionCotangent

set_option autoImplicit false

/-! Tests for the cotangent complex of an augmented simplicial algebra. -/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial
open CommAlgCat

namespace MathlibExtTest.ResolutionCotangent

universe u

section General

variable {A : Type u} [CommRing A] (B : CommAlgCat.{u} A)
  (P : SimplicialObject (CommAlgCat.{u} A))
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)

/-- The alternating face map complex of the simplicial module, before reindexing. -/
noncomputable abbrev faceComplex : ChainComplex (ModuleCat.{u} B) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{u} B)).obj
    (resolutionCotangentSimplicialModule A B P ε).object

/-- Degree `0` of the complex is the term at `⦋0⦌`. -/
noncomputable def degZeroIso :
    (resolutionCotangentComplex A B P ε).X 0 ≅ resolutionCotangentTerm A B P ε (op ⦋0⦌) :=
  (faceComplex B P ε).extendXIso (ComplexShape.embeddingUpIntLE 0) (i := 0) (by simp)

/-- Degree `-1` of the complex is the term at `⦋1⦌`. -/
noncomputable def degNegOneIso :
    (resolutionCotangentComplex A B P ε).X (-1) ≅ resolutionCotangentTerm A B P ε (op ⦋1⦌) :=
  (faceComplex B P ε).extendXIso (ComplexShape.embeddingUpIntLE 0) (i := 1) (by simp)

-- Simplicial degree `n` sits in cohomological degree `-n`.
noncomputable example (n : ℕ) :
    (resolutionCotangentComplex A B P ε).X (-(n : ℤ)) ≅
      resolutionCotangentTerm A B P ε (op ⦋n⦌) :=
  (faceComplex B P ε).extendXIso (ComplexShape.embeddingUpIntLE 0) (by simp)

-- Positive degrees are zero.
example (n : ℤ) (hn : 0 < n) : IsZero ((resolutionCotangentComplex A B P ε).X n) :=
  (faceComplex B P ε).isZero_extend_X (ComplexShape.embeddingUpIntLE 0) n
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 n).2 hn)

-- The terms and structure maps of the simplicial module are the base-changed modules of
-- differentials and the induced maps.
example (n : SimplexCategoryᵒᵖ) :
    (resolutionCotangentSimplicialModule A B P ε).object.obj n =
      resolutionCotangentTerm A B P ε n :=
  rfl

example {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    (resolutionCotangentSimplicialModule A B P ε).object.map f =
      resolutionCotangentMap A B P ε f :=
  rfl

-- `map_differential`, consumed through the public field.
example {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) (p : P.obj i) :
    (((resolutionCotangentSimplicialModule A B P ε).termIso i).inv ≫
        (resolutionCotangentSimplicialModule A B P ε).object.map f ≫
          ((resolutionCotangentSimplicialModule A B P ε).termIso j).hom)
        (resolutionCotangentTermDifferential A B P ε i p) =
      resolutionCotangentTermDifferential A B P ε j (P.map f p) :=
  (resolutionCotangentSimplicialModule A B P ε).map_differential f p

/-- A simplicial operator sends `1 ⊗ d p` to `1 ⊗ d (P.map f p)` (`resolutionCotangentMap_D`
read through the simplicial module). -/
theorem object_map_differential {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) (p : P.obj i) :
    (resolutionCotangentSimplicialModule A B P ε).object.map f
        (resolutionCotangentTermDifferential A B P ε i p) =
      resolutionCotangentTermDifferential A B P ε j (P.map f p) :=
  resolutionCotangentMap_D A B P ε f p

-- The simplicial functor laws, consumed through `.object.map`.
example (i : SimplexCategoryᵒᵖ) (p : P.obj i) :
    (resolutionCotangentSimplicialModule A B P ε).object.map (𝟙 i)
        (resolutionCotangentTermDifferential A B P ε i p) =
      resolutionCotangentTermDifferential A B P ε i p := by
  rw [object_map_differential, CategoryTheory.Functor.map_id, CommAlgCat.id_apply]

example {i j k : SimplexCategoryᵒᵖ} (f : i ⟶ j) (g : j ⟶ k) (p : P.obj i) :
    (resolutionCotangentSimplicialModule A B P ε).object.map (f ≫ g)
        (resolutionCotangentTermDifferential A B P ε i p) =
      (resolutionCotangentSimplicialModule A B P ε).object.map g
        ((resolutionCotangentSimplicialModule A B P ε).object.map f
          (resolutionCotangentTermDifferential A B P ε i p)) := by
  rw [object_map_differential, object_map_differential, object_map_differential,
    CategoryTheory.Functor.map_comp, CommAlgCat.comp_apply]

-- A simplicial identity, `δ₀ ∘ σ₀ = 𝟙`, holds in the simplicial module.
example :
    (resolutionCotangentSimplicialModule A B P ε).object.σ (0 : Fin 1) ≫
        (resolutionCotangentSimplicialModule A B P ε).object.δ (0 : Fin 2) =
      𝟙 _ :=
  SimplicialObject.δ_comp_σ_self _

/-- The differential of the alternating face map complex from `⦋1⦌` to `⦋0⦌` is `δ₀ - δ₁`. -/
theorem objD_zero :
    AlternatingFaceMapComplex.objD (resolutionCotangentSimplicialModule A B P ε).object 0 =
      (resolutionCotangentSimplicialModule A B P ε).object.δ (0 : Fin 2) -
        (resolutionCotangentSimplicialModule A B P ε).object.δ 1 := by
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- Through the identifications of degrees `-1` and `0` with the terms at `⦋1⦌` and `⦋0⦌`, the
differential from degree `-1` to degree `0` is the alternating sum `δ₀ - δ₁` of the face maps,
which sends `1 ⊗ d p` to `1 ⊗ d (δ₀ p) - 1 ⊗ d (δ₁ p)` by `object_map_differential`. -/
theorem d_negOne_zero :
    (resolutionCotangentComplex A B P ε).d (-1) 0 =
      (degNegOneIso B P ε).hom ≫
        ((resolutionCotangentSimplicialModule A B P ε).object.δ (0 : Fin 2) -
          (resolutionCotangentSimplicialModule A B P ε).object.δ 1) ≫ (degZeroIso B P ε).inv := by
  have hd : (resolutionCotangentComplex A B P ε).d (-1) 0 =
      (degNegOneIso B P ε).hom ≫ (faceComplex B P ε).d (0 + 1) 0 ≫ (degZeroIso B P ε).inv :=
    (faceComplex B P ε).extend_d_eq (ComplexShape.embeddingUpIntLE 0) (i' := -1) (j' := 0)
      (i := 0 + 1) (j := 0) (by simp) (by simp)
  rw [hd, alternatingFaceMapComplex_obj_d, objD_zero]
  rfl

end General

section ConstantPolynomial

variable (A : Type u) [CommRing A]

/-- The polynomial algebra `A[X]` as a commutative `A`-algebra. -/
noncomputable abbrev Poly : CommAlgCat.{u} A := CommAlgCat.of A (MvPolynomial (Fin 1) A)

/-- The constant simplicial algebra on `A[X]`. -/
noncomputable abbrev constPoly : SimplicialObject (CommAlgCat.{u} A) :=
  (SimplicialObject.const (CommAlgCat.{u} A)).obj (Poly A)

/-- Evaluation at `0`. -/
noncomputable abbrev evalZero : Poly A ⟶ CommAlgCat.of A A :=
  CommAlgCat.ofHom (MvPolynomial.aeval fun _ => (0 : A))

/-- The constant simplicial algebra on `A[X]`, augmented to `A` by `X ↦ 0`. -/
noncomputable abbrev augZero :
    constPoly A ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A A) :=
  (SimplicialObject.const (CommAlgCat.{u} A)).map (evalZero A)

-- The augmentation is evaluation at `0`.
example (n : SimplexCategoryᵒᵖ) :
    resolutionAugmentationHom A (CommAlgCat.of A A) (constPoly A) (augZero A) n
      (MvPolynomial.X 0) = 0 := by
  simp [resolutionAugmentationHom]

-- `resolutionCotangentMap_D`: every simplicial operator of the constant simplicial algebra fixes
-- the pure differentials.
example {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) (p : MvPolynomial (Fin 1) A) :
    resolutionCotangentMap A (CommAlgCat.of A A) (constPoly A) (augZero A) f
        (resolutionCotangentTermDifferential A (CommAlgCat.of A A) (constPoly A) (augZero A) i p) =
      resolutionCotangentTermDifferential A (CommAlgCat.of A A) (constPoly A) (augZero A) j p := by
  rw [resolutionCotangentMap_D]
  rfl

/-- Substitution `X ↦ X ^ 2`, a morphism of terms that is not a simplicial operator. -/
noncomputable abbrev sq : Poly A ⟶ Poly A :=
  CommAlgCat.ofHom (MvPolynomial.aeval fun _ => MvPolynomial.X 0 ^ 2)

/-- `X ↦ X ^ 2` lies over the augmentation `X ↦ 0`. -/
theorem sq_comp_evalZero : sq A ≫ evalZero A = evalZero A := by
  apply CommAlgCat.hom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp

-- `resolutionCotangentPush_D` along a morphism over `B` which is not a simplicial operator.
example (n : SimplexCategoryᵒᵖ) :
    resolutionCotangentPush A (CommAlgCat.of A A) (constPoly A) (augZero A) (i := n) (j := n)
        (sq A) (resolutionAugmentationHom_comp_of_over A (CommAlgCat.of A A) (constPoly A)
          (augZero A) (i := n) (j := n) (sq A) (sq_comp_evalZero A))
        (resolutionCotangentTermDifferential A (CommAlgCat.of A A) (constPoly A) (augZero A) n
          (MvPolynomial.X 0)) =
      resolutionCotangentTermDifferential A (CommAlgCat.of A A) (constPoly A) (augZero A) n
        (MvPolynomial.X 0 ^ 2) := by
  rw [resolutionCotangentPush_D]
  simp

-- The differential from degree `-1` to degree `0` vanishes for a constant simplicial algebra:
-- both face maps fix the pure differentials, so `δ₀ = δ₁` by `resolutionCotangentTerm_hom_ext`.
example : (resolutionCotangentComplex A (CommAlgCat.of A A) (constPoly A) (augZero A)).d (-1) 0 =
    0 := by
  have hδ : (resolutionCotangentSimplicialModule A (CommAlgCat.of A A) (constPoly A)
      (augZero A)).object.δ (0 : Fin 2) =
      (resolutionCotangentSimplicialModule A (CommAlgCat.of A A) (constPoly A)
        (augZero A)).object.δ 1 :=
    resolutionCotangentTerm_hom_ext A _ _ _ _ _ _ fun p =>
      (object_map_differential _ _ _ (SimplexCategory.δ (0 : Fin 2)).op p).trans
        (object_map_differential _ _ _ (SimplexCategory.δ (1 : Fin 2)).op p).symm
  have h₀ := objD_zero (CommAlgCat.of A A) (constPoly A) (augZero A)
  rw [hδ, sub_self] at h₀
  rw [d_negOne_zero]
  erw [← objD_zero (CommAlgCat.of A A) (constPoly A) (augZero A), h₀, Limits.zero_comp,
    Limits.comp_zero]

end ConstantPolynomial

end MathlibExtTest.ResolutionCotangent
