/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Projections from a tensor total complex

The projection to a chosen bidegree retains that tensor summand and annihilates
all other summands. Its naturality and differential formulas apply to chain
complexes of modules over any commutative ring.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex

/-- The canonical projection to one original tensor-total bidegree. -/
def tensorComponentProjection {R : Type u} [CommRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) (p q : ℕ) :
    (HomologicalComplex.tensorObj K L).X (p + q) ⟶ (K.X p ⊗ L.X q : ModuleCat.{u} R) :=
  HomologicalComplex.mapBifunctorDesc (K₁ := K) (K₂ := L)
    (F := curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.down ℕ)
    (fun i j h => by
      by_cases hi : i = p
      · by_cases hj : j = q
        · subst i; subst j; exact 𝟙 _
        · exact 0
      · exact 0)

/-- The actual selected tensor-total summand is retained by the canonical projection. -/
@[reassoc (attr := simp)]
theorem tensorComponentProjection_ι {R : Type u} [CommRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) (p q : ℕ) :
    HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫
        tensorComponentProjection K L p q = 𝟙 _ := by
  rw [tensorComponentProjection, HomologicalComplex.ι_mapBifunctorDesc]
  simp

/-- Every other original tensor-total summand is annihilated by the canonical projection. -/
theorem tensorComponentProjection_other {R : Type u} [CommRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (p q i j : ℕ) (hij : i + j = p + q) (h : i ≠ p ∨ j ≠ q) :
    HomologicalComplex.ιTensorObj K L i j (p + q) hij ≫ tensorComponentProjection K L p q = 0 := by
  rw [tensorComponentProjection, HomologicalComplex.ι_mapBifunctorDesc]
  rcases h with hi | hj
  · simp [hi]
  · by_cases hi : i = p
    · subst i; simp [hj]
    · simp [hi]

/-- The canonical tensor-total projection is natural under both original chain maps. -/
theorem tensorComponentProjection_map {R : Type u} [CommRing R]
    {K L K' L' : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') (p q : ℕ) :
    (HomologicalComplex.tensorHom f g).f (p + q) ≫ tensorComponentProjection K' L' p q =
      tensorComponentProjection K L p q ≫ (f.f p ⊗ₘ g.f q) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.down ℕ)
  intro i j hij
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  change (f.f i ▷ L.X j ≫ K'.X i ◁ g.f j) ≫
      HomologicalComplex.ιTensorObj K' L' i j (p + q) hij ≫ tensorComponentProjection K' L' p q =
    (HomologicalComplex.ιTensorObj K L i j (p + q) hij ≫ tensorComponentProjection K L p q) ≫
      (f.f p ⊗ₘ g.f q)
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel hij
    subst j
    rw
        [tensorComponentProjection_ι, tensorComponentProjection_ι, Category.comp_id,
          Category.id_comp]
    exact (MonoidalCategory.tensorHom_def _ _).symm
  · rw [tensorComponentProjection_other K' L' p q i j hij (Or.inl hi), comp_zero,
      tensorComponentProjection_other K L p q i j hij (Or.inl hi), zero_comp]

/-- The first differential into the selected component retains the left differential. -/
theorem tensorComponentProjection_d₁_matching
    {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ) (p q : ℕ) :
    HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.down ℕ) (p + 1) q (p + q) ≫
        tensorComponentProjection K L p q = K.d (p + 1) p ▷ L.X q := by
  rw [HomologicalComplex.mapBifunctor.d₁_eq K L (curriedTensor (ModuleCat.{u} R))
    (ComplexShape.down ℕ) (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl) q (p + q) rfl]
  change ((1 : ℤˣ) • ((K.d (p + 1) p ▷ L.X q) ≫
    HomologicalComplex.ιTensorObj K L p q (p + q) rfl)) ≫ _ = _
  rw [one_smul, Category.assoc, tensorComponentProjection_ι, Category.comp_id]

/-- The second differential into the selected component retains its Koszul sign. -/
theorem tensorComponentProjection_d₂_matching
    {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ) (p q : ℕ) :
    HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.down ℕ) p (q + 1) (p + q) ≫
        tensorComponentProjection K L p q =
      (-1 : ℤˣ) ^ p • (K.X p ◁ L.d (q + 1) q) := by
  rw [HomologicalComplex.mapBifunctor.d₂_eq K L (curriedTensor (ModuleCat.{u} R))
    (ComplexShape.down ℕ) p (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl) (p + q) rfl]
  change (((-1 : ℤˣ) ^ p) • ((K.X p ◁ L.d (q + 1) q) ≫
    HomologicalComplex.ιTensorObj K L p q (p + q) rfl)) ≫ _ = _
  rw [Linear.units_smul_comp, Category.assoc,
    tensorComponentProjection_ι, Category.comp_id]

/-- The first differential into any other tensor component has zero selected projection. -/
theorem tensorComponentProjection_d₁_other
    {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (p q i j : ℕ) (hij : i + j = p + q) (h : i ≠ p ∨ j ≠ q) :
    HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.down ℕ) (i + 1) j (p + q) ≫
        tensorComponentProjection K L p q = 0 := by
  rw [HomologicalComplex.mapBifunctor.d₁_eq K L (curriedTensor (ModuleCat.{u} R))
    (ComplexShape.down ℕ) (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl) j (p + q) hij]
  change ((1 : ℤˣ) • ((K.d (i + 1) i ▷ L.X j) ≫
    HomologicalComplex.ιTensorObj K L i j (p + q) hij)) ≫ _ = _
  rw [one_smul, Category.assoc,
    tensorComponentProjection_other K L p q i j hij h, comp_zero]

/-- The second differential into any other tensor component has zero selected projection. -/
theorem tensorComponentProjection_d₂_other
    {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (p q i j : ℕ) (hij : i + j = p + q) (h : i ≠ p ∨ j ≠ q) :
    HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.down ℕ) i (j + 1) (p + q) ≫
        tensorComponentProjection K L p q = 0 := by
  rw [HomologicalComplex.mapBifunctor.d₂_eq K L (curriedTensor (ModuleCat.{u} R))
    (ComplexShape.down ℕ) i (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl) (p + q) hij]
  change (((-1 : ℤˣ) ^ i) • ((K.X i ◁ L.d (j + 1) j) ≫
    HomologicalComplex.ιTensorObj K L i j (p + q) hij)) ≫ _ = _
  rw [Linear.units_smul_comp, Category.assoc,
    tensorComponentProjection_other K L p q i j hij h,
    comp_zero, smul_zero]

end HomologicalComplex
