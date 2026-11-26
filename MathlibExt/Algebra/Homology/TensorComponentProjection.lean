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
# Bidegree projections from a tensor total complex

For nonnegative chain complexes of modules over a commutative ring, the projection from total
degree p+q to K_p ⊗ L_q retains that summand and kills all other antidiagonal summands. It is
natural in both chain maps.

The matching horizontal differential projects to d_K ⊗ id, while the matching vertical
differential projects to (−1)^p id ⊗ d_L. Differentials into other bidegrees project to zero.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex

/-- The projection to a selected tensor bidegree.

Project total degree p+q onto K_p ⊗ L_q by identity on that summand and zero on the others. -/
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

/-- The selected summand is retained by the tensor projection.

Its coprojection followed by the projection is the identity. -/
@[reassoc (attr := simp)]
theorem tensorComponentProjection_ι {R : Type u} [CommRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) (p q : ℕ) :
    HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫
        tensorComponentProjection K L p q = 𝟙 _ := by
  rw [tensorComponentProjection, HomologicalComplex.ι_mapBifunctorDesc]
  simp

/-- Other tensor summands are killed by the selected projection.

For i+j=p+q with (i,j)≠(p,q), the corresponding coprojection has zero composite. -/
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

/-- Naturality of the tensor component projection.

The total tensor map of f,g followed by the target projection equals the source projection
followed by f_p ⊗ g_q. -/
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

/-- The matching horizontal differential under projection.

The differential from (p+1,q) projects to d_K(p+1,p) ⊗ id_{L_q}. -/
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

/-- The matching vertical differential under projection.

The differential from (p,q+1) projects to (−1)^p times id_{K_p} ⊗ d_L(q+1,q). -/
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

/-- Other horizontal differential terms have zero selected projection.

A horizontal term whose target bidegree differs from (p,q) projects to zero. -/
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

/-- Other vertical differential terms have zero selected projection.

A vertical term whose target bidegree differs from (p,q) projects to zero. -/
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
