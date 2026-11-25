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

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Anticommuting bicomplexes and the degree sign bridge

Mathlib's `HomologicalComplex₂` is a complex internal to complexes, so its
horizontal and vertical squares commute.  Many texts instead define a raw
bicomplex by anticommuting squares.  This file records that convention and
the standard bridge: if a unit sign `ε i` changes sign along every horizontal
differential, multiplying the vertical differential in horizontal degree
`i` by `ε i` produces a commuting `HomologicalComplex₂`.

The construction is formulated for arbitrary complex shapes and any
preadditive category.  The specialization `ε p = (-1)^p` for `down ℤ` is
given at the end.
-/

@[expose] public section

open CategoryTheory Limits

universe v u u₁ u₂

namespace HomologicalComplex₂

/-- Raw bicomplex data whose horizontal and vertical squares anticommute. -/
@[ext]
structure Anticommuting
    (C : Type u) [Category.{v} C] [Preadditive C]
    {I₁ : Type u₁} {I₂ : Type u₂}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) where
  /-- The objects in each bidegree. -/
  X : GradedObject (I₁ × I₂) C
  /-- The differential in the first complex direction. -/
  d₁ : ∀ (i₁ i₁' : I₁) (i₂ : I₂), X (i₁, i₂) ⟶ X (i₁', i₂)
  /-- The differential in the second complex direction. -/
  d₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂), X (i₁, i₂) ⟶ X (i₁, i₂')
  shape₁ : ∀ (i₁ i₁' : I₁), ¬c₁.Rel i₁ i₁' → ∀ i₂ : I₂, d₁ i₁ i₁' i₂ = 0
  shape₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂), ¬c₂.Rel i₂ i₂' → d₂ i₁ i₂ i₂' = 0
  d₁_comp_d₁ : ∀ (i₁ i₁' i₁'' : I₁) (i₂ : I₂),
    d₁ i₁ i₁' i₂ ≫ d₁ i₁' i₁'' i₂ = 0
  d₂_comp_d₂ : ∀ (i₁ : I₁) (i₂ i₂' i₂'' : I₂),
    d₂ i₁ i₂ i₂' ≫ d₂ i₁ i₂' i₂'' = 0
  anticomm : ∀ (i₁ i₁' : I₁) (i₂ i₂' : I₂),
    d₁ i₁ i₁' i₂ ≫ d₂ i₁' i₂ i₂' +
      d₂ i₁ i₂ i₂' ≫ d₁ i₁ i₁' i₂' = 0

namespace Anticommuting

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type u₁} {I₂ : Type u₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

/-- A morphism of anticommuting bicomplexes, commuting with both raw
differentials. -/
@[ext]
structure Hom (K L : Anticommuting C c₁ c₂) where
  /-- The morphism in each bidegree. -/
  f : ∀ i₁ i₂, K.X (i₁, i₂) ⟶ L.X (i₁, i₂)
  comm₁ : ∀ i₁ i₁' i₂,
    f i₁ i₂ ≫ L.d₁ i₁ i₁' i₂ = K.d₁ i₁ i₁' i₂ ≫ f i₁' i₂
  comm₂ : ∀ i₁ i₂ i₂',
    f i₁ i₂ ≫ L.d₂ i₁ i₂ i₂' = K.d₂ i₁ i₂ i₂' ≫ f i₁ i₂'

instance : Category (Anticommuting C c₁ c₂) where
  Hom := Hom
  id K :=
    { f := fun i₁ i₂ => 𝟙 (K.X (i₁, i₂))
      comm₁ := by simp
      comm₂ := by simp }
  comp f g :=
    { f := fun i₁ i₂ => f.f i₁ i₂ ≫ g.f i₁ i₂
      comm₁ := by
        intro i₁ i₁' i₂
        simp only [Category.assoc, g.comm₁]
        rw [← Category.assoc, f.comm₁, Category.assoc]
      comm₂ := by
        intro i₁ i₂ i₂'
        simp only [Category.assoc, g.comm₂]
        rw [← Category.assoc, f.comm₂, Category.assoc] }
  id_comp _ := by ext; simp
  comp_id _ := by ext; simp
  assoc _ _ _ := by ext; simp

@[simp]
theorem id_f (K : Anticommuting C c₁ c₂) (i₁ : I₁) (i₂ : I₂) :
    Hom.f (𝟙 K) i₁ i₂ = 𝟙 _ :=
  rfl

@[simp]
theorem comp_f {K L M : Anticommuting C c₁ c₂}
    (f : K ⟶ L) (g : L ⟶ M) (i₁ : I₁) (i₂ : I₂) :
    Hom.f (f ≫ g) i₁ i₂ = f.f i₁ i₂ ≫ g.f i₁ i₂ :=
  rfl

/-- The horizontal row of a raw anticommuting bicomplex. -/
def row (K : Anticommuting C c₁ c₂) (i₂ : I₂) :
    HomologicalComplex C c₁ where
  X i₁ := K.X (i₁, i₂)
  d i₁ i₁' := K.d₁ i₁ i₁' i₂
  shape i₁ i₁' h := K.shape₁ i₁ i₁' h i₂
  d_comp_d' i₁ i₁' i₁'' _ _ := K.d₁_comp_d₁ i₁ i₁' i₁'' i₂

/-- The vertical column of a raw anticommuting bicomplex, retaining the
original second differential and arbitrary source shapes. -/
def column (K : Anticommuting C c₁ c₂) (i₁ : I₁) :
    HomologicalComplex C c₂ where
  X i₂ := K.X (i₁, i₂)
  d i₂ i₂' := K.d₂ i₁ i₂ i₂'
  shape i₂ i₂' h := K.shape₂ i₁ i₂ i₂' h
  d_comp_d' i₂ i₂' i₂'' _ _ := K.d₂_comp_d₂ i₁ i₂ i₂' i₂''

/-- The column retains the original object at the selected bidegree. -/
@[simp]
theorem column_X (K : Anticommuting C c₁ c₂) (i₁ : I₁) (i₂ : I₂) :
    (K.column i₁).X i₂ = K.X (i₁, i₂) :=
  rfl

/-- The column retains the original second-direction differential. -/
@[simp]
theorem column_d (K : Anticommuting C c₁ c₂) (i₁ : I₁) (i₂ i₂' : I₂) :
    (K.column i₁).d i₂ i₂' = K.d₂ i₁ i₂ i₂' :=
  rfl

/-- Multiply the vertical differential in horizontal degree `i₁` by a
sign `ε i₁` which changes sign across every horizontal differential.
The anticommuting squares then become commuting squares. -/
abbrev signTwist (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    HomologicalComplex₂ C c₁ c₂ :=
  HomologicalComplex₂.ofGradedObject c₁ c₂ K.X K.d₁
    (fun i₁ i₂ i₂' => ε i₁ • K.d₂ i₁ i₂ i₂')
    K.shape₁
    (fun i₁ i₂ i₂' h => by rw [K.shape₂ i₁ i₂ i₂' h, smul_zero])
    K.d₁_comp_d₁
    (fun i₁ i₂ i₂' i₂'' => by
      simp only [Linear.units_smul_comp, Linear.comp_units_smul,
        K.d₂_comp_d₂, smul_zero])
    (fun i₁ i₁' i₂ i₂' => by
      by_cases h : c₁.Rel i₁ i₁'
      · rw [Linear.comp_units_smul, Linear.units_smul_comp,
          eq_neg_of_add_eq_zero_left (K.anticomm i₁ i₁' i₂ i₂'), hε h]
        simp only [Units.neg_smul, smul_neg, neg_neg]
      · rw [K.shape₁ i₁ i₁' h i₂, K.shape₁ i₁ i₁' h i₂',
          zero_comp, comp_zero])

@[simp]
theorem signTwist_X_X (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₁ : I₁) (i₂ : I₂) :
    ((K.signTwist ε hε).X i₁).X i₂ = K.X (i₁, i₂) :=
  rfl

@[simp]
theorem signTwist_d_f (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₁ i₁' : I₁) (i₂ : I₂) :
    ((K.signTwist ε hε).d i₁ i₁').f i₂ = K.d₁ i₁ i₁' i₂ :=
  rfl

@[simp]
theorem signTwist_X_d (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₁ : I₁) (i₂ i₂' : I₂) :
    ((K.signTwist ε hε).X i₁).d i₂ i₂' =
      ε i₁ • K.d₂ i₁ i₂ i₂' :=
  rfl

/-- The anticommuting raw square becomes the commuting square of the signed
Mathlib bicomplex. -/
@[reassoc]
theorem signTwist_comm (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ i₁' : I₁) (i₂ i₂' : I₂) :
    K.d₁ i₁ i₁' i₂ ≫ (ε i₁' • K.d₂ i₁' i₂ i₂') =
      (ε i₁ • K.d₂ i₁ i₂ i₂') ≫ K.d₁ i₁ i₁' i₂' :=
  HomologicalComplex₂.d_comm (K.signTwist ε hε) i₁ i₁' i₂ i₂'

/-- The signed vertical differential as a chain map between horizontal rows.
Its component is exactly `ε i₁ • dᵛ`, the source-level sign trick. -/
def signedVerticalRowMap (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₂ i₂' : I₂) : K.row i₂ ⟶ K.row i₂' :=
  HomologicalComplex.Hom.mk
    (fun i₁ => ε i₁ • K.d₂ i₁ i₂ i₂') (by
      intro i₁ i₁' h
      exact (HomologicalComplex₂.d_comm (K.signTwist ε hε) i₁ i₁' i₂ i₂').symm)

@[simp]
theorem signedVerticalRowMap_f (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₂ i₂' : I₂) (i₁ : I₁) :
    (K.signedVerticalRowMap ε hε i₂ i₂').f i₁ =
      ε i₁ • K.d₂ i₁ i₂ i₂' :=
  rfl

/-- The sign twist on morphisms. -/
def signTwistMap {K L : Anticommuting C c₁ c₂} (f : K ⟶ L)
    (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    K.signTwist ε hε ⟶ L.signTwist ε hε :=
  HomologicalComplex.Hom.mk
    (fun i₁ => HomologicalComplex.Hom.mk (fun i₂ => f.f i₁ i₂) (by
      intro i₂ i₂' _
      change f.f i₁ i₂ ≫ (ε i₁ • L.d₂ i₁ i₂ i₂') =
        (ε i₁ • K.d₂ i₁ i₂ i₂') ≫ f.f i₁ i₂'
      rw [Linear.comp_units_smul, Linear.units_smul_comp, f.comm₂])) (by
        intro i₁ i₁' _
        ext i₂
        change f.f i₁ i₂ ≫ L.d₁ i₁ i₁' i₂ =
          K.d₁ i₁ i₁' i₂ ≫ f.f i₁' i₂
        exact f.comm₁ i₁ i₁' i₂)

@[simp]
theorem signTwistMap_f_f {K L : Anticommuting C c₁ c₂} (f : K ⟶ L)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    ((signTwistMap f ε hε).f i₁).f i₂ = f.f i₁ i₂ :=
  rfl

/-- The sign-twist functor from raw anticommuting bicomplexes to Mathlib's
commuting `HomologicalComplex₂`. -/
def signTwistFunctor (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    Anticommuting C c₁ c₂ ⥤ HomologicalComplex₂ C c₁ c₂ where
  obj K := K.signTwist ε hε
  map f := signTwistMap f ε hε
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Undo the sign twist on a commuting Mathlib bicomplex.  Integer units are
self-inverse, so the same sign is used in both directions. -/
abbrev ofHomologicalComplex₂ (K : HomologicalComplex₂ C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    Anticommuting C c₁ c₂ where
  X := fun ij => (K.X ij.1).X ij.2
  d₁ i₁ i₁' i₂ := (K.d i₁ i₁').f i₂
  d₂ i₁ i₂ i₂' := ε i₁ • (K.X i₁).d i₂ i₂'
  shape₁ i₁ i₁' h i₂ := K.shape_f i₁ i₁' h i₂
  shape₂ i₁ i₂ i₂' h := by simp [(K.X i₁).shape i₂ i₂' h]
  d₁_comp_d₁ := K.d_f_comp_d_f
  d₂_comp_d₂ i₁ i₂ i₂' i₂'' := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul,
      HomologicalComplex.d_comp_d, smul_zero]
  anticomm i₁ i₁' i₂ i₂' := by
    by_cases h : c₁.Rel i₁ i₁'
    · rw [Linear.comp_units_smul, Linear.units_smul_comp,
        K.d_comm i₁ i₁' i₂ i₂', hε h]
      simp only [Units.neg_smul, neg_add_cancel]
    · rw [K.shape_f i₁ i₁' h i₂, K.shape_f i₁ i₁' h i₂',
        zero_comp, comp_zero, add_zero]

@[simp]
theorem ofHomologicalComplex₂_X (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    (ofHomologicalComplex₂ K ε hε).X (i₁, i₂) = (K.X i₁).X i₂ :=
  rfl

@[simp]
theorem ofHomologicalComplex₂_d₁ (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ i₁' : I₁) (i₂ : I₂) :
    (ofHomologicalComplex₂ K ε hε).d₁ i₁ i₁' i₂ = (K.d i₁ i₁').f i₂ :=
  rfl

@[simp]
theorem ofHomologicalComplex₂_d₂ (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ i₂' : I₂) :
    (ofHomologicalComplex₂ K ε hε).d₂ i₁ i₂ i₂' =
      ε i₁ • (K.X i₁).d i₂ i₂' :=
  rfl

/-- Undo the sign twist on a morphism of commuting bicomplexes. -/
def ofHomologicalComplex₂Map {K L : HomologicalComplex₂ C c₁ c₂}
    (f : K ⟶ L) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    ofHomologicalComplex₂ K ε hε ⟶ ofHomologicalComplex₂ L ε hε where
  f i₁ i₂ := (f.f i₁).f i₂
  comm₁ i₁ i₁' i₂ := HomologicalComplex₂.comm_f f i₁ i₁' i₂
  comm₂ i₁ i₂ i₂' := by
    rw [ofHomologicalComplex₂_d₂, ofHomologicalComplex₂_d₂,
      Linear.comp_units_smul, Linear.units_smul_comp, (f.f i₁).comm]

@[simp]
theorem ofHomologicalComplex₂Map_f {K L : HomologicalComplex₂ C c₁ c₂}
    (f : K ⟶ L) (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    (ofHomologicalComplex₂Map f ε hε).f i₁ i₂ = (f.f i₁).f i₂ :=
  rfl

/-- The inverse sign-twist functor. -/
def ofHomologicalComplex₂Functor (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    HomologicalComplex₂ C c₁ c₂ ⥤ Anticommuting C c₁ c₂ where
  obj K := ofHomologicalComplex₂ K ε hε
  map f := ofHomologicalComplex₂Map f ε hε
  map_id _ := by
    apply Hom.ext
    funext i₁ i₂
    rfl
  map_comp _ _ := by
    apply Hom.ext
    funext i₁ i₂
    rfl

/-- Twisting and untwisting twice is literally the identity on each vertical
differential, because every integer unit squares to one. -/
theorem ofSignTwist_d₂ (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ : I₁) (i₂ i₂' : I₂) :
    (ofHomologicalComplex₂ (K.signTwist ε hε) ε hε).d₂ i₁ i₂ i₂' =
      K.d₂ i₁ i₂ i₂' := by
  change ε i₁ • (ε i₁ • K.d₂ i₁ i₂ i₂') = _
  rw [smul_smul, Int.units_mul_self, one_smul]

@[simp]
theorem ofSignTwist_d₁ (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ i₁' : I₁) (i₂ : I₂) :
    (ofHomologicalComplex₂ (K.signTwist ε hε) ε hε).d₁ i₁ i₁' i₂ =
      K.d₁ i₁ i₁' i₂ :=
  rfl

/-- The commuting-side double twist is literally the identity on each
vertical differential. -/
theorem signTwistOf_d (K : HomologicalComplex₂ C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ : I₁) (i₂ i₂' : I₂) :
    (((ofHomologicalComplex₂ K ε hε).signTwist ε hε).X i₁).d i₂ i₂' =
      (K.X i₁).d i₂ i₂' := by
  change ε i₁ • (ε i₁ • (K.X i₁).d i₂ i₂') = _
  rw [smul_smul, Int.units_mul_self, one_smul]

@[simp]
theorem signTwistOf_d_f (K : HomologicalComplex₂ C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ i₁' : I₁) (i₂ : I₂) :
    ((((ofHomologicalComplex₂ K ε hε).signTwist ε hε).d i₁ i₁').f i₂) =
      (K.d i₁ i₁').f i₂ :=
  rfl

/-- Componentwise identity isomorphism for the raw-side round trip. -/
def ofSignTwistIso (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    ofHomologicalComplex₂ (K.signTwist ε hε) ε hε ≅ K where
  hom :=
    { f := fun _ _ => 𝟙 _
      comm₁ := by intros; rw [ofSignTwist_d₁]; simp
      comm₂ := by intros; rw [ofSignTwist_d₂]; simp }
  inv :=
    { f := fun _ _ => 𝟙 _
      comm₁ := by intros; rw [ofSignTwist_d₁]; simp
      comm₂ := by intros; rw [ofSignTwist_d₂]; simp }
  hom_inv_id := by
    apply Hom.ext
    funext i₁ i₂
    simp
  inv_hom_id := by
    apply Hom.ext
    funext i₁ i₂
    simp

@[simp]
theorem ofSignTwistIso_hom_f (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₁ : I₁) (i₂ : I₂) :
    (ofSignTwistIso K ε hε).hom.f i₁ i₂ = 𝟙 _ :=
  rfl

@[simp]
theorem ofSignTwistIso_inv_f (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₁ : I₁) (i₂ : I₂) :
    (ofSignTwistIso K ε hε).inv.f i₁ i₂ = 𝟙 _ :=
  rfl

/-- Component object identification on the commuting-side round trip. -/
noncomputable def signTwistOfXIso (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ : I₁) (i₂ : I₂) :
    (((ofHomologicalComplex₂ K ε hε).signTwist ε hε).X i₁).X i₂ ≅
      (K.X i₁).X i₂ :=
  eqToIso (by rfl)

@[simp]
theorem signTwistOfXIso_hom (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    (signTwistOfXIso K ε hε i₁ i₂).hom = 𝟙 _ := by
  rfl

@[simp]
theorem signTwistOfXIso_inv (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    (signTwistOfXIso K ε hε i₁ i₂).inv = 𝟙 _ := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Componentwise identity isomorphism for the commuting-side round trip. -/
noncomputable def signTwistOfIso (K : HomologicalComplex₂ C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    (ofHomologicalComplex₂ K ε hε).signTwist ε hε ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents
      (signTwistOfXIso K ε hε i₁) (by
        intros
        rw [signTwistOf_d]
        simp))
    (by
      intros
      ext i₂
      simp only [HomologicalComplex.comp_f,
        HomologicalComplex.Hom.isoOfComponents_hom_f,
        signTwistOfXIso_hom]
      rw [signTwistOf_d_f]
      simp)

@[simp]
theorem signTwistOfIso_hom_f_f (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    ((signTwistOfIso K ε hε).hom.f i₁).f i₂ = 𝟙 _ := by
  simp [signTwistOfIso]

@[simp]
theorem signTwistOfIso_inv_f_f (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    ((signTwistOfIso K ε hε).inv.f i₁).f i₂ = 𝟙 _ := by
  simp [signTwistOfIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Unit natural isomorphism of the sign-twist equivalence. -/
noncomputable def signTwistUnitIso (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    𝟭 (Anticommuting C c₁ c₂) ≅
      signTwistFunctor ε hε ⋙ ofHomologicalComplex₂Functor ε hε :=
  NatIso.ofComponents (fun K => (ofSignTwistIso K ε hε).symm) (by
    intro K L f
    apply Hom.ext
    funext i₁ i₂
    change f.f i₁ i₂ ≫ 𝟙 _ = 𝟙 _ ≫ f.f i₁ i₂
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Counit natural isomorphism of the sign-twist equivalence. -/
noncomputable def signTwistCounitIso (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    ofHomologicalComplex₂Functor ε hε ⋙ signTwistFunctor ε hε ≅
      𝟭 (HomologicalComplex₂ C c₁ c₂) :=
  NatIso.ofComponents (fun K => signTwistOfIso K ε hε) (by
    intro K L f
    ext i₁ i₂
    change (f.f i₁).f i₂ ≫ 𝟙 _ = 𝟙 _ ≫ (f.f i₁).f i₂
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The general equivalence between raw anticommuting bicomplexes and
Mathlib's commuting `HomologicalComplex₂`, for any horizontal sign which
changes sign along the first complex shape. -/
noncomputable def signTwistEquivalence (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    Anticommuting C c₁ c₂ ≌ HomologicalComplex₂ C c₁ c₂ where
  functor := signTwistFunctor ε hε
  inverse := ofHomologicalComplex₂Functor ε hε
  unitIso := signTwistUnitIso ε hε
  counitIso := signTwistCounitIso ε hε
  functor_unitIso_comp X := by
    ext i₁ i₂
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
/-- `(-1)^p` changes sign along `down ℤ`. -/
theorem negOnePow_rel {p p' : ℤ} (h : (ComplexShape.down ℤ).Rel p p') :
    p'.negOnePow = -p.negOnePow := by
  change p' + 1 = p at h
  subst p
  rw [Int.negOnePow_succ, neg_neg]

end Anticommuting

end HomologicalComplex₂
