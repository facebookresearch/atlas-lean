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
# Anticommuting bicomplexes and integer-unit sign conversion

In a preadditive category C, an anticommuting bicomplex has differentials d₁,d₂ with d₁² = d₂²
= 0 and d₁d₂ + d₂d₁ = 0. Let ε : I₁ → ℤˣ satisfy ε(i₁′) = −ε(i₁) across each first-shape
differential. Multiplying the second differential in first degree i₁ by ε(i₁) gives a
commuting bicomplex, with objects and first differential unchanged.

The same multiplication converts commuting bicomplexes back to anticommuting ones, because
integer units square to one. The two constructions form an equivalence with identity bidegree
components on the round-trip isomorphisms. Rows, columns, morphisms and the signed second-
direction maps between rows are retained with their explicit coordinate laws.

For the homological shape on all integer degrees, ε(p) = (−1)^p satisfies the sign-change
condition. The two index universes and the category object and morphism universes are
independent; only preadditivity is assumed.
-/

@[expose] public section

open CategoryTheory Limits

universe v u u₁ u₂

namespace HomologicalComplex₂

/-- Bicomplexes with anticommuting squares.

For arbitrary complex shapes c₁,c₂ in a preadditive category C, specify bidegree objects and
two shape-supported square-zero differentials satisfying d₁ ≫ d₂ + d₂ ≫ d₁ = 0. -/
@[ext]
structure Anticommuting
    (C : Type u) [Category.{v} C] [Preadditive C]
    {I₁ : Type u₁} {I₂ : Type u₂}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) where
  /-- The objects of an anticommuting bicomplex.

For each (i₁,i₂), the graded object X gives the object in that bidegree of C. -/
  X : GradedObject (I₁ × I₂) C
  /-- The first-direction differential of an anticommuting bicomplex.

For fixed i₂, d₁ maps X(i₁,i₂) to X(i₁′,i₂) in the first complex shape. -/
  d₁ : ∀ (i₁ i₁' : I₁) (i₂ : I₂), X (i₁, i₂) ⟶ X (i₁', i₂)
  /-- The second-direction differential of an anticommuting bicomplex.

For fixed i₁, d₂ maps X(i₁,i₂) to X(i₁,i₂′) in the second complex shape. -/
  d₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂), X (i₁, i₂) ⟶ X (i₁, i₂')
/-- Vanishing outside the first complex shape.

If c₁.Rel i₁ i₁′ does not hold, the first-direction differential is zero in every second
degree. -/
  shape₁ : ∀ (i₁ i₁' : I₁), ¬c₁.Rel i₁ i₁' → ∀ i₂ : I₂, d₁ i₁ i₁' i₂ = 0
/-- Vanishing outside the second complex shape.

If c₂.Rel i₂ i₂′ does not hold, the second-direction differential at i₁ is zero. -/
  shape₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂), ¬c₂.Rel i₂ i₂' → d₂ i₁ i₂ i₂' = 0
/-- The first differential squares to zero.

Every composite d₁(i₁,i₁′,i₂) ≫ d₁(i₁′,i₁″,i₂) is zero. -/
  d₁_comp_d₁ : ∀ (i₁ i₁' i₁'' : I₁) (i₂ : I₂),
    d₁ i₁ i₁' i₂ ≫ d₁ i₁' i₁'' i₂ = 0
/-- The second differential squares to zero.

Every composite d₂(i₁,i₂,i₂′) ≫ d₂(i₁,i₂′,i₂″) is zero. -/
  d₂_comp_d₂ : ∀ (i₁ : I₁) (i₂ i₂' i₂'' : I₂),
    d₂ i₁ i₂ i₂' ≫ d₂ i₁ i₂' i₂'' = 0
/-- The anticommuting square equation.

For each pair of degree changes, the composite first then second plus the composite second
then first is zero: d₁ ≫ d₂ + d₂ ≫ d₁ = 0. -/
  anticomm : ∀ (i₁ i₁' : I₁) (i₂ i₂' : I₂),
    d₁ i₁ i₁' i₂ ≫ d₂ i₁' i₂ i₂' +
      d₂ i₁ i₂ i₂' ≫ d₁ i₁ i₁' i₂' = 0

namespace Anticommuting

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type u₁} {I₂ : Type u₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

/-- Morphisms preserving both anticommuting differentials.

A morphism K → L consists of one map in every bidegree, commuting with the first and second
differentials. -/
@[ext]
structure Hom (K L : Anticommuting C c₁ c₂) where
  /-- The bidegree components of a bicomplex morphism.

The component f(i₁,i₂) maps K.X(i₁,i₂) to L.X(i₁,i₂). -/
  f : ∀ i₁ i₂, K.X (i₁, i₂) ⟶ L.X (i₁, i₂)
/-- Compatibility of a bicomplex morphism with the first differential.

The component map followed by L.d₁ equals K.d₁ followed by the component map in the changed
first degree. -/
  comm₁ : ∀ i₁ i₁' i₂,
    f i₁ i₂ ≫ L.d₁ i₁ i₁' i₂ = K.d₁ i₁ i₁' i₂ ≫ f i₁' i₂
/-- Compatibility of a bicomplex morphism with the second differential.

The component map followed by L.d₂ equals K.d₂ followed by the component map in the changed
second degree. -/
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

/-- Components of the identity anticommuting-bicomplex morphism.

The identity morphism is the identity of the object in every bidegree. -/
@[simp]
theorem id_f (K : Anticommuting C c₁ c₂) (i₁ : I₁) (i₂ : I₂) :
    Hom.f (𝟙 K) i₁ i₂ = 𝟙 _ :=
  rfl

/-- Components of a composite anticommuting-bicomplex morphism.

The bidegree component of f ≫ g is the composite of the corresponding components of f and g. -/
@[simp]
theorem comp_f {K L M : Anticommuting C c₁ c₂}
    (f : K ⟶ L) (g : L ⟶ M) (i₁ : I₁) (i₂ : I₂) :
    Hom.f (f ≫ g) i₁ i₂ = f.f i₁ i₂ ≫ g.f i₁ i₂ :=
  rfl

/-- The first-direction row complex.

Fix the second degree i₂ and use the objects K.X(i₁,i₂) with the first differential d₁, in
shape c₁. -/
def row (K : Anticommuting C c₁ c₂) (i₂ : I₂) :
    HomologicalComplex C c₁ where
  X i₁ := K.X (i₁, i₂)
  d i₁ i₁' := K.d₁ i₁ i₁' i₂
  shape i₁ i₁' h := K.shape₁ i₁ i₁' h i₂
  d_comp_d' i₁ i₁' i₁'' _ _ := K.d₁_comp_d₁ i₁ i₁' i₁'' i₂

/-- The second-direction column complex.

Fix the first degree i₁ and use the objects K.X(i₁,i₂) with the second differential d₂, in
shape c₂. -/
def column (K : Anticommuting C c₁ c₂) (i₁ : I₁) :
    HomologicalComplex C c₂ where
  X i₂ := K.X (i₁, i₂)
  d i₂ i₂' := K.d₂ i₁ i₂ i₂'
  shape i₂ i₂' h := K.shape₂ i₁ i₂ i₂' h
  d_comp_d' i₂ i₂' i₂'' _ _ := K.d₂_comp_d₂ i₁ i₂ i₂' i₂''

/-- Objects of a column complex.

The object at second degree i₂ of column K i₁ is K.X(i₁,i₂). -/
@[simp]
theorem column_X (K : Anticommuting C c₁ c₂) (i₁ : I₁) (i₂ : I₂) :
    (K.column i₁).X i₂ = K.X (i₁, i₂) :=
  rfl

/-- Differentials of a column complex.

The differential of column K i₁ is K.d₂ i₁ i₂ i₂′, with no additional sign. -/
@[simp]
theorem column_d (K : Anticommuting C c₁ c₂) (i₁ : I₁) (i₂ i₂' : I₂) :
    (K.column i₁).d i₂ i₂' = K.d₂ i₁ i₂ i₂' :=
  rfl

/-- The signed conversion to a commuting bicomplex.

Let ε : I₁ → ℤˣ change sign across every c₁-relation. Keep the objects and first differential
of K, and multiply the second differential in first degree i₁ by ε(i₁). The squares then
commute. -/
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

/-- Objects under the bicomplex sign twist.

The object in bidegree (i₁,i₂) of the commuting sign twist is K.X(i₁,i₂). -/
@[simp]
theorem signTwist_X_X (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₁ : I₁) (i₂ : I₂) :
    ((K.signTwist ε hε).X i₁).X i₂ = K.X (i₁, i₂) :=
  rfl

/-- The first differential under the bicomplex sign twist.

The first-direction differential component is the same K.d₁ as before twisting. -/
@[simp]
theorem signTwist_d_f (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₁ i₁' : I₁) (i₂ : I₂) :
    ((K.signTwist ε hε).d i₁ i₁').f i₂ = K.d₁ i₁ i₁' i₂ :=
  rfl

/-- The second differential under the bicomplex sign twist.

In first degree i₁, the commuting second differential is ε(i₁)·K.d₂ i₁ i₂ i₂′. -/
@[simp]
theorem signTwist_X_d (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₁ : I₁) (i₂ i₂' : I₂) :
    ((K.signTwist ε hε).X i₁).d i₂ i₂' =
      ε i₁ • K.d₂ i₁ i₂ i₂' :=
  rfl

/-- The commuting square after vertical sign multiplication.

For the sign function changing across c₁, d₁ ≫ (ε(i₁′)·d₂) = (ε(i₁)·d₂) ≫ d₁. -/
@[reassoc]
theorem signTwist_comm (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ i₁' : I₁) (i₂ i₂' : I₂) :
    K.d₁ i₁ i₁' i₂ ≫ (ε i₁' • K.d₂ i₁' i₂ i₂') =
      (ε i₁ • K.d₂ i₁ i₂ i₂') ≫ K.d₁ i₁ i₁' i₂' :=
  HomologicalComplex₂.d_comm (K.signTwist ε hε) i₁ i₁' i₂ i₂'

/-- The signed second differential as a map between rows.

For second degrees i₂,i₂′, the maps ε(i₁)·d₂(i₁,i₂,i₂′) form a morphism between the first-
direction row complexes. -/
def signedVerticalRowMap (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₂ i₂' : I₂) : K.row i₂ ⟶ K.row i₂' :=
  HomologicalComplex.Hom.mk
    (fun i₁ => ε i₁ • K.d₂ i₁ i₂ i₂') (by
      intro i₁ i₁' h
      exact (HomologicalComplex₂.d_comm (K.signTwist ε hε) i₁ i₁' i₂ i₂').symm)

/-- Components of the signed map between row complexes.

At first degree i₁, the row-map component is ε(i₁)·K.d₂ i₁ i₂ i₂′. -/
@[simp]
theorem signedVerticalRowMap_f (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₂ i₂' : I₂) (i₁ : I₁) :
    (K.signedVerticalRowMap ε hε i₂ i₂').f i₁ =
      ε i₁ • K.d₂ i₁ i₂ i₂' :=
  rfl

/-- The morphism induced by the bicomplex sign twist.

A morphism of anticommuting bicomplexes gives a morphism of their commuting sign twists, using
its same bidegree maps. -/
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

/-- Bidegree components of the sign-twisted morphism.

The component in (i₁,i₂) is exactly the original component f(i₁,i₂). -/
@[simp]
theorem signTwistMap_f_f {K L : Anticommuting C c₁ c₂} (f : K ⟶ L)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    ((signTwistMap f ε hε).f i₁).f i₂ = f.f i₁ i₂ :=
  rfl

/-- The functor from anticommuting to commuting bicomplexes.

For a fixed integer-unit sign function changing across c₁, twist the second differential of
each object and retain each morphism's bidegree components. -/
def signTwistFunctor (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    Anticommuting C c₁ c₂ ⥤ HomologicalComplex₂ C c₁ c₂ where
  obj K := K.signTwist ε hε
  map f := signTwistMap f ε hε
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The signed conversion from a commuting bicomplex.

Keep the objects and first differential of a commuting bicomplex and multiply its second
differential in degree i₁ by ε(i₁). The squares become anticommuting. -/
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

/-- Objects under the inverse bicomplex sign conversion.

The anticommuting object at (i₁,i₂) is the same object as (K.X i₁).X i₂. -/
@[simp]
theorem ofHomologicalComplex₂_X (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    (ofHomologicalComplex₂ K ε hε).X (i₁, i₂) = (K.X i₁).X i₂ :=
  rfl

/-- The first differential under inverse sign conversion.

The anticommuting first differential is the first differential component (K.d i₁ i₁′).f i₂. -/
@[simp]
theorem ofHomologicalComplex₂_d₁ (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ i₁' : I₁) (i₂ : I₂) :
    (ofHomologicalComplex₂ K ε hε).d₁ i₁ i₁' i₂ = (K.d i₁ i₁').f i₂ :=
  rfl

/-- The second differential under inverse sign conversion.

The anticommuting second differential is ε(i₁) times the second differential of K in first
degree i₁. -/
@[simp]
theorem ofHomologicalComplex₂_d₂ (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ i₂' : I₂) :
    (ofHomologicalComplex₂ K ε hε).d₂ i₁ i₂ i₂' =
      ε i₁ • (K.X i₁).d i₂ i₂' :=
  rfl

/-- The inverse sign conversion on bicomplex morphisms.

A commuting-bicomplex morphism gives an anticommuting-bicomplex morphism with the same
bidegree components. -/
def ofHomologicalComplex₂Map {K L : HomologicalComplex₂ C c₁ c₂}
    (f : K ⟶ L) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁) :
    ofHomologicalComplex₂ K ε hε ⟶ ofHomologicalComplex₂ L ε hε where
  f i₁ i₂ := (f.f i₁).f i₂
  comm₁ i₁ i₁' i₂ := HomologicalComplex₂.comm_f f i₁ i₁' i₂
  comm₂ i₁ i₂ i₂' := by
    rw [ofHomologicalComplex₂_d₂, ofHomologicalComplex₂_d₂,
      Linear.comp_units_smul, Linear.units_smul_comp, (f.f i₁).comm]

/-- Components of the inverse-converted bicomplex morphism.

The component of the inverse-converted morphism at (i₁,i₂) is (f.f i₁).f i₂. -/
@[simp]
theorem ofHomologicalComplex₂Map_f {K L : HomologicalComplex₂ C c₁ c₂}
    (f : K ⟶ L) (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    (ofHomologicalComplex₂Map f ε hε).f i₁ i₂ = (f.f i₁).f i₂ :=
  rfl

/-- The functor from commuting to anticommuting bicomplexes.

For the fixed sign function ε, use the signed second differential on objects and the same
bidegree maps on morphisms. -/
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

/-- The anticommuting second differential after a round trip.

Twisting and converting back multiplies d₂ by ε(i₁)² = 1, so the original second differential
is recovered. -/
theorem ofSignTwist_d₂ (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ : I₁) (i₂ i₂' : I₂) :
    (ofHomologicalComplex₂ (K.signTwist ε hε) ε hε).d₂ i₁ i₂ i₂' =
      K.d₂ i₁ i₂ i₂' := by
  change ε i₁ • (ε i₁ • K.d₂ i₁ i₂ i₂') = _
  rw [smul_smul, Int.units_mul_self, one_smul]

/-- The anticommuting first differential after a round trip.

Twisting and converting back retains the original first differential d₁. -/
@[simp]
theorem ofSignTwist_d₁ (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ i₁' : I₁) (i₂ : I₂) :
    (ofHomologicalComplex₂ (K.signTwist ε hε) ε hε).d₁ i₁ i₁' i₂ =
      K.d₁ i₁ i₁' i₂ :=
  rfl

/-- The commuting second differential after a round trip.

Converting to anticommuting form and twisting back recovers the original second differential
because each integer unit squares to one. -/
theorem signTwistOf_d (K : HomologicalComplex₂ C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ : I₁) (i₂ i₂' : I₂) :
    (((ofHomologicalComplex₂ K ε hε).signTwist ε hε).X i₁).d i₂ i₂' =
      (K.X i₁).d i₂ i₂' := by
  change ε i₁ • (ε i₁ • (K.X i₁).d i₂ i₂') = _
  rw [smul_smul, Int.units_mul_self, one_smul]

/-- The commuting first differential after a round trip.

The first differential component after inverse conversion and twisting back equals the
original first component. -/
@[simp]
theorem signTwistOf_d_f (K : HomologicalComplex₂ C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ i₁' : I₁) (i₂ : I₂) :
    ((((ofHomologicalComplex₂ K ε hε).signTwist ε hε).d i₁ i₁').f i₂) =
      (K.d i₁ i₁').f i₂ :=
  rfl

/-- The identity-component round-trip isomorphism on anticommuting bicomplexes.

The anticommuting bicomplex obtained by twisting and converting back is isomorphic to K, with
identity maps in every bidegree. -/
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

/-- The forward anticommuting round-trip components.

The forward component of the round-trip isomorphism at every bidegree is the identity. -/
@[simp]
theorem ofSignTwistIso_hom_f (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₁ : I₁) (i₂ : I₂) :
    (ofSignTwistIso K ε hε).hom.f i₁ i₂ = 𝟙 _ :=
  rfl

/-- The inverse anticommuting round-trip components.

The inverse component of the round-trip isomorphism at every bidegree is the identity. -/
@[simp]
theorem ofSignTwistIso_inv_f (K : Anticommuting C c₁ c₂) (ε : I₁ → ℤˣ)
    (hε) (i₁ : I₁) (i₂ : I₂) :
    (ofSignTwistIso K ε hε).inv.f i₁ i₂ = 𝟙 _ :=
  rfl

/-- The object comparison for the commuting round trip.

The object at (i₁,i₂) after inverse conversion and twisting back is canonically isomorphic to
the corresponding object of K. -/
noncomputable def signTwistOfXIso (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ)
    (hε : ∀ {i₁ i₁' : I₁}, c₁.Rel i₁ i₁' → ε i₁' = -ε i₁)
    (i₁ : I₁) (i₂ : I₂) :
    (((ofHomologicalComplex₂ K ε hε).signTwist ε hε).X i₁).X i₂ ≅
      (K.X i₁).X i₂ :=
  eqToIso (by rfl)

/-- The forward object map of the commuting round trip.

The bidegree object comparison has identity forward morphism. -/
@[simp]
theorem signTwistOfXIso_hom (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    (signTwistOfXIso K ε hε i₁ i₂).hom = 𝟙 _ := by
  rfl

/-- The inverse object map of the commuting round trip.

The bidegree object comparison has identity inverse morphism. -/
@[simp]
theorem signTwistOfXIso_inv (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    (signTwistOfXIso K ε hε i₁ i₂).inv = 𝟙 _ := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identity-component round-trip isomorphism on commuting bicomplexes.

Converting a commuting bicomplex to anticommuting form and twisting back gives a bicomplex
isomorphic to K through identity bidegree components. -/
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

/-- The forward commuting round-trip components.

Each bidegree component of the forward commuting round-trip isomorphism is the identity. -/
@[simp]
theorem signTwistOfIso_hom_f_f (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    ((signTwistOfIso K ε hε).hom.f i₁).f i₂ = 𝟙 _ := by
  simp [signTwistOfIso]

/-- The inverse commuting round-trip components.

Each bidegree component of the inverse commuting round-trip isomorphism is the identity. -/
@[simp]
theorem signTwistOfIso_inv_f_f (K : HomologicalComplex₂ C c₁ c₂)
    (ε : I₁ → ℤˣ) (hε) (i₁ : I₁) (i₂ : I₂) :
    ((signTwistOfIso K ε hε).inv.f i₁).f i₂ = 𝟙 _ := by
  simp [signTwistOfIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit of the bicomplex sign equivalence.

The identity functor on anticommuting bicomplexes is naturally isomorphic to sign twisting
followed by inverse conversion, through identity bidegree maps. -/
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
/-- The counit of the bicomplex sign equivalence.

Inverse conversion followed by sign twisting is naturally isomorphic to the identity on
commuting bicomplexes, through identity bidegree maps. -/
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
/-- The equivalence of anticommuting and commuting bicomplexes.

For ε : I₁ → ℤˣ changing sign along c₁-relations, sign multiplication in the second
differential gives an equivalence between the two bicomplex categories, with the same objects
in each bidegree. -/
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
/-- The integer homological sign changes across adjacent degrees.

For p,p′ ∈ ℤ with p′+1=p, the unit signs satisfy (−1)^{p′} = −(−1)^p. This supplies the sign-
change condition for the homological integer shape. -/
theorem negOnePow_rel {p p' : ℤ} (h : (ComplexShape.down ℤ).Rel p p') :
    p'.negOnePow = -p.negOnePow := by
  change p' + 1 = p at h
  subst p
  rw [Int.negOnePow_succ, neg_neg]

end Anticommuting

end HomologicalComplex₂
