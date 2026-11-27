/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.ChangeObjects
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Differential rescaling and negation

Objectwise automorphisms conjugate the differentials of a homological
complex. In an `R`-linear preadditive category over a semiring, a family
of units `a_i` gives same-object differential
`d′_ij=(a_i⁻¹ a_j) • d_ij` and a natural complex isomorphism with
components `a_i • id`. Bilinearity makes the reverse coefficient order
act identically on morphisms, without a commutativity hypothesis on `R`.
For nonnegative chain complexes in any preadditive category, the signs
`(-1)^n` give a natural isomorphism to the complex with all differentials
negated.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory.Linear

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (R : Type w) [Semiring R] [Linear R C]

/-- Let `R` be a semiring and `C` an `R`-linear preadditive
category. Bilinearity of composition implies
`(r s) • f = (s r) • f` for every `r,s : R` and morphism `f`. -/
theorem scalarProduct_smul_comm {X Y : C} (r s : R) (f : X ⟶ Y) :
    (r * s) • f = (s * r) • f := by
  calc
    (r * s) • f = (r • 𝟙 X) ≫ (s • f) := by
      rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    _ = (s * r) • f := by
      rw [Linear.comp_smul, Linear.smul_comp, Category.id_comp, smul_smul]

end CategoryTheory.Linear

namespace HomologicalComplex

section Linear

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type*} {c : ComplexShape ι} (R : Type w) [Semiring R] [Linear R C]

/-- In an `R`-linear preadditive category over a semiring `R`, a
unit `a : Rˣ` gives an automorphism of `X` with forward map
`a • id_X` and inverse `a⁻¹ • id_X`. -/
def scalarUnitIso (a : Rˣ) (X : C) : X ≅ X where
  hom := (a : R) • 𝟙 X
  inv := ((a⁻¹ : Rˣ) : R) • 𝟙 X
  hom_inv_id := by simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    smul_smul, Units.inv_mul, one_smul]
  inv_hom_id := by simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    smul_smul, Units.mul_inv, one_smul]

/-- Let `R` be a semiring and `C` an `R`-linear preadditive
category. Let `c` be any complex shape with index type `ι`. For a complex `K` and units `a : ι → Rˣ`, conjugating by
the degreewise scalar-unit automorphisms gives a complex on the
same objects with rescaled differentials. -/
def rescale (K : HomologicalComplex C c) (a : ι → Rˣ) : HomologicalComplex C c :=
  K.changeObjects (fun i => scalarUnitIso R (a i) (K.X i))

/-- Let `R` be a semiring and `C` an `R`-linear preadditive
category. Let `c` be any complex shape with index type `ι`. For `a : ι → Rˣ`, the degreewise scalar maps
`a_i • id_(K_i)` give an isomorphism from `K` to its rescaled complex. -/
def rescaleIso (K : HomologicalComplex C c) (a : ι → Rˣ) : K ≅ rescale R K a :=
  K.changeObjectsIso (fun i => scalarUnitIso R (a i) (K.X i))

@[simp]
theorem rescaleIso_hom_f (K : HomologicalComplex C c) (a : ι → Rˣ) (i : ι) :
    (rescaleIso R K a).hom.f i = (a i : R) • 𝟙 (K.X i) := rfl

@[simp]
theorem rescaleIso_inv_f (K : HomologicalComplex C c) (a : ι → Rˣ) (i : ι) :
    (rescaleIso R K a).inv.f i = (((a i)⁻¹ : Rˣ) : R) • 𝟙 (K.X i) := rfl

@[simp]
theorem rescale_X (K : HomologicalComplex C c) (a : ι → Rˣ) (i : ι) :
    (rescale R K a).X i = K.X i := rfl

/-- Let `R` be a semiring and `C` an `R`-linear preadditive
category. Let `c` be any complex shape with index type `ι`. The rescaled differential from `i` to `j` is
`(a_i⁻¹ a_j) • d_K(i,j)` for arbitrary units `a : ι → Rˣ`. -/
theorem rescale_d (K : HomologicalComplex C c) (a : ι → Rˣ) (i j : ι) :
    (rescale R K a).d i j = ((((a i)⁻¹ : Rˣ) : R) * (a j : R)) • K.d i j := by
  simp only [rescale, changeObjects, scalarUnitIso, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Category.comp_id, smul_smul]
  exact CategoryTheory.Linear.scalarProduct_smul_comm R (a j : R)
    (((a i)⁻¹ : Rˣ) : R) (K.d i j)

/-- Let `R` be a semiring and `C` an `R`-linear preadditive
category. Let `c` be any complex shape with index type `ι`. The rescaled differential also equals
`(a_j a_i⁻¹) • d_K(i,j)`, since the two scalar-product orders
act equally on morphisms. -/
theorem rescale_d_reverse (K : HomologicalComplex C c) (a : ι → Rˣ) (i j : ι) :
    (rescale R K a).d i j = ((a j : R) * (((a i)⁻¹ : Rˣ) : R)) • K.d i j :=
  (rescale_d R K a i j).trans
    (CategoryTheory.Linear.scalarProduct_smul_comm R (((a i)⁻¹ : Rˣ) : R) (a j : R) (K.d i j))

/-- Let `R` be a semiring and `C` an `R`-linear preadditive
category. Let `c` be any complex shape with index type `ι`. A fixed unit family `a : ι → Rˣ` defines an endofunctor on
`c`-shaped complexes, rescaling objects and transporting their chain
maps by the scalar-unit isomorphisms. -/
def rescaleFunctor (a : ι → Rˣ) : HomologicalComplex C c ⥤ HomologicalComplex C c :=
  changeObjectsFunctor (𝟭 (HomologicalComplex C c)) (fun K => K.X)
    (fun K i => scalarUnitIso R (a i) (K.X i))

/-- Let `R` be a semiring and `C` an `R`-linear preadditive
category. Let `c` be any complex shape with index type `ι`. The degreewise scalar-unit isomorphisms form a natural
isomorphism from the identity complex functor to rescaling by
`a : ι → Rˣ`. -/
def rescaleNatIso (a : ι → Rˣ) : 𝟭 (HomologicalComplex C c) ≅ rescaleFunctor R a :=
  changeObjectsFunctorIso (𝟭 (HomologicalComplex C c)) (fun K => K.X)
    (fun K i => scalarUnitIso R (a i) (K.X i))

end Linear

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type*} {c : ComplexShape ι}

/-- Let `C` be preadditive and `K` a homological complex of any
shape `c`. Negating every differential gives a homological complex
with the same degree objects and differential `-d_K(i,j)`. -/
def negateDifferentials (K : HomologicalComplex C c) : HomologicalComplex C c where
  X := K.X
  d i j := -K.d i j
  shape i j h := by rw [K.shape i j h, neg_zero]
  d_comp_d' i j l _ _ := by
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, K.d_comp_d, neg_zero]

@[simp]
theorem negateDifferentials_X (K : HomologicalComplex C c) (i : ι) :
    (negateDifferentials K).X i = K.X i := rfl

@[simp]
theorem negateDifferentials_d (K : HomologicalComplex C c) (i j : ι) :
    (negateDifferentials K).d i j = -K.d i j := rfl

/-- Let `C` be preadditive and `K` a homological complex of any
shape `c`. Negating all differentials twice returns the original
complex `K`. -/
theorem negateDifferentials_twice (K : HomologicalComplex C c) :
    negateDifferentials (negateDifferentials K) = K := by
  apply HomologicalComplex.ext
    (C₁ := negateDifferentials (negateDifferentials K)) (C₂ := K) rfl
  intro i j _
  change (-(-K.d i j)) ≫ 𝟙 (K.X j) = 𝟙 (K.X i) ≫ K.d i j
  rw [neg_neg, Category.comp_id, Category.id_comp]

/-- In a preadditive category, a map `f : K → L` of complexes of
shape `c` has the same degree components as a map between the two
complexes with negated differentials. -/
def negateMap {K L : HomologicalComplex C c} (f : K ⟶ L) :
    negateDifferentials K ⟶ negateDifferentials L where
  f := f.f
  comm' i j h := by
    change f.f i ≫ (-L.d i j) = (-K.d i j) ≫ f.f j
    rw [Preadditive.comp_neg, Preadditive.neg_comp, f.comm i j]

/-- In a preadditive category `C`, differential negation defines
an endofunctor on homological complexes of any fixed shape `c`. -/
def negateFunctor : HomologicalComplex C c ⥤ HomologicalComplex C c where
  obj := negateDifferentials
  map := negateMap
  map_id K := by ext i; rfl
  map_comp f g := by ext i; rfl

end Preadditive

end HomologicalComplex

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- For a nonnegative chain degree `n`, the integer degree sign
is `ε_n=(-1)^n`. -/
def degreeSign (n : ℕ) : ℤ := (-1) ^ n

@[simp]
theorem degreeSign_zero : degreeSign 0 = 1 := rfl

theorem degreeSign_add (p q : ℕ) : degreeSign (p + q) = degreeSign p * degreeSign q :=
  pow_add _ _ _

theorem degreeSign_succ (n : ℕ) : degreeSign (n + 1) = -degreeSign n := by
  change (-1 : ℤ) ^ (n + 1) = -((-1 : ℤ) ^ n)
  rw [pow_succ, mul_neg_one]

@[simp]
theorem degreeSign_sq (n : ℕ) : degreeSign n * degreeSign n = 1 := by
  change (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1
  rw [← mul_pow]
  simp only [neg_mul_neg, one_mul, one_pow]

/-- For an object `X` of a preadditive category and `n ∈ ℕ`,
`(-1)^n • id_X` is an involutive automorphism of `X`. -/
def degreeSignIso (X : C) (n : ℕ) : X ≅ X where
  hom := degreeSign n • 𝟙 X
  inv := degreeSign n • 𝟙 X
  hom_inv_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, smul_smul,
      degreeSign_sq, one_smul]
  inv_hom_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, smul_smul,
      degreeSign_sq, one_smul]

/-- Let `C` be preadditive and `K` a nonnegative chain complex. The maps `(-1)^n • id_(K_n)` give a chain isomorphism
`K ≅ negateDifferentials(K)`. -/
def negationIso (K : ChainComplex C ℕ) : K ≅ HomologicalComplex.negateDifferentials K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => degreeSignIso (K.X n) n) (by
    intro i j h
    change j + 1 = i at h
    subst i
    change (degreeSign (j + 1) • 𝟙 _) ≫ (-K.d (j + 1) j) =
      K.d (j + 1) j ≫ (degreeSign j • 𝟙 _)
    rw [degreeSign_succ, Preadditive.comp_neg, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.id_comp, Category.comp_id]
    simp only [neg_smul, neg_neg])

@[simp]
theorem negationIso_hom_f (K : ChainComplex C ℕ) (n : ℕ) :
    (negationIso K).hom.f n = degreeSign n • 𝟙 (K.X n) := rfl

@[simp]
theorem negationIso_inv_f (K : ChainComplex C ℕ) (n : ℕ) :
    (negationIso K).inv.f n = degreeSign n • 𝟙 (K.X n) := rfl

/-- Let `C` be preadditive and `K` a nonnegative chain complex. For any ring `R` making `C` `R`-linear, the degree-`n`
forward component of the negation isomorphism is
`(-1_R)^n • id_(K_n)`. -/
theorem negationIso_hom_f_eq_ring (R : Type w) [Ring R] [Linear R C]
    (K : ChainComplex C ℕ) (n : ℕ) :
    (negationIso K).hom.f n = (-1 : R) ^ n • 𝟙 (K.X n) := by
  rw [negationIso_hom_f]
  have h := Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ n) (𝟙 (K.X n))
  have hc : (((-1 : ℤ) ^ n : ℤ) : R) = (-1 : R) ^ n := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact h.symm.trans (congrArg (fun r : R => r • 𝟙 (K.X n)) hc)

/-- In a preadditive category `C`, for a nonnegative chain map
`f : K → L`, the sign isomorphisms satisfy
`f ≫ ε_L = ε_K ≫ negateMap(f)`. -/
theorem negationIso_naturality {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    f ≫ (negationIso L).hom = (negationIso K).hom ≫ HomologicalComplex.negateMap f := by
  ext n
  change f.f n ≫ (degreeSign n • 𝟙 _) = (degreeSign n • 𝟙 _) ≫ f.f n
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.comp_id, Category.id_comp]

/-- In a preadditive category `C`, the alternating-degree sign
isomorphisms form a natural isomorphism from identity on nonnegative
chain complexes to the differential-negation functor. -/
def negationNatIso : 𝟭 (ChainComplex C ℕ) ≅
    HomologicalComplex.negateFunctor (C := C) (c := ComplexShape.down ℕ) :=
  NatIso.ofComponents negationIso (by
    intro K L f
    exact negationIso_naturality f)

end ChainComplex

end
