/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.GroupTheory.NormalizedCocycleExtension
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Bilinear cocycles and permutation actions
-/

@[expose] public section

universe uA uB uι uA' uB' uA'' uB'' uA3 uB3

namespace PermutationBilinearCocycle

open Finset

/-- Skew-symmetric biadditive pairing.
`toBiadditive` is additive in each `Additive` argument.
Evaluation is via `Additive.ofMul`. -/
structure SkewBicharacter (A : Type uA) (B : Type uB)
    [Group A] [AddCommGroup B] where
  toBiadditive : Additive A →+ Additive A →+ B
  skew : ∀ x y : A,
    toBiadditive (Additive.ofMul x) (Additive.ofMul y) =
      -toBiadditive (Additive.ofMul y) (Additive.ofMul x)

variable {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]

/-- Evaluation at multiplicative arguments. -/
def SkewBicharacter.eval {A : Type uA} {B : Type uB}
    [Group A] [AddCommGroup B]
    (b : SkewBicharacter A B) (x y : A) : B :=
  b.toBiadditive (Additive.ofMul x) (Additive.ofMul y)

theorem SkewBicharacter.eval_skew
    (b : SkewBicharacter A B) (x y : A) :
    b.eval x y = -b.eval y x :=
  b.skew x y

theorem SkewBicharacter.eval_mul_left
    (b : SkewBicharacter A B) (x₁ x₂ y : A) :
    b.eval (x₁ * x₂) y = b.eval x₁ y + b.eval x₂ y := by
  unfold SkewBicharacter.eval
  have h :
      (Additive.ofMul (x₁ * x₂) : Additive A) =
        Additive.ofMul x₁ + Additive.ofMul x₂ := rfl
  rw [h, map_add]
  rfl

theorem SkewBicharacter.eval_mul_right
    (b : SkewBicharacter A B) (x y₁ y₂ : A) :
    b.eval x (y₁ * y₂) = b.eval x y₁ + b.eval x y₂ := by
  unfold SkewBicharacter.eval
  have h :
      (Additive.ofMul (y₁ * y₂) : Additive A) =
        Additive.ofMul y₁ + Additive.ofMul y₂ := rfl
  calc b.toBiadditive (Additive.ofMul x) (Additive.ofMul (y₁ * y₂))
      = b.toBiadditive (Additive.ofMul x)
          (Additive.ofMul y₁ + Additive.ofMul y₂) := by rw [h]
    _ = b.toBiadditive (Additive.ofMul x) (Additive.ofMul y₁) +
        b.toBiadditive (Additive.ofMul x) (Additive.ofMul y₂) := by
        rw [map_add]

@[simp]
theorem SkewBicharacter.eval_one_left
    (b : SkewBicharacter A B) (y : A) :
    b.eval (1 : A) y = 0 := by
  unfold SkewBicharacter.eval
  have h0 : (Additive.ofMul (1 : A) : Additive A) = 0 := rfl
  rw [h0, map_zero]
  rfl

@[simp]
theorem SkewBicharacter.eval_one_right
    (b : SkewBicharacter A B) (x : A) :
    b.eval x (1 : A) = 0 := by
  unfold SkewBicharacter.eval
  have h0 : (Additive.ofMul (1 : A) : Additive A) = 0 := rfl
  have : b.toBiadditive (Additive.ofMul x) 0 = 0 :=
    AddMonoidHom.map_zero (b.toBiadditive (Additive.ofMul x))
  rw [h0, this]

section Permute

/-- Left coordinate permutation `(σ • u) i = u (σ⁻¹ i)`. -/
def permute {A : Type uA} {ι : Type uι}
    (σ : Equiv.Perm ι) (u : ι → A) : ι → A :=
  fun i => u (σ⁻¹ i)

@[simp]
theorem permute_apply {A : Type uA} {ι : Type uι}
    (σ : Equiv.Perm ι) (u : ι → A) (i : ι) :
    permute σ u i = u (σ⁻¹ i) :=
  rfl

theorem permute_one {A : Type uA} {ι : Type uι}
    (u : ι → A) :
    permute (1 : Equiv.Perm ι) u = u := by
  funext i
  simp only [permute, Equiv.Perm.one_apply, inv_one]

theorem permute_mul {A : Type uA} {ι : Type uι}
    (σ τ : Equiv.Perm ι) (u : ι → A) :
    permute (σ * τ) u = permute σ (permute τ u) := by
  funext i
  simp [permute]

theorem permute_symm {A : Type uA} {ι : Type uι}
    (σ : Equiv.Perm ι) (u : ι → A) (i : ι) :
    permute σ⁻¹ u i = u (σ i) := by
  simp [permute]

theorem permute_comp_symm {A : Type uA} {ι : Type uι}
    (σ : Equiv.Perm ι) (u : ι → A) :
    permute σ⁻¹ (permute σ u) = u := by
  funext i
  simp [permute]

theorem permute_comp {A : Type uA} {ι : Type uι}
    (σ : Equiv.Perm ι) (u : ι → A) :
    permute σ (permute σ⁻¹ u) = u := by
  funext i
  simp [permute]

@[simp]
theorem permute_mul_tuple {A : Type uA} [Mul A] {ι : Type uι}
    (σ : Equiv.Perm ι) (u v : ι → A) :
    permute σ (u * v) = permute σ u * permute σ v := by
  funext i
  simp [permute, Pi.mul_apply]

@[simp]
theorem permute_one_tuple {A : Type uA} [One A] {ι : Type uι}
    (σ : Equiv.Perm ι) :
    permute σ (1 : ι → A) = (1 : ι → A) := by
  funext i
  simp [permute]

def permuteHom {A : Type uA} [Monoid A] {ι : Type uι}
    (σ : Equiv.Perm ι) : (ι → A) →* (ι → A) where
  toFun := permute σ
  map_one' := permute_one_tuple σ
  map_mul' := permute_mul_tuple σ

@[simp]
theorem permuteHom_apply {A : Type uA} [Monoid A] {ι : Type uι}
    (σ : Equiv.Perm ι) (u : ι → A) :
    permuteHom σ u = permute σ u :=
  rfl

theorem permuteHom_one {A : Type uA} [Monoid A] {ι : Type uι} :
    permuteHom (A := A) (1 : Equiv.Perm ι) =
      MonoidHom.id (ι → A) := by
  apply MonoidHom.ext
  intro u
  simp [permuteHom, permute_one]

theorem permuteHom_mul {A : Type uA} [Monoid A] {ι : Type uι}
    (σ τ : Equiv.Perm ι) :
    permuteHom (A := A) (σ * τ) =
      (permuteHom σ).comp (permuteHom τ) := by
  apply MonoidHom.ext
  intro u
  simp [permuteHom, permute_mul]

def permuteEquiv {A : Type uA} [Mul A] {ι : Type uι}
    (σ : Equiv.Perm ι) : (ι → A) ≃* (ι → A) where
  toFun := permute σ
  invFun := permute σ⁻¹
  left_inv u := by simp [permute_comp_symm]
  right_inv u := by simp [permute_comp]
  map_mul' := permute_mul_tuple σ

@[simp]
theorem permuteEquiv_apply {A : Type uA} [Mul A] {ι : Type uι}
    (σ : Equiv.Perm ι) (u : ι → A) :
    permuteEquiv σ u = permute σ u :=
  rfl

@[simp]
theorem permuteEquiv_symm_apply {A : Type uA} [Mul A] {ι : Type uι}
    (σ : Equiv.Perm ι) (u : ι → A) :
    (permuteEquiv σ).symm u = permute σ⁻¹ u :=
  rfl

theorem permuteEquiv_one {A : Type uA} [Mul A] {ι : Type uι} :
    permuteEquiv (A := A) (1 : Equiv.Perm ι) =
      MulEquiv.refl (ι → A) := by
  apply MulEquiv.ext
  intro u
  simp [permuteEquiv, permute_one]

theorem permuteEquiv_mul {A : Type uA} [Mul A] {ι : Type uι}
    (σ τ : Equiv.Perm ι) (u : ι → A) :
    permuteEquiv (A := A) (σ * τ) u =
      permuteEquiv σ (permuteEquiv τ u) := by
  simp [permuteEquiv, permute_mul]

/-- Pointwise tuple map induced by `f : A →* A'`. -/
def mapTuple {A : Type uA} {A' : Type uA'} [Monoid A] [Monoid A']
    {ι : Type uι}
    (f : A →* A') (u : ι → A) : ι → A' :=
  fun i => f (u i)

@[simp]
theorem mapTuple_apply {A : Type uA} {A' : Type uA'}
    [Monoid A] [Monoid A'] {ι : Type uι}
    (f : A →* A') (u : ι → A) (i : ι) :
    mapTuple f u i = f (u i) :=
  rfl

theorem mapTuple_one {A : Type uA} {A' : Type uA'}
    [Monoid A] [Monoid A'] {ι : Type uι}
    (f : A →* A') :
    mapTuple (ι := ι) f (1 : ι → A) = (1 : ι → A') := by
  funext i
  simp only [mapTuple_apply, Pi.one_apply, f.map_one]

theorem mapTuple_mul {A : Type uA} {A' : Type uA'}
    [Monoid A] [Monoid A'] {ι : Type uι}
    (f : A →* A') (u v : ι → A) :
    mapTuple f (u * v) = mapTuple f u * mapTuple f v := by
  funext i
  simp only [mapTuple_apply, Pi.mul_apply, f.map_mul]

def mapTupleHom {A : Type uA} {A' : Type uA'}
    [Monoid A] [Monoid A'] {ι : Type uι}
    (f : A →* A') : (ι → A) →* (ι → A') where
  toFun := mapTuple (f := f)
  map_one' := mapTuple_one (f := f)
  map_mul' := mapTuple_mul (f := f)

@[simp]
theorem mapTupleHom_apply {A : Type uA} {A' : Type uA'}
    [Monoid A] [Monoid A'] {ι : Type uι}
    (f : A →* A') (u : ι → A) :
    mapTupleHom (ι := ι) f u = mapTuple f u :=
  rfl

@[simp]
theorem mapTupleHom_id {A : Type uA} [Monoid A] {ι : Type uι} :
    mapTupleHom (ι := ι) (MonoidHom.id A) = MonoidHom.id (ι → A) := by
  apply MonoidHom.ext
  intro u
  funext i
  simp [mapTupleHom, mapTuple]

theorem mapTupleHom_comp {A : Type uA} {A' : Type uA'} {A'' : Type uA''}
    [Monoid A] [Monoid A'] [Monoid A'']
    {ι : Type uι} (f : A →* A') (g : A' →* A'') :
    mapTupleHom (ι := ι) (g.comp f) =
      (mapTupleHom (ι := ι) g).comp (mapTupleHom (ι := ι) f) := by
  apply MonoidHom.ext
  intro u
  funext i
  simp [mapTupleHom, mapTuple, MonoidHom.comp_apply]

theorem permute_mapTuple_comm {A : Type uA} {A' : Type uA'}
    [Monoid A] [Monoid A'] {ι : Type uι}
    (f : A →* A') (σ : Equiv.Perm ι) (u : ι → A) :
    mapTuple f (permute σ u) = permute σ (mapTuple f u) := by
  funext i
  simp only [mapTuple_apply, permute_apply]

end Permute

section LowerInv

variable {ι : Type uι} [Fintype ι] [LinearOrder ι]
variable {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]

/-- Lower-triangular sum `Σ i, Σ j≤i, b(u i, v j)`. -/
def lowerSum (b : SkewBicharacter A B) (u v : ι → A) : B :=
  ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
    b.eval (u i) (v j)

/-- Inversion correction `Σ_{i<j, σ i > σ j} b(u i, u j)`. -/
def inversionSum (b : SkewBicharacter A B)
    (σ : Equiv.Perm ι) (u : ι → A) : B :=
  ∑ i : ι,
    ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
      b.eval (u i) (u j)

theorem lowerSum_one_left (b : SkewBicharacter A B) (v : ι → A) :
    lowerSum (ι := ι) b (1 : ι → A) v = 0 := by
  unfold lowerSum
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  simp only [SkewBicharacter.eval_one_left, Pi.one_apply]

theorem lowerSum_one_right (b : SkewBicharacter A B) (u : ι → A) :
    lowerSum (ι := ι) b u (1 : ι → A) = 0 := by
  unfold lowerSum
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  simp only [SkewBicharacter.eval_one_right, Pi.one_apply]

theorem lowerSum_mul_left (b : SkewBicharacter A B)
    (u₁ u₂ v : ι → A) :
    lowerSum (ι := ι) b (u₁ * u₂) v =
      lowerSum b u₁ v + lowerSum b u₂ v := by
  unfold lowerSum
  have h : ∀ i : ι,
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval ((u₁ * u₂) i) (v j)) =
        (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval (u₁ i) (v j)) +
        (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval (u₂ i) (v j)) := by
    intro i
    have h1 : ((u₁ * u₂) i) = u₁ i * u₂ i := rfl
    calc ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval ((u₁ * u₂) i) (v j)
        = ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
            (b.eval (u₁ i) (v j) + b.eval (u₂ i) (v j)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [h1, SkewBicharacter.eval_mul_left]
        _ = _ := by rw [Finset.sum_add_distrib]
  calc ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        b.eval ((u₁ * u₂) i) (v j)
      = ∑ i : ι,
          ((∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
              b.eval (u₁ i) (v j)) +
            (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
              b.eval (u₂ i) (v j))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h i
      _ = _ := by rw [Finset.sum_add_distrib]

theorem lowerSum_mul_right (b : SkewBicharacter A B)
    (u v₁ v₂ : ι → A) :
    lowerSum (ι := ι) b u (v₁ * v₂) =
      lowerSum b u v₁ + lowerSum b u v₂ := by
  unfold lowerSum
  have h : ∀ i : ι,
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval (u i) ((v₁ * v₂) j)) =
        (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval (u i) (v₁ j)) +
        (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval (u i) (v₂ j)) := by
    intro i
    calc ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval (u i) ((v₁ * v₂) j)
        = ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
            (b.eval (u i) (v₁ j * v₂ j)) := by
          apply Finset.sum_congr rfl
          intro j _
          rfl
        _ = ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
            (b.eval (u i) (v₁ j) + b.eval (u i) (v₂ j)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [SkewBicharacter.eval_mul_right]
        _ = _ := by rw [Finset.sum_add_distrib]
  calc ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
        b.eval (u i) ((v₁ * v₂) j)
      = ∑ i : ι,
          ((∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
              b.eval (u i) (v₁ j)) +
            (∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
              b.eval (u i) (v₂ j))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h i
      _ = _ := by rw [Finset.sum_add_distrib]

theorem inversionSum_one_tuple (b : SkewBicharacter A B)
    (σ : Equiv.Perm ι) :
    inversionSum (ι := ι) b σ (1 : ι → A) = 0 := by
  unfold inversionSum
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  simp only [SkewBicharacter.eval_one_left, Pi.one_apply]

theorem inversionSum_perm_one (b : SkewBicharacter A B) (u : ι → A) :
    inversionSum (ι := ι) b (1 : Equiv.Perm ι) u = 0 := by
  unfold inversionSum
  apply Finset.sum_eq_zero
  intro i _
  have h_empty :
      (Finset.univ.filter
          (fun j : ι => i < j ∧ (1 : Equiv.Perm ι) i > (1 : Equiv.Perm ι) j)) =
        ∅ := by
    ext j
    constructor
    · intro hj
      have hj' := (Finset.mem_filter.mp hj).2
      simp only [Equiv.Perm.one_apply] at hj'
      exact absurd (lt_trans hj'.1 hj'.2) (lt_irrefl _)
    · intro hj
      simp at hj
  rw [h_empty]
  simp

end LowerInv

section Transport

variable {ι : Type uι} [Fintype ι] [LinearOrder ι]
variable {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
variable (b : SkewBicharacter A B)

private def alphaPermAux (b : SkewBicharacter A B)
    (σ : Equiv.Perm ι) (u v : ι → A) : B :=
  ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => σ j ≤ σ i),
    b.eval (u i) (v j)

private theorem filter_le_eq_filter_lt_union_single (p : ι) :
    Finset.univ.filter (fun q : ι => q ≤ p) =
      (Finset.univ.filter (fun q : ι => q < p)) ∪ {p} := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro h
    by_cases h_eq : q = p
    · right; exact h_eq
    · left; exact lt_of_le_of_ne h h_eq
  · intro h
    cases h with
    | inl hlt => exact le_of_lt hlt
    | inr heq => rw [heq]

private theorem filter_sigma_le_eq (σ : Equiv.Perm ι) (p : ι) :
    Finset.univ.filter (fun q : ι => σ q ≤ σ p) =
      (Finset.univ.filter (fun q : ι => σ q < σ p)) ∪ {p} := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro h
    by_cases h_eq : q = p
    · right; exact h_eq
    · left
      have h_ne : σ q ≠ σ p := fun h_eq2 => h_eq (σ.injective h_eq2)
      exact lt_of_le_of_ne h h_ne
  · intro h
    cases h with
    | inl hlt => exact le_of_lt hlt
    | inr heq => rw [heq]

private theorem filter_sigma_lt_disjoint_single
    (σ : Equiv.Perm ι) (p : ι) :
    Disjoint (Finset.univ.filter (fun q : ι => σ q < σ p)) {p} := by
  rw [Finset.disjoint_singleton_right]
  simp

private theorem filter_lt_disjoint_single (p : ι) :
    Disjoint (Finset.univ.filter (fun q : ι => q < p)) {p} := by
  rw [Finset.disjoint_singleton_right]
  simp

private theorem sum_filter_le (p : ι) (f : ι → B) :
    ∑ q ∈ Finset.univ.filter (fun q : ι => q ≤ p), f q =
      (∑ q ∈ Finset.univ.filter (fun q : ι => q < p), f q) + f p := by
  have h_eq := filter_le_eq_filter_lt_union_single (ι := ι) p
  have h_disj := filter_lt_disjoint_single (ι := ι) p
  rw [h_eq, Finset.sum_union h_disj, Finset.sum_singleton]

private theorem sum_filter_sigma_le (σ : Equiv.Perm ι) (p : ι)
    (f : ι → B) :
    ∑ q ∈ Finset.univ.filter (fun q : ι => σ q ≤ σ p), f q =
      (∑ q ∈ Finset.univ.filter (fun q : ι => σ q < σ p), f q) + f p := by
  have h_eq := filter_sigma_le_eq (ι := ι) σ p
  have h_disj := filter_sigma_lt_disjoint_single (ι := ι) σ p
  rw [h_eq, Finset.sum_union h_disj, Finset.sum_singleton]

private theorem lowerSum_perm_reindex
    (σ : Equiv.Perm ι) (u v : ι → A) :
    lowerSum (ι := ι) b (permute σ u) (permute σ v) =
      alphaPermAux (ι := ι) b σ u v := by
  unfold lowerSum alphaPermAux permute
  have h_outer :
      (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval (u (σ⁻¹ i)) (v (σ⁻¹ j))) =
        (∑ p : ι, ∑ j ∈ Finset.univ.filter (fun j => j ≤ σ p),
          b.eval (u p) (v (σ⁻¹ j))) := by
    have h1 :
        (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
            b.eval (u (σ⁻¹ i)) (v (σ⁻¹ j))) =
          ∑ p : ι,
            (∑ j ∈ Finset.univ.filter (fun j => j ≤ σ p),
              b.eval (u (σ⁻¹ (σ p))) (v (σ⁻¹ j))) := by
      rw [← Equiv.sum_comp σ (fun i =>
        ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval (u (σ⁻¹ i)) (v (σ⁻¹ j)))]
    rw [h1]
    apply Finset.sum_congr rfl
    intro p _
    have h2 : u (σ⁻¹ (σ p)) = u p := by simp
    rw [h2]
  rw [h_outer]
  apply Finset.sum_congr rfl
  intro p _
  have h_map :
      (Finset.univ.filter (fun q : ι => σ q ≤ σ p)).map
        ⟨σ, σ.injective⟩ =
        Finset.univ.filter (fun j : ι => j ≤ σ p) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro hj; exact ⟨σ⁻¹ j, by simpa using hj, by simp⟩
  have h_inner :
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ σ p),
          b.eval (u p) (v (σ⁻¹ j))) =
        (∑ q ∈ Finset.univ.filter (fun q => σ q ≤ σ p),
          b.eval (u p) (v q)) := by
    rw [← h_map, Finset.sum_map]
    simp
  exact h_inner

set_option maxRecDepth 10000 in
private theorem generic_transport (σ : Equiv.Perm ι) (u v : ι → A) :
    lowerSum (ι := ι) b u v + inversionSum (ι := ι) b σ (u * v) =
      inversionSum (ι := ι) b σ u +
        inversionSum (ι := ι) b σ v +
        alphaPermAux (ι := ι) b σ u v := by
  have h_q_expand :
      inversionSum (ι := ι) b σ (u * v) =
        inversionSum (ι := ι) b σ u +
          inversionSum (ι := ι) b σ v +
          ∑ i : ι,
            ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              (b.eval (u i) (v j) + b.eval (v i) (u j)) := by
    unfold inversionSum
    have h_expand : ∀ i : ι,
        (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            b.eval ((u * v) i) ((u * v) j)) =
          (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (u i) (u j)) +
            (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (u i) (v j)) +
            (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (v i) (u j)) +
            (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (v i) (v j)) := by
      intro i
      have h1 :
          ∀ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            b.eval ((u * v) i) ((u * v) j) =
              b.eval (u i) (u j) + b.eval (u i) (v j) +
                b.eval (v i) (u j) + b.eval (v i) (v j) := by
        intro j _
        calc b.eval ((u * v) i) ((u * v) j)
            = b.eval (u i * v i) (u j * v j) := rfl
          _ = b.eval (u i * v i) (u j) +
              b.eval (u i * v i) (v j) := by
              rw [b.eval_mul_right]
          _ = (b.eval (u i) (u j) + b.eval (v i) (u j)) +
              (b.eval (u i) (v j) + b.eval (v i) (v j)) := by
              rw [b.eval_mul_left, b.eval_mul_left]
          _ = b.eval (u i) (u j) + b.eval (u i) (v j) +
              b.eval (v i) (u j) + b.eval (v i) (v j) := by abel
      calc ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            b.eval ((u * v) i) ((u * v) j)
          = ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              (b.eval (u i) (u j) + b.eval (u i) (v j) +
                b.eval (v i) (u j) + b.eval (v i) (v j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact h1 j hj
        _ = (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (u i) (u j)) +
            (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (u i) (v j)) +
            (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (v i) (u j)) +
            (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (v i) (v j)) := by
            simp [Finset.sum_add_distrib]
    calc ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
          b.eval ((u * v) i) ((u * v) j)
        = ∑ i : ι,
            ((∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                b.eval (u i) (u j)) +
              (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                b.eval (u i) (v j)) +
              (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                b.eval (v i) (u j)) +
              (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                b.eval (v i) (v j))) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_expand i
      _ = (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            b.eval (u i) (u j)) +
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            b.eval (u i) (v j)) +
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            b.eval (v i) (u j)) +
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            b.eval (v i) (v j)) := by
          simp [Finset.sum_add_distrib]
      _ = inversionSum (ι := ι) b σ u +
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            b.eval (u i) (v j)) +
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            b.eval (v i) (u j)) +
          inversionSum (ι := ι) b σ v := by
          unfold inversionSum; abel
      _ = inversionSum (ι := ι) b σ u +
          inversionSum (ι := ι) b σ v +
          ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            (b.eval (u i) (v j) + b.eval (v i) (u j)) := by
          have h :
              (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                b.eval (u i) (v j)) +
                (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                  b.eval (v i) (u j)) =
                ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                  (b.eval (u i) (v j) + b.eval (v i) (u j)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            rw [← Finset.sum_add_distrib]
          calc inversionSum (ι := ι) b σ u +
              (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                b.eval (u i) (v j)) +
              (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                b.eval (v i) (u j)) +
              inversionSum (ι := ι) b σ v
            = inversionSum (ι := ι) b σ u +
                inversionSum (ι := ι) b σ v +
                ((∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                    b.eval (u i) (v j)) +
                  (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                    b.eval (v i) (u j))) := by abel
            _ = inversionSum (ι := ι) b σ u +
                inversionSum (ι := ι) b σ v +
                ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                  (b.eval (u i) (v j) + b.eval (v i) (u j)) := by rw [h]
  have h_anti : ∀ i j : ι, b.eval (v i) (u j) = -b.eval (u j) (v i) :=
    fun i j => b.skew (v i) (u j)
  have h_cross :
      (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
          (b.eval (u i) (v j) + b.eval (v i) (u j))) =
        (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
          (b.eval (u i) (v j) - b.eval (u j) (v i))) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    rw [h_anti i j, ← sub_eq_add_neg]
  have h_pair :
      alphaPermAux (ι := ι) b σ u v - lowerSum (ι := ι) b u v =
        ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
          (b.eval (u i) (v j) - b.eval (u j) (v i)) := by
    have h_alpha :
        lowerSum (ι := ι) b u v =
          (∑ i : ι, b.eval (u i) (v i)) +
            ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j : ι => j < i),
              b.eval (u i) (v j) := by
      unfold lowerSum
      calc ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
            b.eval (u i) (v j)
          = ∑ i : ι,
              ((∑ j ∈ Finset.univ.filter (fun j => j < i),
                  b.eval (u i) (v j)) +
                b.eval (u i) (v i)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [sum_filter_le (ι := ι) i]
          _ = (∑ i : ι, b.eval (u i) (v i)) +
              ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j < i),
                b.eval (u i) (v j) := by
            rw [Finset.sum_add_distrib]; abel
    have h_alpha_perm :
        alphaPermAux (ι := ι) b σ u v =
          (∑ i : ι, b.eval (u i) (v i)) +
            ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => σ j < σ i),
              b.eval (u i) (v j) := by
      unfold alphaPermAux
      calc ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => σ j ≤ σ i),
            b.eval (u i) (v j)
          = ∑ i : ι,
              ((∑ j ∈ Finset.univ.filter (fun j => σ j < σ i),
                  b.eval (u i) (v j)) +
                b.eval (u i) (v i)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [sum_filter_sigma_le (ι := ι) σ i]
          _ = (∑ i : ι, b.eval (u i) (v i)) +
              ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => σ j < σ i),
                b.eval (u i) (v j) := by
            rw [Finset.sum_add_distrib]; abel
    have h_diff :
        alphaPermAux (ι := ι) b σ u v - lowerSum (ι := ι) b u v =
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => σ j < σ i),
              b.eval (u i) (v j)) -
            (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j < i),
              b.eval (u i) (v j)) := by
      rw [h_alpha, h_alpha_perm]; abel
    have h_split_sigma : ∀ i : ι,
        (∑ j ∈ Finset.univ.filter (fun j => σ j < σ i),
            b.eval (u i) (v j)) =
          (∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j < σ i),
              b.eval (u i) (v j)) +
            (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ j < σ i),
              b.eval (u i) (v j)) := by
      intro i
      have h_eq :
          Finset.univ.filter (fun j : ι => σ j < σ i) =
            (Finset.univ.filter (fun j => j < i ∧ σ j < σ i)) ∪
              (Finset.univ.filter (fun j => i < j ∧ σ j < σ i)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union]
        constructor
        · intro h
          by_cases h_lt : j < i
          · left; exact ⟨h_lt, h⟩
          · right
            have h_le : i ≤ j := le_of_not_gt h_lt
            have h_ne : j ≠ i := by
              intro h_eq
              rw [h_eq] at h
              exact lt_irrefl _ h
            exact ⟨lt_of_le_of_ne h_le h_ne.symm, h⟩
        · intro h
          cases h with
          | inl h => exact h.2
          | inr h => exact h.2
      have h_disj :
          Disjoint
            (Finset.univ.filter (fun j => j < i ∧ σ j < σ i))
            (Finset.univ.filter (fun j => i < j ∧ σ j < σ i)) := by
        rw [Finset.disjoint_filter]
        intro j _ h1 h2
        exact absurd (lt_trans h1.1 h2.1) (lt_irrefl _)
      rw [h_eq, Finset.sum_union h_disj]
    have h_split_lt : ∀ i : ι,
        (∑ j ∈ Finset.univ.filter (fun j => j < i), b.eval (u i) (v j)) =
          (∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j < σ i),
              b.eval (u i) (v j)) +
            (∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j > σ i),
              b.eval (u i) (v j)) := by
      intro i
      have h_eq :
          Finset.univ.filter (fun j : ι => j < i) =
            (Finset.univ.filter (fun j => j < i ∧ σ j < σ i)) ∪
              (Finset.univ.filter (fun j => j < i ∧ σ j > σ i)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union]
        constructor
        · intro h
          by_cases h_σ : σ j < σ i
          · left; exact ⟨h, h_σ⟩
          · right
            have h_ne : σ j ≠ σ i := by
              intro h_eq
              have h_eq2 : j = i := σ.injective h_eq
              rw [h_eq2] at h
              exact lt_irrefl _ h
            exact ⟨h, lt_of_le_of_ne (le_of_not_gt h_σ) h_ne.symm⟩
        · intro h
          cases h with
          | inl h => exact h.1
          | inr h => exact h.1
      have h_disj :
          Disjoint
            (Finset.univ.filter (fun j => j < i ∧ σ j < σ i))
            (Finset.univ.filter (fun j => j < i ∧ σ j > σ i)) := by
        rw [Finset.disjoint_filter]
        intro j _ h1 h2
        exact absurd h1.2 (not_lt.mpr (le_of_lt h2.2))
      rw [h_eq, Finset.sum_union h_disj]
    have h_diff2 :
        (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => σ j < σ i),
            b.eval (u i) (v j)) -
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j < i),
            b.eval (u i) (v j)) =
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ j < σ i),
              b.eval (u i) (v j)) -
            (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j > σ i),
              b.eval (u i) (v j)) := by
      calc (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => σ j < σ i),
              b.eval (u i) (v j)) -
            (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j < i),
              b.eval (u i) (v j))
          = (∑ i : ι,
                ((∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j < σ i),
                    b.eval (u i) (v j)) +
                  (∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ j < σ i),
                    b.eval (u i) (v j)))) -
              (∑ i : ι,
                ((∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j < σ i),
                    b.eval (u i) (v j)) +
                  (∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j > σ i),
                    b.eval (u i) (v j)))) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro i _
              rw [h_split_sigma i]
            · apply Finset.sum_congr rfl
              intro i _
              rw [h_split_lt i]
        _ = (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ j < σ i),
              b.eval (u i) (v j)) -
            (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j > σ i),
              b.eval (u i) (v j)) := by
            simp [Finset.sum_add_distrib]
    have h_swap :
        (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j > σ i),
            b.eval (u i) (v j)) =
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            b.eval (u j) (v i)) := by
      calc (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j > σ i),
              b.eval (u i) (v j)) =
            ∑ i : ι, ∑ j : ι,
              if j < i ∧ σ j > σ i then b.eval (u i) (v j) else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_filter]
        _ = ∑ j : ι, ∑ i : ι,
              if j < i ∧ σ j > σ i then b.eval (u i) (v j) else 0 := by
              rw [Finset.sum_comm]
        _ = ∑ i : ι, ∑ j : ι,
              if i < j ∧ σ i > σ j then b.eval (u j) (v i) else 0 := rfl
        _ = (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (u j) (v i)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_filter]
    calc alphaPermAux (ι := ι) b σ u v - lowerSum (ι := ι) b u v
        = (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ j < σ i),
              b.eval (u i) (v j)) -
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j < i ∧ σ j > σ i),
              b.eval (u i) (v j)) := by
          rw [h_diff, h_diff2]
        _ = (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (u i) (v j)) -
          (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              b.eval (u j) (v i)) := by
          have h_eq1 : ∀ i : ι,
              Finset.univ.filter (fun j => i < j ∧ σ j < σ i) =
                Finset.univ.filter (fun j => i < j ∧ σ i > σ j) := by
            intro i
            ext j
            simp
          have h_eq2 :
              (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ j < σ i),
                  b.eval (u i) (v j)) =
                (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
                  b.eval (u i) (v j)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [h_eq1 i]
          rw [h_eq2, h_swap]
        _ = ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
              (b.eval (u i) (v j) - b.eval (u j) (v i)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_sub_distrib]
  have h_q_cross :
      inversionSum (ι := ι) b σ (u * v) -
          inversionSum (ι := ι) b σ u -
          inversionSum (ι := ι) b σ v =
        ∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
          (b.eval (u i) (v j) - b.eval (u j) (v i)) := by
    calc inversionSum (ι := ι) b σ (u * v) -
            inversionSum (ι := ι) b σ u -
            inversionSum (ι := ι) b σ v
        = (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
            (b.eval (u i) (v j) + b.eval (v i) (u j))) := by
          rw [h_q_expand]; abel
      _ = _ := by rw [h_cross]
  have h_eq :
      alphaPermAux (ι := ι) b σ u v - lowerSum (ι := ι) b u v =
        inversionSum (ι := ι) b σ (u * v) -
          inversionSum (ι := ι) b σ u -
            inversionSum (ι := ι) b σ v := by
    rw [h_pair, h_q_cross]
  calc lowerSum (ι := ι) b u v + inversionSum (ι := ι) b σ (u * v)
      = inversionSum (ι := ι) b σ u +
          inversionSum (ι := ι) b σ v +
        alphaPermAux (ι := ι) b σ u v := by
        have h :
            alphaPermAux (ι := ι) b σ u v =
              lowerSum (ι := ι) b u v +
                (inversionSum (ι := ι) b σ (u * v) -
                  inversionSum (ι := ι) b σ u -
                    inversionSum (ι := ι) b σ v) := by
          rw [← h_eq]; abel
        rw [h]; abel

theorem lowerSum_inversion_transport (σ : Equiv.Perm ι)
    (u v : ι → A) :
    lowerSum (ι := ι) b u v + inversionSum (ι := ι) b σ (u * v) =
      inversionSum (ι := ι) b σ u +
        inversionSum (ι := ι) b σ v +
        lowerSum (ι := ι) b (permute σ u) (permute σ v) := by
  have h1 := generic_transport (b := b) σ u v
  have h2 := lowerSum_perm_reindex (b := b) σ u v
  rw [← h2] at h1
  exact h1

end Transport

section Cocycle

variable {ι : Type uι} [Fintype ι] [LinearOrder ι]
variable {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
variable (b : SkewBicharacter A B)

def lowerAddCocycle (u v : ι → A) : B :=
  lowerSum (ι := ι) b u v

theorem lowerAddCocycle_one_left (v : ι → A) :
    lowerAddCocycle (ι := ι) b (1 : ι → A) v = 0 :=
  lowerSum_one_left (ι := ι) b v

theorem lowerAddCocycle_one_right (u : ι → A) :
    lowerAddCocycle (ι := ι) b u (1 : ι → A) = 0 :=
  lowerSum_one_right (ι := ι) b u

theorem lowerAddCocycle_mul_left (u₁ u₂ v : ι → A) :
    lowerAddCocycle (ι := ι) b (u₁ * u₂) v =
      lowerAddCocycle (ι := ι) b u₁ v +
        lowerAddCocycle (ι := ι) b u₂ v :=
  lowerSum_mul_left (ι := ι) b u₁ u₂ v

theorem lowerAddCocycle_mul_right (u v₁ v₂ : ι → A) :
    lowerAddCocycle (ι := ι) b u (v₁ * v₂) =
      lowerAddCocycle (ι := ι) b u v₁ +
        lowerAddCocycle (ι := ι) b u v₂ :=
  lowerSum_mul_right (ι := ι) b u v₁ v₂

theorem lowerAddCocycle_cocycle (u v w : ι → A) :
    lowerAddCocycle (ι := ι) b u v +
        lowerAddCocycle (ι := ι) b (u * v) w =
      lowerAddCocycle (ι := ι) b u (v * w) +
        lowerAddCocycle (ι := ι) b v w := by
  have h1 : lowerAddCocycle (ι := ι) b (u * v) w =
      lowerAddCocycle (ι := ι) b u w +
        lowerAddCocycle (ι := ι) b v w :=
    lowerAddCocycle_mul_left (ι := ι) b u v w
  have h2 : lowerAddCocycle (ι := ι) b u (v * w) =
      lowerAddCocycle (ι := ι) b u v +
        lowerAddCocycle (ι := ι) b u w :=
    lowerAddCocycle_mul_right (ι := ι) b u v w
  calc lowerAddCocycle (ι := ι) b u v +
        lowerAddCocycle (ι := ι) b (u * v) w
      = lowerAddCocycle (ι := ι) b u v +
        (lowerAddCocycle (ι := ι) b u w +
          lowerAddCocycle (ι := ι) b v w) := by rw [h1]
    _ = lowerAddCocycle (ι := ι) b u v +
        lowerAddCocycle (ι := ι) b u w +
        lowerAddCocycle (ι := ι) b v w := by abel
    _ = (lowerAddCocycle (ι := ι) b u v +
        lowerAddCocycle (ι := ι) b u w) +
        lowerAddCocycle (ι := ι) b v w := by abel
    _ = lowerAddCocycle (ι := ι) b u (v * w) +
        lowerAddCocycle (ι := ι) b v w := by rw [← h2]

def lowerCocycleAll (u v : ι → A) : Multiplicative B :=
  Multiplicative.ofAdd (lowerAddCocycle (ι := ι) b u v)

theorem lowerCocycleAll_one_left (v : ι → A) :
    lowerCocycleAll (ι := ι) b (1 : ι → A) v = 1 := by
  unfold lowerCocycleAll
  rw [lowerAddCocycle_one_left]
  rfl

theorem lowerCocycleAll_one_right (u : ι → A) :
    lowerCocycleAll (ι := ι) b u (1 : ι → A) = 1 := by
  unfold lowerCocycleAll
  rw [lowerAddCocycle_one_right]
  rfl

theorem lowerCocycleAll_mul_left (u₁ u₂ v : ι → A) :
    lowerCocycleAll (ι := ι) b (u₁ * u₂) v =
      lowerCocycleAll (ι := ι) b u₁ v *
        lowerCocycleAll (ι := ι) b u₂ v := by
  unfold lowerCocycleAll
  rw [lowerAddCocycle_mul_left, ofAdd_add]

theorem lowerCocycleAll_mul_right (u v₁ v₂ : ι → A) :
    lowerCocycleAll (ι := ι) b u (v₁ * v₂) =
      lowerCocycleAll (ι := ι) b u v₁ *
        lowerCocycleAll (ι := ι) b u v₂ := by
  unfold lowerCocycleAll
  rw [lowerAddCocycle_mul_right, ofAdd_add]

theorem lowerCocycleAll_cocycle (u v w : ι → A) :
    lowerCocycleAll (ι := ι) b u v *
        lowerCocycleAll (ι := ι) b (u * v) w =
      lowerCocycleAll (ι := ι) b u (v * w) *
        lowerCocycleAll (ι := ι) b v w := by
  unfold lowerCocycleAll
  have h := lowerAddCocycle_cocycle (ι := ι) b u v w
  calc Multiplicative.ofAdd (lowerAddCocycle (ι := ι) b u v) *
        Multiplicative.ofAdd (lowerAddCocycle (ι := ι) b (u * v) w)
      = Multiplicative.ofAdd
          (lowerAddCocycle (ι := ι) b u v +
            lowerAddCocycle (ι := ι) b (u * v) w) := by
        rw [← ofAdd_add]
    _ = Multiplicative.ofAdd
          (lowerAddCocycle (ι := ι) b u (v * w) +
            lowerAddCocycle (ι := ι) b v w) := by rw [h]
    _ = Multiplicative.ofAdd (lowerAddCocycle (ι := ι) b u (v * w)) *
        Multiplicative.ofAdd (lowerAddCocycle (ι := ι) b v w) := by
        rw [ofAdd_add]

def lowerNormalizedCocycle :
    NormalizedCocycleExtension.NormalizedCocycle
      (ι → A) (Multiplicative B) where
  cocycle := lowerCocycleAll (ι := ι) b
  one_left := lowerCocycleAll_one_left (ι := ι) b
  one_right := lowerCocycleAll_one_right (ι := ι) b
  cocycle_assoc := lowerCocycleAll_cocycle (ι := ι) b

abbrev Extension (b : SkewBicharacter A B) (ι : Type uι)
    [Fintype ι] [LinearOrder ι] :=
  NormalizedCocycleExtension.Extension
    (lowerNormalizedCocycle (ι := ι) b)

@[ext]
theorem Extension.ext {b : SkewBicharacter A B} {ι : Type uι}
    [Fintype ι] [LinearOrder ι]
    {x y : Extension b ι} (h1 : x.base = y.base)
    (h2 : x.coeff = y.coeff) : x = y :=
  NormalizedCocycleExtension.Extension.ext h1 h2

@[simp]
theorem Extension.mul_base {b : SkewBicharacter A B} {ι : Type uι}
    [Fintype ι] [LinearOrder ι]
    (x y : Extension b ι) :
    (x * y).base = x.base * y.base :=
  rfl

@[simp]
theorem Extension.mul_coeff {b : SkewBicharacter A B} {ι : Type uι}
    [Fintype ι] [LinearOrder ι]
    (x y : Extension b ι) :
    (x * y).coeff =
      x.coeff * y.coeff * lowerCocycleAll (ι := ι) b x.base y.base :=
  rfl

@[simp]
theorem Extension.one_base {b : SkewBicharacter A B} {ι : Type uι}
    [Fintype ι] [LinearOrder ι] :
    (1 : Extension b ι).base = (1 : ι → A) :=
  rfl

@[simp]
theorem Extension.one_coeff {b : SkewBicharacter A B} {ι : Type uι}
    [Fintype ι] [LinearOrder ι] :
    (1 : Extension b ι).coeff = (1 : Multiplicative B) :=
  rfl

@[simp]
theorem Extension.inv_base {b : SkewBicharacter A B} {ι : Type uι}
    [Fintype ι] [LinearOrder ι] (x : Extension b ι) :
    (x⁻¹ : Extension b ι).base = x.base⁻¹ :=
  rfl

theorem Extension.inv_coeff {b : SkewBicharacter A B} {ι : Type uι}
    [Fintype ι] [LinearOrder ι] (x : Extension b ι) :
    (x⁻¹ : Extension b ι).coeff =
      x.coeff⁻¹ * (lowerCocycleAll (ι := ι) b x.base⁻¹ x.base)⁻¹ :=
  rfl

def extensionGroupExtension (b : SkewBicharacter A B) :
    GroupExtension (Multiplicative B) (Extension b ι) (ι → A) :=
  NormalizedCocycleExtension.extension
    (lowerNormalizedCocycle (ι := ι) b)

theorem extension_isCentral (b : SkewBicharacter A B) :
    (extensionGroupExtension (ι := ι) b).IsCentral :=
  NormalizedCocycleExtension.isCentral
    (lowerNormalizedCocycle (ι := ι) b)

def permCompatibleMap (b : SkewBicharacter A B)
    (σ : Equiv.Perm ι) :
    NormalizedCocycleExtension.CompatibleMap
      (lowerNormalizedCocycle (ι := ι) b)
      (lowerNormalizedCocycle (ι := ι) b) where
  f := permuteHom (A := A) σ
  g := MonoidHom.id (Multiplicative B)
  q := fun u => Multiplicative.ofAdd (inversionSum (ι := ι) b σ u)
  q_one := by simp [inversionSum_one_tuple]
  compat := by
    intro x y
    simp only [MonoidHom.id_apply]
    have h_add :=
      lowerSum_inversion_transport (ι := ι) (b := b) σ x y
    calc Multiplicative.ofAdd (lowerSum (ι := ι) b x y) *
          Multiplicative.ofAdd (inversionSum (ι := ι) b σ (x * y))
        = Multiplicative.ofAdd
            (lowerSum (ι := ι) b x y +
              inversionSum (ι := ι) b σ (x * y)) := by
          rw [← ofAdd_add]
      _ = Multiplicative.ofAdd
            (inversionSum (ι := ι) b σ x +
              inversionSum (ι := ι) b σ y +
              lowerSum (ι := ι) b (permute σ x) (permute σ y)) := by
          rw [h_add]
      _ = Multiplicative.ofAdd (inversionSum (ι := ι) b σ x) *
          Multiplicative.ofAdd (inversionSum (ι := ι) b σ y) *
          Multiplicative.ofAdd
            (lowerSum (ι := ι) b (permute σ x) (permute σ y)) := by
          rw [ofAdd_add, ofAdd_add, mul_assoc]
      _ = Multiplicative.ofAdd (inversionSum (ι := ι) b σ x) *
          Multiplicative.ofAdd (inversionSum (ι := ι) b σ y) *
          lowerCocycleAll (ι := ι) b (permuteHom (A := A) σ x)
            (permuteHom (A := A) σ y) := rfl

def permCompatibleHom (b : SkewBicharacter A B)
    (σ : Equiv.Perm ι) : Extension b ι →* Extension b ι :=
  (permCompatibleMap (ι := ι) b σ).toHom

@[simp]
theorem permCompatibleHom_base (b : SkewBicharacter A B)
    (σ : Equiv.Perm ι) (h : Extension b ι) :
    (permCompatibleHom (ι := ι) b σ h).base = permute σ h.base :=
  rfl

@[simp]
theorem permCompatibleHom_coeff (b : SkewBicharacter A B)
    (σ : Equiv.Perm ι) (h : Extension b ι) :
    (permCompatibleHom (ι := ι) b σ h).coeff =
      h.coeff * Multiplicative.ofAdd (inversionSum (ι := ι) b σ h.base) := by
  simp [permCompatibleHom, permCompatibleMap,
    NormalizedCocycleExtension.CompatibleMap.toHom_coeff]

theorem permCompatibleMap_compat (b : SkewBicharacter A B)
    (σ : Equiv.Perm ι) (x y : ι → A) :
    lowerCocycleAll (ι := ι) b x y *
        Multiplicative.ofAdd (inversionSum (ι := ι) b σ (x * y)) =
      Multiplicative.ofAdd (inversionSum (ι := ι) b σ x) *
        Multiplicative.ofAdd (inversionSum (ι := ι) b σ y) *
        lowerCocycleAll (ι := ι) b (permute σ x) (permute σ y) :=
  (permCompatibleMap (ι := ι) b σ).compat x y

end Cocycle

section Coherence

variable {ι : Type uι} [Fintype ι] [LinearOrder ι]
variable {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
variable (b : SkewBicharacter A B)

/-! ### Correction composition law

`inversionSum b (σ * τ) u = inversionSum b τ u
  + inversionSum b σ (permute τ u)` via pairwise reindexing through `τ`
and `b.eval_skew`. -/

set_option maxRecDepth 10000 in
private theorem inversionSum_permute_reindex
    (σ τ : Equiv.Perm ι) (u : ι → A) :
    inversionSum (ι := ι) b σ (permute τ u) =
      ∑ i : ι, ∑ j ∈ Finset.univ.filter
          (fun j => τ i < τ j ∧ (σ * τ) i > (σ * τ) j),
        b.eval (u i) (u j) := by
  unfold inversionSum permute
  have h_outer :
      (∑ i : ι, ∑ j ∈ Finset.univ.filter
          (fun j => i < j ∧ σ i > σ j),
        b.eval (u (τ⁻¹ i)) (u (τ⁻¹ j))) =
        (∑ p : ι, ∑ j ∈ Finset.univ.filter
            (fun j => τ p < j ∧ σ (τ p) > σ j),
          b.eval (u p) (u (τ⁻¹ j))) := by
    rw [← Equiv.sum_comp τ (fun i =>
      ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ i > σ j),
        b.eval (u (τ⁻¹ i)) (u (τ⁻¹ j)))]
    apply Finset.sum_congr rfl
    intro p _
    have hp : u (τ⁻¹ (τ p)) = u p := by
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [hp]
  rw [h_outer]
  apply Finset.sum_congr rfl
  intro p _
  have h_map :
      (Finset.univ.filter
          (fun q : ι => τ p < τ q ∧ σ (τ p) > σ (τ q))).map
        ⟨τ, τ.injective⟩ =
        Finset.univ.filter
          (fun j : ι => τ p < j ∧ σ (τ p) > σ j) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro hj
      refine ⟨τ⁻¹ j, ?_, by
        simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply]⟩
      simpa using hj
  have h_inner :
      (∑ j ∈ Finset.univ.filter
          (fun j : ι => τ p < j ∧ σ (τ p) > σ j),
        b.eval (u p) (u (τ⁻¹ j))) =
        (∑ q ∈ Finset.univ.filter
            (fun q : ι => τ p < τ q ∧ σ (τ p) > σ (τ q)),
          b.eval (u p) (u q)) := by
    rw [← h_map, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have h_coeff :
      (Finset.univ.filter
          (fun q : ι => τ p < τ q ∧ σ (τ p) > σ (τ q))) =
        (Finset.univ.filter
          (fun q : ι => τ p < τ q ∧ (σ * τ) p > (σ * τ) q)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨h.1, by simpa using h.2⟩
    · intro h
      exact ⟨h.1, by simpa using h.2⟩
  rw [h_coeff] at h_inner
  exact h_inner

set_option maxRecDepth 10000 in
private theorem reindexed_split (σ τ : Equiv.Perm ι) (u : ι → A) :
    (∑ i : ι, ∑ j ∈ Finset.univ.filter
        (fun j => τ i < τ j ∧ (σ * τ) i > (σ * τ) j),
      b.eval (u i) (u j)) =
      (∑ i : ι, ∑ j ∈ Finset.univ.filter
          (fun j => i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ * τ) j),
        b.eval (u i) (u j)) +
      (∑ i : ι, ∑ j ∈ Finset.univ.filter
          (fun j => i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ *τ) j),
        -b.eval (u i) (u j)) := by
  have h_split : ∀ i : ι,
      Finset.univ.filter
          (fun j : ι => τ i < τ j ∧ (σ * τ) i > (σ * τ) j) =
        (Finset.univ.filter
            (fun j : ι => i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j)) ∪
        (Finset.univ.filter
            (fun j : ι => j < i ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j)) := by
    intro i
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro h
      have h_ne : j ≠ i := by
        intro h_eq
        rw [h_eq] at h
        exact lt_irrefl _ h.1
      rcases lt_trichotomy i j with h_lt | h_eq | h_gt
      · left; exact ⟨h_lt, h⟩
      · exact absurd h_eq.symm h_ne
      · right; exact ⟨h_gt, h⟩
    · intro h
      cases h with
      | inl h => exact h.2
      | inr h => exact h.2
  have h_disj : ∀ i : ι, Disjoint
      (Finset.univ.filter
        (fun j : ι => i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j))
      (Finset.univ.filter
        (fun j : ι => j < i ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j)) := by
    intro i
    rw [Finset.disjoint_filter]
    intro j _ h1 h2
    exact absurd (lt_trans h1.1 h2.1) (lt_irrefl _)
  calc (∑ i : ι, ∑ j ∈ Finset.univ.filter
          (fun j => τ i < τ j ∧ (σ * τ) i > (σ * τ) j),
        b.eval (u i) (u j))
      = ∑ i : ι,
          ((∑ j ∈ Finset.univ.filter
              (fun j => i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j),
            b.eval (u i) (u j)) +
          (∑ j ∈ Finset.univ.filter
              (fun j => j < i ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j),
            b.eval (u i) (u j))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [h_split i, Finset.sum_union (h_disj i)]
    _ = (∑ i : ι, ∑ j ∈ Finset.univ.filter
            (fun j => i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j),
          b.eval (u i) (u j)) +
        (∑ i : ι, ∑ j ∈ Finset.univ.filter
            (fun j => j < i ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j),
          b.eval (u i) (u j)) := by
        rw [Finset.sum_add_distrib]
    _ = (∑ i : ι, ∑ j ∈ Finset.univ.filter
            (fun j => i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j),
          b.eval (u i) (u j)) +
        (∑ i : ι, ∑ j ∈ Finset.univ.filter
            (fun j => i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ *τ) j),
          -b.eval (u i) (u j)) := by
        congr 1
        calc (∑ i : ι, ∑ j ∈ Finset.univ.filter
                (fun j => j < i ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j),
              b.eval (u i) (u j))
            = ∑ i : ι, ∑ j : ι,
                if j < i ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j then
                  b.eval (u i) (u j) else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_filter]
          _ = ∑ j : ι, ∑ i : ι,
                if j < i ∧ τ i < τ j ∧ (σ * τ) i > (σ *τ) j then
                  b.eval (u i) (u j) else 0 := by
              rw [Finset.sum_comm]
          _ = ∑ i : ι, ∑ j : ι,
                if i < j ∧ τ j < τ i ∧ (σ * τ) j > (σ *τ) i then
                  b.eval (u j) (u i) else 0 := rfl
          _ = ∑ i : ι, ∑ j ∈ Finset.univ.filter
                (fun j => i < j ∧ τ j < τ i ∧ (σ * τ) j > (σ *τ) i),
              b.eval (u j) (u i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [← Finset.sum_filter]
          _ = ∑ i : ι, ∑ j ∈ Finset.univ.filter
                (fun j => i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ *τ) j),
              -b.eval (u i) (u j) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j hj
              have h_eq : b.eval (u j) (u i) = -b.eval (u i) (u j) :=
                b.eval_skew (u j) (u i)
              rw [h_eq]

omit [Fintype ι] in
private theorem pointwise_split (σ τ : Equiv.Perm ι) (u : ι → A)
    (i j : ι) :
    (if i < j ∧ (σ * τ) i > (σ * τ) j then b.eval (u i) (u j) else (0 : B)) =
      (if i < j ∧ τ i > τ j then b.eval (u i) (u j) else 0) +
      (if i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ * τ) j then
        b.eval (u i) (u j) else 0) +
      (if i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ * τ) j then
        -b.eval (u i) (u j) else 0) := by
  by_cases h_ij : i < j
  · by_cases h_tau : τ i < τ j
    · by_cases h_prod : (σ * τ) i > (σ * τ) j
      · have h_not_tau_gt : ¬ τ i > τ j :=
          not_lt.mpr (le_of_lt h_tau)
        have h_not_prod_lt : ¬ (σ * τ) i < (σ * τ) j :=
          not_lt.mpr (le_of_lt h_prod)
        have h1 : (if i < j ∧ (σ * τ) i > (σ * τ) j then
            b.eval (u i) (u j) else (0 : B)) =
            b.eval (u i) (u j) := ite_eq_left ⟨h_ij, h_prod⟩
        have h2 : (if i < j ∧ τ i > τ j then
            b.eval (u i) (u j) else (0 : B)) = 0 :=
          ite_eq_right (fun h => h_not_tau_gt h.right)
        have h3 : (if i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ * τ) j then
            b.eval (u i) (u j) else (0 : B)) =
            b.eval (u i) (u j) :=
          ite_eq_left ⟨h_ij, And.intro h_tau h_prod⟩
        have h4 : (if i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ * τ) j then
            -b.eval (u i) (u j) else (0 : B)) = 0 :=
          ite_eq_right (fun h => h_not_tau_gt h.right.left)
        rw [h1, h2, h3, h4]
        simp
      · have h_not_tau_gt : ¬ τ i > τ j :=
          not_lt.mpr (le_of_lt h_tau)
        have h1 : (if i < j ∧ (σ * τ) i > (σ * τ) j then
            b.eval (u i) (u j) else (0 : B)) = 0 :=
          ite_eq_right (fun h => h_prod h.right)
        have h2 : (if i < j ∧ τ i > τ j then
            b.eval (u i) (u j) else (0 : B)) = 0 :=
          ite_eq_right (fun h => h_not_tau_gt h.right)
        have h3 : (if i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ * τ) j then
            b.eval (u i) (u j) else (0 : B)) = 0 :=
          ite_eq_right (fun h => h_prod h.right.right)
        have h4 : (if i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ * τ) j then
            -b.eval (u i) (u j) else (0 : B)) = 0 :=
          ite_eq_right (fun h => h_not_tau_gt h.right.left)
        rw [h1, h2, h3, h4]
        simp
    · have h_tau_gt : τ i > τ j := by
        have h_ne : τ i ≠ τ j := by
          intro h_eq
          have : i = j := τ.injective h_eq
          rw [this] at h_ij
          exact lt_irrefl _ h_ij
        exact lt_of_le_of_ne (le_of_not_gt h_tau) h_ne.symm
      by_cases h_prod : (σ * τ) i > (σ * τ) j
      · have h_not_prod_lt : ¬ (σ * τ) i < (σ * τ) j :=
          not_lt.mpr (le_of_lt h_prod)
        have h1 : (if i < j ∧ (σ * τ) i > (σ * τ) j then
            b.eval (u i) (u j) else (0 : B)) =
            b.eval (u i) (u j) := ite_eq_left ⟨h_ij, h_prod⟩
        have h2 : (if i < j ∧ τ i > τ j then
            b.eval (u i) (u j) else (0 : B)) =
            b.eval (u i) (u j) := ite_eq_left ⟨h_ij, h_tau_gt⟩
        have h3 : (if i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ * τ) j then
            b.eval (u i) (u j) else (0 : B)) = 0 :=
          ite_eq_right (fun h => h_tau h.right.left)
        have h4 : (if i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ * τ) j then
            -b.eval (u i) (u j) else (0 : B)) = 0 :=
          ite_eq_right (fun h => h_not_prod_lt h.right.right)
        rw [h1, h2, h3, h4]
        simp
      · have h_prod_lt : (σ * τ) i < (σ * τ) j := by
          have h_ne : (σ * τ) i ≠ (σ * τ) j := by
            intro h_eq
            have : i = j := (σ * τ).injective h_eq
            rw [this] at h_ij
            exact lt_irrefl _ h_ij
          exact lt_of_le_of_ne (le_of_not_gt h_prod) h_ne
        have h1 : (if i < j ∧ (σ * τ) i > (σ * τ) j then
            b.eval (u i) (u j) else (0 : B)) = 0 :=
          ite_eq_right (fun h => h_prod h.right)
        have h2 : (if i < j ∧ τ i > τ j then
            b.eval (u i) (u j) else (0 : B)) =
            b.eval (u i) (u j) := ite_eq_left ⟨h_ij, h_tau_gt⟩
        have h3 : (if i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ * τ) j then
            b.eval (u i) (u j) else (0 : B)) = 0 :=
          ite_eq_right (fun h => h_tau h.right.left)
        have h4 : (if i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ * τ) j then
            -b.eval (u i) (u j) else (0 : B)) =
            -b.eval (u i) (u j) :=
          ite_eq_left ⟨h_ij, And.intro h_tau_gt h_prod_lt⟩
        rw [h1, h2, h3, h4]
        simp
  · have h1 : (if i < j ∧ (σ * τ) i > (σ * τ) j then
        b.eval (u i) (u j) else (0 : B)) = 0 :=
      ite_eq_right (fun h => h_ij h.left)
    have h2 : (if i < j ∧ τ i > τ j then
        b.eval (u i) (u j) else (0 : B)) = 0 :=
      ite_eq_right (fun h => h_ij h.left)
    have h3 : (if i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ * τ) j then
        b.eval (u i) (u j) else (0 : B)) = 0 :=
      ite_eq_right (fun h => h_ij h.left)
    have h4 : (if i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ * τ) j then
        -b.eval (u i) (u j) else (0 : B)) = 0 :=
      ite_eq_right (fun h => h_ij h.left)
    rw [h1, h2, h3, h4]
    simp

set_option maxRecDepth 10000 in
theorem inversionSum_mul (σ τ : Equiv.Perm ι) (u : ι → A) :
    inversionSum (ι := ι) b (σ * τ) u =
      inversionSum (ι := ι) b τ u +
        inversionSum (ι := ι) b σ (permute τ u) := by
  have h_re := inversionSum_permute_reindex (ι := ι) b σ τ u
  have h_split := reindexed_split (ι := ι) b σ τ u
  calc inversionSum (ι := ι) b (σ * τ) u
      = ∑ i : ι, ∑ j ∈ Finset.univ.filter
          (fun j => i < j ∧ (σ * τ) i > (σ * τ) j),
        b.eval (u i) (u j) := rfl
    _ = ∑ i : ι, ∑ j : ι,
          if i < j ∧ (σ * τ) i > (σ * τ) j then
            b.eval (u i) (u j) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_filter]
    _ = ∑ i : ι, ∑ j : ι,
          ((if i < j ∧ τ i > τ j then b.eval (u i) (u j) else 0) +
          (if i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ * τ) j then
            b.eval (u i) (u j) else 0) +
          (if i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ * τ) j then
            -b.eval (u i) (u j) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact pointwise_split (ι := ι) b σ τ u i j
    _ = (∑ i : ι, ∑ j : ι,
            if i < j ∧ τ i > τ j then b.eval (u i) (u j) else 0) +
        (∑ i : ι, ∑ j : ι,
            if i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ * τ) j then
              b.eval (u i) (u j) else 0) +
        (∑ i : ι, ∑ j : ι,
            if i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ * τ) j then
              -b.eval (u i) (u j) else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ i : ι, ∑ j ∈ Finset.univ.filter
            (fun j => i < j ∧ τ i > τ j),
          b.eval (u i) (u j)) +
        (∑ i : ι, ∑ j ∈ Finset.univ.filter
            (fun j => i < j ∧ τ i < τ j ∧ (σ * τ) i > (σ * τ) j),
          b.eval (u i) (u j)) +
        (∑ i : ι, ∑ j ∈ Finset.univ.filter
            (fun j => i < j ∧ τ i > τ j ∧ (σ * τ) i < (σ * τ) j),
          -b.eval (u i) (u j)) := by
        simp only [← Finset.sum_filter]
    _ = inversionSum (ι := ι) b τ u +
        (∑ i : ι, ∑ j ∈ Finset.univ.filter
            (fun j => τ i < τ j ∧ (σ * τ) i > (σ * τ) j),
          b.eval (u i) (u j)) := by
        have h1 : inversionSum (ι := ι) b τ u =
            ∑ i : ι, ∑ j ∈ Finset.univ.filter
                (fun j => i < j ∧ τ i > τ j),
              b.eval (u i) (u j) := rfl
        rw [h1, h_split, add_assoc]
    _ = inversionSum (ι := ι) b τ u +
        inversionSum (ι := ι) b σ (permute τ u) := by
        rw [h_re]

theorem inversionSum_comp (σ τ : Equiv.Perm ι) (u : ι → A) :
    inversionSum (ι := ι) b (σ * τ) u =
      inversionSum (ι := ι) b τ u +
        inversionSum (ι := ι) b σ (permute τ u) :=
  inversionSum_mul (ι := ι) b σ τ u

theorem permCompatibleHom_one :
    permCompatibleHom (ι := ι) b (1 : Equiv.Perm ι) =
      MonoidHom.id (Extension (ι := ι) b) := by
  apply MonoidHom.ext
  intro x
  apply Extension.ext
  · simp [permCompatibleHom, permCompatibleMap, permuteHom_one]
  · simp [permCompatibleHom, permCompatibleMap,
      inversionSum_perm_one]

theorem permCompatibleHom_mul (σ τ : Equiv.Perm ι) :
    permCompatibleHom (ι := ι) b (σ * τ) =
      (permCompatibleHom (ι := ι) b σ).comp
        (permCompatibleHom (ι := ι) b τ) := by
  apply MonoidHom.ext
  intro x
  apply Extension.ext
  · simp [permCompatibleHom, permCompatibleMap, permuteHom_mul]
  · simp only [permCompatibleHom, permCompatibleMap,
      NormalizedCocycleExtension.CompatibleMap.toHom_coeff,
      MonoidHom.comp_apply, MonoidHom.id_apply]
    have h_q : inversionSum (ι := ι) b (σ * τ) x.base =
        inversionSum (ι := ι) b τ x.base +
          inversionSum (ι := ι) b σ (permute τ x.base) :=
      inversionSum_mul (ι := ι) b σ τ x.base
    calc (x.coeff * Multiplicative.ofAdd
            (inversionSum (ι := ι) b (σ * τ) x.base))
        = x.coeff * Multiplicative.ofAdd
            (inversionSum (ι := ι) b τ x.base +
              inversionSum (ι := ι) b σ (permute τ x.base)) := by
          rw [h_q]
      _ = x.coeff * (Multiplicative.ofAdd
            (inversionSum (ι := ι) b τ x.base) *
          Multiplicative.ofAdd
            (inversionSum (ι := ι) b σ (permute τ x.base))) := by
          rw [← ofAdd_add]
      _ = (x.coeff * Multiplicative.ofAdd
            (inversionSum (ι := ι) b τ x.base)) *
          Multiplicative.ofAdd
            (inversionSum (ι := ι) b σ (permute τ x.base)) := by
          rw [mul_assoc]
      _ = ((permCompatibleHom (ι := ι) b σ)
            ((permCompatibleHom (ι := ι) b τ) x)).coeff := by
          simp [permCompatibleHom, permCompatibleMap,
            NormalizedCocycleExtension.CompatibleMap.toHom_coeff]

def permCompatibleEquiv (σ : Equiv.Perm ι) :
    Extension (ι := ι) b ≃* Extension (ι := ι) b where
  toFun := permCompatibleHom (ι := ι) b σ
  invFun := permCompatibleHom (ι := ι) b σ⁻¹
  left_inv x := by
    have h_comp :
        (permCompatibleHom (ι := ι) b σ⁻¹).comp
          (permCompatibleHom (ι := ι) b σ) =
          MonoidHom.id (Extension (ι := ι) b) := by
      rw [← permCompatibleHom_mul, inv_mul_cancel,
        permCompatibleHom_one]
    have h_eq :=
      congrArg (fun f : Extension (ι := ι) b →* Extension (ι := ι) b =>
        f x) h_comp
    simpa using h_eq
  right_inv x := by
    have h_comp :
        (permCompatibleHom (ι := ι) b σ).comp
          (permCompatibleHom (ι := ι) b σ⁻¹) =
          MonoidHom.id (Extension (ι := ι) b) := by
      rw [← permCompatibleHom_mul, mul_inv_cancel,
        permCompatibleHom_one]
    have h_eq :=
      congrArg (fun f : Extension (ι := ι) b →* Extension (ι := ι) b =>
        f x) h_comp
    simpa using h_eq
  map_mul' x y := by
    have h := (permCompatibleHom (ι := ι) b σ).map_mul x y
    exact h

@[simp]
theorem permCompatibleEquiv_apply (σ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    permCompatibleEquiv (ι := ι) b σ x =
      permCompatibleHom (ι := ι) b σ x :=
  rfl

@[simp]
theorem permCompatibleEquiv_symm_apply (σ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    (permCompatibleEquiv (ι := ι) b σ).symm x =
      permCompatibleHom (ι := ι) b σ⁻¹ x :=
  rfl

@[simp]
theorem permCompatibleEquiv_base (σ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    (permCompatibleEquiv (ι := ι) b σ x).base =
      permute σ x.base := rfl

theorem permCompatibleEquiv_coeff (σ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    (permCompatibleEquiv (ι := ι) b σ x).coeff =
      x.coeff * Multiplicative.ofAdd (inversionSum (ι := ι) b σ x.base) :=
  permCompatibleHom_coeff (ι := ι) b σ x

theorem permCompatibleEquiv_symm_base (σ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    ((permCompatibleEquiv (ι := ι) b σ).symm x).base =
      permute σ⁻¹ x.base := rfl

theorem permCompatibleEquiv_symm_coeff (σ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    ((permCompatibleEquiv (ι := ι) b σ).symm x).coeff =
      x.coeff * Multiplicative.ofAdd
        (inversionSum (ι := ι) b σ⁻¹ x.base) :=
  permCompatibleHom_coeff (ι := ι) b σ⁻¹ x

theorem permCompatibleEquiv_one :
    permCompatibleEquiv (ι := ι) b (1 : Equiv.Perm ι) =
      MulEquiv.refl (Extension (ι := ι) b) := by
  apply MulEquiv.ext
  intro x
  simp [permCompatibleEquiv, permCompatibleHom_one]

theorem permCompatibleEquiv_mul (σ τ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    permCompatibleEquiv (ι := ι) b (σ * τ) x =
      permCompatibleEquiv (ι := ι) b σ
        (permCompatibleEquiv (ι := ι) b τ x) := by
  simp [permCompatibleEquiv, permCompatibleHom_mul]

def permActionHom :
    Equiv.Perm ι →* MulAut (Extension (ι := ι) b) where
  toFun σ := permCompatibleEquiv (ι := ι) b σ
  map_one' := by
    simp only [permCompatibleEquiv_one]
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    simp only [permCompatibleEquiv_mul, MulAut.mul_apply]

theorem permActionHom_apply (σ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    (permActionHom (ι := ι) b σ) x =
      permCompatibleHom (ι := ι) b σ x := rfl

@[simp]
theorem permActionHom_one_apply (x : Extension (ι := ι) b) :
    (permActionHom (ι := ι) b (1 : Equiv.Perm ι)) x = x := by
  simp only [permActionHom_apply, permCompatibleHom_one,
    MonoidHom.id_apply]

theorem permActionHom_mul_apply (σ τ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    (permActionHom (ι := ι) b (σ * τ)) x =
      (permActionHom (ι := ι) b σ)
        ((permActionHom (ι := ι) b τ) x) := by
  simp only [permActionHom_apply, permCompatibleHom_mul,
    MonoidHom.comp_apply]

/-- Named `MulAction` via `permActionHom`; not a global instance. -/
@[instance_reducible]
def permMulAction :
    MulAction (Equiv.Perm ι) (Extension (ι := ι) b) where
  smul σ x := permCompatibleHom (ι := ι) b σ x
  one_smul x := by
    change permCompatibleHom (ι := ι) b (1 : Equiv.Perm ι) x = x
    rw [permCompatibleHom_one, MonoidHom.id_apply]
  mul_smul σ τ x := by
    change permCompatibleHom (ι := ι) b (σ * τ) x =
      permCompatibleHom (ι := ι) b σ
        (permCompatibleHom (ι := ι) b τ x)
    rw [permCompatibleHom_mul, MonoidHom.comp_apply]

theorem permMulAction_smul_def (σ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    (permMulAction (ι := ι) b).smul σ x =
      permCompatibleHom (ι := ι) b σ x := rfl

theorem permMulAction_smul_eq_equiv (σ : Equiv.Perm ι)
    (x : Extension (ι := ι) b) :
    (permMulAction (ι := ι) b).smul σ x =
      permCompatibleEquiv (ι := ι) b σ x := rfl

end Coherence

section Functoriality

variable {A : Type uA} {B : Type uB} [Group A] [AddCommGroup B]
variable {A' : Type uA'} {B' : Type uB'} [Group A'] [AddCommGroup B']
variable {A'' : Type uA''} {B'' : Type uB''} [Group A''] [AddCommGroup B'']
variable {ι : Type uι} [Fintype ι] [LinearOrder ι]

/-- Morphism between skew bicharacters. -/
structure SkewBicharacter.Hom
    (b : SkewBicharacter A B) (b' : SkewBicharacter A' B') where
  source : A →* A'
  target : B →+ B'
  map_eval : ∀ x y : A,
    target (b.eval x y) = b'.eval (source x) (source y)

namespace SkewBicharacter.Hom

variable {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
  {b'' : SkewBicharacter A'' B''}

def id (b : SkewBicharacter A B) : Hom b b where
  source := MonoidHom.id A
  target := AddMonoidHom.id B
  map_eval _ _ := rfl

@[simp]
theorem id_source (b : SkewBicharacter A B) : (id b).source = MonoidHom.id A :=
  rfl

@[simp]
theorem id_target (b : SkewBicharacter A B) : (id b).target = AddMonoidHom.id B :=
  rfl

def comp {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    {b'' : SkewBicharacter A'' B''}
    (f : Hom b b') (g : Hom b' b'') : Hom b b'' where
  source := g.source.comp f.source
  target := g.target.comp f.target
  map_eval x y := by
    calc (g.target.comp f.target) (b.eval x y)
        = g.target (f.target (b.eval x y)) := rfl
      _ = g.target (b'.eval (f.source x) (f.source y)) := by
          rw [f.map_eval]
      _ = b''.eval (g.source (f.source x)) (g.source (f.source y)) := by
          rw [g.map_eval]
      _ = b''.eval ((g.source.comp f.source) x)
            ((g.source.comp f.source) y) := by
          simp [MonoidHom.comp_apply]

@[simp]
theorem comp_source {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    {b'' : SkewBicharacter A'' B''}
    (f : Hom b b') (g : Hom b' b'') :
    (comp f g).source = g.source.comp f.source :=
  rfl

@[simp]
theorem comp_target {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    {b'' : SkewBicharacter A'' B''}
    (f : Hom b b') (g : Hom b' b'') :
    (comp f g).target = g.target.comp f.target :=
  rfl

theorem ext {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    {f g : Hom b b'} (h_source : f.source = g.source)
    (h_target : f.target = g.target) : f = g := by
  cases f with
  | mk source1 target1 map_eval1 =>
    cases g with
    | mk source2 target2 map_eval2 =>
      simp only at h_source h_target
      subst h_source
      subst h_target
      rfl

@[simp]
theorem id_comp {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (f : Hom b b') : comp (id b) f = f := by
  apply ext
  · simp [id_source, comp_source]
  · simp [id_target, comp_target]

@[simp]
theorem comp_id {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (f : Hom b b') : comp f (id b') = f := by
  apply ext
  · simp [id_source, comp_source]
  · simp [id_target, comp_target]

theorem comp_assoc {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    {b'' : SkewBicharacter A'' B''} {A3 : Type uA3} {B3 : Type uB3}
    [Group A3] [AddCommGroup B3] {b3 : SkewBicharacter A3 B3}
    (f : Hom b b') (g : Hom b' b'') (h : Hom b'' b3) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  · simp [comp_source, MonoidHom.comp_assoc]
  · simp [comp_target, AddMonoidHom.comp_assoc]

end SkewBicharacter.Hom

theorem lowerSum_naturality
    {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') (u v : ι → A) :
    φ.target (lowerSum (ι := ι) b u v) =
      lowerSum (ι := ι) b' (mapTuple φ.source u)
        (mapTuple φ.source v) := by
  unfold lowerSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact φ.map_eval (u i) (v j)

theorem inversionSum_naturality
    {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') (σ : Equiv.Perm ι)
    (u : ι → A) :
    φ.target (inversionSum (ι := ι) b σ u) =
      inversionSum (ι := ι) b' σ (mapTuple φ.source u) := by
  unfold inversionSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact φ.map_eval (u i) (u j)

theorem mapTuple_permute_comm
    {A : Type uA} {A' : Type uA'} [Monoid A] [Monoid A']
    {ι : Type uι}
    (f : A →* A') (σ : Equiv.Perm ι) (u : ι → A) :
    mapTuple f (permute σ u) = permute σ (mapTuple f u) :=
  permute_mapTuple_comm f σ u

def extensionHomOfHom {b : SkewBicharacter A B}
    {b' : SkewBicharacter A' B'} (φ : SkewBicharacter.Hom b b') :
    NormalizedCocycleExtension.CompatibleMap
      (lowerNormalizedCocycle (ι := ι) b)
      (lowerNormalizedCocycle (ι := ι) b') where
  f := mapTupleHom (ι := ι) φ.source
  g := AddMonoidHom.toMultiplicative φ.target
  q := fun _ => 1
  q_one := rfl
  compat := by
    intro x y
    simp only [mul_one, one_mul]
    have h :=
      lowerSum_naturality (ι := ι) (b := b) (b' := b') φ x y
    change (AddMonoidHom.toMultiplicative φ.target)
        (lowerCocycleAll (ι := ι) b x y) =
      lowerCocycleAll (ι := ι) b' (mapTuple φ.source x)
        (mapTuple φ.source y)
    unfold lowerCocycleAll lowerAddCocycle
    simp [h]

def extensionHom {b : SkewBicharacter A B}
    {b' : SkewBicharacter A' B'} (φ : SkewBicharacter.Hom b b') :
    Extension (A := A) (B := B) b ι →*
      Extension (A := A') (B := B') b' ι :=
  (extensionHomOfHom (ι := ι) φ).toHom

@[simp]
theorem extensionHom_base {b : SkewBicharacter A B}
    {b' : SkewBicharacter A' B'} (φ : SkewBicharacter.Hom b b')
    (x : Extension (A := A) (B := B) b ι) :
    (extensionHom (ι := ι) φ x).base = mapTuple φ.source x.base :=
  rfl

theorem extensionHom_coeff {b : SkewBicharacter A B}
    {b' : SkewBicharacter A' B'} (φ : SkewBicharacter.Hom b b')
    (x : Extension (A := A) (B := B) b ι) :
    (extensionHom (ι := ι) φ x).coeff =
      (AddMonoidHom.toMultiplicative φ.target) x.coeff := by
  simp [extensionHom, extensionHomOfHom,
    NormalizedCocycleExtension.CompatibleMap.toHom_coeff]

theorem perm_naturality_comm
    {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') (σ : Equiv.Perm ι) :
    (permCompatibleMap (ι := ι) b' σ).toHom.comp
        (extensionHom (ι := ι) φ) =
      (extensionHom (ι := ι) φ).comp
        (permCompatibleMap (ι := ι) b σ).toHom := by
  apply MonoidHom.ext
  intro x
  apply NormalizedCocycleExtension.Extension.ext
  · simp [permCompatibleMap, permuteHom_apply, permute_mapTuple_comm]
  · have h_inv :=
      inversionSum_naturality (ι := ι) (b := b) (b' := b') φ σ x.base
    have h_left :
        ((permCompatibleMap (ι := ι) b' σ).toHom
            ((extensionHom (ι := ι) φ) x)).coeff =
          (AddMonoidHom.toMultiplicative φ.target) x.coeff *
            Multiplicative.ofAdd
              (inversionSum (ι := ι) b' σ
                (mapTuple φ.source x.base)) := by
      calc ((permCompatibleMap (ι := ι) b' σ).toHom
              ((extensionHom (ι := ι) φ) x)).coeff
          = ((extensionHom (ι := ι) φ) x).coeff *
              Multiplicative.ofAdd
                (inversionSum (ι := ι) b' σ
                  ((extensionHom (ι := ι) φ) x).base) := by
            simp [permCompatibleMap,
              NormalizedCocycleExtension.CompatibleMap.toHom_coeff]
        _ = (AddMonoidHom.toMultiplicative φ.target) x.coeff *
              Multiplicative.ofAdd
                (inversionSum (ι := ι) b' σ
                  (mapTuple φ.source x.base)) := by
            rw [extensionHom_coeff, extensionHom_base]
    have h_right :
        ((extensionHom (ι := ι) φ)
            ((permCompatibleMap (ι := ι) b σ).toHom x)).coeff =
          (AddMonoidHom.toMultiplicative φ.target) x.coeff *
            Multiplicative.ofAdd
              (φ.target (inversionSum (ι := ι) b σ x.base)) := by
      calc ((extensionHom (ι := ι) φ)
              ((permCompatibleMap (ι := ι) b σ).toHom x)).coeff
          = (AddMonoidHom.toMultiplicative φ.target)
              (((permCompatibleMap (ι := ι) b σ).toHom x).coeff) := by
            rw [extensionHom_coeff]
        _ = (AddMonoidHom.toMultiplicative φ.target)
              (x.coeff *
                Multiplicative.ofAdd
                  (inversionSum (ι := ι) b σ x.base)) := by
            rw [NormalizedCocycleExtension.CompatibleMap.toHom_coeff]
            rfl
        _ = (AddMonoidHom.toMultiplicative φ.target) x.coeff *
              (AddMonoidHom.toMultiplicative φ.target)
                (Multiplicative.ofAdd
                  (inversionSum (ι := ι) b σ x.base)) := by
            rw [map_mul]
        _ = (AddMonoidHom.toMultiplicative φ.target) x.coeff *
              Multiplicative.ofAdd
                (φ.target (inversionSum (ι := ι) b σ x.base)) := rfl
    simp only [MonoidHom.comp_apply]
    rw [h_left, h_right, h_inv]

theorem extensionHom_permCompatibleHom
    {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') (σ : Equiv.Perm ι)
    (x : Extension (A := A) (B := B) b ι) :
    extensionHom (ι := ι) φ
        (permCompatibleHom (ι := ι) b σ x) =
      permCompatibleHom (ι := ι) b' σ
        (extensionHom (ι := ι) φ x) := by
  have h := perm_naturality_comm (ι := ι) (b := b) (b' := b') φ σ
  have h2 :=
    congrArg (fun f : Extension (A := A) (B := B) b ι → Extension (A := A')
            (B := B') b' ι => f x)
      (congrArg DFunLike.coe h)
  simpa [MonoidHom.comp_apply, permCompatibleHom] using h2.symm

theorem extensionHom_permCompatibleEquiv
    {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') (σ : Equiv.Perm ι)
    (x : Extension (A := A) (B := B) b ι) :
    extensionHom (ι := ι) φ
        (permCompatibleEquiv (ι := ι) b σ x) =
      permCompatibleEquiv (ι := ι) b' σ
        (extensionHom (ι := ι) φ x) := by
  simp only [permCompatibleEquiv_apply,
    extensionHom_permCompatibleHom]

theorem extensionHom_perm_smul
    {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b') (σ : Equiv.Perm ι)
    (x : Extension (A := A) (B := B) b ι) :
    extensionHom (ι := ι) φ
        ((permMulAction (ι := ι) b).smul σ x) =
      (permMulAction (ι := ι) b').smul σ
        (extensionHom (ι := ι) φ x) := by
  simp only [permMulAction_smul_def,
    extensionHom_permCompatibleHom]

@[simp]
theorem extensionHom_id (b : SkewBicharacter A B) :
    extensionHom (SkewBicharacter.Hom.id b) =
      MonoidHom.id (Extension b ι) := by
  apply MonoidHom.ext
  intro x
  apply Extension.ext
  · simp only [extensionHom_base, SkewBicharacter.Hom.id_source]
    funext i
    simp [mapTuple_apply, MonoidHom.id_apply]
  · simp [extensionHom_coeff, SkewBicharacter.Hom.id_target,
      AddMonoidHom.toMultiplicative_id]

theorem extensionHom_comp {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'}
    {b'' : SkewBicharacter A'' B''}
    (f : SkewBicharacter.Hom b b') (g : SkewBicharacter.Hom b' b'') :
    extensionHom (SkewBicharacter.Hom.comp f g) =
      (extensionHom (ι := ι) g).comp (extensionHom (ι := ι) f) := by
  apply MonoidHom.ext
  intro x
  apply Extension.ext
  · simp only [extensionHom_base, SkewBicharacter.Hom.comp_source]
    funext i
    simp [mapTuple_apply, MonoidHom.comp_apply]
  · simp [extensionHom_coeff, SkewBicharacter.Hom.comp_target]

end Functoriality

end PermutationBilinearCocycle

end
