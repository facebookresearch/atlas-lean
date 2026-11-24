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

public import MathlibExt.GroupTheory.PermutationBilinearSchurTitsCocycle
public import MathlibExt.GroupTheory.NormalizedCocycleExtension
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Stabilization of Tits monomial extensions

Appending a unit coordinate and extending permutations by a fixed point define
compatible stabilization maps for the Tits monomial extensions. The extension
homomorphism is injective and natural under compatible maps of bicharacters.
-/

@[expose] public section

open PermutationBilinearCocycle
open PermutationBilinearTitsAction
open PermutationBilinearSchurTitsCocycle

universe uA uB

namespace PermutationBilinearTitsStabilization

variable {A : Type uA} [CommGroup A]
variable {B : Type uB} [AddCommGroup B]
variable {b : SkewBicharacter A B}
variable {n : ℕ}

section TupleSucc

/-- Tuple successor appending `1` at the last coordinate. -/
def tupleSucc {n : ℕ} {A : Type uA} [Group A] (u : Fin n → A) : Fin (n + 1) → A :=
  @Fin.snoc n (fun _ => A) u 1

@[simp]
theorem tupleSucc_apply_castSucc {n : ℕ} {A : Type uA} [Group A] (u : Fin n → A)
    (i : Fin n) :
    tupleSucc (n := n) u (Fin.castSucc i) = u i := by
  simp [tupleSucc]

@[simp]
theorem tupleSucc_apply_last {n : ℕ} {A : Type uA} [Group A] (u : Fin n → A) :
    tupleSucc (n := n) u (Fin.last n) = 1 := by
  simp [tupleSucc]

@[simp]
theorem tupleSucc_comp_castSucc {n : ℕ} {A : Type uA} [Group A] (u : Fin n → A) :
    (tupleSucc (n := n) u) ∘ Fin.castSucc = u := by
  ext i
  simp [tupleSucc]

def tupleSuccHom {n : ℕ} {A : Type uA} [CommGroup A] : (Fin n → A) →* (Fin (n + 1) → A) where
  toFun u := tupleSucc u
  map_one' := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [tupleSucc]
    · simp [tupleSucc_apply_castSucc]
  map_mul' u v := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [tupleSucc_apply_last]
    · simp [tupleSucc_apply_castSucc, Pi.mul_apply]

@[simp]
theorem tupleSuccHom_apply {n : ℕ} {A : Type uA} [CommGroup A] (u : Fin n → A) :
    tupleSuccHom (n := n) (A := A) u = tupleSucc u :=
  rfl

@[simp]
theorem tupleSuccHom_apply_castSucc {n : ℕ} {A : Type uA} [CommGroup A] (u : Fin n → A)
    (i : Fin n) :
    (tupleSuccHom (n := n) (A := A) u) (Fin.castSucc i) = u i :=
  tupleSucc_apply_castSucc u i

@[simp]
theorem tupleSuccHom_apply_last {n : ℕ} {A : Type uA} [CommGroup A] (u : Fin n → A) :
    (tupleSuccHom (n := n) (A := A) u) (Fin.last n) = 1 :=
  tupleSucc_apply_last u

theorem tupleSuccHom_injective {n : ℕ} {A : Type uA} [CommGroup A] :
    Function.Injective (tupleSuccHom (n := n) (A := A)) := by
  intro u v h
  ext i
  have hi : (tupleSuccHom (n := n) (A := A) u) (Fin.castSucc i) =
      (tupleSuccHom (n := n) (A := A) v) (Fin.castSucc i) := by rw [h]
  simpa using hi

theorem tupleSucc_mapTuple_comm {n : ℕ} {A : Type uA} {A' : Type*} [CommGroup A] [CommGroup A']
    (f : A →* A') (u : Fin n → A) :
    mapTuple (f := f) (tupleSucc (n := n) u) = tupleSucc (n := n) (mapTuple (f := f) u) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [tupleSucc_apply_last, mapTuple_apply, f.map_one]
  · simp [tupleSucc_apply_castSucc, mapTuple_apply]

theorem tupleSuccHom_mapTuple_comm {n : ℕ} {A : Type uA} {A' : Type*} [CommGroup A] [CommGroup A']
    (f : A →* A') :
    (mapTupleHom (ι := Fin (n + 1)) f).comp (tupleSuccHom (n := n) (A := A)) =
      (tupleSuccHom (n := n) (A := A')).comp (mapTupleHom (ι := Fin n) f) := by
  apply MonoidHom.ext
  intro u
  simp [tupleSucc_mapTuple_comm]

theorem tupleProd_tupleSucc {n : ℕ} {A : Type uA} [CommGroup A] (u : Fin n → A) :
    tupleProd (n := n + 1) (tupleSucc (n := n) u) = tupleProd (n := n) u := by
  simp [tupleProd, tupleSucc, Fin.prod_snoc]

end TupleSucc

section PermSucc

/-- Equivalence between `Fin n` and the subtype `{x : Fin (n+1) // x ≠ last n}` via `castSucc`. -/
def finSuccSubtypeEquiv (n : ℕ) : Fin n ≃ {x : Fin (n + 1) // x ≠ Fin.last n} where
  toFun i := ⟨Fin.castSucc i, ne_of_lt (Fin.castSucc_lt_last i)⟩
  invFun x := Fin.castPred x.1 x.2
  left_inv i := by simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- Permutation successor fixing the last coordinate. -/
def permSuccHom {n : ℕ} : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.extendDomainHom (finSuccSubtypeEquiv n)

@[simp]
theorem permSuccHom_apply_castSucc {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (permSuccHom (n := n) σ) (Fin.castSucc i) = Fin.castSucc (σ i) := by
  have h_eq : ((finSuccSubtypeEquiv n) i).val = Fin.castSucc i := rfl
  have h_img : ((finSuccSubtypeEquiv n) (σ i)).val = Fin.castSucc (σ i) := rfl
  have h_perm : (permSuccHom (n := n) σ) ((finSuccSubtypeEquiv n) i).val =
      ((finSuccSubtypeEquiv n) (σ i)).val := by
    simp [permSuccHom, Equiv.Perm.extendDomainHom, Equiv.Perm.extendDomain_apply_image]
  simpa [h_eq, h_img] using h_perm

@[simp]
theorem permSuccHom_apply_last {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permSuccHom (n := n) σ) (Fin.last n) = Fin.last n := by
  have h_not : ¬ ((Fin.last n : Fin (n + 1)) ≠ Fin.last n) := by simp
  exact Equiv.Perm.extendDomain_apply_not_subtype (f := finSuccSubtypeEquiv n) (e := σ) h_not

theorem permSuccHom_injective {n : ℕ} : Function.Injective (permSuccHom (n := n)) :=
  Equiv.Perm.extendDomainHom_injective (finSuccSubtypeEquiv n)

@[simp]
theorem permSuccHom_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permSuccHom (n := n) σ)⁻¹ = permSuccHom (n := n) σ⁻¹ := by
  simp [permSuccHom]

@[simp]
theorem permSuccHom_one {n : ℕ} : permSuccHom (n := n) (1 : Equiv.Perm (Fin n)) = 1 := by
  simp [permSuccHom]

theorem permSuccHom_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permSuccHom (n := n) (σ * τ) = permSuccHom (n := n) σ * permSuccHom (n := n) τ := by
  simp [permSuccHom]

theorem permSuccHom_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (permSuccHom (n := n) σ) = Equiv.Perm.sign σ := by
  simp [permSuccHom, Equiv.Perm.sign_extendDomain]

theorem permSuccHom_parityUnit {n : ℕ} {A : Type uA} [CommGroup A] (eps : A)
    (σ : Equiv.Perm (Fin n)) :
    parityUnit (n := n + 1) eps (permSuccHom (n := n) σ) = parityUnit (n := n) eps σ := by
  unfold parityUnit
  rw [permSuccHom_sign]

theorem permute_permSucc_tupleSucc {n : ℕ} {A : Type uA} [CommGroup A]
    (σ : Equiv.Perm (Fin n)) (u : Fin n → A) :
    permute (permSuccHom (n := n) σ) (tupleSucc (n := n) u) =
      tupleSucc (n := n) (permute σ u) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have h_inv_last : (permSuccHom (n := n) σ)⁻¹ (Fin.last n) = Fin.last n := by
      have h1 : (permSuccHom (n := n) σ)⁻¹ = permSuccHom (n := n) σ⁻¹ := permSuccHom_inv σ
      rw [h1, permSuccHom_apply_last]
    simp only [permute_apply, h_inv_last, tupleSucc_apply_last]
  · have h_inv : (permSuccHom (n := n) σ)⁻¹ (Fin.castSucc j) = Fin.castSucc (σ⁻¹ j) := by
      have h_eq : (permSuccHom (n := n) σ⁻¹) (Fin.castSucc j) = Fin.castSucc (σ⁻¹ j) :=
        permSuccHom_apply_castSucc (σ⁻¹) j
      have h_inv_eq : (permSuccHom (n := n) σ)⁻¹ = permSuccHom (n := n) σ⁻¹ :=
        permSuccHom_inv σ
      rw [h_inv_eq, h_eq]
    simp only [permute_apply, h_inv, tupleSucc_apply_castSucc]

end PermSucc

section MonomialSucc

def monomialSuccHom {n : ℕ} {A : Type uA} [CommGroup A] :
    MonomialBase A (Fin n) →* MonomialBase A (Fin (n + 1)) :=
  SemidirectProduct.map (tupleSuccHom (n := n) (A := A)) (permSuccHom (n := n)) (by
    intro σ
    apply MonoidHom.ext
    intro u
    exact (permute_permSucc_tupleSucc σ u).symm)

@[simp]
theorem monomialSuccHom_left {n : ℕ} {A : Type uA} [CommGroup A]
    (x : MonomialBase A (Fin n)) :
    (monomialSuccHom (n := n) (A := A) x).left = tupleSuccHom (n := n) x.left :=
  rfl

@[simp]
theorem monomialSuccHom_right {n : ℕ} {A : Type uA} [CommGroup A]
    (x : MonomialBase A (Fin n)) :
    (monomialSuccHom (n := n) (A := A) x).right = permSuccHom (n := n) x.right :=
  rfl

theorem monomialSuccHom_injective {n : ℕ} {A : Type uA} [CommGroup A] :
    Function.Injective (monomialSuccHom (n := n) (A := A)) := by
  intro x y h
  have h_left : (monomialSuccHom (n := n) (A := A) x).left =
      (monomialSuccHom (n := n) (A := A) y).left := by rw [h]
  have h_right : (monomialSuccHom (n := n) (A := A) x).right =
      (monomialSuccHom (n := n) (A := A) y).right := by rw [h]
  simp only [monomialSuccHom_left, monomialSuccHom_right] at h_left h_right
  have hx_left : x.left = y.left := tupleSuccHom_injective h_left
  have hx_right : x.right = y.right := permSuccHom_injective h_right
  apply SemidirectProduct.ext
  · exact hx_left
  · exact hx_right

theorem monomialSuccHom_naturality {n : ℕ} {A : Type uA} {A' : Type*} [CommGroup A] [CommGroup A']
    (f : A →* A') :
    (monomialBaseHom (ι := Fin (n + 1)) f).comp (monomialSuccHom (n := n) (A := A)) =
      (monomialSuccHom (n := n) (A := A')).comp (monomialBaseHom (ι := Fin n) f) := by
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · simp [tupleSucc_mapTuple_comm]
  · rfl

theorem monomialSuccHom_skewNaturality {n : ℕ} {A : Type uA} {B : Type uB}
    {A' : Type*} {B' : Type*} [CommGroup A] [AddCommGroup B] [CommGroup A'] [AddCommGroup B']
    {b : SkewBicharacter A B} {b' : SkewBicharacter A' B'} (φ : SkewBicharacter.Hom b b')
    (x : MonomialBase A (Fin n)) :
    monomialBaseHom (ι := Fin (n + 1)) φ.source (monomialSuccHom x) =
      monomialSuccHom (monomialBaseHom (ι := Fin n) φ.source x) := by
  have h := monomialSuccHom_naturality (n := n) (f := φ.source)
  have hx :
      ((monomialBaseHom (ι := Fin (n + 1)) φ.source).comp
          (monomialSuccHom (n := n) (A := A))) x =
      ((monomialSuccHom (n := n) (A := A')).comp
          (monomialBaseHom (ι := Fin n) φ.source)) x := by
    rw [h]
  simpa using hx

end MonomialSucc

section Invariants

variable {A : Type uA} [CommGroup A]
variable {B : Type uB} [AddCommGroup B]
variable (b : SkewBicharacter A B) (eps : A)

private theorem filter_le_castSucc_eq {n : ℕ} (k : Fin n) :
    (Finset.univ.filter (fun j : Fin (n + 1) => j ≤ Fin.castSucc k)) =
      (Finset.univ.filter (fun j : Fin n => j ≤ k)).map
        ⟨Fin.castSucc, Fin.castSucc_injective n⟩ := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro h_le
    by_cases hj_last : j = Fin.last n
    · subst hj_last
      have h_lt : Fin.castSucc k < Fin.last n := Fin.castSucc_lt_last k
      have h_not_le : ¬ (Fin.last n ≤ Fin.castSucc k) := not_le_of_gt h_lt
      exact absurd h_le h_not_le
    · have hj_pred : j = Fin.castSucc (Fin.castPred j hj_last) := by
        rw [Fin.castSucc_castPred]
      obtain ⟨j', hj_eq⟩ : ∃ j' : Fin n, j = Fin.castSucc j' := ⟨Fin.castPred j hj_last, hj_pred⟩
      rw [hj_eq] at h_le ⊢
      exact ⟨j', (Fin.castSucc_le_castSucc_iff.mp h_le), rfl⟩
  · rintro ⟨j', hj', rfl⟩
    exact (Fin.castSucc_le_castSucc_iff.mpr hj')

private theorem filter_lt_castSucc_eq {n : ℕ} (k : Fin n) :
    (Finset.univ.filter (fun j : Fin (n + 1) => j < Fin.castSucc k)) =
      (Finset.univ.filter (fun j : Fin n => j < k)).map
        ⟨Fin.castSucc, Fin.castSucc_injective n⟩ := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro h_lt
    by_cases hj_last : j = Fin.last n
    · subst hj_last
      have h_lt2 : Fin.castSucc k < Fin.last n := Fin.castSucc_lt_last k
      exact absurd (lt_trans h_lt h_lt2) (lt_irrefl _)
    · have hj_pred : j = Fin.castSucc (Fin.castPred j hj_last) := by
        rw [Fin.castSucc_castPred]
      obtain ⟨j', hj_eq⟩ : ∃ j' : Fin n, j = Fin.castSucc j' := ⟨Fin.castPred j hj_last, hj_pred⟩
      rw [hj_eq] at h_lt ⊢
      exact ⟨j', (Fin.castSucc_lt_castSucc_iff.mp h_lt), rfl⟩
  · rintro ⟨j', hj', rfl⟩
    exact (Fin.castSucc_lt_castSucc_iff.mpr hj')

theorem lowerSum_tupleSucc {n : ℕ} {A : Type uA} {B : Type uB} [CommGroup A] [AddCommGroup B]
    (b : SkewBicharacter A B) (u v : Fin n → A) :
    lowerSum (ι := Fin (n + 1)) b (tupleSucc (n := n) u) (tupleSucc (n := n) v) =
      lowerSum (ι := Fin n) b u v := by
  unfold lowerSum
  rw [Fin.sum_univ_castSucc (fun i => ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
      b.eval (tupleSucc (n := n) u i) (tupleSucc (n := n) v j))]
  have h_last_zero : (∑ j ∈ Finset.univ.filter (fun j => j ≤ Fin.last n),
      b.eval (tupleSucc (n := n) u (Fin.last n)) (tupleSucc (n := n) v j)) = 0 := by
    have hu_last : tupleSucc (n := n) u (Fin.last n) = 1 := tupleSucc_apply_last u
    rw [hu_last]
    apply Finset.sum_eq_zero
    intro j _
    rw [SkewBicharacter.eval_one_left]
  rw [h_last_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  have hu : tupleSucc (n := n) u (Fin.castSucc k) = u k := tupleSucc_apply_castSucc u k
  rw [hu]
  have h_filter := filter_le_castSucc_eq (n := n) k
  calc (∑ j ∈ Finset.univ.filter (fun j => j ≤ Fin.castSucc k),
        b.eval (u k) (tupleSucc (n := n) v j))
      = ∑ j ∈ (Finset.univ.filter (fun j : Fin n => j ≤ k)).map
          ⟨Fin.castSucc, Fin.castSucc_injective n⟩,
          b.eval (u k) (tupleSucc (n := n) v j) := by rw [← h_filter]
    _ = ∑ j' ∈ Finset.univ.filter (fun j' : Fin n => j' ≤ k),
          b.eval (u k) (tupleSucc (n := n) v (Fin.castSucc j')) := by
        rw [Finset.sum_map]
        simp
    _ = ∑ j' ∈ Finset.univ.filter (fun j' : Fin n => j' ≤ k),
          b.eval (u k) (v j') := by
        apply Finset.sum_congr rfl
        intro j' _
        rw [tupleSucc_apply_castSucc]

theorem inversionSum_permSucc_tupleSucc {n : ℕ} {A : Type uA} {B : Type uB}
    [CommGroup A] [AddCommGroup B] (b : SkewBicharacter A B)
    (σ : Equiv.Perm (Fin n)) (u : Fin n → A) :
    inversionSum (ι := Fin (n + 1)) b (permSuccHom σ) (tupleSucc u) =
      inversionSum (ι := Fin n) b σ u := by
  let σ' := permSuccHom (n := n) σ
  let u' := tupleSucc (n := n) u
  unfold inversionSum
  rw [Fin.sum_univ_castSucc
      (fun i =>
        ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ σ' i > σ' j),
          b.eval (u' i) (u' j))]
  have h_last_zero :
      (∑ j ∈ Finset.univ.filter
          (fun j => Fin.last n < j ∧ σ' (Fin.last n) > σ' j),
        b.eval (u' (Fin.last n)) (u' j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    have h_lt : Fin.last n < j := hj'.1
    exact absurd h_lt (not_lt.mpr (Fin.le_last j))
  rw [h_last_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  have hu_k : u' (Fin.castSucc k) = u k := tupleSucc_apply_castSucc u k
  rw [hu_k]
  -- Show inner filter maps via castSucc
  have h_filter_eq :
      Finset.univ.filter
          (fun j : Fin (n + 1) =>
            Fin.castSucc k < j ∧ σ' (Fin.castSucc k) > σ' j) =
        (Finset.univ.filter (fun j : Fin n => k < j ∧ σ k > σ j)).map
          ⟨Fin.castSucc, Fin.castSucc_injective n⟩ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hj
      have hj1 := hj.1
      have hj2 := hj.2
      have h_not_last : j ≠ Fin.last n := by
        intro h_eq
        rw [h_eq] at hj2
        have h_perm_last : σ' (Fin.last n) = Fin.last n :=
          permSuccHom_apply_last σ
        rw [h_perm_last] at hj2
        have h_cast_lt_last : Fin.castSucc (σ k) < Fin.last n :=
          Fin.castSucc_lt_last (σ k)
        have h_perm_cast : σ' (Fin.castSucc k) = Fin.castSucc (σ k) :=
          permSuccHom_apply_castSucc σ k
        rw [h_perm_cast] at hj2
        exact absurd hj2 (not_lt.mpr (le_of_lt h_cast_lt_last))
      obtain ⟨j', rfl⟩ : ∃ j' : Fin n, j = Fin.castSucc j' := by
        refine ⟨Fin.castPred j h_not_last,
          (Fin.castSucc_castPred j h_not_last).symm⟩
      refine ⟨j', ?_, rfl⟩
      · have h_lt :
            Fin.castSucc k < Fin.castSucc j' ↔ k < j' := by
            simp [Fin.castSucc_lt_castSucc_iff]
        have h_gt :
            Fin.castSucc (σ k) > Fin.castSucc (σ j') ↔
              σ k > σ j' := by
            simp [Fin.castSucc_lt_castSucc_iff]
        have h_perm_k : σ' (Fin.castSucc k) = Fin.castSucc (σ k) :=
          permSuccHom_apply_castSucc σ k
        have h_perm_j : σ' (Fin.castSucc j') = Fin.castSucc (σ j') :=
          permSuccHom_apply_castSucc σ j'
        rw [h_perm_k, h_perm_j] at hj
        exact ⟨h_lt.mp hj.1, h_gt.mp hj.2⟩
    · rintro ⟨j', hj', rfl⟩
      have h_lt : k < j' := hj'.1
      have h_gt : σ k > σ j' := hj'.2
      have h_lt_cast : Fin.castSucc k < Fin.castSucc j' := by
        simpa [Fin.castSucc_lt_castSucc_iff] using h_lt
      have h_gt_cast : Fin.castSucc (σ k) > Fin.castSucc (σ j') := by
        simpa [Fin.castSucc_lt_castSucc_iff] using h_gt
      have h_perm_k : σ' (Fin.castSucc k) = Fin.castSucc (σ k) :=
        permSuccHom_apply_castSucc σ k
      have h_perm_j : σ' (Fin.castSucc j') = Fin.castSucc (σ j') :=
        permSuccHom_apply_castSucc σ j'
      rw [h_perm_k, h_perm_j]
      exact ⟨h_lt_cast, h_gt_cast⟩
  calc (∑ j ∈ Finset.univ.filter
          (fun j => Fin.castSucc k < j ∧ σ' (Fin.castSucc k) > σ' j),
        b.eval (u k) (u' j))
      = ∑ j ∈ (Finset.univ.filter
          (fun j : Fin n => k < j ∧ σ k > σ j)).map
          ⟨Fin.castSucc, Fin.castSucc_injective n⟩,
          b.eval (u k) (u' j) := by rw [← h_filter_eq]
    _ = ∑ j' ∈ Finset.univ.filter (fun j : Fin n => k < j ∧ σ k > σ j),
          b.eval (u k) (u' (Fin.castSucc j')) := by
        rw [Finset.sum_map]
        simp
    _ = ∑ j' ∈ Finset.univ.filter (fun j : Fin n => k < j ∧ σ k > σ j),
          b.eval (u k) (u j') := by
        apply Finset.sum_congr rfl
        intro j' _
        have hj : u' (Fin.castSucc j') = u j' :=
          tupleSucc_apply_castSucc (n := n) u j'
        rw [hj]

theorem orientAdd_permSucc_tupleSucc {n : ℕ} {A : Type uA} {B : Type uB}
    [CommGroup A] [AddCommGroup B] (b : SkewBicharacter A B) (eps : A)
    (σ : Equiv.Perm (Fin n)) (u : Fin n → A) :
    orientAdd (b := b) (n := n + 1) eps (permSuccHom σ) (tupleSucc u) =
      orientAdd (b := b) (n := n) eps σ u := by
  let σ' := permSuccHom (n := n) σ
  let u' := tupleSucc (n := n) u
  unfold orientAdd
  rw [Fin.sum_univ_castSucc
      (fun i => b.eval (orientUnit eps σ' i) (u' i))]
  have h_last_zero : b.eval (orientUnit eps σ' (Fin.last n)) (u' (Fin.last n)) = 0 := by
    have hu_last : u' (Fin.last n) = 1 := tupleSucc_apply_last (n := n) u
    rw [hu_last, SkewBicharacter.eval_one_right]
  rw [h_last_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  have hu : u' (Fin.castSucc k) = u k := tupleSucc_apply_castSucc (n := n) u k
  have h_orient :
      orientUnit (n := n + 1) eps σ' (Fin.castSucc k) =
        orientUnit (n := n) eps σ k := by
    unfold orientUnit indexParityUnit parityUnit
    have h_parity :
        (if Equiv.Perm.sign σ' = 1 then (1 : A) else eps) =
          if Equiv.Perm.sign σ = 1 then 1 else eps := by
        rw [permSuccHom_sign]
    rw [h_parity]
    have h_val_cast : (Fin.castSucc k).val = k.val := Fin.val_castSucc k
    have h_val_perm : (Fin.castSucc (σ k)).val = (σ k).val :=
      Fin.val_castSucc (σ k)
    have h_perm_cast : σ' (Fin.castSucc k) = Fin.castSucc (σ k) :=
      permSuccHom_apply_castSucc σ k
    have h_val_permSucc : (σ' (Fin.castSucc k)).val = (σ k).val := by
      rw [h_perm_cast, h_val_perm]
    rw [h_val_cast, h_val_permSucc]
  rw [hu, h_orient]

theorem titsAlphaAdd_tupleSucc {n : ℕ} {A : Type uA} {B : Type uB}
    [CommGroup A] [AddCommGroup B] (b : SkewBicharacter A B) (eps : A)
    (u v : Fin n → A) :
    titsAlphaAdd (n := n + 1) b eps (tupleSucc (n := n) u) (tupleSucc (n := n) v) =
      titsAlphaAdd (n := n) b eps u v := by
  unfold titsAlphaAdd
  rw [lowerSum_tupleSucc b u v, tupleProd_tupleSucc, tupleProd_tupleSucc]

theorem titsQAdd_permSucc_tupleSucc {n : ℕ} {A : Type uA} {B : Type uB}
    [CommGroup A] [AddCommGroup B] (b : SkewBicharacter A B) (eps : A)
    (σ : Equiv.Perm (Fin n)) (u : Fin n → A) :
    titsQAdd (n := n + 1) b eps (permSuccHom (n := n) σ) (tupleSucc (n := n) u) =
      titsQAdd (n := n) b eps σ u := by
  unfold titsQAdd
  rw [inversionSum_permSucc_tupleSucc b σ u, orientAdd_permSucc_tupleSucc b eps σ u]

end Invariants

section TitsCocycleSucc

variable {A : Type uA} [CommGroup A]
variable {B : Type uB} [AddCommGroup B]
variable (b : SkewBicharacter A B) (eps : A)

theorem titsMonomialAddCocycle_monomialSucc {n : ℕ}
    (x y : MonomialBase A (Fin n)) :
    titsMonomialAddCocycle (n := n + 1) b eps
        (monomialSuccHom (n := n) x) (monomialSuccHom (n := n) y) =
      titsMonomialAddCocycle (n := n) b eps x y := by
  simp only [titsMonomialAddCocycle, monomialSuccHom_left, monomialSuccHom_right]
  have h_perm : permute (permSuccHom (n := n) x.right) (tupleSuccHom (n := n) y.left) =
      tupleSuccHom (n := n) (permute x.right y.left) := by
    have h := permute_permSucc_tupleSucc (n := n) x.right y.left
    simpa [tupleSuccHom_apply] using h
  have h_alpha : titsAlphaAdd (n := n + 1) b eps (tupleSuccHom (n := n) x.left)
      (permute (permSuccHom (n := n) x.right) (tupleSuccHom (n := n) y.left)) =
      titsAlphaAdd (n := n) b eps x.left (permute x.right y.left) := by
    have h1 : permute (permSuccHom (n := n) x.right) (tupleSuccHom (n := n) y.left) =
        tupleSuccHom (n := n) (permute x.right y.left) := h_perm
    rw [h1]
    exact titsAlphaAdd_tupleSucc (b := b) (eps := eps) x.left (permute x.right y.left)
  have h_q : titsQAdd (n := n + 1) b eps (permSuccHom (n := n) x.right)
      (tupleSuccHom (n := n) y.left) =
      titsQAdd (n := n) b eps x.right y.left := by
    have h := titsQAdd_permSucc_tupleSucc (b := b) (eps := eps) (σ := x.right) (u := y.left)
    simpa [tupleSuccHom_apply] using h
  rw [h_alpha, h_q]

end TitsCocycleSucc

section CompatibleMapSucc

variable {A : Type uA} [CommGroup A]
variable {B : Type uB} [AddCommGroup B]
variable {b : SkewBicharacter A B} {eps : A} (heps : eps * eps = 1) {n : ℕ}

noncomputable def titsSuccCompatibleMap :
    NormalizedCocycleExtension.CompatibleMap
      (titsMonomialNormalizedCocycle (n := n) b eps heps)
      (titsMonomialNormalizedCocycle (n := n + 1) b eps heps) where
  f := monomialSuccHom (n := n) (A := A)
  g := MonoidHom.id (Multiplicative B)
  q := fun _ => 1
  q_one := rfl
  compat x y := by
    simp only [MonoidHom.id_apply, mul_one, one_mul]
    change Multiplicative.ofAdd (titsMonomialAddCocycle (n := n) b eps x y) =
      Multiplicative.ofAdd (titsMonomialAddCocycle (n := n + 1) b eps
        (monomialSuccHom x) (monomialSuccHom y))
    rw [titsMonomialAddCocycle_monomialSucc b eps x y]

noncomputable def titsSuccCompatibleHom :
    TitsMonomialExtension (n := n) b eps heps →*
      TitsMonomialExtension (n := n + 1) b eps heps :=
  (titsSuccCompatibleMap (n := n) heps).toHom

@[simp]
theorem titsSuccCompatibleHom_base (x : TitsMonomialExtension (n := n) b eps heps) :
    (titsSuccCompatibleHom (n := n) heps x).base = monomialSuccHom (n := n) x.base :=
  rfl

@[simp]
theorem titsSuccCompatibleHom_coeff (x : TitsMonomialExtension (n := n) b eps heps) :
    (titsSuccCompatibleHom (n := n) heps x).coeff = x.coeff := by
  simp [titsSuccCompatibleHom, titsSuccCompatibleMap]

theorem titsSuccCompatibleHom_injective :
    Function.Injective (titsSuccCompatibleHom (n := n) (b := b) (eps := eps) heps) := by
  intro x y h
  have h_base : (titsSuccCompatibleHom (n := n) heps x).base =
      (titsSuccCompatibleHom (n := n) heps y).base := by rw [h]
  have h_coeff : (titsSuccCompatibleHom (n := n) heps x).coeff =
      (titsSuccCompatibleHom (n := n) heps y).coeff := by rw [h]
  simp only [titsSuccCompatibleHom_base, titsSuccCompatibleHom_coeff] at h_base h_coeff
  have hx_base : x.base = y.base := monomialSuccHom_injective h_base
  have hx_coeff : x.coeff = y.coeff := h_coeff
  apply NormalizedCocycleExtension.Extension.ext hx_base hx_coeff

theorem titsSuccCompatibleHom_naturality {A' : Type*} {B' : Type*} [CommGroup A'] [AddCommGroup B']
    {b' : SkewBicharacter A' B'} (φ : SkewBicharacter.Hom b b')
    {eps' : A'} (heps' : eps' * eps' = 1) (hε : φ.source eps = eps')
    (x : TitsMonomialExtension (n := n) b eps heps) :
    titsMonomialCompatibleHom (n := n + 1) φ hε heps heps'
        (titsSuccCompatibleHom (n := n) heps x) =
      titsSuccCompatibleHom (n := n) heps'
        (titsMonomialCompatibleHom (n := n) φ hε heps heps' x) := by
  apply NormalizedCocycleExtension.Extension.ext
  · simp only [titsSuccCompatibleHom_base, titsMonomialCompatibleHom_base,
      monomialSuccHom_skewNaturality]
  · simp only [titsSuccCompatibleHom_coeff, titsMonomialCompatibleHom_coeff]

end CompatibleMapSucc

end PermutationBilinearTitsStabilization

end
