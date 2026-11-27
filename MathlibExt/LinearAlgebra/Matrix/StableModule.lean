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

public import MathlibExt.LinearAlgebra.Matrix.ZeroExtension
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Stable modules of finitely supported matrices

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. The k-module S is linearly equivalent to (ℕ × ℕ) →₀ A. Every element has a
finite matrix representative, and its coordinates vanish outside some finite square. Each
finite-stage inclusion is injective, including the size-zero stage.
-/

@[expose] public section

noncomputable section

namespace Matrix

universe u v

variable (k : Type u) [Semiring k] (A : Type v) [AddCommMonoid A] [Module k A]

local instance : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) h) :=
  zeroExtendLinear_directedSystem (k := k) (A := A)

/-- **The stable coefficient module.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. This defines the stable k-module of coefficient matrices; its coordinate
realization is the space of finitely supported functions ℕ × ℕ → A.
-/
abbrev StableModule : Type v :=
  letI : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
      (fun _ _ h => zeroExtendLinear (k := k) h) :=
    zeroExtendLinear_directedSystem (k := k) (A := A)
  DirectLimit (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) h)

namespace StableModule

/-- **Inclusion of a finite coefficient matrix.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. For every n, the k-linear inclusion iₙ : Mat(n,n;A) → S takes a matrix to
its colimit class. One has iₘ(zeroExtend B) = iₙ(B) for n ≤ m.
-/
def ofFinite (n : ℕ) : Matrix (Fin n) (Fin n) A →ₗ[k] StableModule k A :=
  DirectLimit.Module.of k ℕ (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) h) n

@[simp]
theorem ofFinite_zeroExtend {n m : ℕ} (h : n ≤ m) (B : Matrix (Fin n) (Fin n) A) :
    ofFinite k A m (zeroExtend h B) = ofFinite k A n B :=
  DirectLimit.Module.of_f (hij := h)

/-- **Finite matrix representatives of stable elements.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. For every x ∈ S there exist n and B ∈ Mat(n,n;A) such that x = iₙ(B), where
iₙ is the finite-stage inclusion.
-/
theorem exists_ofFinite (x : StableModule k A) :
    ∃ (n : ℕ) (B : Matrix (Fin n) (Fin n) A), x = ofFinite k A n B :=
  DirectLimit.exists_eq_mk (f := fun _ _ h => zeroExtendLinear (k := k) (A := A) h) x

/-- **Positive finite matrix representatives.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. For every x ∈ S there exist n ≥ 0 and B ∈ Mat(n+1,n+1;A) such that x =
iₙ₊₁(B). This includes elements represented initially by a size-zero matrix.
-/
theorem exists_positive_ofFinite (x : StableModule k A) :
    ∃ (n : ℕ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) A), x = ofFinite k A (n + 1) B := by
  obtain ⟨n, B, rfl⟩ := exists_ofFinite k A x
  exact ⟨n, zeroExtend (Nat.le_succ n) B, (ofFinite_zeroExtend k A (Nat.le_succ n) B).symm⟩

/-- **Extending finite matrix entries by zero.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. For B ∈
Mat(n,n;A), define its natural-number entries E(B)ᵢⱼ = Bᵢⱼ when i,j < n and E(B)ᵢⱼ = 0
otherwise. The formula applies also at n = 0.
-/
def finiteEntries {n : ℕ} (B : Matrix (Fin n) (Fin n) A) : Matrix ℕ ℕ A :=
  Matrix.of fun i j => if hi : i < n then
    if hj : j < n then B ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

theorem finiteEntries_zeroExtend {n m : ℕ} (h : n ≤ m)
    (B : Matrix (Fin n) (Fin n) A) : finiteEntries A (zeroExtend h B) = finiteEntries A B := by
  ext i j
  by_cases hi : i < n
  · have him : i < m := hi.trans_le h
    by_cases hj : j < n
    · have hjm : j < m := hj.trans_le h
      simp only [finiteEntries, Matrix.of_apply, zeroExtend_apply, hi, hj, him, hjm,
        ↓reduceDIte]
    · by_cases hjm : j < m <;>
        simp only [finiteEntries, Matrix.of_apply, zeroExtend_apply, hi, hj, him, hjm,
          ↓reduceDIte]
  · by_cases him : i < m <;> by_cases hjm : j < m <;>
      simp only [finiteEntries, Matrix.of_apply, zeroExtend_apply, hi, him, hjm, ↓reduceDIte]

/-- **Entries of a stable coefficient matrix.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. The natural-number matrix E(x) of x ∈ S is specified by E(iₙ(B))ᵢⱼ = Bᵢⱼ
for i,j < n and zero otherwise. Extending a representative by zero leaves these entries
unchanged.
-/
def entries : StableModule k A → Matrix ℕ ℕ A :=
  DirectLimit.lift (fun _ _ h => zeroExtendLinear (k := k) (A := A) h)
    (fun _ B => finiteEntries A B)
    (fun _ _ h B => (finiteEntries_zeroExtend A h B).symm)

@[simp]
theorem entries_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) (i j : ℕ) :
    entries k A (ofFinite k A n B) i j =
      if hi : i < n then if hj : j < n then B ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := rfl

theorem entries_ofFinite_fin (n : ℕ) (B : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    entries k A (ofFinite k A n B) i.val j.val = B i j := by
  simp only [entries_ofFinite, dite_eq_left i.is_lt, dite_eq_left j.is_lt]

/-- **Faithfulness of stable matrix entries.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. For E(x) the zero-extended natural-number matrix of x, equality E(x) = E(y)
implies x = y.
-/
theorem entries_injective : Function.Injective (entries k A) := by
  apply DirectLimit.lift_injective
  intro n B C h
  ext i j
  have he := congrArg (fun D : Matrix ℕ ℕ A => D i.val j.val) h
  simpa only [finiteEntries, Matrix.of_apply, dite_eq_left i.is_lt, dite_eq_left j.is_lt] using he

/-- **Injectivity of finite coefficient inclusions.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. For every n, the finite-stage map iₙ : Mat(n,n;A) → S is injective.
-/
theorem ofFinite_injective (n : ℕ) : Function.Injective (ofFinite k A n) := by
  intro B C h
  ext i j
  simpa only [entries_ofFinite_fin] using
    congrArg (fun x : StableModule k A => entries k A x i.val j.val) h

/-- **A finite square contains the support.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. For every x ∈ S there is n such that its entry E(x)ᵢⱼ vanishes whenever n ≤
i or n ≤ j.
-/
theorem entries_bounded (x : StableModule k A) :
    ∃ n, ∀ i j : ℕ, n ≤ i ∨ n ≤ j → entries k A x i j = 0 := by
  obtain ⟨n, B, rfl⟩ := exists_ofFinite k A x
  refine ⟨n, fun i j h => ?_⟩
  rcases h with hi | hj
  · rw [entries_ofFinite, dite_eq_right (Nat.not_lt.mpr hi)]
  · by_cases hi : i < n <;>
      simp only [entries_ofFinite, hi, ↓reduceDIte, dite_eq_right (Nat.not_lt.mpr hj)]

/-- **Finite support of stable matrix entries.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. For every x ∈ S, the support of the function (i,j) ↦ E(x)ᵢⱼ on ℕ × ℕ is
finite.
-/
theorem entries_finiteSupport (x : StableModule k A) :
    (Function.support (fun p : ℕ × ℕ => entries k A x p.1 p.2)).Finite := by
  obtain ⟨n, hn⟩ := entries_bounded k A x
  apply ((Finset.range n).product (Finset.range n)).finite_toSet.subset
  intro p hp
  have hrow : p.1 < n := by
    by_contra h
    exact hp (hn p.1 p.2 (Or.inl (Nat.le_of_not_gt h)))
  have hcol : p.2 < n := by
    by_contra h
    exact hp (hn p.1 p.2 (Or.inr (Nat.le_of_not_gt h)))
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hrow, Finset.mem_range.mpr hcol⟩

/-- **The finite-support coordinates of a stable matrix.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. Define F(x) ∈ (ℕ × ℕ) →₀ A by F(x)(i,j) = E(x)ᵢⱼ, the zero-extended entries
of a finite matrix representative.
-/
def toFinsupp (x : StableModule k A) : (ℕ × ℕ) →₀ A :=
  Finsupp.ofSupportFinite (fun p => entries k A x p.1 p.2) (entries_finiteSupport k A x)

@[simp]
theorem toFinsupp_apply (x : StableModule k A) (p : ℕ × ℕ) :
    toFinsupp k A x p = entries k A x p.1 p.2 := rfl

theorem toFinsupp_injective : Function.Injective (toFinsupp k A) := by
  intro x y h
  apply entries_injective k A
  ext i j
  exact congrArg (fun f : (ℕ × ℕ) →₀ A => f (i, j)) h

/-- **Every finitely supported matrix has a finite representative.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. Every f ∈ (ℕ × ℕ) →₀ A equals the entry function F(x) of some x ∈ S.
-/
theorem toFinsupp_surjective : Function.Surjective (toFinsupp k A) := by
  intro f
  let n := f.support.sup (fun p => max p.1 p.2) + 1
  let B : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => f (i.val, j.val)
  refine ⟨ofFinite k A n B, ?_⟩
  ext p
  change entries k A (ofFinite k A n B) p.1 p.2 = f p
  rw [entries_ofFinite]
  by_cases hi : p.1 < n
  · by_cases hj : p.2 < n
    · rw [dite_eq_left hi, dite_eq_left hj]
      rfl
    · rw [dite_eq_left hi, dite_eq_right hj]
      symm
      by_contra hp
      have hmem : p ∈ f.support := Finsupp.mem_support_iff.mpr hp
      have hsup := Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hmem
      have hmax := Nat.le_max_right p.1 p.2
      have hj' : p.2 < n := Nat.lt_succ_of_le (hmax.trans hsup)
      exact hj hj'
  · rw [dite_eq_right hi]
    symm
    by_contra hp
    have hmem : p ∈ f.support := Finsupp.mem_support_iff.mpr hp
    have hsup := Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hmem
    have hmax := Nat.le_max_left p.1 p.2
    have hi' : p.1 < n := Nat.lt_succ_of_le (hmax.trans hsup)
    exact hi hi'

/-- **The linear map to finite-support coordinates.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. The coordinate map F : S → (ℕ × ℕ) →₀ A, F(x)(i,j) = E(x)ᵢⱼ, is k-linear.
-/
def toFinsuppLinear : StableModule k A →ₗ[k] (ℕ × ℕ) →₀ A where
  toFun := toFinsupp k A
  map_add' x y := by
    refine DirectLimit.induction₂ _ (fun n B C => ?_) x y
    change toFinsupp k A (ofFinite k A n B + ofFinite k A n C) =
      toFinsupp k A (ofFinite k A n B) + toFinsupp k A (ofFinite k A n C)
    rw [← map_add]
    ext p
    by_cases hi : p.1 < n <;> by_cases hj : p.2 < n <;>
      simp only [toFinsupp_apply, entries_ofFinite, hi, hj, ↓reduceDIte,
        Finsupp.add_apply, Matrix.add_apply, zero_add]
  map_smul' c x := by
    refine DirectLimit.induction _ (fun n B => ?_) x
    change toFinsupp k A (c • ofFinite k A n B) = c • toFinsupp k A (ofFinite k A n B)
    rw [← map_smul]
    ext p
    by_cases hi : p.1 < n <;> by_cases hj : p.2 < n <;>
      simp only [toFinsupp_apply, entries_ofFinite, hi, hj, ↓reduceDIte,
        Finsupp.smul_apply, Matrix.smul_apply, smul_zero]

/-- **Stable matrices and finite-support functions.**

Let k be a semiring and A an additive commutative monoid with a k-module structure. Write S =
colimₙ Mat(n,n;A), with transition maps extending each finite matrix by zero outside its
upper-left square. The map x ↦ ((i,j) ↦ E(x)ᵢⱼ) gives a k-linear equivalence S ≃ (ℕ × ℕ) →₀ A.
-/
def finsuppEquiv : StableModule k A ≃ₗ[k] (ℕ × ℕ) →₀ A :=
  { toFinsuppLinear k A,
    Equiv.ofBijective (toFinsupp k A)
      ⟨toFinsupp_injective k A, toFinsupp_surjective k A⟩ with }

@[simp]
theorem finsuppEquiv_apply (x : StableModule k A) (p : ℕ × ℕ) :
    finsuppEquiv k A x p = entries k A x p.1 p.2 := rfl

end StableModule

end Matrix
