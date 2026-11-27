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
# Stable matrix modules

Let `k` be a semiring and `A` a `k`-semimodule. The direct limit of finite
square matrices under top-left zero extension is k-linearly equivalent to
finitely supported functions on `ℕ × ℕ`. The finite-stage inclusions are
injective, and every element is supported in a finite square.
-/

@[expose] public section

noncomputable section

namespace Matrix

universe u v

variable (k : Type u) [Semiring k] (A : Type v) [AddCommMonoid A] [Module k A]

local instance : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) h) :=
  zeroExtendLinear_directedSystem (k := k) (A := A)

/-- The direct limit of finite square matrix semimodules under top-left zero extension. -/
abbrev StableModule : Type v :=
  letI : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
      (fun _ _ h => zeroExtendLinear (k := k) h) :=
    zeroExtendLinear_directedSystem (k := k) (A := A)
  DirectLimit (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) h)

namespace StableModule

/-- The k-linear inclusion of a finite matrix stage into the stable matrix module. -/
def ofFinite (n : ℕ) : Matrix (Fin n) (Fin n) A →ₗ[k] StableModule k A :=
  DirectLimit.Module.of k ℕ (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) h) n

@[simp]
theorem ofFinite_zeroExtend {n m : ℕ} (h : n ≤ m) (B : Matrix (Fin n) (Fin n) A) :
    ofFinite k A m (zeroExtend h B) = ofFinite k A n B :=
  DirectLimit.Module.of_f (hij := h)

/-- Every stable matrix is represented in a finite matrix stage. -/
theorem exists_ofFinite (x : StableModule k A) :
    ∃ (n : ℕ) (B : Matrix (Fin n) (Fin n) A), x = ofFinite k A n B :=
  DirectLimit.exists_eq_mk (f := fun _ _ h => zeroExtendLinear (k := k) (A := A) h) x

/-- Every stable matrix is represented in a matrix stage of positive size. -/
theorem exists_positive_ofFinite (x : StableModule k A) :
    ∃ (n : ℕ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) A), x = ofFinite k A (n + 1) B := by
  obtain ⟨n, B, rfl⟩ := exists_ofFinite k A x
  exact ⟨n, zeroExtend (Nat.le_succ n) B, (ofFinite_zeroExtend k A (Nat.le_succ n) B).symm⟩

/-- The entries of a finite matrix, extended by zero to natural-number coordinates. -/
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

/-- The entries of a stable matrix, indexed by pairs of natural numbers. -/
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

/-- The entry map is injective. -/
theorem entries_injective : Function.Injective (entries k A) := by
  apply DirectLimit.lift_injective
  intro n B C h
  ext i j
  have he := congrArg (fun D : Matrix ℕ ℕ A => D i.val j.val) h
  simpa only [finiteEntries, Matrix.of_apply, dite_eq_left i.is_lt, dite_eq_left j.is_lt] using he

/-- The finite-stage inclusions are injective. -/
theorem ofFinite_injective (n : ℕ) : Function.Injective (ofFinite k A n) := by
  intro B C h
  ext i j
  simpa only [entries_ofFinite_fin] using
    congrArg (fun x : StableModule k A => entries k A x i.val j.val) h

/-- Every stable matrix is supported in a finite square. -/
theorem entries_bounded (x : StableModule k A) :
    ∃ n, ∀ i j : ℕ, n ≤ i ∨ n ≤ j → entries k A x i j = 0 := by
  obtain ⟨n, B, rfl⟩ := exists_ofFinite k A x
  refine ⟨n, fun i j h => ?_⟩
  rcases h with hi | hj
  · rw [entries_ofFinite, dite_eq_right (Nat.not_lt.mpr hi)]
  · by_cases hi : i < n <;>
      simp only [entries_ofFinite, hi, ↓reduceDIte, dite_eq_right (Nat.not_lt.mpr hj)]

/-- The entry function of a stable matrix has finite support. -/
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

/-- A stable matrix as a finitely supported function on `ℕ × ℕ`. -/
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

/-- Every finitely supported natural-number matrix is represented in a finite matrix stage. -/
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

/-- The k-linear realization of stable matrices as finitely supported coordinate functions. -/
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

/-- The k-linear equivalence between stable matrices and finitely supported functions on `ℕ × ℕ`.
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
