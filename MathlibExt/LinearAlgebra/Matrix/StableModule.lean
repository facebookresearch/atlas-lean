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
# Stable matrix semimodules and finitely supported entries

Let `k` be a semiring and `A` a `k`-semimodule, with independent scalar and coefficient
universes. The direct limit of the finite square matrix semimodules under top-left zero
extension is the stable matrix semimodule.

Its elements are represented by finite matrices and are uniquely determined by their entries
on `ℕ × ℕ`. These entry functions have bounded support, and every finitely supported function
occurs. The entry map therefore gives a `k`-linear equivalence with `(ℕ × ℕ) →₀ A`.
-/

@[expose] public section

noncomputable section

namespace Matrix

universe u v

variable (k : Type u) [Semiring k] (A : Type v) [AddCommMonoid A] [Module k A]

local instance : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) h) :=
  zeroExtendLinear_directedSystem (k := k) (A := A)

/-- Stable matrix semimodule as a direct limit.

For a semiring `k` and an additive commutative monoid `A` with a `k`-module structure,
`Matrix.StableModule k A` is the direct limit of `n × n` matrix semimodules under top-left
zero extension. The carrier lies in the universe of `A`. -/
abbrev StableModule : Type v :=
  letI : DirectedSystem (fun n : ℕ => Matrix (Fin n) (Fin n) A)
      (fun _ _ h => zeroExtendLinear (k := k) h) :=
    zeroExtendLinear_directedSystem (k := k) (A := A)
  DirectLimit (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) h)

namespace StableModule

/-- Finite-stage inclusion in the stable matrix semimodule.

For natural `n`, the `k`-linear map `Matrix.StableModule.ofFinite k A n` sends an `n × n`
matrix to its class in the stable matrix semimodule. -/
def ofFinite (n : ℕ) : Matrix (Fin n) (Fin n) A →ₗ[k] StableModule k A :=
  DirectLimit.Module.of k ℕ (fun n : ℕ => Matrix (Fin n) (Fin n) A)
    (fun _ _ h => zeroExtendLinear (k := k) h) n

/-- Stable semimodule class is unchanged by zero extension.

If `n ≤ m`, the class in stage `m` of the zero extension of a stage-`n` matrix is its class in
stage `n`. -/
@[simp]
theorem ofFinite_zeroExtend {n m : ℕ} (h : n ≤ m) (B : Matrix (Fin n) (Fin n) A) :
    ofFinite k A m (zeroExtend h B) = ofFinite k A n B :=
  DirectLimit.Module.of_f (hij := h)

/-- Finite representative of every stable matrix semimodule element.

Every element of `Matrix.StableModule k A` is the class of an `n × n` matrix for some natural
`n`. -/
theorem exists_ofFinite (x : StableModule k A) :
    ∃ (n : ℕ) (B : Matrix (Fin n) (Fin n) A), x = ofFinite k A n B :=
  DirectLimit.exists_eq_mk (f := fun _ _ h => zeroExtendLinear (k := k) (A := A) h) x

/-- Positive-size representative in the stable matrix semimodule.

Every stable matrix semimodule element is represented by a matrix of size `n + 1` for some
natural `n`. -/
theorem exists_positive_ofFinite (x : StableModule k A) :
    ∃ (n : ℕ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) A), x = ofFinite k A (n + 1) B := by
  obtain ⟨n, B, rfl⟩ := exists_ofFinite k A x
  exact ⟨n, zeroExtend (Nat.le_succ n) B, (ofFinite_zeroExtend k A (Nat.le_succ n) B).symm⟩

/-- Finite matrix entries extended by zero.

For an `n × n` matrix `B`, define its entry function on natural indices by `B i j` inside the
first `n` rows and columns and by zero outside that square. -/
def finiteEntries {n : ℕ} (B : Matrix (Fin n) (Fin n) A) : Matrix ℕ ℕ A :=
  Matrix.of fun i j => if hi : i < n then
    if hj : j < n then B ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

/-- Zero extension preserves the natural entry function.

For `n ≤ m`, extending an `n × n` matrix by zero to size `m` leaves its zero-extended entry
function on `ℕ × ℕ` unchanged. -/
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

/-- Natural-number entry coordinates of stable matrix semimodule elements.

The finite-stage zero-extended entry functions descend to a function from `Matrix.StableModule
k A` to matrices indexed by `ℕ × ℕ`. -/
def entries : StableModule k A → Matrix ℕ ℕ A :=
  DirectLimit.lift (fun _ _ h => zeroExtendLinear (k := k) (A := A) h)
    (fun _ B => finiteEntries A B)
    (fun _ _ h B => (finiteEntries_zeroExtend A h B).symm)

/-- Entry formula for a finite matrix semimodule class.

The `(i, j)` entry of the stage-`n` class of `B` is `B ⟨i, hi⟩ ⟨j, hj⟩` when both natural
indices are less than `n`, and is zero otherwise. -/
@[simp]
theorem entries_ofFinite (n : ℕ) (B : Matrix (Fin n) (Fin n) A) (i j : ℕ) :
    entries k A (ofFinite k A n B) i j =
      if hi : i < n then if hj : j < n then B ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := rfl

/-- Stable semimodule entries agree with finite entries inside the square.

For `i, j : Fin n`, the entry function of the stable class of `B` at `(i.val, j.val)` equals
`B i j`. -/
theorem entries_ofFinite_fin (n : ℕ) (B : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    entries k A (ofFinite k A n B) i.val j.val = B i j := by
  simp only [entries_ofFinite, dite_eq_left i.is_lt, dite_eq_left j.is_lt]

/-- Entries determine a stable matrix semimodule element.

The entry map from `Matrix.StableModule k A` to `Matrix ℕ ℕ A` is injective. -/
theorem entries_injective : Function.Injective (entries k A) := by
  apply DirectLimit.lift_injective
  intro n B C h
  ext i j
  have he := congrArg (fun D : Matrix ℕ ℕ A => D i.val j.val) h
  simpa only [finiteEntries, Matrix.of_apply, dite_eq_left i.is_lt, dite_eq_left j.is_lt] using he

/-- Each finite matrix semimodule stage embeds injectively.

For every natural `n`, the stage inclusion `Matrix.StableModule.ofFinite k A n` is injective. -/
theorem ofFinite_injective (n : ℕ) : Function.Injective (ofFinite k A n) := by
  intro B C h
  ext i j
  simpa only [entries_ofFinite_fin] using
    congrArg (fun x : StableModule k A => entries k A x i.val j.val) h

/-- Stable matrix semimodule entries vanish outside a finite square.

For every stable semimodule element `x`, some natural `n` bounds both indices of every nonzero
entry. The entry is zero whenever `n ≤ i` or `n ≤ j`. -/
theorem entries_bounded (x : StableModule k A) :
    ∃ n, ∀ i j : ℕ, n ≤ i ∨ n ≤ j → entries k A x i j = 0 := by
  obtain ⟨n, B, rfl⟩ := exists_ofFinite k A x
  refine ⟨n, fun i j h => ?_⟩
  rcases h with hi | hj
  · rw [entries_ofFinite, dite_eq_right (Nat.not_lt.mpr hi)]
  · by_cases hi : i < n <;>
      simp only [entries_ofFinite, hi, ↓reduceDIte, dite_eq_right (Nat.not_lt.mpr hj)]

/-- Stable matrix semimodule entry functions have finite support.

The support of `(i, j) ↦ Matrix.StableModule.entries k A x i j` is a finite subset of `ℕ × ℕ`. -/
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

/-- Stable matrix semimodule element as a finitely supported function.

Use the finite support of the natural entry function to regard a stable matrix semimodule
element as an element of `(ℕ × ℕ) →₀ A`. -/
def toFinsupp (x : StableModule k A) : (ℕ × ℕ) →₀ A :=
  Finsupp.ofSupportFinite (fun p => entries k A x p.1 p.2) (entries_finiteSupport k A x)

/-- Evaluation of stable semimodule finitely supported coordinates.

At a pair `p : ℕ × ℕ`, `Matrix.StableModule.toFinsupp k A x p` equals the entry of `x` at row
`p.1` and column `p.2`. -/
@[simp]
theorem toFinsupp_apply (x : StableModule k A) (p : ℕ × ℕ) :
    toFinsupp k A x p = entries k A x p.1 p.2 := rfl

/-- Finitely supported entries determine the stable semimodule class.

The map `Matrix.StableModule.toFinsupp k A` is injective. -/
theorem toFinsupp_injective : Function.Injective (toFinsupp k A) := by
  intro x y h
  apply entries_injective k A
  ext i j
  exact congrArg (fun f : (ℕ × ℕ) →₀ A => f (i, j)) h

/-- Every finitely supported matrix is a stable semimodule class.

Every finitely supported `A`-valued function on `ℕ × ℕ` is the entry function of a stable
matrix semimodule element. A finite square containing its support provides a representative. -/
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

/-- Linear entry map for the stable matrix semimodule.

The finitely supported entry map preserves addition and the `k`-action, giving a linear map
`Matrix.StableModule k A →ₗ[k] (ℕ × ℕ) →₀ A`. -/
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

/-- Stable matrix semimodule is equivalent to finitely supported functions.

The bijective linear entry map gives a `k`-linear equivalence `Matrix.StableModule k A ≃ₗ[k]
(ℕ × ℕ) →₀ A`. -/
def finsuppEquiv : StableModule k A ≃ₗ[k] (ℕ × ℕ) →₀ A :=
  { toFinsuppLinear k A,
    Equiv.ofBijective (toFinsupp k A)
      ⟨toFinsupp_injective k A, toFinsupp_surjective k A⟩ with }

/-- Entry formula for the stable semimodule equivalence.

The equivalence with finitely supported functions evaluates at `p : ℕ × ℕ` as the stable entry
at `(p.1, p.2)`. -/
@[simp]
theorem finsuppEquiv_apply (x : StableModule k A) (p : ℕ × ℕ) :
    finsuppEquiv k A x p = entries k A x p.1 p.2 := rfl

end StableModule

end Matrix
