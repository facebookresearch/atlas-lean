/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Algebra.Module.LinearMap.Index

import Mathlib.Algebra.Module.LinearMap.FiniteRange
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum

/-!
# Fredholm index of powers of the unilateral shift on `ℓ²(ℕ, 𝕜)`

Let `S` be the unilateral (forward) shift on `ℓ²(ℕ, 𝕜)`, `(S x) 0 = 0`,
`(S x) (n + 1) = x n`, and let `B` be the backward shift,
`(B x) n = x (n + 1)`. The shift is the textbook example of a
Fredholm operator that is not invertible: it is injective with
one-dimensional cokernel, while the backward shift `B` is surjective
with one-dimensional kernel. This file computes the Fredholm index of
every power:

* `index (S ^ n) = -n`,
* `index (B ^ n) = n`,

together with the kernel and range descriptions that drive the
computation: `ker (B ^ n)` is the `n`-dimensional space of sequences
supported in the first `n` coordinates, and `range (S ^ n)` is the
space of sequences whose first `n` coordinates vanish, so the
corresponding quotient has dimension `n`. As a consistency check,
`S ∘L B` is Fredholm of index `0`, as index additivity under
composition demands.

This is a companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the spectral theorem, the Fredholm alternative, the Green's
operator). It is not one of the 72 v1 targets, and the index
computations are not in the pinned Mathlib (which has the general
Fredholm-operator API `ContinuousLinearMap.IsFredholm` and
`LinearMap.index`, but no computation for the shift) or in base
MathlibExt. This file uses the established shift operators from
`LpShiftOperator` and extends their API with power and index results.
See e.g. Reed–Simon, *Methods of
Modern Mathematical Physics I: Functional Analysis*, Section VII.2,
and Conway, *A Course in Functional Analysis*, Chapter VII, for the
classical statements.

## Main declarations

* `shiftCLM_pow_apply`, `backwardCLM_pow_apply` : the pointwise action
  of the powers.
* `backwardCLM_pow_comp_shiftCLM_pow` : `B ^ n ∘L S ^ n = 1`.
* `mem_ker_backwardCLM_pow`, `mem_range_shiftCLM_pow` : kernel and
  range characterizations of the powers.
* `kerBackwardCLM_powEquiv` : `ker (B ^ n)` is linearly equivalent to
  `Fin n → 𝕜`.
* `finrank_ker_backwardCLM_pow`, `finrank_quotient_range_shiftCLM_pow` :
  the kernel and cokernel dimensions are both `n`.
* `isFredholm_shiftCLM_pow`, `isFredholm_backwardCLM_pow` : the powers
  are Fredholm operators.
* `index_shiftCLM_pow`, `index_backwardCLM_pow` : the index formulas.
* `index_shift_comp_backward` : `S ∘L B` has index `0`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.ShiftFredholmIndex

open Filter Topology Set
open LpShiftOperator
open scoped _root_.lp ENNReal
open scoped LinearMap.FiniteRangeSetoid

variable {𝕜 : Type*} [RCLike 𝕜]

section Iterates

/-- Iterating the forward-shift function `n` times inserts `n` zeroes
in front of the sequence. -/
theorem shiftFun_iterate_apply (n : ℕ) (x : ℕ → 𝕜) (i : ℕ) :
    (shiftFun^[n]) x i = if i < n then 0 else x (i - n) := by
  induction n generalizing x i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      by_cases h1 : i < n
      · rw [ite_eq_left h1, ite_eq_left (by omega : i < n + 1)]
      · by_cases h2 : i < n + 1
        · have hi : i = n := by omega
          rw [hi, ite_eq_right (lt_irrefl n), ite_eq_left (Nat.lt_succ_self n), Nat.sub_self,
            shiftFun_zero]
        · rw [ite_eq_right h1, ite_eq_right h2]
          have hsub : i - n = (i - (n + 1)) + 1 := by omega
          rw [hsub]
          rfl

set_option linter.unusedSectionVars false in
/-- Iterating the backward-shift function `n` times drops the first
`n` coordinates. -/
theorem backwardFun_iterate_apply (n : ℕ) (x : ℕ → 𝕜) (i : ℕ) :
    (backwardFun^[n]) x i = x (i + n) := by
  induction n generalizing x i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', backwardFun_apply, ih]
      congr 1
      omega

/-- The coercion of `S ^ n` is the `n`-fold iterate of `shiftFun`. -/
theorem shiftCLM_pow_coe (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    ((shiftCLM (𝕜 := 𝕜) ^ n) x : ℕ → 𝕜) = (shiftFun^[n]) (x : ℕ → 𝕜) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp, ih]
      have hcoe : ((shiftCLM x : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) = shiftFun (x : ℕ → 𝕜) :=
        funext fun i => shiftCLM_apply x i
      rw [hcoe, Function.iterate_succ_apply]

/-- The coercion of `B ^ n` is the `n`-fold iterate of `backwardFun`. -/
theorem backwardCLM_pow_coe (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    ((backwardCLM (𝕜 := 𝕜) ^ n) x : ℕ → 𝕜) = (backwardFun^[n]) (x : ℕ → 𝕜) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp, ih]
      have hcoe : ((backwardCLM x : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) = backwardFun (x : ℕ → 𝕜) :=
        funext fun i => backwardCLM_apply x i
      rw [hcoe, Function.iterate_succ_apply]

/-- Pointwise action of `S ^ n`: it inserts `n` zeroes in front. -/
theorem shiftCLM_pow_apply (n : ℕ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (shiftCLM (𝕜 := 𝕜) ^ n) x i = if i < n then 0 else x (i - n) := by
  rw [shiftCLM_pow_coe, shiftFun_iterate_apply]

/-- Pointwise action of `B ^ n`: it drops the first `n` coordinates. -/
theorem backwardCLM_pow_apply (n : ℕ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (backwardCLM (𝕜 := 𝕜) ^ n) x i = x (i + n) := by
  rw [backwardCLM_pow_coe, backwardFun_iterate_apply]

end Iterates

section Composition

/-- `B ^ n` is a left inverse of `S ^ n`: shifting up then down
recovers the original sequence. -/
theorem backwardCLM_pow_comp_shiftCLM_pow (n : ℕ) :
    (backwardCLM (𝕜 := 𝕜) ^ n) ∘L (shiftCLM (𝕜 := 𝕜) ^ n) = (1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, backwardCLM_pow_apply, shiftCLM_pow_apply,
    one_apply_eq_self]
  rw [ite_eq_right (by omega : ¬ i + n < n), Nat.add_sub_cancel]

/-- The unilateral shift power is injective. -/
theorem injective_shiftCLM_pow (n : ℕ) :
    Function.Injective ⇑(shiftCLM (𝕜 := 𝕜) ^ n) := by
  apply Function.LeftInverse.injective (g := ⇑(backwardCLM (𝕜 := 𝕜) ^ n))
  intro x
  simpa using DFunLike.congr_fun (backwardCLM_pow_comp_shiftCLM_pow n) x

/-- The backward shift power is surjective. -/
theorem surjective_backwardCLM_pow (n : ℕ) :
    Function.Surjective ⇑(backwardCLM (𝕜 := 𝕜) ^ n) := by
  intro y
  exact ⟨(shiftCLM (𝕜 := 𝕜) ^ n) y,
    by simpa using DFunLike.congr_fun (backwardCLM_pow_comp_shiftCLM_pow n) y⟩

/-- A vector is in the kernel of `B ^ n` iff its coordinates from `n`
onwards all vanish. -/
theorem mem_ker_backwardCLM_pow (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    (backwardCLM (𝕜 := 𝕜) ^ n) x = 0 ↔ ∀ i, x (i + n) = 0 := by
  constructor
  · intro h i
    have hii := congr_fun (congr_arg (fun z : ℓ²(ℕ, 𝕜) => (z : ℕ → 𝕜)) h) i
    rw [backwardCLM_pow_apply] at hii
    simpa using hii
  · intro h
    apply lp.ext
    funext i
    simp only [backwardCLM_pow_apply, h i, lp.coeFn_zero, Pi.zero_apply]

/-- A vector is in the range of `S ^ n` iff its first `n` coordinates
vanish. -/
theorem mem_range_shiftCLM_pow (n : ℕ) (y : ℓ²(ℕ, 𝕜)) :
    (∃ x, (shiftCLM (𝕜 := 𝕜) ^ n) x = y) ↔ ∀ i < n, y i = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ i hi
    rw [shiftCLM_pow_apply, ite_eq_left hi]
  · intro hy
    refine ⟨(backwardCLM (𝕜 := 𝕜) ^ n) y, ?_⟩
    apply lp.ext
    funext i
    rw [shiftCLM_pow_apply, backwardCLM_pow_apply]
    by_cases hi : i < n
    · rw [ite_eq_left hi]
      exact (hy i hi).symm
    · rw [ite_eq_right hi, Nat.sub_add_cancel (show n ≤ i by omega)]

end Composition

section FirstCoordinates

/-- The map taking a sequence to its first `n` coordinates. -/
noncomputable def firstCoords (n : ℕ) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] (Fin n → 𝕜) where
  toFun x i := (x : ℕ → 𝕜) (i : ℕ)
  map_add' x y := by
    funext i
    simp
  map_smul' c x := by
    funext i
    simp [lp.coeFn_smul]

/-- The extension of a tuple of `n` coordinates by zeroes. -/
def extZeroFun {n : ℕ} (v : Fin n → 𝕜) (j : ℕ) : 𝕜 :=
  if h : j < n then v ⟨j, h⟩ else 0

theorem extZeroFun_apply_of_lt {n : ℕ} (v : Fin n → 𝕜) {j : ℕ} (hj : j < n) :
    extZeroFun v j = v ⟨j, hj⟩ :=
  dite_eq_left hj

theorem extZeroFun_apply_of_ge {n : ℕ} (v : Fin n → 𝕜) {j : ℕ} (hj : ¬ j < n) :
    extZeroFun v j = 0 :=
  dite_eq_right hj

/-- A finitely supported sequence is in `ℓ²`. -/
theorem memℓp_extZeroFun {n : ℕ} (v : Fin n → 𝕜) : Memℓp (extZeroFun v) 2 := by
  apply memℓp_gen
  apply summable_of_ne_finset_zero (s := Finset.range n)
  intro j hj
  rw [Finset.mem_range] at hj
  rw [extZeroFun_apply_of_ge v hj]
  simp

/-- The linear extension-by-zero map `(Fin n → 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)`. -/
noncomputable def extZero (n : ℕ) : (Fin n → 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun v := ⟨extZeroFun v, memℓp_extZeroFun v⟩
  map_add' v w := by
    apply lp.ext
    funext j
    show extZeroFun (v + w) j = extZeroFun v j + extZeroFun w j
    by_cases hj : j < n
    · rw [extZeroFun_apply_of_lt (v + w) hj, extZeroFun_apply_of_lt v hj,
        extZeroFun_apply_of_lt w hj, Pi.add_apply]
    · rw [extZeroFun_apply_of_ge (v + w) hj, extZeroFun_apply_of_ge v hj,
        extZeroFun_apply_of_ge w hj, add_zero]
  map_smul' c v := by
    apply lp.ext
    funext j
    show extZeroFun (c • v) j = c • extZeroFun v j
    by_cases hj : j < n
    · rw [extZeroFun_apply_of_lt (c • v) hj, extZeroFun_apply_of_lt v hj, Pi.smul_apply]
    · rw [extZeroFun_apply_of_ge (c • v) hj, extZeroFun_apply_of_ge v hj, smul_zero]

/-- Pointwise action of the extension-by-zero map. -/
theorem extZero_apply (n : ℕ) (v : Fin n → 𝕜) (j : ℕ) :
    (extZero n v : ℕ → 𝕜) j = extZeroFun v j :=
  rfl

/-- Taking first coordinates after extension by zeroes is the identity. -/
theorem firstCoords_extZero (n : ℕ) (v : Fin n → 𝕜) :
    firstCoords n (extZero n v) = v := by
  funext i
  show (extZero n v : ℕ → 𝕜) (i : ℕ) = v i
  rw [extZero_apply, extZeroFun_apply_of_lt _ i.isLt]

/-- A vector in the kernel of `B ^ n` is determined by its first `n`
coordinates: extending those coordinates by zeroes recovers it. -/
theorem extZero_firstCoords_of_mem_ker (n : ℕ) {x : ℓ²(ℕ, 𝕜)}
    (hx : x ∈ (↑(backwardCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)).ker) :
    extZero n (firstCoords n x) = x := by
  apply lp.ext
  funext j
  rw [extZero_apply]
  by_cases hj : j < n
  · rw [extZeroFun_apply_of_lt _ hj]
    rfl
  · rw [extZeroFun_apply_of_ge _ hj]
    have hx' : x ((j - n) + n) = 0 := by
      rw [LinearMap.mem_ker] at hx
      exact (mem_ker_backwardCLM_pow n x).mp hx (j - n)
    rw [Nat.sub_add_cancel (by omega : n ≤ j)] at hx'
    exact hx'.symm

/-- The kernel of `B ^ n` is linearly equivalent to `Fin n → 𝕜`: a
vector in the kernel is exactly its first `n` coordinates. -/
noncomputable def kerBackwardCLM_powEquiv (n : ℕ) :
    (↑(backwardCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)).ker ≃ₗ[𝕜] (Fin n → 𝕜) where
  toFun x := firstCoords n x
  invFun v := ⟨extZero n v, by
    rw [LinearMap.mem_ker]
    exact (mem_ker_backwardCLM_pow n (extZero n v)).mpr (fun i => by
      rw [extZero_apply, extZeroFun_apply_of_ge _ (by omega : ¬ i + n < n)])⟩
  left_inv x := by
    apply Subtype.ext
    exact extZero_firstCoords_of_mem_ker n x.property
  right_inv v := firstCoords_extZero n v
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The kernel of `B ^ n` is finite-dimensional. -/
theorem finiteDimensional_ker_backwardCLM_pow (n : ℕ) :
    FiniteDimensional 𝕜 (↑(backwardCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)).ker := by
  exact Module.Finite.equiv (kerBackwardCLM_powEquiv n).symm

/-- The kernel of `B ^ n` has dimension `n`. -/
theorem finrank_ker_backwardCLM_pow (n : ℕ) :
    Module.finrank 𝕜 (↑(backwardCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)).ker = n := by
  rw [LinearEquiv.finrank_eq (kerBackwardCLM_powEquiv n),
    Module.finrank_fintype_fun_eq_card 𝕜, Fintype.card_fin]

/-- The kernel of the first-`n`-coordinates map is the range of
`S ^ n`: both consist of the sequences whose first `n` coordinates
vanish. -/
theorem ker_firstCoords_eq_range_shiftCLM_pow (n : ℕ) :
    (firstCoords n).ker = (↑(shiftCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)).range := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro h
    have hx : ∀ i < n, x i = 0 := by
      intro i hi
      have h' := congr_fun h ⟨i, hi⟩
      rw [show (firstCoords n x) ⟨i, hi⟩ = (x : ℕ → 𝕜) i from rfl] at h'
      simpa using h'
    refine ⟨(backwardCLM (𝕜 := 𝕜) ^ n) x, ?_⟩
    apply lp.ext
    funext i
    show (shiftCLM (𝕜 := 𝕜) ^ n) ((backwardCLM (𝕜 := 𝕜) ^ n) x) i = x i
    rw [shiftCLM_pow_apply, backwardCLM_pow_apply]
    by_cases hi : i < n
    · rw [ite_eq_left hi]
      exact (hx i hi).symm
    · rw [ite_eq_right hi, Nat.sub_add_cancel (show n ≤ i by omega)]
  · rintro ⟨y, rfl⟩
    funext i
    show (shiftCLM (𝕜 := 𝕜) ^ n) y (i : ℕ) = (0 : Fin n → 𝕜) i
    rw [shiftCLM_pow_apply, ite_eq_left i.isLt]
    rfl

/-- The cokernel of `S ^ n` has dimension `n`: the quotient of `ℓ²`
by the range of `S ^ n` is equivalent to `Fin n → 𝕜` via the first
`n` coordinates. -/
theorem finrank_quotient_range_shiftCLM_pow (n : ℕ) :
    Module.finrank 𝕜 (ℓ²(ℕ, 𝕜) ⧸ (↑(shiftCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)).range) = n := by
  have hsurj : Function.Surjective (firstCoords n) :=
    fun v => ⟨extZero (𝕜 := 𝕜) n v, firstCoords_extZero (𝕜 := 𝕜) n v⟩
  have heq := LinearEquiv.finrank_eq
    (LinearMap.quotKerEquivOfSurjective (firstCoords (𝕜 := 𝕜) n) hsurj)
  rw [ker_firstCoords_eq_range_shiftCLM_pow n] at heq
  rw [heq, Module.finrank_fintype_fun_eq_card 𝕜, Fintype.card_fin]

end FirstCoordinates

section Fredholm

/-- The quasi-inverse relation `B ^ n ∘L S ^ n = 1` holds exactly,
hence also modulo finite-rank operators. -/
theorem approx_backward_comp_shift (n : ℕ) :
    (↑(backwardCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) ∘ₗ ↑(shiftCLM (𝕜 := 𝕜) ^ n) ≈
      LinearMap.id := by
  rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
  have hcomp : (↑(backwardCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) ∘ₗ ↑(shiftCLM (𝕜 := 𝕜) ^ n) =
      LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    show (backwardCLM (𝕜 := 𝕜) ^ n) ((shiftCLM (𝕜 := 𝕜) ^ n) x) = x
    have h := DFunLike.congr_fun (backwardCLM_pow_comp_shiftCLM_pow n) x
    simpa using h
  rw [hcomp, sub_self]
  exact LinearMap.HasFiniteRange.zero

/-- The defect `S ^ n ∘L B ^ n - 1` has finite rank: its range lies in
the finite-dimensional kernel of `B ^ n`, since applying `B ^ n`
after it gives `0`. -/
theorem approx_shift_comp_backward (n : ℕ) :
    (↑(shiftCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) ∘ₗ ↑(backwardCLM (𝕜 := 𝕜) ^ n) ≈
      LinearMap.id := by
  rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange,
    LinearMap.hasFiniteRange_iff_range, Submodule.fg_iff_finiteDimensional]
  have hle : ((↑(shiftCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) ∘ₗ ↑(backwardCLM (𝕜 := 𝕜) ^ n) -
        LinearMap.id).range ≤ (↑(backwardCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)).ker := by
    intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [LinearMap.mem_ker]
    show (backwardCLM (𝕜 := 𝕜) ^ n) ((shiftCLM (𝕜 := 𝕜) ^ n) ((backwardCLM (𝕜 := 𝕜) ^ n) x) - x) = 0
    rw [map_sub]
    have hB : (backwardCLM (𝕜 := 𝕜) ^ n) ((shiftCLM (𝕜 := 𝕜) ^ n) ((backwardCLM (𝕜 := 𝕜) ^ n) x)) =
        (backwardCLM (𝕜 := 𝕜) ^ n) x := by
      have h := DFunLike.congr_fun (backwardCLM_pow_comp_shiftCLM_pow n)
        ((backwardCLM (𝕜 := 𝕜) ^ n) x)
      simpa using h
    rw [hB]
    exact sub_self _
  have hfin : FiniteDimensional 𝕜 (↑(backwardCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)).ker :=
    finiteDimensional_ker_backwardCLM_pow n
  exact Submodule.finiteDimensional_of_le hle

/-- Every power of the unilateral shift is a Fredholm operator: `B ^ n`
is a quasi-inverse. -/
theorem isFredholm_shiftCLM_pow (n : ℕ) : (shiftCLM (𝕜 := 𝕜) ^ n).IsFredholm := by
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := backwardCLM (𝕜 := 𝕜) ^ n)
  exact ⟨approx_backward_comp_shift n, approx_shift_comp_backward n⟩

/-- Every power of the backward shift is a Fredholm operator: `S ^ n`
is a quasi-inverse. -/
theorem isFredholm_backwardCLM_pow (n : ℕ) : (backwardCLM (𝕜 := 𝕜) ^ n).IsFredholm := by
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := shiftCLM (𝕜 := 𝕜) ^ n)
  exact ⟨approx_shift_comp_backward n, approx_backward_comp_shift n⟩

/-- The Fredholm index of `S ^ n` is `-n`: the shift power is
injective, and its cokernel has dimension `n`. -/
theorem index_shiftCLM_pow (n : ℕ) : (shiftCLM (𝕜 := 𝕜) ^ n).index = -(n : ℤ) := by
  have hinj : Function.Injective (↑(shiftCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) :=
    injective_shiftCLM_pow n
  have hfin := finrank_quotient_range_shiftCLM_pow (𝕜 := 𝕜) n
  rw [LinearMap.index_of_injective hinj, hfin]

/-- The Fredholm index of `B ^ n` is `n`: the backward shift power is
surjective, and its kernel has dimension `n`. -/
theorem index_backwardCLM_pow (n : ℕ) : (backwardCLM (𝕜 := 𝕜) ^ n).index = (n : ℤ) := by
  have hsurj : Function.Surjective (↑(backwardCLM (𝕜 := 𝕜) ^ n) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) :=
    surjective_backwardCLM_pow n
  have hfin := finrank_ker_backwardCLM_pow (𝕜 := 𝕜) n
  rw [LinearMap.index_of_surjective hsurj, hfin]

/-- The Fredholm index of the unilateral shift is `-1`. -/
theorem index_shiftCLM : (shiftCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)).index = -1 := by
  simpa using index_shiftCLM_pow (𝕜 := 𝕜) 1

/-- The Fredholm index of the backward shift is `1`. -/
theorem index_backwardCLM : (backwardCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)).index = 1 := by
  simpa using index_backwardCLM_pow (𝕜 := 𝕜) 1

/-- `S ∘L B` is Fredholm: it is the composite of two Fredholm operators. -/
theorem isFredholm_shift_comp_backward : (shiftCLM (𝕜 := 𝕜) ∘L backwardCLM (𝕜 := 𝕜)).IsFredholm := by
  have h := (isFredholm_shiftCLM_pow (𝕜 := 𝕜) 1).comp (isFredholm_backwardCLM_pow (𝕜 := 𝕜) 1)
  simpa using h

/-- `S ∘L B` has Fredholm index `0`, as index additivity under
composition demands: `(-1) + 1 = 0`. -/
theorem index_shift_comp_backward : (shiftCLM (𝕜 := 𝕜) ∘L backwardCLM (𝕜 := 𝕜)).index = 0 := by
  have hcomp := ContinuousLinearMap.IsFredholm.index_comp (isFredholm_shiftCLM_pow (𝕜 := 𝕜) 1)
    (isFredholm_backwardCLM_pow (𝕜 := 𝕜) 1)
  simp only [pow_one] at hcomp
  rw [hcomp, index_shiftCLM, index_backwardCLM]
  norm_num

end Fredholm

end MathlibExt.Analysis.InnerProductSpace.ShiftFredholmIndex
