/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.ControlTheory.Signals.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Natural-time signals: zero extension and restriction

`zeroExt 𝕜 E : (ℕ → E) →ₗ[𝕜] (ℤ → E)` extends a natural-time signal by
zero to negative times: `(zeroExt 𝕜 E x) n = x n` for `0 ≤ n` (reading
`n` as a natural) and `0` for `n < 0`. It is injective, with left
inverse the restriction `restrNat 𝕜 E : (ℤ → E) →ₗ[𝕜] (ℕ → E)`,
`restrNat 𝕜 E y n = y n`. The zero-padded right shift on natural-time
signals, `rshiftNat 𝕜 E x 0 = 0` and `rshiftNat 𝕜 E x (n + 1) = x n`,
is intertwined with the integer-time shift of `Signals.Basic`:
`zeroExt ∘ rshiftNat = shiftₗ 1 ∘ zeroExt`. Note that `rshiftNat` is
not `shiftₗ` specialized to `ℕ`: truncated subtraction there would
give `x 0` at time `0` instead of `0`. The right shift `rshiftNat` is
not surjective when `E` is nontrivial (every signal in its range
vanishes at `0`), and transporting a causal natural-time operator `S`
to integer time as `zeroExt ∘ S ∘ restrNat` gives a causal
integer-time operator.

Provenance: control-theory roadmap leaf `SSC-U01.T02` (clauses
`SSC-F04.c02`, `SSC-U01.c03`), on top of the merged signals foundation
`SSC-U01.T01` (`MathlibExt.ControlTheory.Signals.Basic`).
-/

@[expose] public section

namespace ControlTheory

/-- Zero extension of a natural-time signal to integer time:
`(zeroExt 𝕜 E x) n = x n` for `0 ≤ n` (reading `n` as a natural) and `0`
for `n < 0`. Linear in the signal. -/
def zeroExt (𝕜 : Type*) (E : Type*) [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] : (ℕ → E) →ₗ[𝕜] (ℤ → E) where
  toFun x n := if 0 ≤ n then x n.toNat else 0
  map_add' x y := by
    funext n
    by_cases h : 0 ≤ n <;> simp [h]
  map_smul' c x := by
    funext n
    by_cases h : 0 ≤ n <;> simp [h]

/-- Right shift on natural-time signals, zero-padded on the left:
`(rshiftNat 𝕜 E x) 0 = 0` and `(rshiftNat 𝕜 E x) (n + 1) = x n`. -/
def rshiftNat (𝕜 : Type*) (E : Type*) [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] : (ℕ → E) →ₗ[𝕜] (ℕ → E) where
  toFun x n := if n = 0 then 0 else x (n - 1)
  map_add' x y := by
    funext n
    by_cases h : n = 0 <;> simp [h]
  map_smul' c x := by
    funext n
    by_cases h : n = 0 <;> simp [h]

/-- Restriction of an integer-time signal to natural time, as a linear
map: `restrNat 𝕜 E y n = y n` for `n : ℕ` cast into `ℤ`. -/
def restrNat (𝕜 : Type*) (E : Type*) [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] : (ℤ → E) →ₗ[𝕜] (ℕ → E) :=
  LinearMap.funLeft 𝕜 E (fun n : ℕ => (n : ℤ))

@[simp]
theorem zeroExt_apply {𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    (x : ℕ → E) (n : ℤ) :
    zeroExt 𝕜 E x n = if 0 ≤ n then x n.toNat else 0 := by
  rfl

@[simp]
theorem zeroExt_apply_natCast {𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] (x : ℕ → E) (n : ℕ) : zeroExt 𝕜 E x (n : ℤ) = x n := by
  rw [zeroExt_apply, ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast]

theorem zeroExt_injective {𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] : Function.Injective (zeroExt 𝕜 E) := by
  intro x y h
  funext n
  have h2 : zeroExt 𝕜 E x (n : ℤ) = zeroExt 𝕜 E y (n : ℤ) := by rw [h]
  simpa using h2

@[simp]
theorem rshiftNat_apply {𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    (x : ℕ → E) (n : ℕ) :
    rshiftNat 𝕜 E x n = if n = 0 then 0 else x (n - 1) := by
  rfl

@[simp]
theorem restrNat_apply {𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    (y : ℤ → E) (n : ℕ) : restrNat 𝕜 E y n = y (n : ℤ) := by
  rfl

/-- Restriction after zero extension is the identity on natural-time
signals. -/
theorem restrNat_comp_zeroExt {𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] :
    (restrNat 𝕜 E).comp (zeroExt 𝕜 E) = LinearMap.id := by
  ext x n
  simp

/-- Zero extension intertwines the two right shifts: extending a
right-shifted natural-time signal is the integer-time shift by `1` of
the extension, `ι ∘ rshiftNat = shiftₗ 1 ∘ ι`. -/
theorem zeroExt_comp_rshiftNat {𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] :
    (zeroExt 𝕜 E).comp (rshiftNat 𝕜 E) =
      (shiftₗ 𝕜 E (1 : ℤ)).comp (zeroExt 𝕜 E) := by
  ext x n
  simp only [LinearMap.comp_apply, zeroExt_apply, rshiftNat_apply]
  have hshift : (shiftₗ 𝕜 E (1 : ℤ)) (zeroExt 𝕜 E x) n
      = zeroExt 𝕜 E x (n - 1) := rfl
  rw [hshift, zeroExt_apply]
  by_cases hn : 0 ≤ n
  · by_cases hn0 : n = 0
    · subst hn0
      simp
    · have h1 : 0 ≤ n - 1 := by omega
      have h2 : n.toNat ≠ 0 := by omega
      rw [ite_eq_left hn, ite_eq_right h2, ite_eq_left h1]
      congr 1
      omega
  · have h1 : ¬ 0 ≤ n - 1 := by omega
    rw [ite_eq_right hn, ite_eq_right h1]

/-- The right shift on natural-time signals is not surjective when the
value type is nontrivial: every signal in its range vanishes at `0`. -/
theorem not_surjective_rshiftNat {𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [Nontrivial E] :
    ¬ Function.Surjective (rshiftNat 𝕜 E) := by
  intro hsurj
  obtain ⟨b, hb⟩ := exists_ne (0 : E)
  obtain ⟨x, hx⟩ := hsurj (fun _ => b)
  have h1 : (rshiftNat 𝕜 E x) 0 = 0 := by simp
  rw [hx] at h1
  simp at h1
  exact hb h1

/-- Transporting a causal natural-time operator along zero extension
and restriction gives a causal integer-time operator:
`ι ∘ S ∘ restr` is causal on `ℤ`-time signals whenever `S` is causal
on `ℕ`-time signals. -/
theorem IsCausal.zeroExt_restrNat {𝕜 E F : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]
    {S : (ℕ → E) →ₗ[𝕜] (ℕ → F)} (hS : IsCausal S) :
    IsCausal ((zeroExt 𝕜 F).comp (S.comp (restrNat 𝕜 E))) := by
  unfold IsCausal
  intro t x y hxy
  simp only [LinearMap.comp_apply, zeroExt_apply]
  by_cases ht : 0 ≤ t
  · simp only [ite_eq_left ht]
    apply hS
    intro s hs
    simp only [restrNat_apply]
    apply hxy
    have hcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht
    rw [← hcast]
    exact_mod_cast hs
  · simp only [ite_eq_right ht]

end ControlTheory
