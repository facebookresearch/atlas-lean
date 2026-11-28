/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Euler identities for finite exact module chains

For an exact finite sequence with zero endpoints and finite module lengths,
the alternating sum of lengths vanishes. Exactness identifies consecutive
ranges with kernels, so their finite lengths telescope.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped BigOperators

universe u v w x

namespace Module

variable (R : Type u) [Ring R]

/-- Range-sum formula for the middle length of an exact pair.

For R-linear maps f : L → M and g : M → N with Im(f) = Ker(g), ℓ_R(M) = ℓ_R(Im f) + ℓ_R(Im g)
in ℕ∞. The injective inclusion of Im(f) and surjective range restriction of g present the
corresponding short exact sequence. -/
theorem length_eq_range_add_range_of_exact
    {L : Type v} {M : Type w} {N : Type x}
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (h : Function.Exact f g) :
    Module.length R M =
      Module.length R f.range + Module.length R g.range := by
  apply Module.length_eq_add_of_exact
    f.range.subtype g.rangeRestrict
      (Submodule.injective_subtype f.range) g.surjective_rangeRestrict
  exact h.rangeFactorization ⟨0, g.map_zero⟩

/-- Over a ring R, an exact pair of R-linear maps with finite middle length has
middle natural length equal to the sum of its two range lengths. The ring and
three module carrier universes are independent. -/
theorem exactPair_length_toNat {L : Type v} {M : Type w} {N : Type x}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (f : L →ₗ[R] M) (g : M →ₗ[R] N) (h : Function.Exact f g)
    (hM : Module.length R M ≠ ⊤) :
    (Module.length R M).toNat =
      (Module.length R f.range).toNat + (Module.length R g.range).toNat := by
  have he := length_eq_range_add_range_of_exact R f g h
  have hf : Module.length R f.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_injective f.range.subtype (Submodule.injective_subtype _))
  have hg : Module.length R g.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_surjective g.rangeRestrict g.surjective_rangeRestrict)
  rw [he, ENat.toNat_add hf hg]

/-- Algebraic telescoping of an actual finite sequence of consecutive ranges. -/
theorem alternating_sum_of_consecutive_ranges
    (a r : ℕ → ℤ) (n : ℕ) (h0 : a 0 = r 0)
    (hstep : ∀ i < n, a (i + 1) = r i + r (i + 1)) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * a i) =
      (-1 : ℤ) ^ n * r n := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self n)))]
      rw [hstep n (Nat.lt_succ_self n), pow_succ]
      ring

/-- A finite exact module chain with zero endpoints in which each module `M i` with `i ≤ n`
has finite length has zero alternating length sum. -/
theorem alternating_length_of_exact_chain
    (M : ℕ → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (d : ∀ i, M i →ₗ[R] M (i + 1)) (n : ℕ)
    (hfirst : Function.Injective (d 0))
    (hexact : ∀ i < n, Function.Exact (d i) (d (i + 1)))
    (hlast : (d n).range = ⊥)
    (hlen : ∀ i ≤ n, Module.length R (M i) ≠ ⊤) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
      (Module.length R (M i)).toNat) = 0 := by
  let a : ℕ → ℤ := fun i => (Module.length R (M i)).toNat
  let r : ℕ → ℤ := fun i => (Module.length R (d i).range).toNat
  have h0 : a 0 = r 0 := by
    let e := LinearEquiv.ofBijective (d 0).rangeRestrict
      ⟨(LinearMap.injective_rangeRestrict_iff _).mpr hfirst,
        (d 0).surjective_rangeRestrict⟩
    exact congrArg (fun x : ENat => (x.toNat : ℤ)) e.length_eq
  have hstep : ∀ i < n, a (i + 1) = r i + r (i + 1) := by
    intro i hi
    have h := exactPair_length_toNat R (d i) (d (i + 1)) (hexact i hi)
      (hlen (i + 1) (Nat.succ_le_of_lt hi))
    dsimp only [a, r]
    exact_mod_cast h
  have he := alternating_sum_of_consecutive_ranges a r n h0 hstep
  have hr : r n = 0 := by
    dsimp [r]
    rw [hlast]
    have hz : Module.length R (⊥ : Submodule R (M (n + 1))) = 0 :=
      Module.length_eq_zero_iff.mpr inferInstance
    rw [hz]
    rfl
  rw [hr, mul_zero] at he
  exact he

end Module
