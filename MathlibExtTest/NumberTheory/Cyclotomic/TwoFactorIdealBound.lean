/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The source-facing signatures and integer-input ideal definition are adapted
from `P2M/Sol/S_flt_regular.lean`, lines 328-329, 490-498, and 3496-3508,
in anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Copyright (c) the flt-regular authors, as recorded in that repository.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Its ATTRIBUTION.md credits the flt-regular project: Alex J. Best,
Christopher Birkbeck, Riccardo Brasca, Eric Rodriguez Boidi,
Ruben Van de Velde, and Andrew Yang.
-/

import MathlibExt.NumberTheory.Cyclotomic.TwoFactorIdealBound
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
Importing consumers and boundary tests for the two-factor ideal bound.
The source signature is retained separately from the Dedekind-domain API.
The source-facing signatures and integer-ideal definition are from
`P2M/Sol/S_flt_regular.lean`, R328-329, R490-498, and R3496-3508,
at the commit and with the flt-regular attribution stated in the
production module. No extraction module is imported.
-/

open Ideal Polynomial
open scoped NumberField

namespace TwoFactorIdealBoundTest

/-- Exact inferred signature of source R3496-3508, with no FLT equation,
regularity, oddness, or cyclotomic-extension assumption. -/
theorem source_bound {K : Type} {p : ℕ} [NeZero p] [Field K]
    [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y : 𝓞 K}
    [hp : Fact p.Prime] (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K))
    (hne : η₁ ≠ η₂) :
    span {x + y * η₁} ⊔ span {x + y * η₂} ∣
      gcd (span {x}) (span {y}) * span {hζ.toInteger - 1} :=
  hζ.toInteger_isPrimitiveRoot.span_add_mul_sup_dvd_gcd_mul_sub_one
    hp.out η₁.prop η₂.prop (Subtype.coe_injective.ne hne)

/-- Removing a nonzero common gcd/ramified factor leaves coprime ideals.
The factorizations are supplied, not chosen by a descent construction. -/
theorem normalized_factors_coprime {R : Type*} [CommRing R]
    [IsDedekindDomain R] {p : ℕ} {ζ x y η₁ η₂ : R}
    (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hη₁ : η₁ ∈ nthRootsFinset p (1 : R))
    (hη₂ : η₂ ∈ nthRootsFinset p (1 : R)) (hne : η₁ ≠ η₂)
    (C D : Ideal R)
    (hG : gcd (span {x}) (span {y}) * span {ζ - 1} ≠ 0)
    (hC : (gcd (span {x}) (span {y}) * span {ζ - 1}) * C =
      span {x + y * η₁})
    (hD : (gcd (span {x}) (span {y}) * span {ζ - 1}) * D =
      span {x + y * η₂}) : IsCoprime C D := by
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_iff_le_sup,
    ← Ideal.dvd_iff_le, ← mul_dvd_mul_iff_left hG, Ideal.mul_top,
    Ideal.mul_sup, hC, hD]
  exact hζ.span_add_mul_sup_dvd_gcd_mul_sub_one hp hη₁ hη₂ hne

/-- Coprime integer inputs away from the ramified factor give coprime
cyclotomic linear factors, using the bound rather than prime-ideal descent. -/
theorem integer_factors_coprime {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [NeZero p]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {x y : ℤ} (hxy : IsCoprime x y)
    (hpsum : ¬ (p : ℤ) ∣ x + y) {η₁ η₂ : 𝓞 K}
    (hη₁ : η₁ ∈ nthRootsFinset p (1 : 𝓞 K))
    (hη₂ : η₂ ∈ nthRootsFinset p (1 : 𝓞 K)) (hne : η₁ ≠ η₂) :
    IsCoprime (span {x + (y : 𝓞 K) * η₁})
      (span {x + (y : 𝓞 K) * η₂}) := by
  have hb := hζ.toInteger_isPrimitiveRoot.span_add_mul_sup_dvd_gcd_mul_sub_one
    (x := (x : 𝓞 K)) (y := (y : 𝓞 K)) hp.out hη₁ hη₂ hne
  have hg : gcd (span {(x : 𝓞 K)}) (span {(y : 𝓞 K)}) = 1 :=
    Ideal.isCoprime_iff_gcd.mp
      ((Ideal.isCoprime_span_singleton_iff _ _).mpr
        (hxy.map (Int.castRingHom (𝓞 K))))
  rw [hg, one_mul, Ideal.dvd_iff_le] at hb
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_iff]
  by_contra hproper
  have hmax := (IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one'
    p hζ).isMaximal (by
      rw [Ne, Ideal.span_singleton_eq_bot, sub_eq_zero]
      exact hζ.toInteger_isPrimitiveRoot.ne_one hp.out.one_lt)
  have heq := hmax.eq_of_le hproper hb
  have hform : (x : 𝓞 K) + y * η₁ ∈ span {hζ.toInteger - 1} := by
    rw [heq]
    exact mem_sup_left (subset_span rfl)
  have hr := hζ.toInteger_isPrimitiveRoot.sub_one_dvd_sub hp.out
    hη₁ (Polynomial.one_mem_nthRootsFinset hp.out.pos)
  have hsum : ((x + y : ℤ) : 𝓞 K) ∈ span {hζ.toInteger - 1} := by
    convert Ideal.sub_mem _ hform
      (Ideal.mul_mem_left _ (y : 𝓞 K) (Ideal.mem_span_singleton.mpr hr)) using 1
    push_cast
    ring
  exact hpsum ((IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff'
    p hζ).mp (Ideal.mem_span_singleton.mp hsum))

/-- The source's custom integer-input ideal, retained only for its bridge. -/
private noncomputable def sourceFltIdeal {p : ℕ} (x y : ℤ)
    {η : 𝓞 (CyclotomicField p ℚ)}
    (_ : η ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))) :
    Ideal (𝓞 (CyclotomicField p ℚ)) := span {↑x + η * ↑y}

/-- The source representation differs only in multiplication order. -/
private theorem sourceFltIdeal_eq {p : ℕ} (x y : ℤ)
    {η : 𝓞 (CyclotomicField p ℚ)}
    (hη : η ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))) :
    sourceFltIdeal x y hη = span {↑x + (y : 𝓞 (CyclotomicField p ℚ)) * η} := by
  simp only [sourceFltIdeal, mul_comm η]

/-- Source R490-498 with every hypothesis retained, including the redundant
lower bound and distinguished nonidentity root. No FLT equation is assumed. -/
theorem source_integer_coprime {p : ℕ} [hp : Fact p.Prime]
    (_ph : 5 ≤ p) {x y : ℤ} {η₁ η₂ : 𝓞 (CyclotomicField p ℚ)}
    (hη₁ : η₁ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)))
    (hη₂ : η₂ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)))
    (hdiff : η₁ ≠ η₂) (hxy : IsCoprime x y)
    (hpsum : ¬ (p : ℤ) ∣ x + y) (_hwlog : η₁ ≠ 1) :
    IsCoprime (sourceFltIdeal x y hη₁) (sourceFltIdeal x y hη₂) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p : ℚ) := ⟨by exact_mod_cast hp.out.ne_zero⟩
  let _ : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  rw [sourceFltIdeal_eq, sourceFltIdeal_eq]
  exact integer_factors_coprime
    (IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ))
    hxy hpsum hη₁ hη₂ hdiff

/-- The smallest prime gives the integer sum/difference bound. -/
theorem prime_two_bound (x y : ℤ) :
    span {x + y} ⊔ span {x - y} ∣
      gcd (span {x}) (span {y}) * span {(2 : ℤ)} := by
  have hroot := IsPrimitiveRoot.neg_one (R := ℤ) 0 (by decide)
  have h := hroot.span_add_mul_sup_dvd_gcd_mul_sub_one (x := x) (y := y)
      Nat.prime_two (Polynomial.one_mem_nthRootsFinset (by decide))
      (show (-1 : ℤ) ∈ nthRootsFinset 2 1 from
        (Polynomial.mem_nthRootsFinset (by decide) 1).mpr (by norm_num))
      (by norm_num)
  simpa only [mul_one, mul_neg, sub_eq_add_neg, neg_add_rev,
    neg_one_mul, mul_one, show (-1 : ℤ) + -1 = -2 by norm_num,
    span_singleton_neg] using h

/-- The source itself admits `p = 2` over the rational number field. -/
theorem source_prime_two (x y : 𝓞 ℚ) :
    span {x + y} ⊔ span {x - y} ∣
      gcd (span {x}) (span {y}) * span {(2 : 𝓞 ℚ)} := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hroot := IsPrimitiveRoot.neg_one (R := ℚ) 0 (by decide)
  have hcast : hroot.toInteger = -1 := by ext; rfl
  have hb := source_bound (x := x) (y := y) hroot
    ⟨1, Polynomial.one_mem_nthRootsFinset (by decide)⟩
    ⟨-1, (Polynomial.mem_nthRootsFinset (by decide) 1).mpr (by norm_num)⟩
    (by intro h; have := congrArg Subtype.val h; norm_num at this)
  simpa only [hcast, mul_one, mul_neg, sub_eq_add_neg,
    show (-1 : 𝓞 ℚ) + -1 = -2 by norm_num, span_singleton_neg] using hb

/-- Zero left input still gives a nonzero common-factor bound. -/
theorem zero_left_bound : (span {(3 : ℤ)}) ∣ span {3} * span {2} := by
  convert prime_two_bound 0 3 using 1 <;> norm_num [Ideal.gcd_eq_sup]

/-- Zero right input is also admitted. -/
theorem zero_right_bound : (span {(3 : ℤ)}) ∣ span {3} * span {2} := by
  convert prime_two_bound 3 0 using 1 <;> norm_num [Ideal.gcd_eq_sup]

/-- Both zero inputs are admitted without using cancellation. -/
theorem both_zero_bound : (0 : Ideal ℤ) ∣ 0 := by
  convert prime_two_bound 0 0 using 1 <;>
    norm_num [Ideal.gcd_eq_sup, Ideal.zero_eq_bot] <;> rfl

/-- The one-zero-input tests have nonzero factor ideals. -/
theorem boundary_ideals_nonzero : span {(3 : ℤ)} ≠ 0 ∧
    span {(2 : ℤ)} ≠ 0 ∧ span {(4 : ℤ)} ≠ 0 := by
  simp

/-- A nonzero, nonunit common factor: at `(x,y) = (6,2)` the bound is `(4)`. -/
theorem sharp_common_factor : span {(8 : ℤ)} ⊔ span {4} = span {4} := by
  have hg : gcd (span {(6 : ℤ)}) (span {2}) = span {2} := by
    rw [Ideal.gcd_eq_sup, ← Ideal.span_insert]
    exact Ideal.span_pair_eq_span_right_iff_dvd.mpr (by norm_num)
  have hb := prime_two_bound 6 2
  rw [hg, Ideal.span_singleton_mul_span_singleton] at hb
  have hbound : span {(8 : ℤ)} ⊔ span {4} ∣ span {4} := by
    convert hb using 1 <;> norm_num
  apply le_antisymm ?_ (Ideal.dvd_iff_le.mp hbound)
  refine sup_le ?_ le_rfl
  rw [span_singleton_le_iff_mem, mem_span_singleton]
  norm_num

/-- Equal roots would assert `(3) ∣ (2)` at `(x,y) = (2,1)`, which is false. -/
theorem equal_root_counterexample :
    ¬ (span {(2 : ℤ) + 1 * 1} ⊔ span {2 + 1 * 1} ∣
      gcd (span {(2 : ℤ)}) (span {1}) * span {(-1 : ℤ) - 1}) := by
  norm_num [Ideal.gcd_eq_sup, Ideal.dvd_span_singleton,
    Ideal.mem_span_singleton]

/-- Reversing divisibility fails at `(x,y) = (4,1)`. -/
theorem reversed_direction_counterexample :
    ¬ (span {(2 : ℤ)} ∣ span {5} ⊔ span {3}) := by
  intro h
  have h5 : (5 : ℤ) ∈ span {(2 : ℤ)} :=
    (Ideal.dvd_iff_le.mp h) (mem_sup_left (subset_span rfl))
  norm_num [Ideal.mem_span_singleton] at h5

/-- At `(x,y) = (5,-1)`, cancellation of `(2)` from `(4)` and `(6)`
proves coprimality of two nonzero, nonunit ideals `(2)` and `(3)`. -/
theorem normalized_nontrivial_example :
    IsCoprime (span {(2 : ℤ)}) (span {3}) := by
  have hroot := IsPrimitiveRoot.neg_one (R := ℤ) 0 (by decide)
  apply normalized_factors_coprime (x := 5) (y := -1) hroot
    Nat.prime_two (Polynomial.one_mem_nthRootsFinset (by decide))
    (show (-1 : ℤ) ∈ nthRootsFinset 2 1 from
      (Polynomial.mem_nthRootsFinset (by decide) 1).mpr (by norm_num))
    (by norm_num)
  all_goals norm_num [Ideal.gcd_eq_sup,
    Ideal.span_singleton_mul_span_singleton]
  exact boundary_ideals_nonzero.2.1

/-- Neither of the normalized example's ideals is a unit ideal. -/
theorem normalized_ideals_nonunit :
    span {(2 : ℤ)} ≠ ⊤ ∧ span {(3 : ℤ)} ≠ ⊤ := by
  norm_num [Ideal.span_singleton_eq_top, Int.isUnit_iff]

/-- The integer-input application at prime `5` has two nonzero ideals. -/
theorem prime_five_nonzero_example {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    IsCoprime (span {2 + hζ.toInteger}) (span {(3 : 𝓞 K)}) ∧
      span {2 + hζ.toInteger} ≠ 0 ∧ span {(3 : 𝓞 K)} ≠ 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hr := hζ.toInteger_isPrimitiveRoot
  refine ⟨?_, ?_, by simp⟩
  · convert integer_factors_coprime hζ (x := 2) (y := 1)
      (by simp) (by norm_num)
      ((Polynomial.mem_nthRootsFinset (by decide) 1).mpr hr.pow_eq_one)
      (Polynomial.one_mem_nthRootsFinset (by decide))
      (hr.ne_one (by decide)) using 1 <;> norm_num
  · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    intro h
    have he : hζ.toInteger = -2 :=
      eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h)
    have hpow := hr.pow_eq_one
    norm_num [he] at hpow

end TwoFactorIdealBoundTest
