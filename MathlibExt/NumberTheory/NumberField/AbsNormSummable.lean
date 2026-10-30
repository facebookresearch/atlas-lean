/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt.lean`
and
`P2M/Sol/S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Analysis.PSeries

/-!
# Summability of the Dedekind zeta terms

For a number field `F` and `σ > 1`, the sum over height-one primes `v` of
the ring of integers of `(N v) ^ (-σ)` is summable: each prime `v` lies
over a rational prime `p` with `N v = p ^ n`, so `N v ^ (-σ) ≤ p ^ (-σ)`,
and at most `[F : ℚ]` primes lie over any given `p`. The bound by the
convergent `p`-series follows.
-/

@[expose] public section

open NumberField IsDedekindDomain

namespace NumberField

/-- The ring of integers of a number field is infinite. Mathlib has no such
instance. -/
instance (F : Type*) [Field F] [NumberField F] : Infinite (𝓞 F) :=
  Infinite.of_injective (algebraMap ℤ (𝓞 F)) (by
    intro a b h
    exact Int.cast_injective (by exact_mod_cast h))

/-- For `σ > 1`, the Dedekind zeta terms `(N v) ^ (-σ)` are summable over
the height-one primes of the ring of integers. -/
theorem summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
    (F : Type*) [Field F] [NumberField F] {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ p n : ℕ, 0 < n ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal ∧
      p.Prime ∧ Ideal.absNorm v.asIdeal = p ^ n := fun v => by
    haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    exact Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  choose p n hn hmem hp hN using hex
  have hterm : ∀ v : HeightOneSpectrum (𝓞 F),
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) ≤ ((p v : ℕ) : ℝ) ^ (-σ) := by
    intro v
    refine Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (hp v).pos) ?_ (by linarith)
    rw [hN v]
    exact_mod_cast Nat.le_self_pow (hn v).ne' (p v)
  have hfib : ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (v₀ : HeightOneSpectrum (𝓞 F)),
      (T.filter fun v => p v = p v₀).card ≤ Module.finrank ℚ F := by
    intro T v₀
    have hqZ : Prime ((p v₀ : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (hp v₀)
    have hq0 : Ideal.span {((p v₀ : ℕ) : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hqZ.ne_zero
    haveI hqmax : (Ideal.span {((p v₀ : ℕ) : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime hqZ.ne_zero).mpr hqZ).isMaximal hq0
    refine (Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal ?_ ?_).trans
      (Ideal.card_primesOverFinset_le_finrank (S := 𝓞 F) ℚ F hq0)
    · intro v hv
      have hv' : (p v : ℕ) = p v₀ := (Finset.mem_filter.mp hv).2
      rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hq0]
      refine ⟨v.isPrime, ⟨?_⟩⟩
      refine hqmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hv']
      exact hmem v
    · intro v₁ _ v₂ _ h
      exact HeightOneSpectrum.ext h
  have hnat : Summable fun m : ℕ => (m : ℝ) ^ (-σ) := Real.summable_nat_rpow.mpr (by linarith)
  refine summable_of_sum_le (c := (Module.finrank ℚ F : ℝ) * ∑' m : ℕ, (m : ℝ) ^ (-σ))
    (fun v => by positivity) (fun T => ?_)
  calc ∑ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ)
      ≤ ∑ v ∈ T, ((p v : ℕ) : ℝ) ^ (-σ) := Finset.sum_le_sum fun v _ => hterm v
    _ = ∑ q ∈ T.image p, ∑ v ∈ T.filter (fun v => p v = q), ((p v : ℕ) : ℝ) ^ (-σ) :=
        (Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem p hv) _).symm
    _ ≤ ∑ q ∈ T.image p, (Module.finrank ℚ F : ℝ) * (q : ℝ) ^ (-σ) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨v₀, -, rfl⟩ := Finset.mem_image.mp hq
        calc ∑ v ∈ T.filter (fun v => p v = p v₀), ((p v : ℕ) : ℝ) ^ (-σ)
            = ∑ v ∈ T.filter (fun v => p v = p v₀), ((p v₀ : ℕ) : ℝ) ^ (-σ) := by
              refine Finset.sum_congr rfl fun v hv => ?_
              rw [(Finset.mem_filter.mp hv).2]
          _ = ((T.filter fun v => p v = p v₀).card : ℝ) * ((p v₀ : ℕ) : ℝ) ^ (-σ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Module.finrank ℚ F : ℝ) * ((p v₀ : ℕ) : ℝ) ^ (-σ) := by
              gcongr
              exact hfib T v₀
    _ = (Module.finrank ℚ F : ℝ) * ∑ q ∈ T.image p, (q : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ F : ℝ) * ∑' m : ℕ, (m : ℝ) ^ (-σ) := by
        gcongr
        exact hnat.sum_le_tsum _ (fun m _ => by positivity)

end NumberField
