/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.RankinSelberg
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for the Rankin–Selberg product in the Selberg class

`tensorLog` at small arguments, and non-vacuity of `IsTensorSimple`: `ζ` is `⊗`-simple
(`ζ ⊗ ζ̄ = ζ`), while the constant function `1` is not (`1 ⊗ 1 = 1` has no pole).
-/

open Complex ArithmeticFunction SelbergClass Filter Topology

@[expose] public section

namespace SelbergClassTest

/-! ### `tensorLog` -/

example (b c : ℕ → ℂ) : tensorLog b c 1 = 0 := by simp [tensorLog]
example (b c : ℕ → ℂ) : tensorLog b c 0 = 0 := by simp [tensorLog]
example (b c : ℕ → ℂ) : tensorLog b c 6 = 0 :=
  tensorLog_of_not_isPrimePow b c (by
    rw [isPrimePow_nat_iff]
    rintro ⟨p, k, hp, hk, hpk⟩
    have h2 : 2 ∣ p ^ k := hpk ▸ (by norm_num : 2 ∣ 6)
    have h3 : 3 ∣ p ^ k := hpk ▸ (by norm_num : 3 ∣ 6)
    have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h2)
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h3)
    omega)
example (b c : ℕ → ℂ) : tensorLog b c 7 = b 7 * c 7 := by
  simpa using tensorLog_prime_pow b c (p := 7) (k := 1) (by norm_num) one_ne_zero
example (b c : ℕ → ℂ) : tensorLog b c 8 = 3 * b 8 * c 8 := by
  simpa using tensorLog_prime_pow b c (p := 2) (k := 3) Nat.prime_two (by norm_num)

example (b : ℕ → ℂ) (s : ℂ) : tensor b 0 s = 1 := by
  have : tensorLog b 0 = 0 := funext fun n => by simp [tensorLog]
  simp [tensor, this, LSeries_zero]

/-- For `ζ`, `k · (1/k) · (1/k) = 1/k`: the Rankin–Selberg logarithm of `ζ ⊗ ζ̄` is that of `ζ`. -/
example : tensorLog zetaLog (fun n => starRingEnd ℂ (zetaLog n)) = zetaLog :=
  tensorLog_zetaLog_conj

/-- `IsEulerLog.norm_apply_prime_pow_le` at `ζ` (`c = 1`, `ε = 0`): `1/k ≤ (2^k - 1)/k`. -/
example {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    ‖zetaLog (p ^ k)‖ ≤ ((1 + 1) ^ k - 1) * (p : ℝ) ^ ((k : ℝ) * 0) / k :=
  isEulerLog_zeta.norm_apply_prime_pow_le (by simp)
    (fun _ hs => LSeriesSummable_of_mem zeta_mem_selbergClass hs)
    (fun n hn => by simp [hn.ne']) hp hk

/-- `LSeriesSummable_tensorLog` at `ζ ⊗ ζ`. -/
example {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (tensorLog zetaLog zetaLog) s :=
  LSeriesSummable_tensorLog zeta_mem_selbergClass zeta_mem_selbergClass isEulerLog_zeta
    isEulerLog_zeta hs

/-! ### `IsTensorSimple` -/

/-- **`ζ` is `⊗`-simple.** -/
example : IsTensorSimple zetaC := isTensorSimple_zeta

/-- **`1` is not `⊗`-simple**: `1 ⊗ 1 = 1` has no pole at `s = 1`. -/
theorem not_isTensorSimple_one : ¬ IsTensorSimple (1 : ArithmeticFunction ℂ) := by
  rintro ⟨-, b, hb, H, hH, -, hord⟩
  have hb0 : b = 0 := IsEulerLog.unique one_one
    (fun _ hs => LSeriesSummable_of_mem one_mem_selbergClass hs) hb isEulerLog_one
  subst hb0
  have hH1 : ∀ σ : ℝ, 1 < σ → H σ = 1 := fun σ hσ => by
    rw [hH σ (by simpa using hσ)]
    have : tensorLog (0 : ℕ → ℂ) (fun n => starRingEnd ℂ ((0 : ℕ → ℂ) n)) = 0 :=
      funext fun n => by simp [tensorLog]
    rw [tensor, this, LSeries_zero]
    simp
  have hm : MeromorphicAt H 1 :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hord]; decide)
  obtain ⟨g, hga, hg1, hg⟩ := (meromorphicOrderAt_eq_int_iff (n := -1) hm).1 hord
  have hpath : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simpa using (ne_of_gt (Set.mem_Ioi.mp hσ))
  -- along `σ → 1⁺`, `g σ = (σ - 1) H σ = σ - 1 → 0`, so `g 1 = 0`
  have hlim : Tendsto (fun σ : ℝ => g σ) (𝓝[>] 1) (𝓝 (g 1)) :=
    hga.continuousAt.tendsto.comp (hpath.mono_right nhdsWithin_le_nhds)
  have heq : ∀ᶠ σ : ℝ in 𝓝[>] 1, g σ = (σ : ℂ) - 1 := by
    filter_upwards [hpath.eventually hg, self_mem_nhdsWithin] with σ h1 h2
    have hσ : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (ne_of_gt h2))
    rw [hH1 σ h2, zpow_neg_one, smul_eq_mul] at h1
    field_simp at h1
    exact h1.symm
  have hlim2 : Tendsto (fun σ : ℝ => (σ : ℂ) - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun σ : ℝ => (σ : ℂ) - 1) (𝓝 1) (𝓝 ((1 : ℝ) - 1 : ℂ)) :=
      ((Complex.continuous_ofReal.sub continuous_const).tendsto 1)
    simpa using this.mono_left nhdsWithin_le_nhds
  exact hg1 (tendsto_nhds_unique (hlim.congr' heq) hlim2)

/-- `IsTensorSimple.neg_one_le_meromorphicOrderAt` at `ζ`. -/
example : -1 ≤ meromorphicOrderAt riemannZeta 1 :=
  isTensorSimple_zeta.neg_one_le_meromorphicOrderAt isLSeriesContinuation_zeta

end SelbergClassTest
