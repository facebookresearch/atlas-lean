/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Asymptotic
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Closure properties of negligible functions

This file extends the canonical negligibility API, the `ℚ`-valued
`Cslib.Complexity.Classes.Negligible` and the real-valued
`Cslib.Crypto.Framework.NegligibleAdv` of `CSLibExt.Crypto.Framework.Asymptotic`, with the
remaining closure properties of Katz and Lindell, Proposition 3.6. Closure under addition
(`negligible_add`, `NegligibleAdv.add`) is already in that file.

* `NegligibleAdv.of_eventually_le` is the converse of `NegligibleAdv.eventually_le`, so
  `negligibleAdv_iff_eventually_le` characterizes `NegligibleAdv ε` as "`ε n ≤ 1 / n ^ c`
  eventually, for every `c`". `negligibleAdv_ratCast_iff` identifies `Negligible e` with
  `NegligibleAdv` of the real cast of `e`.
* `NegligibleAdv.const_mul` and `NegligibleAdv.mul_of_poly_bound`: a nonnegative constant
  multiple, and a product with an eventually nonnegative, eventually polynomially bounded function,
  of a negligible advantage is negligible. `negligible_const_mul` and
  `negligible_mul_of_poly_bound` are the same statements for `Negligible`.
* `NegligibleAdv.of_superpolynomialDecay` and `negligibleAdv_iff_superpolynomialDecay`: for an
  eventually nonnegative function, `NegligibleAdv` agrees with Mathlib's
  `Asymptotics.SuperpolynomialDecay atTop (fun n => (n : ℝ))`, the negligibility notion of
  upstream CSLib (`Cslib.Crypto.PRG.Family.Secure`). Mathlib's notion bounds `|ε n|`, so for
  signed functions use it directly; its closure lemmas (`SuperpolynomialDecay.add`, `.const_mul`,
  `.mul_polynomial`) need no sign hypotheses.

Both canonical predicates are one-sided upper bounds, which is why scaling needs signs: the
constant `-1` is negligible and `-1` times it is not (see the tests).

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 3.1 (Definition 3.4, Proposition 3.6).
-/

@[expose] public section

namespace Cslib.Crypto.Framework

open Cslib.Complexity.Classes Filter Topology

/-- A real function that is eventually below `1 / n ^ c` for every `c` is a negligible
advantage. This is the converse of `NegligibleAdv.eventually_le`; the rational majorant is chosen
within `1 / (n + 1) ^ n` of `ε n`. -/
theorem NegligibleAdv.of_eventually_le {ε : ℕ → ℝ}
    (h : ∀ c : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ε n ≤ 1 / (n : ℝ) ^ c) : NegligibleAdv ε := by
  have hgap : ∀ n : ℕ, ε n < ε n + 1 / ((n : ℝ) + 1) ^ n := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) ^ n := by positivity
    linarith
  choose e he using fun n => exists_rat_btwn (hgap n)
  refine ⟨e, fun c => ?_, fun n => (he n).1.le⟩
  obtain ⟨N, hN⟩ := h (c + 1)
  refine ⟨max N (c + 2), fun n hn => ?_⟩
  have hnN : N ≤ n := by omega
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hnpos : (0 : ℝ) < n := by linarith
  have hgapb : 1 / ((n : ℝ) + 1) ^ n ≤ 1 / (n : ℝ) ^ (c + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    calc (n : ℝ) ^ (c + 1) ≤ (n : ℝ) ^ n := pow_le_pow_right₀ (by linarith) (by omega)
      _ ≤ ((n : ℝ) + 1) ^ n := pow_le_pow_left₀ hnpos.le (by linarith) n
  have key : (e n : ℝ) ≤ 1 / (n : ℝ) ^ c := by
    calc (e n : ℝ) ≤ ε n + 1 / ((n : ℝ) + 1) ^ n := (he n).2.le
      _ ≤ 1 / (n : ℝ) ^ (c + 1) + 1 / (n : ℝ) ^ (c + 1) := add_le_add (hN n hnN) hgapb
      _ = (2 / n) * (1 / (n : ℝ) ^ c) := by rw [pow_succ]; field_simp; ring
      _ ≤ 1 * (1 / (n : ℝ) ^ c) := by
          gcongr
          rw [div_le_one hnpos]
          exact hn2
      _ = 1 / (n : ℝ) ^ c := one_mul _
  exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact key)

/-- `NegligibleAdv ε` holds exactly when `ε` is eventually below `1 / n ^ c` for every `c`. -/
theorem negligibleAdv_iff_eventually_le {ε : ℕ → ℝ} :
    NegligibleAdv ε ↔ ∀ c : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ε n ≤ 1 / (n : ℝ) ^ c :=
  ⟨NegligibleAdv.eventually_le, NegligibleAdv.of_eventually_le⟩

/-- A rational function is negligible exactly when its real cast is a negligible advantage. -/
theorem negligibleAdv_ratCast_iff {e : ℕ → ℚ} :
    NegligibleAdv (fun n => (e n : ℝ)) ↔ Negligible e := by
  refine ⟨fun h c => ?_, fun h => ⟨e, h, fun _ => le_rfl⟩⟩
  obtain ⟨N, hN⟩ := h.eventually_le c
  exact ⟨N, fun n hn => (Rat.cast_le (K := ℝ)).mp (by push_cast; exact hN n hn)⟩

/-- A nonnegative constant multiple of a negligible advantage is negligible
(Katz and Lindell, Proposition 3.6). -/
theorem NegligibleAdv.const_mul {ε : ℕ → ℝ} (h : NegligibleAdv ε) {a : ℝ} (ha : 0 ≤ a) :
    NegligibleAdv (fun n => a * ε n) := by
  refine NegligibleAdv.of_eventually_le fun c => ?_
  obtain ⟨M, hM⟩ := exists_nat_ge a
  obtain ⟨N, hN⟩ := h.eventually_le (c + 1)
  refine ⟨max (max N M) 1, fun n hn => ?_⟩
  have hnN : N ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have han : a ≤ n := hM.trans (by exact_mod_cast (by omega : M ≤ n))
  calc a * ε n ≤ a * (1 / (n : ℝ) ^ (c + 1)) := mul_le_mul_of_nonneg_left (hN n hnN) ha
    _ = (a / n) * (1 / (n : ℝ) ^ c) := by rw [pow_succ]; field_simp
    _ ≤ 1 * (1 / (n : ℝ) ^ c) := by
        gcongr
        rw [div_le_one hnpos]
        exact han
    _ = 1 / (n : ℝ) ^ c := one_mul _

/-- The product of a negligible advantage with a function that is eventually nonnegative and
eventually bounded by `n ^ d` is negligible (Katz and Lindell, Proposition 3.6). -/
theorem NegligibleAdv.mul_of_poly_bound {ε g : ℕ → ℝ} (h : NegligibleAdv ε) {d : ℕ}
    (hg : ∃ N : ℕ, ∀ n, N ≤ n → 0 ≤ g n ∧ g n ≤ (n : ℝ) ^ d) :
    NegligibleAdv (fun n => g n * ε n) := by
  refine NegligibleAdv.of_eventually_le fun c => ?_
  obtain ⟨Ng, hNg⟩ := hg
  obtain ⟨N, hN⟩ := h.eventually_le (c + d)
  refine ⟨max (max N Ng) 1, fun n hn => ?_⟩
  have hnN : N ≤ n := by omega
  obtain ⟨hg0, hgd⟩ := hNg n (by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc g n * ε n ≤ g n * (1 / (n : ℝ) ^ (c + d)) := mul_le_mul_of_nonneg_left (hN n hnN) hg0
    _ ≤ (n : ℝ) ^ d * (1 / (n : ℝ) ^ (c + d)) :=
        mul_le_mul_of_nonneg_right hgd (by positivity)
    _ = 1 / (n : ℝ) ^ c := by rw [pow_add]; field_simp

/-- A nonnegative constant multiple of a negligible function is negligible
(Katz and Lindell, Proposition 3.6). -/
theorem negligible_const_mul {e : ℕ → ℚ} (h : Negligible e) {a : ℚ} (ha : 0 ≤ a) :
    Negligible (fun n => a * e n) := by
  rw [← negligibleAdv_ratCast_iff] at h ⊢
  simpa using h.const_mul (a := (a : ℝ)) (by exact_mod_cast ha)

/-- The product of a negligible function with a function that is eventually nonnegative and
eventually bounded by `n ^ d` is negligible (Katz and Lindell, Proposition 3.6). -/
theorem negligible_mul_of_poly_bound {e g : ℕ → ℚ} (h : Negligible e) {d : ℕ}
    (hg : ∃ N : ℕ, ∀ n, N ≤ n → 0 ≤ g n ∧ g n ≤ (n : ℚ) ^ d) :
    Negligible (fun n => g n * e n) := by
  rw [← negligibleAdv_ratCast_iff] at h ⊢
  obtain ⟨N, hN⟩ := hg
  simpa using h.mul_of_poly_bound (g := fun n => (g n : ℝ)) ⟨N, fun n hn => by
    obtain ⟨h0, h1⟩ := hN n hn
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩⟩

/-- A function with superpolynomial decay in Mathlib's sense is a negligible advantage. -/
theorem NegligibleAdv.of_superpolynomialDecay {ε : ℕ → ℝ}
    (h : Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) ε) :
    NegligibleAdv ε := by
  refine NegligibleAdv.of_eventually_le fun c => ?_
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c * ε n ≤ 1 :=
    (h c).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨max N 1, fun n hn => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) ^ c := pow_pos (by exact_mod_cast (by omega : 0 < n)) c
  rw [le_div_iff₀ hpos, mul_comm]
  exact hN n (by omega)

/-- An eventually nonnegative negligible advantage has superpolynomial decay in Mathlib's
sense. -/
theorem NegligibleAdv.superpolynomialDecay {ε : ℕ → ℝ} (h : NegligibleAdv ε)
    (h0 : ∀ᶠ n in atTop, 0 ≤ ε n) :
    Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) ε := by
  intro k
  obtain ⟨N, hN⟩ := h.eventually_le (k + 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_ ?_
  · filter_upwards [h0] with n hn using mul_nonneg (by positivity) hn
  · filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    calc (n : ℝ) ^ k * ε n ≤ (n : ℝ) ^ k * (1 / (n : ℝ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left (hN n hnN) (by positivity)
      _ = 1 / (n : ℝ) := by rw [pow_succ]; field_simp

/-- For an eventually nonnegative function, `NegligibleAdv` is Mathlib's superpolynomial
decay. -/
theorem negligibleAdv_iff_superpolynomialDecay {ε : ℕ → ℝ} (h0 : ∀ᶠ n in atTop, 0 ≤ ε n) :
    NegligibleAdv ε ↔ Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) ε :=
  ⟨fun h => h.superpolynomialDecay h0, NegligibleAdv.of_superpolynomialDecay⟩

end Cslib.Crypto.Framework
