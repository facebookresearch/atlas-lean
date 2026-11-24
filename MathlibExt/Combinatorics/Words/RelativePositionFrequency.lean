/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords
import MathlibExt.Data.Set.Density

/-!
# Relative position and letter frequency

In a binary word with positive frequencies for both letters, the normalized relative position
tends to the difference of their reciprocal frequencies.
-/

namespace MetaMathlibExt

open Filter Topology

namespace tendsto_relativePosition_div_of_frequency

private theorem tendsto_letterPosition_div {w : ℕ → Bool} {α : Bool} {d : ℝ} (hd : 0 < d)
    (hfreq : Tendsto (fun m : ℕ => (letterCount w α m : ℝ) / m) atTop (𝓝 d)) :
    Tendsto (fun n : ℕ => (letterPosition w α n : ℝ) / n) atTop (𝓝 (1 / d)) := by
  let p := fun i => w i = α
  have hinf : (Set.ofPred p).Infinite := by
    apply Nat.infinite_of_hasDensity_pos (α := d) _ hd.ne'
    apply hfreq.congr
    intro m
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat, letterCount,
      ← Set.ncard_coe_finset, Finset.coe_filter, Finset.mem_range]
    rw [Set.inter_comm]
    rfl
  -- The prefix ending just after occurrence number n + 1 contains exactly n + 1 copies.
  have hcount (n : ℕ) : letterCount w α (Nat.nth p n + 1) = n + 1 := by
    simpa only [letterCount, ← Nat.count_eq_card_filter_range] using
      Nat.count_nth_succ_of_infinite hinf n
  have hsub := hfreq.comp ((tendsto_add_atTop_nat 1).comp (Nat.nth_strictMono hinf).tendsto_atTop)
  have hrecip := hsub.inv₀ hd.ne'
  simp only [Function.comp_apply, hcount, inv_div] at hrecip
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa [letterPosition, p, add_div, one_div] using
    hrecip.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end tendsto_relativePosition_div_of_frequency

open tendsto_relativePosition_div_of_frequency in
/-- **Relative position of a word with given letter frequency.** Let
$w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite word over the letters $a$ and $b$. Let $\#_b(m)$
be the number of letters $b$ among $\ell_0, \ldots, \ell_{m-1}$, and for $n \ge 1$ let
$r(n) = p_b(n) - p_a(n)$, where $p_\alpha(n)$ is the position of the $n$-th occurrence of the
letter $\alpha$ in $w$, counting positions from $0$. If $0 < d < 1$ and $\#_b(m)/m \to d$ as
$m \to \infty$, then $r(n)/n \to 1/d - 1/(1-d)$ as $n \to \infty$.

Such a word contains both letters infinitely often, so no separate hypothesis that both letters
occur infinitely often is needed.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 31
(`jis-2025-25.1.5-cor-31`). -/
public theorem tendsto_relativePosition_div_of_frequency {w : ℕ → Bool} {d : ℝ}
    (hd₀ : 0 < d) (hd₁ : d < 1)
    (hfreq : Tendsto (fun m : ℕ => (letterCount w false m : ℝ) / m) atTop (𝓝 d)) :
    Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 (1 / d - 1 / (1 - d))) := by
  have hsum (m : ℕ) : letterCount w true m + letterCount w false m = m := by
    simpa [letterCount] using
      (Finset.range m).card_filter_add_card_filter_not (fun i => w i = true)
  have ha : Tendsto (fun m : ℕ => (letterCount w true m : ℝ) / m) atTop (𝓝 (1 - d)) := by
    apply (tendsto_const_nhds.sub hfreq).congr'
    filter_upwards [eventually_ne_atTop 0] with m hm
    have h : (letterCount w true m : ℝ) + letterCount w false m = m := by exact_mod_cast hsum m
    rw [eq_sub_of_add_eq h, sub_div, div_self (Nat.cast_ne_zero.mpr hm)]
  have hbPos := tendsto_letterPosition_div hd₀ hfreq
  have haPos := tendsto_letterPosition_div (sub_pos.mpr hd₁) ha
  simpa [relativePosition, sub_div] using hbPos.sub haPos

end MetaMathlibExt
