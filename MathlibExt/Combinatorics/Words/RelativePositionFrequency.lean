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

/-- **Letter frequency and growth of letter positions.** Let $w = \ell_0 \ell_1 \ell_2 \cdots$ be
an infinite word over the letters $a$ and $b$ in which both letters occur infinitely often, and
let $\alpha$ be a letter. Write $\#_\alpha(m)$ for the number of occurrences of $\alpha$ among
$\ell_0, \ldots, \ell_{m-1}$, and for $n \ge 1$ write $p_\alpha(n)$ for the position of the
$n$-th occurrence of $\alpha$ in $w$, counting positions from $0$. Then (a) for every real $d$
with $0 < d \le 1$, $\#_\alpha(m)/m \to d$ as $m \to \infty$ if and only if
$p_\alpha(n)/n \to 1/d$ as $n \to \infty$; and (b) $\#_\alpha(m)/m \to 0$ as $m \to \infty$ if and
only if $p_\alpha(n)/n \to \infty$ as $n \to \infty$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 28
(`jis-2025-25.1.5-lem-28`). -/
public theorem tendsto_letterCount_div_iff_tendsto_letterPosition_div {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (α : Bool) :
    (∀ d : ℝ, 0 < d → d ≤ 1 →
      (Tendsto (fun m : ℕ => (letterCount w α m : ℝ) / m) atTop (𝓝 d) ↔
        Tendsto (fun n : ℕ => (letterPosition w α n : ℝ) / n) atTop (𝓝 (1 / d)))) ∧
      (Tendsto (fun m : ℕ => (letterCount w α m : ℝ) / m) atTop (𝓝 0) ↔
        Tendsto (fun n : ℕ => (letterPosition w α n : ℝ) / n) atTop atTop) := by
  let p : ℕ → Prop := fun i => w i = α
  let t := letterCount w α
  let r (n : ℕ) : ℝ := (letterPosition w α n : ℝ) / n
  have hp : (Set.ofPred p).Infinite := by
    cases α with
    | false => exact hw.2
    | true => exact hw.1
  have ht_eq (m : ℕ) : t m = Nat.count p m := (Nat.count_eq_card_filter_range p m).symm
  have ht : Tendsto t atTop atTop := by
    rw [show t = Nat.count p from funext ht_eq]
    exact (Nat.count_monotone p).tendsto_atTop_atTop fun k =>
      ⟨Nat.nth p k, (Nat.count_nth_of_infinite hp k).ge⟩
  have ht_pos : ∀ᶠ m in atTop, 0 < t m := tendsto_atTop.1 ht 1
  -- Sample just after the (n + 1)-st occurrence to recover its position from the frequency.
  let s (n : ℕ) := Nat.nth p n + 1
  have hs : Tendsto s atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (Nat.nth_strictMono hp).tendsto_atTop
  have hs_count (n : ℕ) : t (s n) = n + 1 := by
    rw [ht_eq, Nat.count_nth_succ_of_infinite hp n]
  have hsample (n : ℕ) : r (n + 1) = ((t (s n) : ℝ) / (s n : ℝ))⁻¹ - 1 / ((n : ℝ) + 1) := by
    rw [inv_div, hs_count]
    simp only [r, s, Nat.cast_add, Nat.cast_one, letterPosition, Nat.add_sub_cancel,
      add_div, add_sub_cancel_right]
    rfl
  have hsmall := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- A prefix of length m contains occurrence t m, but not occurrence t m + 1.
  have hlower : ∀ᶠ m in atTop, r (t m) ≤ (m : ℝ) / t m := by
    filter_upwards [ht_pos] with m hm
    have h : letterPosition w α (t m) < m := by
      change Nat.nth p (t m - 1) < m
      apply Nat.nth_lt_of_lt_count
      rw [← ht_eq]
      omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast h.le) (Nat.cast_nonneg _)
  refine ⟨fun d hd _ => ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hfreq
    apply (tendsto_add_atTop_iff_nat 1).mp
    have h := ((hfreq.comp hs).inv₀ hd.ne').sub hsmall
    simpa only [sub_zero, one_div] using h.congr fun n => (hsample n).symm
  · intro hpos
    have hfactor : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      rw [Nat.cast_add, Nat.cast_one, add_div, div_self (Nat.cast_ne_zero.mpr hn)]
    have hupper : ∀ᶠ m : ℕ in atTop,
        (m : ℝ) / t m ≤ r (t m + 1) * (((t m + 1 : ℕ) : ℝ) / t m) := by
      have h (m : ℕ) : m ≤ letterPosition w α (t m + 1) := by
        simpa only [letterPosition, Nat.add_sub_cancel, ht_eq] using Nat.le_nth_count hp m
      filter_upwards [] with m
      dsimp only [r]
      rw [← mul_div_assoc, div_mul_cancel₀ _ (by positivity)]
      exact div_le_div_of_nonneg_right (by exact_mod_cast h m) (Nat.cast_nonneg _)
    have hu := (hpos.comp ((tendsto_add_atTop_nat 1).comp ht)).mul (hfactor.comp ht)
    rw [mul_one] at hu
    have h := tendsto_of_tendsto_of_tendsto_of_le_of_le' (hpos.comp ht) hu hlower hupper
    simpa only [one_div, inv_inv, inv_div] using h.inv₀ (by positivity : (1 / d : ℝ) ≠ 0)
  · intro hfreq
    have hfreq_pos : ∀ᶠ m in atTop, 0 < (t m : ℝ) / m := by
      filter_upwards [ht_pos, eventually_gt_atTop (0 : ℕ)] with m hm hm'
      exact div_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hm')
    have hright : Tendsto (fun m : ℕ => (t m : ℝ) / m) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hfreq, hfreq_pos⟩
    have hrecip := (hright.comp hs).inv_tendsto_nhdsGT_zero
    apply (tendsto_add_atTop_iff_nat 1).mp
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-1 : ℝ) hrecip)
    filter_upwards [hsmall.eventually_lt_const zero_lt_one] with n hn
    change ((t (s n) : ℝ) / (s n : ℝ))⁻¹ + (-1) ≤ r (n + 1)
    rw [hsample, ← sub_eq_add_neg]
    exact sub_le_sub_left hn.le _
  · intro hpos
    have h := tendsto_atTop_mono' atTop hlower (hpos.comp ht)
    have hi : Tendsto (fun m : ℕ => ((m : ℝ) / t m)⁻¹) atTop (𝓝 0) := h.inv_tendsto_atTop
    simpa only [inv_div] using hi

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
