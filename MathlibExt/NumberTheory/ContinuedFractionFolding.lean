/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.Ring.Real
public import MathlibExt.Combinatorics.InfiniteWord.CloitreSequence

import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Digit frequencies in Cloitre's approximants

The proportions of digits `1` and `2` in Cloitre's finite approximants tend to `2/3` and `1/3`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 17.
-/

namespace MetaMathlibExt

private theorem cloitreApprox_structure (k : ℕ) :
    ∃ l : List ℕ, cloitreApprox (k + 2) = [1, 1] ++ l ++ [1, 1] ∧
      l.count 1 = 2 * l.count 2 ∧ l.length = 3 * l.count 2 ∧ k ≤ l.length := by
  induction k with
  | zero =>
      exact ⟨[2, 1, 1], rfl, by decide, by decide, by decide⟩
  | succ k ih =>
      obtain ⟨l, hl, hcount, hlength, hbound⟩ := ih
      refine ⟨l ++ [1, 1, 2] ++ l.reverse, ?_, ?_, ?_, ?_⟩
      · change cloitreApprox (k + 2) ++ cloitreMirror (cloitreApprox (k + 2)) = _
        simp [hl, cloitreMirror, cloitreComplementFirst, List.reverse_append, List.append_assoc]
      · simp only [List.count_append, List.count_reverse]
        norm_num
        omega
      · simp only [List.length_append, List.length_reverse, List.count_append, List.count_reverse]
        norm_num
        omega
      · simp only [List.length_append, List.length_reverse]
        norm_num
        omega

private theorem cloitreApprox_statistics (k : ℕ) :
    ((cloitreApprox (k + 2)).count 1 : ℝ) =
        2 * ((cloitreApprox (k + 2)).count 2 : ℝ) + 4 ∧
      ((cloitreApprox (k + 2)).length : ℝ) =
        3 * ((cloitreApprox (k + 2)).count 2 : ℝ) + 4 ∧
      k + 4 ≤ (cloitreApprox (k + 2)).length := by
  obtain ⟨l, hl, hcount, hlength, hbound⟩ := cloitreApprox_structure k
  have hc : (l.count 1 : ℝ) = 2 * (l.count 2 : ℝ) := by exact_mod_cast hcount
  have hn : (l.length : ℝ) = 3 * (l.count 2 : ℝ) := by exact_mod_cast hlength
  simp only [hl, List.count_append, List.length_append]
  norm_num
  exact ⟨by linarith, by linarith, by omega⟩

/-- **Digit frequencies in Cloitre's approximants.** Let $A_k$ be the $k$-th approximant of
Cloitre's sequence. As $k \to \infty$, the proportion of entries of $A_k$ equal to $1$ tends to
$2/3$, and the proportion of entries equal to $2$ tends to $1/3$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 17
(`jis-2026-26.3.6-thm-17`). -/
public theorem tendsto_cloitreApprox_count_div_length :
    Filter.Tendsto (fun k => ((cloitreApprox k).count 1 : ℝ) / (cloitreApprox k).length)
        Filter.atTop (nhds (2 / 3)) ∧
      Filter.Tendsto (fun k => ((cloitreApprox k).count 2 : ℝ) / (cloitreApprox k).length)
        Filter.atTop (nhds (1 / 3)) := by
  have hg : Filter.Tendsto (fun k => ((cloitreApprox (k + 2)).length : ℝ))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro k
    exact_mod_cast (show k ≤ (cloitreApprox (k + 2)).length by
      have := (cloitreApprox_statistics k).2.2
      omega)
  have hi := tendsto_inv_atTop_zero.comp hg
  have h₁ : Filter.Tendsto (fun k => (2 / 3 : ℝ) + (4 / 3) *
      ((cloitreApprox (k + 2)).length : ℝ)⁻¹) Filter.atTop (nhds (2 / 3)) := by
    simpa using (tendsto_const_nhds (x := (2 / 3 : ℝ))).add (hi.const_mul (4 / 3))
  have h₂ : Filter.Tendsto (fun k => (1 / 3 : ℝ) - (4 / 3) *
      ((cloitreApprox (k + 2)).length : ℝ)⁻¹) Filter.atTop (nhds (1 / 3)) := by
    simpa using (tendsto_const_nhds (x := (1 / 3 : ℝ))).sub (hi.const_mul (4 / 3))
  constructor
  · apply (Filter.tendsto_add_atTop_iff_nat 2).mp
    apply h₁.congr
    intro k
    obtain ⟨hc, hl, _⟩ := cloitreApprox_statistics k
    have hn : ((cloitreApprox (k + 2)).length : ℝ) ≠ 0 := by
      have := Nat.cast_nonneg (α := ℝ) ((cloitreApprox (k + 2)).count 2)
      linarith
    field_simp [hn]
    linarith
  · apply (Filter.tendsto_add_atTop_iff_nat 2).mp
    apply h₂.congr
    intro k
    obtain ⟨_, hl, _⟩ := cloitreApprox_statistics k
    have hn : ((cloitreApprox (k + 2)).length : ℝ) ≠ 0 := by
      have := Nat.cast_nonneg (α := ℝ) ((cloitreApprox (k + 2)).count 2)
      linarith
    field_simp [hn]
    linarith

end MetaMathlibExt
