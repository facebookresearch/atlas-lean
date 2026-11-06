/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Subadditive
import Mathlib.Tactic.FieldSimp

/-!
# Fekete's lemma with a general normalization

For a subadditive real sequence `u`, Fekete's lemma gives `u n / n → lim` when these ratios
are bounded below. Dividing by `e n / n → c ≠ 0` gives `u n / e n → lim / c`.

## i. Overview

These are scalar hypotheses. `fkl_superMultiplicative_satisfiable` checks them together for
`u = 0`, `e n = n`; it does not establish a graph free-energy limit. In particular, the raw
random-cluster partition function sums over loop and non-edge coordinates too. Its
supermultiplicativity alone does not supply the lower bound required here. The existing
`EdgePartitionFunction` development uses the edge-restricted partition function for graph
limits instead.

## ii. Key results

- `StatMech.FK.fkl_tendsto_div_of_subadditive` : Fekete's lemma with a general normalization.
- `StatMech.FK.fkl_superMultiplicative_satisfiable` : joint scalar hypotheses and convergence.

## iii. Table of contents

- A. Fekete's lemma with a general normalization
- B. A scalar consistency witness

## iv. References

- M. Fekete, *Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit
  ganzzahligen Koeffizienten*, Math. Z. 17 (1923).
-/

@[expose] public section

open Set Filter Topology Real

namespace StatMech

namespace FK

/-! ## A. Fekete's lemma with a general normalization -/

/-- **Fekete's lemma with a general normalization.**
Fekete's lemma normalized by `e n` instead of `n`: if `u` is subadditive with `u n / n`
bounded below and `e n / n → c ≠ 0`, then `u n / e n → lim / c`. Built on Mathlib's
`Subadditive.tendsto_lim`. -/
lemma fkl_tendsto_div_of_subadditive (u : ℕ → ℝ) (hsub : Subadditive u)
    (hbdd : BddBelow (Set.range fun n => u n / n))
    (e : ℕ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (he : Tendsto (fun n => e n / n) atTop (𝓝 c)) :
    Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / c)) := by
  have hu : Tendsto (fun n => u n / n) atTop (𝓝 hsub.lim) := hsub.tendsto_lim hbdd
  have hdiv : Tendsto (fun n => (u n / n) / (e n / n)) atTop (𝓝 (hsub.lim / c)) :=
    hu.div he hc
  refine hdiv.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-! ## B. A scalar consistency witness -/

lemma fkl_subadditive_zero : Subadditive (fun _ : ℕ => (0:ℝ)) := by
  intro m n; simp

/-- **Hypotheses of the normalized Fekete lemma are satisfiable.**
The hypotheses of `fkl_tendsto_div_of_subadditive` hold together for `u = 0`, `e n = n`. -/
lemma fkl_superMultiplicative_satisfiable :
    ∃ (u : ℕ → ℝ) (hsub : Subadditive u) (e : ℕ → ℝ) (c : ℝ),
      c ≠ 0 ∧ BddBelow (Set.range fun n => u n / n)
        ∧ Tendsto (fun n => e n / n) atTop (𝓝 c)
        ∧ Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / c)) := by
  refine ⟨fun _ => (0:ℝ), fkl_subadditive_zero, fun n => (n:ℝ), 1, one_ne_zero, ?_, ?_, ?_⟩
  · exact ⟨0, by rintro x ⟨n, rfl⟩; simp⟩
  · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1:ℝ)))
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  · exact fkl_tendsto_div_of_subadditive _ fkl_subadditive_zero ⟨0, by rintro x ⟨n, rfl⟩; simp⟩
      (fun n => (n:ℝ)) 1 one_ne_zero
      (by
        refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1:ℝ)))
        filter_upwards [eventually_ne_atTop 0] with n hn
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        field_simp)

end FK

end StatMech
