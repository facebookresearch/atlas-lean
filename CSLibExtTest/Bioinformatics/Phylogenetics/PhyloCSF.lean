/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.PhyloCSF
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# PhyloCSF tests

Two leaves on a cherry over `S = Bool`, with transition matrices `P_C` (stay with weight `9/10`)
for the coding model and `P_N` (uniform `1/2`) for the non-coding one, and uniform root
distributions. Both models give positive site likelihoods (the non-vacuity witness of the
hypotheses of `weighted_power_le_scoreTest`); for the column `(true, true)` the site likelihoods are
`41/100` and `1/4`, so the one-column score is `log (41/25) > 0` and the column is called coding
at cutoff `0`. The theorem instance below compares the threshold test with the test that never
calls coding.
-/

namespace Cslib.Bioinformatics.Phylogenetics.PhyloCSF

open Cslib.Bioinformatics.Phylogenetics.FelsensteinPruning

/-- Coding-model transitions: stay with weight `9/10`. -/
noncomputable def PC : Bool → Bool → ℝ := fun a b => if a = b then 9 / 10 else 1 / 10

/-- Non-coding-model transitions: uniform. -/
noncomputable def PN : Bool → Bool → ℝ := fun _ _ => 1 / 2

/-- A cherry with leaves `false` and `true`. -/
noncomputable def cherry (P : Bool → Bool → ℝ) : FelsensteinPruning.Tree Bool Bool ℝ :=
  FelsensteinPruning.Tree.node P (FelsensteinPruning.Tree.leaf false) P
    (FelsensteinPruning.Tree.leaf true)

/-- Uniform root distribution. -/
noncomputable def unif : Bool → ℝ := fun _ => 1 / 2

private theorem siteLik_cherry (P : Bool → Bool → ℝ) (col : Bool → Bool) :
    siteLik (cherry P) unif col =
      1 / 2 * (P false (col false) * P false (col true)) +
        1 / 2 * (P true (col false) * P true (col true)) := by
  rw [siteLik_eq_sum_prune]
  simp [cherry, prune, leafData, unif]
  ring

theorem siteLik_C_pos (col : Bool → Bool) : 0 < siteLik (cherry PC) unif col := by
  rw [siteLik_cherry]
  have h : ∀ a b, 0 < PC a b := fun a b => by unfold PC; split_ifs <;> norm_num
  have := h false (col false); have := h false (col true)
  have := h true (col false); have := h true (col true)
  positivity

theorem siteLik_N_pos (col : Bool → Bool) : 0 < siteLik (cherry PN) unif col := by
  rw [siteLik_cherry]; norm_num [PN]

example : siteLik (cherry PC) unif (fun _ => true) = 41 / 100 := by
  rw [siteLik_cherry]; norm_num [PC]

example : siteLik (cherry PN) unif (fun _ => true) = 1 / 4 := by
  rw [siteLik_cherry]; norm_num [PN]

/-- The one-column alignment `(true, true)` scores `log (41/25) > 0`. -/
example : 0 < score (cherry PC) unif (cherry PN) unif (fun (_ : Fin 1) _ => true) := by
  have hC : siteLik (cherry PC) unif (fun _ => true) = 41 / 100 := by
    rw [siteLik_cherry]; norm_num [PC]
  have hN : siteLik (cherry PN) unif (fun _ => true) = 1 / 4 := by
    rw [siteLik_cherry]; norm_num [PN]
  simp only [score, Fin.sum_univ_one, hC, hN]
  exact Real.log_pos (by norm_num)

/-- The threshold test has at least as much weighted power as never calling coding. -/
example (c : ℝ) :
    ∑ A : Fin 1 → Bool → Bool, (0 : ℝ) * alignLik (cherry PC) unif A ≤
      ∑ A : Fin 1 → Bool → Bool,
        (scoreTest (cherry PC) unif (cherry PN) unif c A).val * alignLik (cherry PC) unif A :=
  weighted_power_le_scoreTest siteLik_C_pos siteLik_N_pos c (fun _ => ⟨0, le_rfl, by norm_num⟩)
    (Finset.sum_le_sum fun A _ => by
      simp only [zero_mul]
      exact mul_nonneg (scoreTest _ _ _ _ c A).2.1
        (Finset.prod_pos fun k _ => siteLik_N_pos (A k)).le)

end Cslib.Bioinformatics.Phylogenetics.PhyloCSF
