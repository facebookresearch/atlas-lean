/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.BayesianDirichletScore
public import Mathlib.Tactic.NormNum

/-!
# Bayesian–Dirichlet score tests

Two binary variables `false, true`. The structure `false → true` has the covered edge
`false → true` (the parents of `true` are `false` plus the parents of `false`); reversing it
gives `true → false`, so the two one-edge structures have the same BDe score. The rising
factorial is `1` at `n = 0` (no data) and `a` at `n = 1`. Counts are checked on a two-case data
set; the empty variable set is matched by every case.
-/

namespace Cslib.MachineLearning.GraphicalModels.BayesianDirichlet

private abbrev σ2 : Bool → Type := fun _ => Bool

private def paFT : Bool → Finset Bool := fun v => if v then {false} else ∅

private def paTF : Bool → Finset Bool := fun v => if v then ∅ else {true}

example (a : ℝ) : rising a 0 = 1 := by simp [rising]

example (a : ℝ) : rising a 1 = a := by simp [rising]

example (a : ℝ) : rising a 2 = a * (a + 1) := by
  simp [rising, ascPochhammer_succ_eval]

/-- Reversing the covered edge `false → true` of `paFT` gives `paTF`. -/
theorem coveredReversal_FT_TF : CoveredReversal paFT paTF := by
  refine ⟨false, true, by decide, by decide, ?_⟩
  funext v
  cases v <;> rfl

/-- The two one-edge structures on two binary variables have the same BDe score, for any
positive prior and equivalent sample size. -/
example (p : ((v : Bool) → σ2 v) → ℝ) (hp : ∀ x, 0 < p x) (D : List ((v : Bool) → σ2 v)) :
    bdeScore p 1 D paTF = bdeScore p 1 D paFT :=
  bdeScore_coveredReversal p hp one_pos D coveredReversal_FT_TF

private def caseTT : (v : Bool) → σ2 v := fun _ => true
private def caseFT : (v : Bool) → σ2 v := fun v => v

/-- Every case matches the empty configuration. -/
example (c : Config σ2 ∅) : count [caseTT, caseFT] ∅ c = 2 := by
  simp [count, Subsingleton.elim _ c]

/-- `N_j = ∑_k N_jk` on the example. -/
example (j : Config σ2 {false}) :
    ∑ c with Finset.restrict₂ (Finset.subset_insert true {false}) c = j,
      count [caseTT, caseFT] (insert true {false}) c = count [caseTT, caseFT] {false} j :=
  sum_count_restrict₂ _ _ j

/-- The BD score equals the sequential prediction probability. -/
example (α : (v : Bool) → Config σ2 (insert v (paFT v)) → ℝ) :
    seqProb paFT α [caseTT, caseFT] = bdScore [caseTT, caseFT] paFT α :=
  seqProb_eq_bdScore paFT α _

/-- The score does not depend on the order of the cases. -/
example (α : (v : Bool) → Config σ2 (insert v (paFT v)) → ℝ) :
    seqProb paFT α [caseTT, caseFT] = seqProb paFT α [caseFT, caseTT] := by
  have h : ∀ S c, count [caseTT, caseFT] S c = count [caseFT, caseTT] S c := fun _ _ =>
    (List.Perm.swap caseFT caseTT []).countP_eq _
  rw [seqProb_eq_bdScore, seqProb_eq_bdScore]
  simp only [bdScore, bdFamily, h]

/-- With no data every family score is `1`. -/
example (α : (v : Bool) → Config σ2 (insert v (paFT v)) → ℝ) : bdScore [] paFT α = 1 := by
  simp [bdScore, bdFamily, count, rising]

end Cslib.MachineLearning.GraphicalModels.BayesianDirichlet
