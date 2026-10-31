/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.FrontierFamilyRevealment

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.FrontierFamilyRevealment`

* `frf_familyFrontierConn_false_concrete`: the refutation of `psr_FamilyFrontierConn` on the
  library's 3-edge witness, for the one-element family with the identity order;
* `frf_revealmentMu_le_one` and `frf_avg_treeReveal_le_one` for the random-cluster mass on `K₂`
  and an arbitrary decision tree (family);
* `frf_mean_reveal_le_of_queried_imp_or` with the trivially true event `P`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.FrontierFamilyRevealment

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.FrontierFamilyClose
open _root_.StatMech.OSSS.LindebergTree _root_.StatMech.OSSS.PerScaleRevealmentClose
open _root_.StatMech.OSSS.RevealmentConstruction _root_.StatMech.OSSS.ReachDomination

-- The frontier-connection hypothesis is refuted on the explicit witness.
example :
    ¬ psr_FamilyFrontierConn (fun _ : Unit => Equiv.refl (Fin 3))
        (indicatorConn psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) ({3} : Set (Fin 4)))
        psr_witnessEndU psr_witnessEndV (fun _ => ({0} : Set (Fin 4))) :=
  frf_familyFrontierConn_false_concrete _ () rfl

-- Revealments under the random-cluster mass on `K₂` are at most one.
example (T : DecisionTree (Sym2 (Fin 2))) (e : Sym2 (Fin 2)) :
    revealmentMu (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) T e ≤ 1 :=
  frf_revealmentMu_le_one
    (fun ω => (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num) ω).le)
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num)) T e

-- The average revealment over a two-tree family on `K₂` is at most one.
example (Tf : Bool → DecisionTree (Sym2 (Fin 2))) (e : Sym2 (Fin 2)) :
    (1 / (Fintype.card Bool : ℝ))
        * ∑ k, revealmentMu (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) (Tf k) e
      ≤ 1 :=
  frf_avg_treeReveal_le_one
    (fun ω => (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num) ω).le)
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num)) Tf e

-- Revealment is bounded by `P(P) + P(Q)` when querying `e` forces `P ∨ Q`; here `P` is true.
example {E : Type*} [Fintype E] [DecidableEq E] {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (T : DecisionTree E) (e : E) :
    revealmentMu μ T e
      ≤ Lindeberg.mean μ (fun _ => if True then (1 : ℝ) else 0)
        + Lindeberg.mean μ (fun _ => if False then (1 : ℝ) else 0) :=
  frf_mean_reveal_le_of_queried_imp_or hμ0 T e (fun _ => True) (fun _ => False)
    (fun _ _ => Or.inl trivial)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.FrontierFamilyRevealment
