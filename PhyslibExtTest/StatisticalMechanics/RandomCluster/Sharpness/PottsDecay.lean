/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PottsDecay

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PottsDecay`

* `ofa_summary` on the complete graph on `Fin 2` for the empty event on `[1/4, 3/4]` with
  `κ = 1/2`: `hbridge` and `hθub` are discharged, so the conditional hypotheses are
  satisfiable;
* `ofa_fk_q2_differential_inequality` applied to the empty event on `K₂` at `p = 1/2`;
* `ofa_fk_q2_sharpness` in its conditional form (all hypotheses as binders).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.PottsDecay

open Set Filter Topology
open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.OSFKAssemblyClose
open _root_.StatMech.FK _root_.StatMech.OSSS.BetaCMatch

/-- The bridge identity holds for the empty event: every covariance vanishes. -/
theorem bridge_empty (x : ℝ) :
    ∑ e, fkCov (⊤ : SimpleGraph (Fin 2)) x 2
        ((∅ : Set (ConfigSpace (Sym2 (Fin 2)))).indicator (fun _ => (1 : ℝ))) (FK.coord e)
      = ∑ e ∈ (⊤ : SimpleGraph (Fin 2)).edgeFinset, fkCov ⊤ x 2
        ((∅ : Set (ConfigSpace (Sym2 (Fin 2)))).indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
  simp [fkCov, fkMean]

-- Non-vacuity: the hypotheses of `ofa_summary` hold for the empty event on `K₂`.
example :
    (fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 4) 2 ∅
        * (1 - fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 4) 2 ∅)
        ≤ ∑ e, fkCov (⊤ : SimpleGraph (Fin 2)) (1 / 4) 2
          ((∅ : Set (ConfigSpace (Sym2 (Fin 2)))).indicator (fun _ => (1 : ℝ))) (FK.coord e))
      ∧ fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 4) 2 ∅
        ≤ Real.exp (-(4 * (1 / 2) * (3 / 4 - 1 / 4))) :=
  ofa_summary ⊤ ∅ isUpperSet_empty (1 / 4) (3 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun x _ => bridge_empty x)
    (fun x _ => by simp [fkProbOf, fkMean]; norm_num)

-- The `q = 2` differential inequality for the empty event on `K₂` at `p = 1/2`.
example :
    russoPrefactor (1 / 2) * (fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 ∅
        * (1 - fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 ∅))
      ≤ deriv (fun p => fkProbOf (⊤ : SimpleGraph (Fin 2)) p 2 ∅) (1 / 2) :=
  ofa_fk_q2_differential_inequality ⊤ (by norm_num) (by norm_num) ∅ isUpperSet_empty
    (bridge_empty _)

-- The full sharpness package, conditional on its hypotheses.
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hbridge : ∀ x ∈ Icc a b,
        ∑ e, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
          = ∑ e ∈ G.edgeFinset, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    (hθub : ∀ x ∈ Icc a b, fkProbOf G x 2 A ≤ 1 - κ)
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hboundMF : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β')
    (Θ : ℝ → ℝ) (β₁ : ℝ)
    (hP1 : ∀ b₀, b₀ < β₁ → Θ b₀ = 0)
    (hP2 : ∀ b₀, β₁ < b₀ → 0 < Θ b₀) :
    sSup (bcm_subcriticalSet Θ) = β₁ :=
  (ofa_fk_q2_sharpness G A hA a b κ hab ha0 hb1 hκ hbridge hθub T mseq β' β fβ fβ' m hββ hm1
    hTβ hTβ' hmlim hboundMF Θ β₁ hP1 hP2).2.2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.PottsDecay
