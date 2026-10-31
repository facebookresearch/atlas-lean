/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.Assembly

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.Assembly`

* `lind_var_indicator` for the constant indicator `1` under the random-cluster mass on `K₂`;
* `fk_poincare_indicator` (unconditional) on `K₂` at `p = 1/2`, `q = 2` for the increasing event
  "edge `s(0, 1)` is open";
* `fk_q2_crossing_decay_poincare`, conditional on `hbridge` and `hθub`, applied on `K₂`;
* `fk_sharpness_both`, the conditional decay and mean-field bounds, stated as a term.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.Assembly

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.FK Set Filter Topology

-- The Lindeberg variance of an indicator is `m (1 - m)`; here the constant `1` has variance `0`.
example :
    Lindeberg.var (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) (fun _ => 1)
      = Lindeberg.mean (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) (fun _ => 1)
        * (1 - Lindeberg.mean (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
          (fun _ => 1)) :=
  lind_var_indicator _ (fun _ => Or.inr rfl)

-- The Poincaré inequality for the increasing event "`s(0, 1)` is open" on `K₂`.
example :
    fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 {ω | ω (s(0, 1) : Sym2 (Fin 2)) = true}
        * (1 - fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2
          {ω | ω (s(0, 1) : Sym2 (Fin 2)) = true})
      ≤ ∑ e, fkCov (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2
          ({ω | ω (s(0, 1) : Sym2 (Fin 2)) = true}.indicator (fun _ => (1 : ℝ))) (FK.coord e) :=
  fk_poincare_indicator ⊤ (by norm_num) (by norm_num) (by norm_num) _
    (fun a b hab ha => by
      have h := hab s(0, 1)
      rw [show a s(0, 1) = true from ha] at h
      exact Bool.eq_true_of_true_le h)

-- The `q = 2` crossing decay on `K₂` on the window `[1/4, 3/4]`, given its two hypotheses.
example (A : Set (ConfigSpace (Sym2 (Fin 2)))) (hA : IsIncreasing A) (κ : ℝ) (hκ : 0 < κ)
    (hbridge : ∀ p ∈ Icc (1 / 4 : ℝ) (3 / 4),
      ∑ e, fkCov (⊤ : SimpleGraph (Fin 2)) p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
        = ∑ e ∈ (⊤ : SimpleGraph (Fin 2)).edgeFinset,
            fkCov ⊤ p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    (hθub : ∀ p ∈ Icc (1 / 4 : ℝ) (3 / 4), fkProbOf (⊤ : SimpleGraph (Fin 2)) p 2 A ≤ 1 - κ) :
    fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 4) 2 A ≤ Real.exp (-(4 * κ * (3 / 4 - 1 / 4))) :=
  fk_q2_crossing_decay_poincare ⊤ A hA _ _ κ (by norm_num) (by norm_num) (by norm_num) hκ
    hbridge hθub

-- The combined decay and mean-field statement elaborates with its full hypothesis list.
example := @fk_sharpness_both

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.Assembly
