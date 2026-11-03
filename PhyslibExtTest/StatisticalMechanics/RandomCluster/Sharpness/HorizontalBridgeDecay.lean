/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.HorizontalBridgeDecay

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.HorizontalBridgeDecay`

* `flipE` on a concrete configuration (`flipE_self`, `flipE_flipE`) and `coord_add_flip`;
* `hbg_connEvent_bridge` (unconditional) on the complete graph on `Fin 2` at `p = 1/2`, `q = 2`:
  the diagonal "edges" `s(0, 0)`, `s(1, 1)` lie off the graph and drop out of the covariance sum;
* `hbg_fk_q2_subcritical_decay_connEvent`, conditional on `hθub`, on the same graph.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.HorizontalBridgeDecay

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.OSSS _root_.StatMech.OSSS.HBridgeClose
open Set

-- Flipping `s(0, 1)` in the all-open configuration closes it, and flipping twice is the identity.
example :
    flipE (s(0, 1) : Sym2 (Fin 2)) (fun _ => true) s(0, 1) = false ∧
      flipE (s(0, 1) : Sym2 (Fin 2)) (flipE s(0, 1) (fun _ => true)) = fun _ => true :=
  ⟨by simp, flipE_flipE _ _⟩

-- An edge coordinate and its flip add up to one.
example (ω : ConfigSpace (Sym2 (Fin 2))) : coord s(0, 1) ω + coord s(0, 1) (flipE s(0, 1) ω) = 1 :=
  coord_add_flip _ ω

-- The bridge identity for the connection event `0 ↔ 1` on `K₂`.
example :
    ∑ e, fkCov (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2
        ((connEvent (⊤ : SimpleGraph (Fin 2)) 0 1).indicator (fun _ => (1 : ℝ))) (coord e)
      = ∑ e ∈ (⊤ : SimpleGraph (Fin 2)).edgeFinset,
          fkCov ⊤ (1 / 2) 2 ((connEvent ⊤ 0 1).indicator (fun _ => (1 : ℝ))) (coord e) :=
  hbg_connEvent_bridge ⊤ (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num) 0 1

-- Exponential decay of `P(0 ↔ 1)` on `K₂` over `[1/4, 3/4]`, given the uniform upper bound.
example (κ : ℝ) (hκ : 0 < κ)
    (hθub : ∀ s ∈ Icc (1 / 4 : ℝ) (3 / 4),
      fkProbOf (⊤ : SimpleGraph (Fin 2)) s 2 (connEvent ⊤ 0 1) ≤ 1 - κ) :
    fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 4) 2 (connEvent ⊤ 0 1)
      ≤ Real.exp (-(4 * κ * (3 / 4 - 1 / 4))) :=
  hbg_fk_q2_subcritical_decay_connEvent ⊤ 0 1 _ _ κ (by norm_num) (by norm_num) (by norm_num) hκ
    hθub

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.HorizontalBridgeDecay
