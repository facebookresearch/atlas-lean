/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.FK.RandomCluster
import Code.FK.SuperMultiplicative
import Code.FK.FKInterfaceSubadd
import Code.FK.EdgeConfigZ
import Code.Walls.fkc_rqinterface

open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false

namespace StatMech.Walls

open StatMech StatMech.FK







section Interface
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)} [DecidableRel K.Adj]












theorem fc_clusterCount_splits (hci : fis_CrossInterface G H K)
    (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    numClusters K (fsm_combine σ τ) = numClusters G σ + numClusters H τ :=
  fis_numClusters_combine hci σ τ










theorem fc_factorisation_is_engine (hci : fis_CrossInterface G H K) (p q : ℝ)
    (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    fkWeight K p q (fsm_combine σ τ)
      = (1 - p) ^ (fis_interface G H K).card * (fkWeight G p q σ * fkWeight H p q τ) :=
  fis_fkWeight_combine hci p q σ τ
















theorem fc_interface_ge (hci : fis_CrossInterface G H K) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      ≤ ecz_fkZEdge K p q :=
  fkc_edgeConfig_interface_ge hci hp hp1 hq








theorem fc_neglog_interface_le (hci : fis_CrossInterface G H K) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    - Real.log (ecz_fkZEdge K p q)
      ≤ - Real.log (ecz_fkZEdge G p q) + - Real.log (ecz_fkZEdge H p q)
        - (fis_interface G H K).card * Real.log (1 - p) :=
  fkc_neglog_edgeConfig_interface_le hci hp hp1 hq






theorem fc_lhs_eq_glued_sum (hci : fis_CrossInterface G H K) (p q : ℝ) :
    (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      = ∑ στ : ecz_ClosedOff G × ecz_ClosedOff H,
          fkWeight K p q (fsm_combine στ.1.val στ.2.val) :=
  fkc_factorisation_load_bearing hci p q

end Interface










theorem fc_interface_realisable {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] :
    fis_CrossInterface (⊥ : SimpleGraph V) (⊥ : SimpleGraph W)
      (⊥ : SimpleGraph (V ⊕ W)) :=
  fkc_crossInterface_realisable

end StatMech.Walls
