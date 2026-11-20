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


















theorem fkc_edgeConfig_interface_ge (hci : fis_CrossInterface G H K) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      ≤ ecz_fkZEdge K p q := by
  classical
  
  let glue : ecz_ClosedOff G → ecz_ClosedOff H → ecz_ClosedOff K :=
    fun σ τ => ⟨fsm_combine σ.val τ.val, ecz_combine_closedOff hci σ τ⟩
  
  
  have hprod : (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      = ∑ στ : ecz_ClosedOff G × ecz_ClosedOff H, fkWeight K p q (glue στ.1 στ.2).val := by
    rw [ecz_fkZEdge, ecz_fkZEdge, Fintype.sum_mul_sum, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    show _ = fkWeight K p q (fsm_combine σ.val τ.val)
    rw [fis_fkWeight_combine hci p q σ.val τ.val]
  rw [hprod]
  
  have hinj : Function.Injective
      (fun στ : ecz_ClosedOff G × ecz_ClosedOff H => glue στ.1 στ.2) := by
    rintro ⟨σ₁, τ₁⟩ ⟨σ₂, τ₂⟩ h
    have heq : fsm_combine σ₁.val τ₁.val = fsm_combine σ₂.val τ₂.val := congrArg Subtype.val h
    have h2 : ((σ₁.val, τ₁.val) : (Sym2 V → Bool) × (Sym2 W → Bool)) = (σ₂.val, τ₂.val) :=
      fsm_combine_injective heq
    rw [Prod.mk.injEq] at h2
    exact Prod.ext (Subtype.ext h2.1) (Subtype.ext h2.2)
  
  rw [ecz_fkZEdge,
    show (∑ στ : ecz_ClosedOff G × ecz_ClosedOff H, fkWeight K p q (glue στ.1 στ.2).val)
        = ∑ ω ∈ Finset.univ.image (fun στ : ecz_ClosedOff G × ecz_ClosedOff H => glue στ.1 στ.2),
            fkWeight K p q ω.val from by
      rw [Finset.sum_image]; intro a _ b _ h; exact hinj h]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro ω _ _
  exact fkWeight_nonneg K hp hp1 hq ω.val








theorem fkc_neglog_edgeConfig_interface_le (hci : fis_CrossInterface G H K) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    - Real.log (ecz_fkZEdge K p q)
      ≤ - Real.log (ecz_fkZEdge G p q) + - Real.log (ecz_fkZEdge H p q)
        - (fis_interface G H K).card * Real.log (1 - p) := by
  have hZG : 0 < ecz_fkZEdge G p q := ecz_fkZEdge_pos G hp hp1 hq
  have hZH : 0 < ecz_fkZEdge H p q := ecz_fkZEdge_pos H hp hp1 hq
  have hZK : 0 < ecz_fkZEdge K p q := ecz_fkZEdge_pos K hp hp1 hq
  have h1mp : (0:ℝ) < 1 - p := by linarith
  have hge : (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      ≤ ecz_fkZEdge K p q := fkc_edgeConfig_interface_ge hci hp hp1 hq
  have hpos : 0 < (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q) :=
    mul_pos (pow_pos h1mp _) (mul_pos hZG hZH)
  have hlog : Real.log ((1 - p) ^ (fis_interface G H K).card
        * (ecz_fkZEdge G p q * ecz_fkZEdge H p q))
      ≤ Real.log (ecz_fkZEdge K p q) := Real.log_le_log hpos hge
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hZG.ne' hZH.ne',
    Real.log_pow] at hlog
  linarith






theorem fkc_factorisation_load_bearing (hci : fis_CrossInterface G H K) (p q : ℝ) :
    (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      = ∑ στ : ecz_ClosedOff G × ecz_ClosedOff H,
          fkWeight K p q (fsm_combine στ.1.val στ.2.val) := by
  classical
  rw [ecz_fkZEdge, ecz_fkZEdge, Fintype.sum_mul_sum, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [fis_fkWeight_combine hci p q σ.val τ.val]

end Interface











theorem fkc_crossInterface_realisable {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] :
    fis_CrossInterface (⊥ : SimpleGraph V) (⊥ : SimpleGraph W)
      (⊥ : SimpleGraph (V ⊕ W)) :=
  fis_crossInterface_satisfiable

end StatMech.Walls
