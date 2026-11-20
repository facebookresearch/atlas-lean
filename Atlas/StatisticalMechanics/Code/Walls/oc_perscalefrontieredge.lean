/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Code.OSSS.PerScaleRevealmentClose

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatMech

namespace Walls

open StatMech.OSSS
open StatMech.OSSS.AdaptMConditional
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.ReachBoxCrossing
open StatMech.OSSS.ReachDomination
open StatMech.OSSS.RevealmentBoxCrossing
open StatMech.OSSS.PrefixCoversClose
open StatMech.OSSS.PerScaleRevealmentClose
open StatMech.Lattice
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

section Lattice

variable {d : ℕ}






















theorem oc_perscale_frontier_edge {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k n : ℕ) (nE : ℕ) (hnE : Fintype.card E = nE)
    (hne : (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).Nonempty) :
    ∃ (σ : Fin nE ≃ E) (e : E),
      TopIncident endU endV (vertexBoundary d k) e ∧
      revealAdapt μ σ (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n)) e
        ≤ Lindeberg.mean μ
            (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                      then (1 : ℝ) else 0)
          + Lindeberg.mean μ
            (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                      then (1 : ℝ) else 0) :=
  psr_revealAdapt_le_connBox_frontier hpos hμ1 hinj hcoh hadj k n nE hnE hne







theorem oc_perscale_frontier_edge_high_pos {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {nE : ℕ} (σ : Fin nE ≃ E)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k n : ℕ)
    (hσ : ∀ e' : E, (TopIncident endU endV (vertexBoundary d k) e' ↔
        (σ.symm e' : ℕ) <
          (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card))
    (e : E)
    (he : (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card - 1
        ≤ (σ.symm e : ℕ)) :
    revealAdapt μ σ (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n)) e
      ≤ Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) :=
  psr_revealAdapt_le_connBox_of_pos hpos hμ1 σ hinj hcoh hadj k n hσ e he

end Lattice









variable {V : Type*} [DecidableEq V]




theorem oc_topIncident_of_endU_mem {endU endV : E → V} {B : Set V} {e₀ : E}
    (hmem : endU e₀ ∈ B) :
    TopIncident endU endV B e₀ :=
  Or.inl (connOpenSet_of_mem hmem)





theorem oc_frontier_edge_nonvacuous {endU endV : E → V} {B : Set V} {e₀ : E}
    (hmem : endU e₀ ∈ B) :
    (Finset.univ.filter (TopIncident endU endV B)).Nonempty :=
  ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_univ e₀, oc_topIncident_of_endU_mem hmem⟩⟩

end Walls

end StatMech
