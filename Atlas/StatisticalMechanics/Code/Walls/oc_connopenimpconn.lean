/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Code.OSSS.ReachBoxCrossing

open scoped BigOperators

namespace StatMech

namespace Walls

open StatMech.OSSS
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.RevealmentBoxCrossing
open StatMech.OSSS.ReachBoxCrossing
open StatMech.Lattice

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

variable {E : Type*} [Fintype E] [DecidableEq E]








section Lattice

variable {d : ℕ}







theorem oc_reachOpen_imp_connected {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    {ω : ConfigSpace E} {x y : Site d} (h : ReachOpen endU endV ω x y) :
    Connected d (liftCfg edge ω) x y :=
  reachOpen_imp_connected hinj hcoh hadj h








theorem oc_connOpenSet_imp_connectedToSet {edge : E → Sym2 (Site d)}
    (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    {ω : ConfigSpace E} {x : Site d} {B : Set (Site d)}
    (h : ConnOpenSet endU endV ω x B) : ConnectedToSet d (liftCfg edge ω) x B :=
  connOpenSet_imp_connectedToSet hinj hcoh hadj h





















theorem oc_mean_connOpen_le_connBox {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k : ℕ) (x : Site d)
    [DecidablePred (fun X => ConnOpenSet endU endV X x (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) x (vertexBoundary d k))] :
    Lindeberg.mean μ
        (fun X => if ConnOpenSet endU endV X x (vertexBoundary d k) then (1 : ℝ) else 0)
      ≤ Lindeberg.mean μ
        (fun X => if ConnectedToSet d (liftCfg edge X) x (vertexBoundary d k)
                  then (1 : ℝ) else 0) :=
  mean_indicator_mono hμ0
    (fun X => ConnOpenSet endU endV X x (vertexBoundary d k))
    (fun X => ConnectedToSet d (liftCfg edge X) x (vertexBoundary d k))
    (fun _ hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)












theorem oc_mean_connOpen_sum_le_connBox_sum {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k : ℕ) (e : E)
    [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))] :
    Lindeberg.mean μ
        (fun X => if ConnOpenSet endU endV X (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
      + Lindeberg.mean μ
        (fun X => if ConnOpenSet endU endV X (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
    ≤ Lindeberg.mean μ
        (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                  then (1 : ℝ) else 0)
      + Lindeberg.mean μ
        (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                  then (1 : ℝ) else 0) :=
  add_le_add
    (oc_mean_connOpen_le_connBox hμ0 hinj hcoh hadj k (endU e))
    (oc_mean_connOpen_le_connBox hμ0 hinj hcoh hadj k (endV e))



















theorem oc_reachProb_le_connBox_via_conversion {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k : ℕ) (e : E)
    (hfront : FrontierConn σ f endU endV (vertexBoundary d k) e)
    [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))] :
    reachProb μ σ f e
      ≤ Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) :=
  (reachProb_le_connOpen hμ0 σ f endU endV (vertexBoundary d k) e hfront).trans
    (oc_mean_connOpen_sum_le_connBox_sum hμ0 hinj hcoh hadj k e)

end Lattice














def oc_site0 : Site 1 := ![0]


def oc_site1 : Site 1 := ![1]



def oc_witnessEndU : Fin 1 → Site 1 := fun _ => oc_site0
def oc_witnessEndV : Fin 1 → Site 1 := fun _ => oc_site1



def oc_witnessEdge : Fin 1 → Sym2 (Site 1) := fun _ => s(oc_site0, oc_site1)


theorem oc_adj_site0_site1 : (hypercubicLattice 1).Adj oc_site0 oc_site1 := by
  rw [hypercubicLattice_adj]
  simp [oc_site0, oc_site1]


theorem oc_witness_hcoh : ∀ e, oc_witnessEdge e = s(oc_witnessEndU e, oc_witnessEndV e) :=
  fun _ => rfl


theorem oc_witness_hadj :
    ∀ e, (hypercubicLattice 1).Adj (oc_witnessEndU e) (oc_witnessEndV e) :=
  fun _ => oc_adj_site0_site1


theorem oc_witness_hinj : Function.Injective oc_witnessEdge := by
  intro a b _; exact Subsingleton.elim a b







theorem oc_connectedToSet_witness :
    ConnectedToSet 1 (liftCfg oc_witnessEdge (fun _ => true)) oc_site0
      ({oc_site1} : Set (Site 1)) := by
  have hopen : ConnOpenSet oc_witnessEndU oc_witnessEndV (fun _ => true) oc_site0
      ({oc_site1} : Set (Site 1)) := by
    refine ⟨oc_site1, Set.mem_singleton _, ?_⟩
    refine ReachOpen.step 0 rfl (Or.inl ⟨rfl, rfl⟩) ?_
    exact ReachOpen.refl oc_site1
  exact oc_connOpenSet_imp_connectedToSet oc_witness_hinj oc_witness_hcoh oc_witness_hadj hopen





theorem oc_site0_ne_site1 : oc_site0 ≠ oc_site1 := by
  intro h
  have : (oc_site0 0 : ℤ) = oc_site1 0 := by rw [h]
  simp [oc_site0, oc_site1] at this

end Walls

end StatMech
