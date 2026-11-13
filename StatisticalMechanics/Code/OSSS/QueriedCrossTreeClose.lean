/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Code.OSSS.PrefixCoversClose
import Code.OSSS.SharpnessUncond

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatMech

namespace OSSS

namespace QueriedCrossTreeClose

open StatMech.OSSS.DecisionTree
open StatMech.OSSS.Revealment
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.ReachBoxCrossing
open StatMech.OSSS.ReachDomination
open StatMech.OSSS.PrefixCoversClose
open StatMech.OSSS.CovLowerBound
open StatMech.OSSS.SharpnessFK
open StatMech.Lattice
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [DecidableEq V]


















theorem incidentCluster_of_queried_crossTree (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (ω : ConfigSpace E) (i : E)
    (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
    IncidentCluster endU endV ω B i :=
  queried_crossTree_imp endU endV o B C l disc₀ hdisc₀ ω i hi




















theorem reveal_crossTree_le_incidentCluster {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (endU endV : E → V) (o : V) (B C : Set V) (l : List E) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (i : E) :
    reveal ν (crossTree endU endV o C l disc₀) i
      ≤ expect ν (fun ω => if ConnOpenSet endU endV ω (endU i) B then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnOpenSet endU endV ω (endV i) B then (1 : ℝ) else 0) := by
  have h := revealment_le_of_queried_imp_or hν (crossTree endU endV o C l disc₀) i
    (fun ω => ConnOpenSet endU endV ω (endU i) B)
    (fun ω => ConnOpenSet endU endV ω (endV i) B)
    (fun ω hq => incidentCluster_of_queried_crossTree endU endV o B C l disc₀ hdisc₀ ω i hq)
  rwa [Revealment.revealment] at h








section Lattice

variable {d : ℕ}











theorem reveal_crossTree_le_connBox {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (C : Set (Site d)) (k : ℕ) (l : List E) (disc₀ : Finset (Site d))
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ vertexBoundary d k) (i : E) :
    reveal ν (crossTree endU endV o C l disc₀) i
      ≤ expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU i) (vertexBoundary d k) then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV i) (vertexBoundary d k) then (1 : ℝ) else 0) := by
  refine le_trans
    (reveal_crossTree_le_incidentCluster hν endU endV o (vertexBoundary d k) C l disc₀ hdisc₀ i) ?_
  apply add_le_add
  · exact expect_indicator_mono hν _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)
  · exact expect_indicator_mono hν _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)








































theorem covSum_ge_crossTree {n : ℕ} (hn : 1 ≤ n)
    {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (l : List E) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D)
    (hD : ∀ e,
      (∑ k ∈ Finset.Icc 1 n,
        (expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
          + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0))) ≤ D) :
    (n : ℝ) * c₀
        * (expect ν ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ)))))
      ≤ D * ∑ e, cov ν (coordI e) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) := by
  classical
  
  haveI hne : Nonempty (↥(Finset.Icc 1 n)) :=
    ⟨⟨1, by rw [Finset.mem_Icc]; exact ⟨le_refl 1, hn⟩⟩⟩
  set A : Set (ConfigSpace E) := crossEvent edge o (vertexBoundary d n) with hA0
  
  have hAinc : IsIncreasing A := by
    rw [hA0]; unfold crossEvent; exact connectedToSet_increasing edge o (vertexBoundary d n)
  
  set T : ↥(Finset.Icc 1 n) → DecisionTree E :=
    fun k => crossTree endU endV o (vertexBoundary d n) l (disc₀ (k : ℕ)) with hTdef
  
  have hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)) := by
    intro k
    funext ω
    have hk1 : 1 ≤ (k : ℕ) := (Finset.mem_Icc.mp k.2).1
    have hkn : (k : ℕ) ≤ n := (Finset.mem_Icc.mp k.2).2
    have hokm1 : o ∈ box d ((k : ℕ) - 1) := ho (k : ℕ) hk1
    have heval := evalR_crossTree_connected (E := E) (d := d) hinj hcoh hadj
      (k : ℕ) n hk1 hkn o hokm1 l hl (disc₀ (k : ℕ))
      (hdisc₀sup (k : ℕ)) (hoB (k : ℕ)) ω
    rw [hTdef]; rw [heval]
    by_cases hconn : ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n)
    · have hmem : ω ∈ A := by rw [hA0]; exact hconn
      rw [if_pos hconn, Set.indicator_of_mem hmem]
    · have hmem : ω ∉ A := by rw [hA0]; exact hconn
      rw [if_neg hconn, Set.indicator_of_notMem hmem]
  
  
  set R : ↥(Finset.Icc 1 n) → E → ℝ :=
    fun k e => expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d (k : ℕ)) then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d (k : ℕ)) then (1 : ℝ) else 0) with hRdef
  have hR : ∀ k e, reveal ν (T k) e ≤ R k e := by
    intro k e
    rw [hTdef, hRdef]
    exact reveal_crossTree_le_connBox (E := E) (d := d) hν hinj hcoh hadj o
      (vertexBoundary d n) (k : ℕ) l (disc₀ (k : ℕ)) (hdisc₀sub (k : ℕ)) e
  
  have hDsum : ∀ e, (∑ k, R k e) ≤ D := by
    intro e
    rw [hRdef,
      Finset.sum_coe_sort (Finset.Icc 1 n)
        (fun k => expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
            + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0))]
    exact hD e
  
  have hcard : (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) = n := by
    rw [Fintype.card_coe, Nat.card_Icc]
    have hsub : n + 1 - 1 = n := by omega
    rw [hsub]
  have hmain := covSum_ge_of_indicator (κ := ↥(Finset.Icc 1 n)) hν hAinc T hT R hR
    c₀ hc₀nn hc₀ D hDnn hDsum
  rw [hcard] at hmain
  exact hmain

end Lattice

end QueriedCrossTreeClose

end OSSS

end StatMech
