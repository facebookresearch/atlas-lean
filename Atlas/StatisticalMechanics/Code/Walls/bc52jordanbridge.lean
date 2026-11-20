/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.OpenSpanningForestClose
import Code.Percolation.CanonForestCount
import Code.Percolation.CanonicalTrifCount
import Code.Walls.bc51armforest
import Code.Lattice.JordanEnclosureDuality
import Code.Lattice.EulerFaces2

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}














theorem bc52_spanForest_acyclic {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (osf_spanForest G).IsAcyclic :=
  osf_spanForest_acyclic G






theorem bc52_subgraph_acyclic {V : Type*} [Fintype V] (G T : SimpleGraph V)
    (hsub : T ≤ osf_spanForest G) : T.IsAcyclic :=
  (osf_spanForest_acyclic G).anti hsub












namespace Bc52Witness




def thetaRel (a b : Fin 4) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨      
  (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨      
  (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨      
  (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3)        

instance : DecidableRel thetaRel := fun a b => by unfold thetaRel; infer_instance

def thetaG : SimpleGraph (Fin 4) := SimpleGraph.fromRel thetaRel
instance : DecidableRel thetaG.Adj := by unfold thetaG fromRel; intro a b; infer_instance







theorem thetaG_not_acyclic : ¬ thetaG.IsAcyclic := by
  intro hac
  have h01 : thetaG.Adj 0 1 := by
    rw [thetaG, fromRel_adj]; refine ⟨by decide, ?_⟩; unfold thetaRel; decide
  have h12 : thetaG.Adj 1 2 := by
    rw [thetaG, fromRel_adj]; refine ⟨by decide, ?_⟩; unfold thetaRel; decide
  have h23 : thetaG.Adj 2 3 := by
    rw [thetaG, fromRel_adj]; refine ⟨by decide, ?_⟩; unfold thetaRel; decide
  have h30 : thetaG.Adj 3 0 := by
    rw [thetaG, fromRel_adj]; refine ⟨by decide, ?_⟩; unfold thetaRel; decide
  refine hac (Walk.cons h01 (Walk.cons h12 (Walk.cons h23 (Walk.cons h30 Walk.nil)))) ?_
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, by simp, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]
    decide
  · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
    decide






theorem thetaG_spanForest_subgraph_acyclic {H : SimpleGraph (Fin 4)}
    (hsub : H ≤ osf_spanForest thetaG) : H.IsAcyclic :=
  bc52_subgraph_acyclic thetaG H hsub

end Bc52Witness



















theorem bc52_acyclic_no_boundedRegion (P : Lattice.PlanarZ2Subgraph) (hac : P.G.IsAcyclic) :
    IsEmpty {c : (Lattice.whb_faceRegion (Lattice.imageGraph P)).ConnectedComponent // c.supp.Finite} := by
  have hnull : Lattice.nullity P.G = 0 := Lattice.nullity_eq_zero_of_isAcyclic hac
  obtain ⟨e⟩ := Lattice.jed_faithfulDiscreteJordan P
  rw [hnull] at e
  exact e.isEmpty







theorem bc52_boundedRegion_forces_cycle (P : Lattice.PlanarZ2Subgraph)
    (hne : Nonempty {c : (Lattice.whb_faceRegion (Lattice.imageGraph P)).ConnectedComponent //
      c.supp.Finite}) :
    ¬ P.G.IsAcyclic := by
  intro hac
  exact (bc52_acyclic_no_boundedRegion P hac).false hne.some



















open Classical in








theorem bc52_globalArmForest_of_canonical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
    (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
    bc51_GlobalArmForest ω n := by
  classical
  
  have harms : arc_TrifArmsRemoveSiteInfinite ω n :=
    ctc2_armsRemoveSiteInfinite_of_canonical ω n hcanon
  have hdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
        (∀ i, (cfc_T ω n).Adj x (c i)) ∧
        (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
         ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
         ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
        (∀ i, zr i ∈ vertexBoundary d n ∧
          ∃ w : (cfc_T ω n).Walk (c i) (zr i), x ∉ w.support) := by
    intro x hxbox htri
    obtain ⟨c0, hadj, hne, hcut, hinf⟩ := harms x hxbox htri
    have hcbox : ∀ i, c0 i ∈ box d n := fun i =>
      harmbox x hxbox htri (c0 i) (hadj i) (hinf i)
    exact cfc_trif_data ω n hn hxbox c0 hadj hne hcbox hcut hinf
  choose! c zr hcadj hccut hcreach using hdata
  refine ⟨boxFinsetBK d (n + 1), cfc_T ω n, Classical.decRel _, vertexBoundary d n, c, zr,
    cfc_T_acyclic ω n, cfc_T_open ω n, ?_, le_refl _, Or.inl hexists, ?_⟩
  · 
    intro u v huv
    rw [boxFinsetBK, Set.Finite.mem_toFinset]
    exact cfc_T_support ω n u v huv
  · 
    intro x hxbox htri
    exact ⟨hcadj x hxbox htri, hccut x hxbox htri, hcreach x hxbox htri⟩






theorem bc52_Tcount_le_boundary_of_canonical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  classical
  by_cases hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x
  · exact bc51_Tcount_le_boundary_of_globalArmForest ω n
      (bc52_globalArmForest_of_canonical ω n hn hcanon harmbox hexists)
  · push Not at hexists
    exact cfc_Tcount_le_boundary_of_no_trif ω n hexists



































theorem bc52_status :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (osf_spanForest G).IsAcyclic) ∧
    (¬ Bc52Witness.thetaG.IsAcyclic) ∧
    (∀ (P : Lattice.PlanarZ2Subgraph), P.G.IsAcyclic →
      IsEmpty {c : (Lattice.whb_faceRegion (Lattice.imageGraph P)).ConnectedComponent //
        c.supp.Finite}) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) →
      (∀ x, x ∈ box d n → IsTrifurcation d ω x →
        ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) →
      (∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) →
      bc51_GlobalArmForest ω n) :=
  ⟨fun G => bc52_spanForest_acyclic G, Bc52Witness.thetaG_not_acyclic,
   bc52_acyclic_no_boundedRegion, fun ω n => bc52_globalArmForest_of_canonical ω n⟩

end StatMech.Walls
