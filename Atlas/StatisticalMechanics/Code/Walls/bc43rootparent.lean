/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.ArmReachComponentClose
import Code.Percolation.BKForestLib
import Code.Walls.bc26forest
import Code.Walls.bc37armadj
import Code.Walls.bc38acyclic
import Code.Walls.bc39spanning
import Code.Walls.bc40funnel
import Code.Walls.bc41rootside
import Code.Walls.bc42rootward

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}






























def bc43_RootWardRootParent (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d) : Prop :=
  
  
  
  (∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b →
      a ≠ b → Connected d ω a b → rank a ≠ rank b) →
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
    x ≠ y → Connected d ω x y → rank x < rank y → x ≠ par y →
    par y ∈ box d n → IsTrifurcation d ω (par y) →
    bc37_ArmAdjacent ω n y (par y) → rank (par y) < rank y →
    ∃ p : (openSubgraph d ω).Walk x (par y), ∀ v ∈ p.support, v ≠ y






theorem bc43_rootWardRootParent_of_rootWardAvoidingWalk (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hold : bc41_RootWardAvoidingWalk ω n rank par) :
    bc43_RootWardRootParent ω n rank par := by
  intro _hinj x hxbox htri y hybox htriy hxy hconn hlt hxpar _hpbox _hptri hadj _hprank
  exact hold x hxbox htri y hybox htriy hxy hconn hlt hxpar hadj





























theorem bc43_farWitness_rank_not_injective (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ z₀ : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hz0box : z₀ ∈ box d n) (htriz0 : IsTrifurcation d ω z₀)
    (hne : x₀ ≠ y₀) (hz0y0 : z₀ ≠ y₀) (hx0z0 : x₀ ≠ z₀) (hconnxz : Connected d ω x₀ z₀) :
    ¬ (∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b →
        a ≠ b → Connected d ω a b →
        (fun w => toLex (if w = y₀ then (1 : ℕ) else 0, (0 : ℕ))) a ≠
          (fun w => toLex (if w = y₀ then (1 : ℕ) else 0, (0 : ℕ))) b) := by
  intro hinj
  
  refine hinj x₀ hx0box htri0 z₀ hz0box htriz0 hx0z0 hconnxz ?_
  simp only [if_neg hne, if_neg hz0y0]

set_option linter.unusedVariables false in














theorem bc43_rootWardRootParent_no_farParent_trap
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ z₀ : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hz0box : z₀ ∈ box d n) (htriz0 : IsTrifurcation d ω z₀)
    (hne : x₀ ≠ y₀) (hz0y0 : z₀ ≠ y₀) (hx0z0 : x₀ ≠ z₀) (hconnxz : Connected d ω x₀ z₀)
    (hfar : ¬ Connected d (removeSite y₀ ω) x₀ z₀) :
    bc43_RootWardRootParent ω n
      (fun w => toLex (if w = y₀ then (1 : ℕ) else 0, (0 : ℕ))) (fun _ => z₀) := by
  intro hinj
  
  exact absurd hinj
    (bc43_farWitness_rank_not_injective ω n hx0box htri0 hz0box htriz0 hne hz0y0 hx0z0 hconnxz)










theorem bc43_rootWardRootParent_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc43_RootWardRootParent ω n rank par := by
  intro _hinj x hxbox htri; exact absurd htri (hno x hxbox)

set_option linter.unusedVariables false in











theorem bc43_rootWardRootParent_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d}
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hx0y0 : x₀ ≠ y₀) :
    ∀ (rank : Site d → ℕ ×ₗ ℕ), bc43_RootWardRootParent ω n rank (fun _ => x₀) := by
  intro rank _hinj x hxbox htri y hybox htriy hxy hconn hlt hxpar _hpbox _hptri hadj _hprank
  
  simp only at hxpar hadj
  rcases htwo x hxbox htri with hx | hx
  · 
    exact absurd hx hxpar
  · 
    rcases htwo y hybox htriy with hy | hy
    · rw [hy] at hadj
      exact absurd hadj (bc37_armAdjacent_irrefl ω n x₀)
    · rw [hx, hy] at hxy
      exact absurd rfl hxy

set_option linter.unusedVariables false in
















theorem bc43_rootWardRootParent_of_twoTrif_allPar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d}
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hx0y0 : x₀ ≠ y₀) :
    ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc43_RootWardRootParent ω n rank par := by
  intro rank par _hinj x hxbox htri y hybox htriy hxy hconn hlt hxpar hpbox hptri hadj _hprank
  
  obtain ⟨hpne, hpconn, _⟩ := hadj
  have hpar_two : par y = x₀ ∨ par y = y₀ := htwo (par y) hpbox hptri
  have hx_two : x = x₀ ∨ x = y₀ := htwo x hxbox htri
  have hy_two : y = x₀ ∨ y = y₀ := htwo y hybox htriy
  
  refine absurd ?_ hxpar
  
  rcases hx_two with hx | hx <;> rcases hy_two with hy | hy <;>
    rcases hpar_two with hp | hp
  · exact absurd (hx.trans hy.symm) hxy              
  · exact absurd (hx.trans hy.symm) hxy              
  · rw [hx, hp]                                       
  · exact absurd (hy.trans hp.symm) hpne             
  · exact absurd (hy.trans hp.symm) hpne             
  · rw [hx, hp]                                       
  · exact absurd (hx.trans hy.symm) hxy              
  · exact absurd (hx.trans hy.symm) hxy              



























theorem bc43_exists_rootedArmForest_mem (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∃ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank x < rank y →
          par y ∈ tfc_trifFinset ω n ∧
          bc37_ArmAdjacent ω n y (par y) ∧ rank (par y) < rank y) := by
  classical
  set G := bc37_armAdjGraph ω n with hG
  obtain ⟨idx, hidx⟩ := (inferInstance : Countable (Site d)).exists_injective_nat
  set root : {x : Site d // x ∈ tfc_trifFinset ω n} → {x : Site d // x ∈ tfc_trifFinset ω n} :=
    fun v => (G.connectedComponentMk v).nonempty_supp.some with hroot
  have hrr : ∀ v, G.Reachable (root v) v := by
    intro v; rw [← SimpleGraph.ConnectedComponent.eq]
    exact (G.connectedComponentMk v).nonempty_supp.some_mem
  have hroot_inv : ∀ v w, G.Reachable v w → root v = root w := by
    intro v w hvw
    have : G.connectedComponentMk v = G.connectedComponentMk w :=
      SimpleGraph.ConnectedComponent.eq.mpr hvw
    simp only [hroot, this]
  set dep : Site d → ℕ := fun v =>
    if hv : v ∈ tfc_trifFinset ω n then G.dist (root ⟨v, hv⟩) ⟨v, hv⟩ else 0 with hdep
  set par : Site d → Site d := fun v =>
    if hv : v ∈ tfc_trifFinset ω n then (bc38_parentTo G root ⟨v, hv⟩).1 else v with hpar
  have hdep0 : ∀ (v : Site d) (hv : v ∈ tfc_trifFinset ω n),
      dep v = 0 ↔ (⟨v, hv⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = root ⟨v, hv⟩ := by
    intro v hv
    simp only [hdep, dif_pos hv]
    rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable]
    constructor
    · rintro (h | h); · exact h.symm
      · exact absurd (hrr ⟨v, hv⟩) h
    · intro h; exact Or.inl h.symm
  refine ⟨fun v => toLex (dep v, idx v), par, ?_, ?_⟩
  · intro x _hxbox _htri y _hybox _htriy hxy _hconn hrankeq
    have hidxeq : idx x = idx y := by simpa using congrArg (fun p => (ofLex p).2) hrankeq
    exact hxy (hidx hidxeq)
  · intro x hxbox htri y hybox htriy hxy hconn hlt
    have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    simp only at hlt
    have hxyreach : G.Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ := (bc39_armAdjSpanning ω n) ⟨x, hxT⟩ ⟨y, hyT⟩ hconn
    have hrootxy : root ⟨x, hxT⟩ = root ⟨y, hyT⟩ := hroot_inv _ _ hxyreach
    have hynonroot : (⟨y, hyT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) ≠ root ⟨y, hyT⟩ := by
      intro hyroot
      have hdepy0 : dep y = 0 := (hdep0 y hyT).mpr hyroot
      rw [hdepy0, Prod.Lex.toLex_lt_toLex] at hlt
      have hdepx0 : dep x = 0 := by rcases hlt with h | ⟨h, _⟩; · omega
                                    · exact h
      have hxroot : (⟨x, hxT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = root ⟨x, hxT⟩ :=
        (hdep0 x hxT).mp hdepx0
      apply hxy
      have hxy_eq : (⟨x, hxT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = ⟨y, hyT⟩ := by
        rw [hxroot, hrootxy, ← hyroot]
      exact congrArg Subtype.val hxy_eq
    obtain ⟨hadj, hdlt⟩ := bc38_parentTo_spec G root hynonroot (hrr ⟨y, hyT⟩)
    have hpary : par y = (bc38_parentTo G root ⟨y, hyT⟩).1 := by simp only [hpar, dif_pos hyT]
    have hparyT : par y ∈ tfc_trifFinset ω n := by
      rw [hpary]; exact (bc38_parentTo G root ⟨y, hyT⟩).2
    have hpar_pack : (⟨par y, hparyT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n})
        = bc38_parentTo G root ⟨y, hyT⟩ := Subtype.ext hpary
    refine ⟨hparyT, ?_, ?_⟩
    · have : G.Adj ⟨y, hyT⟩ ⟨par y, hparyT⟩ := by rw [hpar_pack]; exact hadj
      exact this
    · have hyparreach : G.Reachable ⟨y, hyT⟩ (bc38_parentTo G root ⟨y, hyT⟩) := hadj.reachable
      have hrootpary : root (bc38_parentTo G root ⟨y, hyT⟩) = root ⟨y, hyT⟩ :=
        hroot_inv _ _ hyparreach.symm
      have hdeppary : dep (par y) = G.dist (root ⟨y, hyT⟩) (bc38_parentTo G root ⟨y, hyT⟩) := by
        simp only [hdep, dif_pos hparyT]
        rw [hpar_pack, hrootpary]
      have hdepy : dep y = G.dist (root ⟨y, hyT⟩) ⟨y, hyT⟩ := by simp only [hdep, dif_pos hyT]
      have hdeplt : dep (par y) < dep y := by rw [hdeppary, hdepy]; exact hdlt
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hdeplt)


















theorem bc43_parentFunneling_of_cutGeometryFixed'_rootParent (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hwalk : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc43_RootWardRootParent ω n rank par) :
    bc37_ParentFunneling ω n := by
  obtain ⟨rank, par, hinj, hroot⟩ := bc43_exists_rootedArmForest_mem ω n
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  refine ⟨b, rank, par, hdata, hinj, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hparyT, hpadj, hprank⟩ := hroot x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hpbox, hptri⟩ := tfc_mem_trifFinset.mp hparyT
  obtain ⟨hloc, hself, hfun⟩ := hclauses y (par y) hybox htriy hpadj
  refine ⟨hloc, hself, fun hxne => ?_⟩
  
  obtain ⟨p, hp⟩ :=
    hwalk rank par hinj x hxbox htri y hybox htriy hxy hconn hlt hxne hpbox hptri hpadj hprank
  
  have hrs : Connected d (removeSite y ω) x (par y) :=
    (bc42_avoidingWalk_iff_connected_removeSite ω hxy).mp ⟨p, hp⟩
  exact hfun x hxy hrs


theorem bc43_selfDownArm_of_cutGeometryFixed'_rootParent (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hwalk : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc43_RootWardRootParent ω n rank par) :
    bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n
    (bc43_parentFunneling_of_cutGeometryFixed'_rootParent ω n hgeo hwalk)














theorem bc43_burton_keane_bernoulli_of_rootWardRootParent (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
    (hwalk : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc43_RootWardRootParent ω n rank par)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc36_burton_keane_bernoulli_of_selfDownArm hd p hp1 hp0
    (fun ω n hn =>
      bc43_selfDownArm_of_cutGeometryFixed'_rootParent ω n (hgeo ω n hn) (hwalk ω n hn))
    htrif

end StatMech.Walls
