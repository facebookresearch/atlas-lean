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
import Code.Percolation.BKForestLib
import Code.Walls.bc26forest
import Code.Walls.bc37armadj
import Code.Walls.bc38acyclic
import Code.Walls.bc39spanning

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}













theorem bc40_funnel_demands_all_sites_reach_s (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc39_ArmCutGeometryFixed ω n)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s) :
    ∃ b : Site d → Site d, ∀ x, x ≠ s → x ≠ t → Connected d (removeSite t ω) (b x) s := by
  obtain ⟨b, _hdata, hclauses⟩ := hgeo
  obtain ⟨_hloc, _hself, hfun⟩ := hclauses t s htbox htri hadj
  exact ⟨b, hfun⟩
















theorem bc40_armCutGeometryFixed_false_of_idempotentDownArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s)
    (hidem : ∀ b : Site d → Site d,
      (∀ x, x ∈ box d n → IsTrifurcation d ω x →
        b x ∈ box d n ∧ Connected d ω x (b x) ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) →
      b (b t) = b t ∧ b t ≠ s ∧ b t ≠ t) :
    ¬ bc39_ArmCutGeometryFixed ω n := by
  rintro ⟨b, hdata, hclauses⟩
  obtain ⟨_hloc, hself, hfun⟩ := hclauses t s htbox htri hadj
  obtain ⟨hbbt, hbts, hbtt⟩ := hidem b hdata
  
  have hreach : Connected d (removeSite t ω) (b (b t)) s := hfun (b t) hbts hbtt
  rw [hbbt] at hreach
  exact hself hreach































def bc40_ArmCutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ t s, t ∈ box d n → IsTrifurcation d ω t → bc37_ArmAdjacent ω n t s →
      (¬ Connected d (removeSite t ω) (b t) (b s)) ∧
      (¬ Connected d (removeSite t ω) (b t) s) ∧
      (∀ x, x ≠ t → Connected d (removeSite t ω) x s →
        Connected d (removeSite t ω) (b x) s))








def bc40_RootSideComparable (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
    x ≠ y → Connected d ω x y → rank x < rank y → x ≠ par y →
    Connected d (removeSite y ω) x (par y)










theorem bc40_armRealisation_of_cutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc40_RootSideComparable ω n rank par) :
    bc38_ArmRealisation ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  intro rank par hroot
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hpadj, _hprank⟩ := hroot x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hloc, hself, hfun⟩ := hclauses y (par y) hybox htriy hpadj
  refine ⟨hloc, hself, fun hxne => ?_⟩
  
  
  have hxy' : x ≠ y := hxy
  have hrs : Connected d (removeSite y ω) x (par y) :=
    hroot_side rank par x hxbox htri y hybox htriy hxy hconn hlt hxne
  exact hfun x hxy' hrs



theorem bc40_parentFunneling_of_cutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc40_RootSideComparable ω n rank par) :
    bc37_ParentFunneling ω n :=
  bc38_parentFunneling_of_residues ω n (bc39_armAdjSpanning ω n)
    (bc40_armRealisation_of_cutGeometryFixed' ω n hgeo hroot_side)


theorem bc40_selfDownArm_of_cutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc40_RootSideComparable ω n rank par) :
    bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n
    (bc40_parentFunneling_of_cutGeometryFixed' ω n hgeo hroot_side)


theorem bc40_Tcount_le_boundary_of_cutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc40_RootSideComparable ω n rank par) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn
    (bc40_selfDownArm_of_cutGeometryFixed' ω n hgeo hroot_side)









theorem bc40_burton_keane_bernoulli_of_cutGeometryFixed' (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc40_RootSideComparable ω n rank par)
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
    (fun ω n hn => bc40_selfDownArm_of_cutGeometryFixed' ω n (hgeo ω n hn) (hroot_side ω n hn)) htrif











theorem bc40_armCutGeometryFixed'_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc40_ArmCutGeometryFixed' ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro t s htbox htri _; exact absurd htri (hno t htbox)








theorem bc40_armCutGeometryFixed'_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    
    (hloc_x : ∀ s, bc37_ArmAdjacent ω n x₀ s → ¬ Connected d (removeSite x₀ ω) (b x₀) (b s))
    (hself_x : ∀ s, bc37_ArmAdjacent ω n x₀ s → ¬ Connected d (removeSite x₀ ω) (b x₀) s)
    (hloc_y : ∀ s, bc37_ArmAdjacent ω n y₀ s → ¬ Connected d (removeSite y₀ ω) (b y₀) (b s))
    (hself_y : ∀ s, bc37_ArmAdjacent ω n y₀ s → ¬ Connected d (removeSite y₀ ω) (b y₀) s)
    
    (hfun_x : ∀ s, bc37_ArmAdjacent ω n x₀ s → ∀ x, x ≠ x₀ →
      Connected d (removeSite x₀ ω) x s → Connected d (removeSite x₀ ω) (b x) s)
    (hfun_y : ∀ s, bc37_ArmAdjacent ω n y₀ s → ∀ x, x ≠ y₀ →
      Connected d (removeSite y₀ ω) x s → Connected d (removeSite y₀ ω) (b x) s) :
    bc40_ArmCutGeometryFixed' ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · intro t s htbox htri hadj
    rcases htwo t htbox htri with rfl | rfl
    · exact ⟨hloc_x s hadj, hself_x s hadj, hfun_x s hadj⟩
    · exact ⟨hloc_y s hadj, hself_y s hadj, hfun_y s hadj⟩

set_option linter.unusedVariables false in













theorem bc40_armCutGeometryFixed'_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
    
    (hloc : ∀ t s, (t = x₀ ∨ t = m ∨ t = g) → bc37_ArmAdjacent ω n t s →
      ¬ Connected d (removeSite t ω) (b t) (b s))
    (hself : ∀ t s, (t = x₀ ∨ t = m ∨ t = g) → bc37_ArmAdjacent ω n t s →
      ¬ Connected d (removeSite t ω) (b t) s)
    
    (hfun : ∀ t s, (t = x₀ ∨ t = m ∨ t = g) → bc37_ArmAdjacent ω n t s → ∀ x, x ≠ t →
      Connected d (removeSite t ω) x s → Connected d (removeSite t ω) (b x) s) :
    bc40_ArmCutGeometryFixed' ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
  · intro t s htbox htri hadj
    have ht3 : t = x₀ ∨ t = m ∨ t = g := hthree t htbox htri
    exact ⟨hloc t s ht3 hadj, hself t s ht3 hadj, hfun t s ht3 hadj⟩




























def bc40_chainLab (c v : Fin 6) : ℕ :=
  if v = c then 100 + (c : ℕ)                     
  else if c = 0 then
    (if v = 3 then 103 else 1)                    
  else if c = 1 then
    (if v = 4 then 104                            
     else if v = 0 ∨ v = 3 then 2                 
     else 3)                                      
  else 
    (if v = 5 then 105 else 4)                    







theorem bc40_chainShadow_universalFunnel_false :
    ¬ ∀ (b : Fin 6 → Fin 6),
        b = ![3, 4, 5, 3, 4, 5] →
        ∀ t s : Fin 6, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) →
          ∀ x : Fin 6, x ≠ s → x ≠ t →
            bc40_chainLab t (b x) = bc40_chainLab t s := by
  intro h
  have h40 : (4 : Fin 6) ≠ 0 := by decide
  have h41 : (4 : Fin 6) ≠ 1 := by decide
  have hkey := h ![3, 4, 5, 3, 4, 5] rfl 1 0 (Or.inr (Or.inl ⟨rfl, rfl⟩)) 4 h40 h41
  
  have hb : (![3, 4, 5, 3, 4, 5] : Fin 6 → Fin 6) 4 = 4 := by
    simp [Matrix.cons_val, Fin.isValue]
  have hL1 : bc40_chainLab 1 4 = 104 := by simp [bc40_chainLab]
  have hL2 : bc40_chainLab 1 0 = 2 := by simp [bc40_chainLab]
  rw [hb, hL1, hL2] at hkey
  exact absurd hkey (by norm_num)







theorem bc40_chainShadow_allTrifFunnel_false :
    ¬ ∀ (b : Fin 6 → Fin 6),
        b = ![3, 4, 5, 3, 4, 5] →
        ∀ t s : Fin 6, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) →
          ∀ x : Fin 6, (x = 0 ∨ x = 1 ∨ x = 2) → x ≠ s → x ≠ t →
            bc40_chainLab t (b x) = bc40_chainLab t s := by
  intro h
  have h20 : (2 : Fin 6) ≠ 0 := by decide
  have h21 : (2 : Fin 6) ≠ 1 := by decide
  have hkey := h ![3, 4, 5, 3, 4, 5] rfl 1 0 (Or.inr (Or.inl ⟨rfl, rfl⟩)) 2
    (Or.inr (Or.inr rfl)) h20 h21
  
  have hb : (![3, 4, 5, 3, 4, 5] : Fin 6 → Fin 6) 2 = 5 := by
    simp [Matrix.cons_val, Fin.isValue]
  have hL1 : bc40_chainLab 1 5 = 3 := by simp [bc40_chainLab]
  have hL2 : bc40_chainLab 1 0 = 2 := by simp [bc40_chainLab]
  rw [hb, hL1, hL2] at hkey
  exact absurd hkey (by norm_num)














theorem bc40_chainShadow_consistent :
    ∃ (b : Fin 6 → Fin 6) (Rc : Fin 6 → Fin 6 → Fin 6 → Prop),
      (∀ c u v, Rc c u v ↔ bc40_chainLab c u = bc40_chainLab c v) ∧
      (∀ t s : Fin 6, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) →
        (¬ Rc t (b t) (b s)) ∧
        (¬ Rc t (b t) s) ∧
        (∀ x : Fin 6, x ≠ t → Rc t x s → Rc t (b x) s)) := by
  refine ⟨![3, 4, 5, 3, 4, 5], (fun c u v => bc40_chainLab c u = bc40_chainLab c v),
    fun _ _ _ => Iff.rfl, ?_⟩
  decide









theorem bc40_rootSideComparable_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc40_RootSideComparable ω n rank par := by
  intro x hxbox htri; exact absurd htri (hno x hxbox)





def bc40_chainSiteLab (c v : Fin 3) : ℕ :=
  if v = c then 100 + (c : ℕ) else 0   












theorem bc40_rootSideComparable_chain_consistent :
    ∃ (rank : Fin 3 → ℕ) (par : Fin 3 → Fin 3) (R : Fin 3 → Fin 3 → Fin 3 → Prop),
      (∀ c u v, R c u v ↔ bc40_chainSiteLab c u = bc40_chainSiteLab c v) ∧
      rank 0 < rank 1 ∧ rank 1 < rank 2 ∧ par 1 = 0 ∧ par 2 = 1 ∧
      (∀ x y : Fin 3, rank x < rank y → x ≠ par y → R y x (par y)) := by
  refine ⟨![0, 1, 2], ![0, 0, 1], (fun c u v => bc40_chainSiteLab c u = bc40_chainSiteLab c v),
    fun _ _ _ => Iff.rfl, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · rfl
  · rfl
  · decide

end StatMech.Walls
