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
import Code.Percolation.BurtonKeaneMerge
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose2
import Code.Percolation.DisjointArmEndsClose
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.DisjointArmEndsFinal
import Code.Percolation.BKForestLib
import Code.Percolation.BKHallSDRClose
import Code.Percolation.ArmEndDisjointClose
import Code.Percolation.ForestSelectorProve
import Code.Percolation.SpanningTreeArmClose
import Code.Percolation.ForestAcyclicityClose
import Code.Percolation.FacPairwiseClose
import Code.Percolation.BKArmSelectorClose
import Code.Percolation.RootedTreeSelectorClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}














noncomputable def stt_trifGraph (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph {x : Site d // x ∈ tfc_trifFinset ω n} where
  Adj a b := a ≠ b ∧ Connected d ω a.1 b.1
  symm := by rintro a b ⟨hne, hc⟩; exact ⟨hne.symm, hc.symm⟩
  loopless := ⟨fun a ⟨hne, _⟩ => hne rfl⟩




theorem stt_reachable_iff (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (a b : {x : Site d // x ∈ tfc_trifFinset ω n}) :
    (stt_trifGraph ω n).Reachable a b ↔ Connected d ω a.1 b.1 := by
  constructor
  · intro h
    obtain ⟨w⟩ := h
    induction w with
    | nil => exact connected_rfl
    | cons hadj _ ih => exact hadj.2.trans ih
  · intro hc
    by_cases hab : a = b
    · exact hab ▸ Reachable.refl a
    · exact ⟨Walk.cons ⟨hab, hc⟩ Walk.nil⟩







theorem stt_lex_ne_fst {a₁ a₂ b₁ b₂ : ℕ} (h : a₁ ≠ a₂) :
    (toLex (a₁, b₁)) ≠ toLex (a₂, b₂) :=
  fun he => h (congrArg (fun p => (ofLex p).1) he)


theorem stt_lex_ne_snd {a b₁ b₂ : ℕ} (h : b₁ ≠ b₂) :
    (toLex (a, b₁)) ≠ toLex (a, b₂) :=
  fun he => h (by simpa using congrArg (fun p => (ofLex p).2) he)


theorem stt_lex_lt_fst {a₁ a₂ b₁ b₂ : ℕ} (h : a₁ < a₂) :
    (toLex (a₁, b₁)) < toLex (a₂, b₂) := by
  rw [Prod.Lex.toLex_lt_toLex]; exact Or.inl h


theorem stt_lex_not_lt_fst {a₁ a₂ b₁ b₂ : ℕ} (h : a₁ < a₂) :
    ¬ ((toLex (a₂, b₂)) < toLex (a₁, b₁)) := by
  rw [Prod.Lex.toLex_lt_toLex]; rintro (h1 | ⟨h1, h2⟩) <;> omega














open Classical in





theorem stt_exists_depthRank (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∃ rank : Site d → ℕ ×ₗ ℕ,
      ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank x ≠ rank y := by
  classical
  
  obtain ⟨idx, hidx⟩ := (inferInstance : Countable (Site d)).exists_injective_nat
  
  obtain ⟨F, _hFle, _hFacyc, _hFreach⟩ :=
    (exists_isAcyclic_reachable_eq_le (G := stt_trifGraph ω n))
  
  set root : F.ConnectedComponent → {x : Site d // x ∈ tfc_trifFinset ω n} :=
    fun C => C.nonempty_supp.some with hroot
  
  set dep : Site d → ℕ := fun v =>
    if hv : v ∈ tfc_trifFinset ω n then
      F.dist (root (F.connectedComponentMk ⟨v, hv⟩)) ⟨v, hv⟩
    else 0 with hdep
  refine ⟨fun v => toLex (dep v, idx v), ?_⟩
  
  intro x _hxbox _htri y _hybox _htriy hxy _hconn hrankeq
  
  have hidxeq : idx x = idx y := by simpa using congrArg (fun p => (ofLex p).2) hrankeq
  exact hxy (hidx hidxeq)





























def stt_RootedSpanningForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (b : Site d → Site d) (rank : Site d → ℕ ×ₗ ℕ) (c : Site d → Site d → Fin 3),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ y, y ∈ box d n → IsTrifurcation d ω y → ∀ u v,
      Connected d ω y u → y ≠ u → Connected d ω y v → y ≠ v →
      (c y u = c y v ↔ fsp_sameArm ω y u v)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y → c y (b x) ≠ c y (b y))












theorem stt_rootedColoredForest_of_rootedSpanningForest (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : stt_RootedSpanningForest ω n) :
    rts_RootedColoredForest ω n := by
  obtain ⟨b, rank, c, hdata, hcolor, hinj, hdiv⟩ := h
  refine ⟨b, (fun x y => rank x < rank y), c, hdata, ?_, hcolor, ?_⟩
  · 
    intro x hxbox htri y hybox htriy hxy hconn
    have hne : rank x ≠ rank y := hinj x hxbox htri y hybox htriy hxy hconn
    rcases lt_trichotomy (rank x) (rank y) with h | h | h
    · exact Or.inl h
    · exact absurd h hne
    · exact Or.inr h
  · 
    intro x hxbox htri y hybox htriy hconn hlt
    have hxy : x ≠ y := by rintro rfl; exact lt_irrefl _ hlt
    exact hdiv x hxbox htri y hybox htriy hxy hconn hlt



theorem stt_rootedTreeArmSelection_of_rootedSpanningForest (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : stt_RootedSpanningForest ω n) :
    bas_RootedTreeArmSelection ω n :=
  rts_rootedTreeArmSelection_of_rootedColoredForest ω n
    (stt_rootedColoredForest_of_rootedSpanningForest ω n h)











theorem stt_rootedSpanningForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    stt_RootedSpanningForest ω n := by
  refine ⟨id, (fun _ => (0, 0)), (fun _ _ => 0), ?_, ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)






theorem stt_rootedSpanningForest_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (cx0 cy0 : Site d → Fin 3) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hcx0faith : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (cx0 u = cx0 v ↔ fsp_sameArm ω x₀ u v))
    (hcy0faith : ∀ u v, Connected d ω y₀ u → y₀ ≠ u → Connected d ω y₀ v → y₀ ≠ v →
      (cy0 u = cy0 v ↔ fsp_sameArm ω y₀ u v))
    (hdeep : cy0 (b x₀) ≠ cy0 (b y₀)) :
    stt_RootedSpanningForest ω n := by
  classical
  refine ⟨b, (fun z => if z = y₀ then toLex (1, 0) else toLex (0, 0)),
    (fun z => if z = y₀ then cy0 else cx0), ?_, ?_, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · 
    intro yy hyybox htriy u v hyu hneu hyv hnev
    rcases htwo yy hyybox htriy with rfl | rfl
    · simp only [if_neg hx0y0]; exact hcx0faith u v hyu hneu hyv hnev
    · simp only [if_pos]; exact hcy0faith u v hyu hneu hyv hnev
  · 
    intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · simp only [if_neg hx0y0, if_pos]; exact (stt_lex_ne_fst (by norm_num))
    · rcases htwo y hybox htriy with rfl | rfl
      · simp only [if_neg hx0y0, if_pos]; exact (stt_lex_ne_fst (by norm_num))
      · exact absurd rfl hxy
  · 
    intro x hxbox htri y hybox htriy hxy _ hlt
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · simpa only [if_neg hx0y0, if_pos] using hdeep
    · rcases htwo y hybox htriy with rfl | rfl
      · 
        simp only [if_neg hx0y0, if_pos] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxy


















theorem stt_rootedSpanningForest_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
    (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v →
      (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
    (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w →
      (ly i w = 0 ↔ lx w ≠ i))
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (b : Site d → Site d)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hcy : ∀ i, lx (b (y i)) = i)
    {j₀ : Fin 3} (hcx : lx (b x₀) = j₀)
    (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
    stt_RootedSpanningForest ω n := by
  classical
  set T := tfc_trifFinset ω n with hT
  have hx0T : x₀ ∈ T := tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩
  have hyT : ∀ i, y i ∈ T := fun i => tfc_mem_trifFinset.mpr ⟨(hydata i).1, (hydata i).2.1⟩
  have hx0y : ∀ i, x₀ ≠ y i := fun i => (hydata i).2.2.1
  have hbx0notin : b x₀ ∉ T := stac_infiniteCluster_notMem T ω (hbdata x₀ hx0box htri0).2.2
  have hbynotin : ∀ i, b (y i) ∉ T := fun i =>
    stac_infiniteCluster_notMem T ω (hbdata (y i) (hydata i).1 (hydata i).2.1).2.2
  have hne_bx0 : x₀ ≠ b x₀ := fun h => hbx0notin (h ▸ hx0T)
  have hne_x0_byi : ∀ i, x₀ ≠ b (y i) := fun i h => hbynotin i (h ▸ hx0T)
  have hne_yi_byj : ∀ i j, y i ≠ b (y j) := fun i j h => hbynotin j (h ▸ hyT i)
  have hne_yi_bx0 : ∀ i, y i ≠ b x₀ := fun i h => hbx0notin (h ▸ hyT i)
  have hx0byi : ∀ i, Connected d ω x₀ (b (y i)) := fun i =>
    (hydata i).2.2.2.trans (hbdata (y i) (hydata i).1 (hydata i).2.1).2.1
  have hyi_byi : ∀ i, Connected d ω (y i) (b (y i)) := fun i =>
    (hbdata (y i) (hydata i).1 (hydata i).2.1).2.1
  have hyi_byj : ∀ i j, Connected d ω (y i) (b (y j)) := fun i j =>
    (hydata i).2.2.2.symm.trans (hx0byi j)
  have hx0bx0 : Connected d ω x₀ (b x₀) := (hbdata x₀ hx0box htri0).2.1
  have hyi_bx0 : ∀ i, Connected d ω (y i) (b x₀) := fun i =>
    (hydata i).2.2.2.symm.trans hx0bx0
  
  set c : Site d → Site d → Fin 3 :=
    fun z => if z = x₀ then lx
             else if h : ∃ i, z = y i then ly h.choose else lx with hc
  have hcyi : ∀ i, c (y i) = ly i := by
    intro i
    have hne : y i ≠ x₀ := (hx0y i).symm
    have hex : ∃ j, y i = y j := ⟨i, rfl⟩
    rw [hc]
    simp only [if_neg hne, dif_pos hex]
    rw [hyinj hex.choose_spec.symm]
  have hcx0 : c x₀ = lx := by simp [hc]
  
  set rk : Site d → ℕ ×ₗ ℕ :=
    fun z => if z = x₀ then toLex (0, 0)
             else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrk
  have hrkx0 : rk x₀ = toLex (0, 0) := by simp [hrk]
  have hrkyi : ∀ i, rk (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hx0y i).symm
    have hex : ∃ j, y i = y j := ⟨i, rfl⟩
    rw [hrk]
    simp only [if_neg hne, dif_pos hex]
    rw [hyinj hex.choose_spec.symm]
  refine ⟨b, rk, c, hbdata, ?_, ?_, ?_⟩
  · 
    intro yy hyybox htriy u v hyu hneu hyv hnev
    rcases hsingle yy hyybox htriy with rfl | ⟨i, rfl⟩
    · rw [hcx0]; exact hlxf u v hyu hneu hyv hnev
    · rw [hcyi i]; exact hlyf i u v hyu hneu hyv hnev
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · rcases hsingle x' hx'box htri' with rfl | ⟨i, rfl⟩
      · exact absurd rfl hxx'
      · rw [hrkx0, hrkyi i]; exact stt_lex_ne_fst (by norm_num)
    · rcases hsingle x' hx'box htri' with rfl | ⟨j, rfl⟩
      · rw [hrkx0, hrkyi i]; exact (stt_lex_ne_fst (by norm_num)).symm
      · rw [hrkyi i, hrkyi j]
        refine stt_lex_ne_snd ?_
        intro hij
        exact hxx' (by rw [Fin.val_inj.mp hij])
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn hlt
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · 
      rcases hsingle x' hx'box htri' with rfl | ⟨i, rfl⟩
      · exact absurd rfl hxx'
      · 
        rw [hcyi i]
        by_cases hji : (j₀ : Fin 3) = i
        · 
          subst hji; exact hcentral
        · 
          have hG_bx0 : ly i (b x) = 0 :=
            (hGstar i (b x) hx0bx0 hne_bx0 (hyi_bx0 i) (hne_yi_bx0 i)).mpr
              (by rw [hcx]; exact hji)
          have hG_byi : ly i (b (y i)) ≠ 0 :=
            (not_iff_not.mpr (hGstar i (b (y i)) (hx0byi i) (hne_x0_byi i)
              (hyi_byi i) (hne_yi_byj i i))).mpr (by rw [not_not, hcy i])
          rw [hG_bx0]; exact fun h => hG_byi h.symm
    · rcases hsingle x' hx'box htri' with rfl | ⟨j, rfl⟩
      · 
        rw [hrkx0, hrkyi i] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · 
        rw [hcyi j]
        
        have hij' : i ≠ j := fun h => hxx' (by rw [h])
        
        have hG_byi : ly j (b (y i)) = 0 :=
          (hGstar j (b (y i)) (hx0byi i) (hne_x0_byi i)
            (hyi_byj j i) (hne_yi_byj j i)).mpr (by rw [hcy i]; exact hij')
        have hG_byj : ly j (b (y j)) ≠ 0 :=
          (not_iff_not.mpr (hGstar j (b (y j)) (hx0byi j) (hne_x0_byi j)
            (hyi_byi j) (hne_yi_byj j j))).mpr (by rw [not_not, hcy j])
        rw [hG_byi]; exact fun h => hG_byj h.symm












theorem stt_rootedSpanningForest_of_tree (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (r m : Site d) (g : Fin 2 → Site d) (b : Site d → Site d)
    (cr cm : Site d → Fin 3) (cg : Fin 2 → Site d → Fin 3)
    (hdistinct : r ≠ m ∧ (∀ i, r ≠ g i) ∧ (∀ i, m ≠ g i) ∧ Function.Injective g)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r ∨ x = m ∨ ∃ i, x = g i)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hcrf : ∀ u v, Connected d ω r u → r ≠ u → Connected d ω r v → r ≠ v →
      (cr u = cr v ↔ fsp_sameArm ω r u v))
    (hcmf : ∀ u v, Connected d ω m u → m ≠ u → Connected d ω m v → m ≠ v →
      (cm u = cm v ↔ fsp_sameArm ω m u v))
    (hcgf : ∀ i u v, Connected d ω (g i) u → g i ≠ u → Connected d ω (g i) v → g i ≠ v →
      (cg i u = cg i v ↔ fsp_sameArm ω (g i) u v))
    (hrm : cm (b r) ≠ cm (b m))
    (hrg : ∀ i, cg i (b r) ≠ cg i (b (g i)))
    (hmg : ∀ i, cg i (b m) ≠ cg i (b (g i)))
    (hgg : cg 1 (b (g 0)) ≠ cg 1 (b (g 1))) :
    stt_RootedSpanningForest ω n := by
  classical
  obtain ⟨hrm_ne, hrg_ne, hmg_ne, hginj⟩ := hdistinct
  
  set c : Site d → Site d → Fin 3 :=
    fun z => if z = r then cr
             else if z = m then cm
             else if h : ∃ i, z = g i then cg h.choose else cr with hc
  have hcr : c r = cr := by simp [hc]
  have hcm : c m = cm := by simp [hc, Ne.symm hrm_ne]
  have hcg : ∀ i, c (g i) = cg i := by
    intro i
    have h1 : g i ≠ r := (hrg_ne i).symm
    have h2 : g i ≠ m := (hmg_ne i).symm
    have hex : ∃ j, g i = g j := ⟨i, rfl⟩
    rw [hc]
    simp only [if_neg h1, if_neg h2, dif_pos hex]
    rw [hginj hex.choose_spec.symm]
  
  set rk : Site d → ℕ ×ₗ ℕ :=
    fun z => if z = r then toLex (0, 0) else if z = m then toLex (1, 0)
             else if h : ∃ i, z = g i then toLex (2, (h.choose : ℕ)) else toLex (3, 0) with hrk
  have hrkr : rk r = toLex (0, 0) := by simp [hrk]
  have hrkm : rk m = toLex (1, 0) := by simp [hrk, Ne.symm hrm_ne]
  have hrkg : ∀ i, rk (g i) = toLex (2, (i : ℕ)) := by
    intro i
    have h1 : g i ≠ r := (hrg_ne i).symm
    have h2 : g i ≠ m := (hmg_ne i).symm
    have hex : ∃ j, g i = g j := ⟨i, rfl⟩
    rw [hrk]
    simp only [if_neg h1, if_neg h2, dif_pos hex]
    rw [hginj hex.choose_spec.symm]
  refine ⟨b, rk, c, hbdata, ?_, ?_, ?_⟩
  · 
    intro yy hyybox htriy u v hyu hneu hyv hnev
    rcases hsingle yy hyybox htriy with rfl | rfl | ⟨i, rfl⟩
    · rw [hcr]; exact hcrf u v hyu hneu hyv hnev
    · rw [hcm]; exact hcmf u v hyu hneu hyv hnev
    · rw [hcg i]; exact hcgf i u v hyu hneu hyv hnev
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn
    rcases hsingle x hxbox htri with rfl | rfl | ⟨i, rfl⟩ <;>
      rcases hsingle x' hx'box htri' with rfl | rfl | ⟨j, rfl⟩
    · exact absurd rfl hxx'
    · rw [hrkr, hrkm]; exact stt_lex_ne_fst (by norm_num)
    · rw [hrkr, hrkg j]; exact stt_lex_ne_fst (by norm_num)
    · rw [hrkr, hrkm]; exact (stt_lex_ne_fst (by norm_num)).symm
    · exact absurd rfl hxx'
    · rw [hrkm, hrkg j]; exact stt_lex_ne_fst (by norm_num)
    · rw [hrkr, hrkg i]; exact (stt_lex_ne_fst (by norm_num)).symm
    · rw [hrkm, hrkg i]; exact (stt_lex_ne_fst (by norm_num)).symm
    · rw [hrkg i, hrkg j]
      refine stt_lex_ne_snd ?_
      intro hij
      exact hxx' (by rw [Fin.val_inj.mp hij])
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn hlt
    rcases hsingle x hxbox htri with rfl | rfl | ⟨i, rfl⟩
    · rcases hsingle x' hx'box htri' with rfl | rfl | ⟨i, rfl⟩
      · exact absurd rfl hxx'
      · rw [hcm]; exact hrm
      · rw [hcg i]; exact hrg i
    · rcases hsingle x' hx'box htri' with rfl | rfl | ⟨i, rfl⟩
      · 
        rw [hrkr, hrkm] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxx'
      · rw [hcg i]; exact hmg i
    · rcases hsingle x' hx'box htri' with rfl | rfl | ⟨j, rfl⟩
      · 
        rw [hrkr, hrkg i] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · 
        rw [hrkm, hrkg i] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · 
        rw [hcg j]
        rw [hrkg i, hrkg j, Prod.Lex.toLex_lt_toLex] at hlt
        have hijlt : (i : ℕ) < (j : ℕ) := by rcases hlt with h | ⟨_, h⟩ <;> [omega; exact h]
        have hi0 : i = 0 := by omega
        have hj1 : j = 1 := by omega
        subst hi0; subst hj1
        exact hgg










theorem stt_Tcount_le_boundary_of_rootedSpanningForest (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : stt_RootedSpanningForest ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  rts_Tcount_le_boundary_of_rootedColoredForest ω n hn
    (stt_rootedColoredForest_of_rootedSpanningForest ω n h)

















theorem stt_burton_keane_bernoulli_of_rootedSpanningForest (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      stt_RootedSpanningForest ω n)
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
  rts_burton_keane_bernoulli_of_rootedColoredForest hd p hp1 hp0
    (fun ω n hn => stt_rootedColoredForest_of_rootedSpanningForest ω n (hres ω n hn))
    htrif

end Percolation

end StatMech
