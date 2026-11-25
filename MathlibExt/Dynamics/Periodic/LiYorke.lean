/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linarith
import Mathlib.Topology.GDelta.MetrizableSpace

@[expose] public section

section
namespace MathlibExt.Dynamics.Periodic.LiYorkeWanted

/-!
# Period three implies chaos — periodic existence

Period-existence conclusion of period three implies chaos for continuous
interval maps: period three forces existence of points of every positive
period.
-/


private theorem fix_of_cover (G : ℝ → ℝ) (hG : Continuous G) (u v : ℝ) (huv : u ≤ v)
    (hcov : Set.Icc u v ⊆ G '' Set.Icc u v) : ∃ x ∈ Set.Icc u v, G x = x := by
  obtain ⟨s, hs_mem, hs_eq⟩ := hcov (Set.mem_Icc.mpr ⟨le_rfl, huv⟩)
  obtain ⟨t, ht_mem, ht_eq⟩ := hcov (Set.mem_Icc.mpr ⟨huv, le_rfl⟩)
  have hH : Continuous (fun x => G x - x) := hG.sub continuous_id'
  rw [Set.mem_Icc] at hs_mem ht_mem
  rcases le_total s t with hst | hst
  · have hmem : (0 : ℝ) ∈ Set.Icc (G s - s) (G t - t) :=
      Set.mem_Icc.mpr ⟨by linarith [hs_mem.1], by linarith [ht_mem.2]⟩
    have hsub := intermediate_value_Icc hst hH.continuousOn hmem
    obtain ⟨w, hw_mem, hw_eq⟩ := hsub
    rw [Set.mem_Icc] at hw_mem
    refine ⟨w, Set.mem_Icc.mpr ⟨le_trans hs_mem.1 hw_mem.1, le_trans hw_mem.2 ht_mem.2⟩, ?_⟩
    have : G w - w = 0 := hw_eq
    linarith
  · have hmem : (0 : ℝ) ∈ Set.Icc (G s - s) (G t - t) :=
      Set.mem_Icc.mpr ⟨by linarith [hs_mem.1], by linarith [ht_mem.2]⟩
    have hsub := intermediate_value_Icc' hst hH.continuousOn hmem
    obtain ⟨w, hw_mem, hw_eq⟩ := hsub
    rw [Set.mem_Icc] at hw_mem
    refine ⟨w, Set.mem_Icc.mpr ⟨le_trans ht_mem.1 hw_mem.1, le_trans hw_mem.2 hs_mem.2⟩, ?_⟩
    have : G w - w = 0 := hw_eq
    linarith


private theorem pullback_interval (F : ℝ → ℝ) (hF : Continuous F) (a b c d : ℝ)
    (_hab : a ≤ b) (hcd : c ≤ d)
    (hcov : Set.Icc c d ⊆ F '' Set.Icc a b) :
    ∃ α β : ℝ, a ≤ α ∧ α ≤ β ∧ β ≤ b ∧ F '' Set.Icc α β = Set.Icc c d := by
  have hSc : IsClosed {x : ℝ | x ∈ Set.Icc a b ∧ F x = c} := by
    have heq : {x : ℝ | x ∈ Set.Icc a b ∧ F x = c} = F ⁻¹' {c} ∩ Set.Icc a b := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_inter_iff]
      tauto
    rw [heq]
    exact (isClosed_singleton.preimage hF).inter isClosed_Icc
  have hTc : IsClosed {x : ℝ | x ∈ Set.Icc a b ∧ F x = d} := by
    have heq : {x : ℝ | x ∈ Set.Icc a b ∧ F x = d} = F ⁻¹' {d} ∩ Set.Icc a b := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_inter_iff]
      tauto
    rw [heq]
    exact (isClosed_singleton.preimage hF).inter isClosed_Icc
  obtain ⟨s0c, hs0c_mem, hs0c_eq⟩ := hcov (Set.mem_Icc.mpr ⟨le_rfl, hcd⟩)
  obtain ⟨s0d, hs0d_mem, hs0d_eq⟩ := hcov (Set.mem_Icc.mpr ⟨hcd, le_rfl⟩)
  have hSne : {x : ℝ | x ∈ Set.Icc a b ∧ F x = c}.Nonempty := ⟨s0c, hs0c_mem, hs0c_eq⟩
  have hTne : {x : ℝ | x ∈ Set.Icc a b ∧ F x = d}.Nonempty := ⟨s0d, hs0d_mem, hs0d_eq⟩
  by_cases hcase : ∃ s0 : ℝ, ∃ t0 : ℝ, s0 ∈ Set.Icc a b ∧ F s0 = c ∧
      t0 ∈ Set.Icc a b ∧ F t0 = d ∧ s0 ≤ t0
  · obtain ⟨s0, t0, hs0mem, hs0eq, ht0mem, ht0eq, hle⟩ := hcase
    have hA1c : IsClosed ({x : ℝ | x ∈ Set.Icc a b ∧ F x = c} ∩ Set.Iic t0) :=
      hSc.inter isClosed_Iic
    have hA1ne : ({x : ℝ | x ∈ Set.Icc a b ∧ F x = c} ∩ Set.Iic t0).Nonempty :=
      ⟨s0, ⟨hs0mem, hs0eq⟩, hle⟩
    have hA1bdd : BddAbove ({x : ℝ | x ∈ Set.Icc a b ∧ F x = c} ∩ Set.Iic t0) :=
      ⟨t0, fun x hx => hx.2⟩
    set α := sSup ({x : ℝ | x ∈ Set.Icc a b ∧ F x = c} ∩ Set.Iic t0) with hαdef
    have hαmem := hA1c.csSup_mem hA1ne hA1bdd
    obtain ⟨⟨hαmem_ab, hαF⟩, hαt⟩ := hαmem
    have hB1c : IsClosed ({x : ℝ | x ∈ Set.Icc a b ∧ F x = d} ∩ Set.Ici α) :=
      hTc.inter isClosed_Ici
    have hB1ne : ({x : ℝ | x ∈ Set.Icc a b ∧ F x = d} ∩ Set.Ici α).Nonempty :=
      ⟨t0, ⟨ht0mem, ht0eq⟩, hαt⟩
    have hB1bdd : BddBelow ({x : ℝ | x ∈ Set.Icc a b ∧ F x = d} ∩ Set.Ici α) :=
      ⟨α, fun x hx => hx.2⟩
    set β := sInf ({x : ℝ | x ∈ Set.Icc a b ∧ F x = d} ∩ Set.Ici α) with hβdef
    have hβmem := hB1c.csInf_mem hB1ne hB1bdd
    obtain ⟨⟨hβmem_ab, hβF⟩, hαβ⟩ := hβmem
    have hβt : β ≤ t0 := csInf_le hB1bdd ⟨⟨ht0mem, ht0eq⟩, hαt⟩
    rw [Set.mem_Icc] at hαmem_ab hβmem_ab
    refine ⟨α, β, hαmem_ab.1, hαβ, hβmem_ab.2, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx_mem, hx_eq⟩
      rw [Set.mem_Icc] at hx_mem
      subst hx_eq
      constructor
      · by_contra hlt
        have hlt : F x < c := lt_of_not_ge hlt
        have hxne : x ≠ β := by
          intro h; rw [h, hβF] at hlt; exact absurd hlt (not_lt_of_ge hcd)
        have hxb : x < β := lt_of_le_of_ne hx_mem.2 hxne
        have hmemc : c ∈ Set.Icc (F x) (F β) :=
          Set.mem_Icc.mpr ⟨hlt.le, by rw [hβF]; exact hcd⟩
        obtain ⟨v, hv_mem, hv_eq⟩ :=
          intermediate_value_Icc hxb.le hF.continuousOn hmemc
        rw [Set.mem_Icc] at hv_mem
        have hvA1 : v ∈ ({x : ℝ | x ∈ Set.Icc a b ∧ F x = c} ∩ Set.Iic t0) := by
          refine ⟨⟨Set.mem_Icc.mpr ⟨le_trans hαmem_ab.1 (le_trans hx_mem.1 hv_mem.1),
            le_trans hv_mem.2 (le_trans hβt ht0mem.2)⟩, hv_eq⟩, le_trans hv_mem.2 hβt⟩
        have hvα : v ≤ α := le_csSup hA1bdd hvA1
        have hxα : x = α := le_antisymm (le_trans hv_mem.1 hvα) hx_mem.1
        rw [hxα, hαF] at hlt
        exact lt_irrefl c hlt
      · by_contra hgt
        have hgt : d < F x := lt_of_not_ge hgt
        have hxne : x ≠ α := by
          intro h; rw [h, hαF] at hgt; exact absurd hgt (not_lt_of_ge hcd)
        have hαx : α < x := lt_of_le_of_ne hx_mem.1 (fun h => hxne h.symm)
        have hmemd : d ∈ Set.Icc (F α) (F x) :=
          Set.mem_Icc.mpr ⟨by rw [hαF]; exact hcd, hgt.le⟩
        obtain ⟨w, hw_mem, hw_eq⟩ :=
          intermediate_value_Icc hαx.le hF.continuousOn hmemd
        rw [Set.mem_Icc] at hw_mem
        have hwB1 : w ∈ ({x : ℝ | x ∈ Set.Icc a b ∧ F x = d} ∩ Set.Ici α) := by
          refine ⟨⟨Set.mem_Icc.mpr ⟨le_trans hαmem_ab.1 hw_mem.1,
            le_trans hw_mem.2 (le_trans hx_mem.2 hβmem_ab.2)⟩, hw_eq⟩, hw_mem.1⟩
        have hβw : β ≤ w := csInf_le hB1bdd hwB1
        have hxβ : x = β := le_antisymm hx_mem.2 (le_trans hβw hw_mem.2)
        rw [hxβ, hβF] at hgt
        exact lt_irrefl d hgt
    · intro hy
      have hy' : y ∈ Set.Icc (F α) (F β) := by rw [hαF, hβF]; exact hy
      exact intermediate_value_Icc hαβ hF.continuousOn hy'
  · have hlt : ∀ s0 t0 : ℝ, s0 ∈ Set.Icc a b → F s0 = c → t0 ∈ Set.Icc a b →
        F t0 = d → t0 < s0 := by
      intro s0 t0 h1 h2 h3 h4
      by_contra hle
      exact hcase ⟨s0, t0, h1, h2, h3, h4, le_of_not_gt hle⟩
    have hle_d : s0d ≤ s0c :=
      le_of_lt (hlt s0c s0d hs0c_mem hs0c_eq hs0d_mem hs0d_eq)
    have hA2c : IsClosed ({x : ℝ | x ∈ Set.Icc a b ∧ F x = d} ∩ Set.Iic s0c) :=
      hTc.inter isClosed_Iic
    have hA2ne : ({x : ℝ | x ∈ Set.Icc a b ∧ F x = d} ∩ Set.Iic s0c).Nonempty :=
      ⟨s0d, ⟨hs0d_mem, hs0d_eq⟩, hle_d⟩
    have hA2bdd : BddAbove ({x : ℝ | x ∈ Set.Icc a b ∧ F x = d} ∩ Set.Iic s0c) :=
      ⟨s0c, fun x hx => hx.2⟩
    set α := sSup ({x : ℝ | x ∈ Set.Icc a b ∧ F x = d} ∩ Set.Iic s0c) with hαdef
    have hαmem := hA2c.csSup_mem hA2ne hA2bdd
    obtain ⟨⟨hαmem_ab, hαF⟩, hαs⟩ := hαmem
    have hB2c : IsClosed ({x : ℝ | x ∈ Set.Icc a b ∧ F x = c} ∩ Set.Ici α) :=
      hSc.inter isClosed_Ici
    have hB2ne : ({x : ℝ | x ∈ Set.Icc a b ∧ F x = c} ∩ Set.Ici α).Nonempty :=
      ⟨s0c, ⟨hs0c_mem, hs0c_eq⟩, hαs⟩
    have hB2bdd : BddBelow ({x : ℝ | x ∈ Set.Icc a b ∧ F x = c} ∩ Set.Ici α) :=
      ⟨α, fun x hx => hx.2⟩
    set β := sInf ({x : ℝ | x ∈ Set.Icc a b ∧ F x = c} ∩ Set.Ici α) with hβdef
    have hβmem := hB2c.csInf_mem hB2ne hB2bdd
    obtain ⟨⟨hβmem_ab, hβF⟩, hαβ⟩ := hβmem
    have hβs : β ≤ s0c := csInf_le hB2bdd ⟨⟨hs0c_mem, hs0c_eq⟩, hαs⟩
    rw [Set.mem_Icc] at hαmem_ab hβmem_ab
    refine ⟨α, β, hαmem_ab.1, hαβ, hβmem_ab.2, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx_mem, hx_eq⟩
      rw [Set.mem_Icc] at hx_mem
      subst hx_eq
      constructor
      · by_contra hlt2
        have hlt2 : F x < c := lt_of_not_ge hlt2
        have hxne : x ≠ β := by
          intro h; rw [h, hβF] at hlt2; exact lt_irrefl c hlt2
        have hxb : x < β := lt_of_le_of_ne hx_mem.2 hxne
        have hmemc : c ∈ Set.Icc (F x) (F α) :=
          Set.mem_Icc.mpr ⟨hlt2.le, by rw [hαF]; exact hcd⟩
        obtain ⟨w, hw_mem, hw_eq⟩ :=
          intermediate_value_Icc' hx_mem.1 hF.continuousOn hmemc
        rw [Set.mem_Icc] at hw_mem
        have hwB2 : w ∈ ({x : ℝ | x ∈ Set.Icc a b ∧ F x = c} ∩ Set.Ici α) := by
          refine ⟨⟨Set.mem_Icc.mpr ⟨le_trans hαmem_ab.1 hw_mem.1,
            le_trans hw_mem.2 (le_trans hx_mem.2 hβmem_ab.2)⟩, hw_eq⟩, hw_mem.1⟩
        have hβw : β ≤ w := csInf_le hB2bdd hwB2
        have hxβ : x = β := le_antisymm hx_mem.2 (le_trans hβw hw_mem.2)
        rw [hxβ, hβF] at hlt2
        exact lt_irrefl c hlt2
      · by_contra hgt
        have hgt : d < F x := lt_of_not_ge hgt
        have hxne : x ≠ α := by
          intro h; rw [h, hαF] at hgt; exact lt_irrefl d hgt
        have hαx : α < x := lt_of_le_of_ne hx_mem.1 (fun h => hxne h.symm)
        have hmemd : d ∈ Set.Icc (F β) (F x) :=
          Set.mem_Icc.mpr ⟨by rw [hβF]; exact hcd, hgt.le⟩
        obtain ⟨v, hv_mem, hv_eq⟩ :=
          intermediate_value_Icc' hx_mem.2 hF.continuousOn hmemd
        rw [Set.mem_Icc] at hv_mem
        have hvA2 : v ∈ ({x : ℝ | x ∈ Set.Icc a b ∧ F x = d} ∩ Set.Iic s0c) := by
          refine ⟨⟨Set.mem_Icc.mpr ⟨le_trans hαmem_ab.1 (le_trans hx_mem.1 hv_mem.1),
            le_trans hv_mem.2 hβmem_ab.2⟩, hv_eq⟩, le_trans hv_mem.2 hβs⟩
        have hvα : v ≤ α := le_csSup hA2bdd hvA2
        have hxα : x = α := le_antisymm (le_trans hv_mem.1 hvα) hx_mem.1
        rw [hxα, hαF] at hgt
        exact lt_irrefl d hgt
    · intro hy
      have hy' : y ∈ Set.Icc (F β) (F α) := by rw [hβF, hαF]; exact hy
      exact intermediate_value_Icc' hαβ hF.continuousOn hy'


private theorem tower_aux (F : ℝ → ℝ) (hF : Continuous F) (b1 b2 : ℝ)
    (hb : b1 ≤ b2) (hcover : Set.Icc b1 b2 ⊆ F '' Set.Icc b1 b2) (i : ℕ) :
    ∀ u1 u2 : ℝ, u1 ≤ u2 → Set.Icc u1 u2 ⊆ Set.Icc b1 b2 →
    ∃ α β : ℝ, α ≤ β ∧ Set.Icc α β ⊆ Set.Icc b1 b2 ∧
      F^[i] '' Set.Icc α β = Set.Icc u1 u2 ∧
      ∀ k < i, F^[k] '' Set.Icc α β ⊆ Set.Icc b1 b2 := by
  induction i with
  | zero =>
    intro u1 u2 hle hsub
    refine ⟨u1, u2, hle, hsub, ?_, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    rw [Function.iterate_zero, Set.image_id]
  | succ i ih =>
    intro u1 u2 hle hsub
    have hUV : Set.Icc u1 u2 ⊆ F '' Set.Icc b1 b2 := le_trans hsub hcover
    obtain ⟨γ, δ, hγb, hγδ, hδb, hmap⟩ :=
      pullback_interval F hF b1 b2 u1 u2 hb hle hUV
    obtain ⟨α, β, hαβ, hTsub, hTmap, hTinter⟩ :=
      ih γ δ hγδ (Set.Icc_subset_Icc hγb hδb)
    refine ⟨α, β, hαβ, hTsub, ?_, ?_⟩
    · have hcomp : F^[i + 1] = F ∘ F^[i] := Function.iterate_succ' F i
      rw [hcomp, Set.image_comp, hTmap]
      exact hmap
    · intro k hk
      have hki : k ≤ i := by omega
      rcases eq_or_lt_of_le hki with rfl | hki'
      · rw [hTmap]
        exact Set.Icc_subset_Icc hγb hδb
      · exact hTinter k hki'

private theorem horseshoe_main (F : ℝ → ℝ) (hF : Continuous F)
    (a1 a2 b1 b2 mid : ℝ)
    (hmidA : mid ∈ Set.Icc a1 a2) (hmidB : mid ∈ Set.Icc b1 b2)
    (hinter : Set.Icc a1 a2 ∩ Set.Icc b1 b2 ⊆ {mid})
    (hFA : Set.Icc b1 b2 ⊆ F '' Set.Icc a1 a2)
    (hFB : Set.Icc a1 a2 ∪ Set.Icc b1 b2 ⊆ F '' Set.Icc b1 b2)
    (hex : F (F mid) ∉ Set.Icc b1 b2) :
    ∀ n : ℕ, 0 < n → ∃ y, Function.minimalPeriod F y = n := by
  obtain ⟨hmidA1, hmidA2⟩ := Set.mem_Icc.mp hmidA
  obtain ⟨hmidB1, hmidB2⟩ := Set.mem_Icc.mp hmidB
  have hb12 : b1 ≤ b2 := le_trans hmidB1 hmidB2
  have ha12 : a1 ≤ a2 := le_trans hmidA1 hmidA2
  have hcoverB : Set.Icc b1 b2 ⊆ F '' Set.Icc b1 b2 :=
    le_trans Set.subset_union_right hFB
  intro n hn
  by_cases hn1 : n = 1
  · subst hn1
    obtain ⟨x, hx_mem, hx_eq⟩ := fix_of_cover F hF b1 b2 hb12 hcoverB
    exact ⟨x, Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hx_eq⟩
  · have hn2 : 2 ≤ n := by omega
    have hex2 : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    obtain ⟨m, rfl⟩ := hex2
    obtain ⟨γ, δ, hγa, hγδ, hδa, hSmap⟩ :=
      pullback_interval F hF a1 a2 b1 b2 ha12 hb12 hFA
    have hSsub : Set.Icc γ δ ⊆ Set.Icc a1 a2 := Set.Icc_subset_Icc hγa hδa
    have hSV : Set.Icc γ δ ⊆ F '' Set.Icc b1 b2 :=
      le_trans hSsub (le_trans Set.subset_union_left hFB)
    obtain ⟨η, θ, hηb, hηθ, hθb, hVmap⟩ :=
      pullback_interval F hF b1 b2 γ δ hb12 hγδ hSV
    have hVsub : Set.Icc η θ ⊆ Set.Icc b1 b2 := Set.Icc_subset_Icc hηb hθb
    obtain ⟨α, β, hαβ, hJsub, hJmap, hJinter⟩ :=
      tower_aux F hF b1 b2 hb12 hcoverB m η θ hηθ hVsub
    have hFm1 : F^[m + 1] '' Set.Icc α β = Set.Icc γ δ := by
      have hcomp : F^[m + 1] = F ∘ F^[m] := Function.iterate_succ' F m
      rw [hcomp, Set.image_comp, hJmap]
      exact hVmap
    have hFm2 : F^[m + 2] '' Set.Icc α β = Set.Icc b1 b2 := by
      have hcomp : F^[m + 2] = F ∘ F^[m + 1] := Function.iterate_succ' F (m + 1)
      rw [hcomp, Set.image_comp, hFm1]
      exact hSmap
    obtain ⟨x, hxJ, hxfixed⟩ := fix_of_cover (F^[m + 2]) (hF.iterate (m + 2)) α β hαβ
      (by rw [hFm2]; exact hJsub)
    have hper : Function.IsPeriodicPt F (m + 2) x := hxfixed
    have hpdvd : Function.minimalPeriod F x ∣ m + 2 := hper.minimalPeriod_dvd
    have hppos : 0 < Function.minimalPeriod F x :=
      Function.minimalPeriod_pos_of_mem_periodicPts
        (Function.mem_periodicPts.mpr ⟨m + 2, by omega, hper⟩)
    have hple : Function.minimalPeriod F x ≤ m + 2 := Nat.le_of_dvd (by omega) hpdvd
    by_cases hpeq : Function.minimalPeriod F x = m + 2
    · exact ⟨x, hpeq⟩
    · exfalso
      have hplt : Function.minimalPeriod F x < m + 2 := lt_of_le_of_ne hple hpeq
      have hxA : F^[m + 1] x ∈ Set.Icc a1 a2 := by
        have hmem : F^[m + 1] x ∈ F^[m + 1] '' Set.Icc α β := ⟨x, hxJ, rfl⟩
        rw [hFm1] at hmem
        exact hSsub hmem
      have hmod : F^[m + 1] x = F^[(m + 1) % Function.minimalPeriod F x] x := by
        rw [Function.iterate_mod_minimalPeriod_eq]
      have hmodle : (m + 1) % Function.minimalPeriod F x ≤ m := by
        have h1 : (m + 1) % Function.minimalPeriod F x < Function.minimalPeriod F x :=
          Nat.mod_lt _ hppos
        omega
      have hxB : F^[m + 1] x ∈ Set.Icc b1 b2 := by
        rw [hmod]
        by_cases hltm : (m + 1) % Function.minimalPeriod F x < m
        · have hmem : F^[(m + 1) % Function.minimalPeriod F x] x ∈
              F^[(m + 1) % Function.minimalPeriod F x] '' Set.Icc α β := ⟨x, hxJ, rfl⟩
          exact hJinter _ hltm hmem
        · have heqm : (m + 1) % Function.minimalPeriod F x = m := by omega
          have hmem : F^[(m + 1) % Function.minimalPeriod F x] x ∈
              F^[(m + 1) % Function.minimalPeriod F x] '' Set.Icc α β := ⟨x, hxJ, rfl⟩
          rw [heqm, hJmap] at hmem
          rw [heqm]
          exact hVsub hmem
      have hmid_eq : F^[m + 1] x = mid := by
        have hmem : F^[m + 1] x ∈ Set.Icc a1 a2 ∩ Set.Icc b1 b2 := ⟨hxA, hxB⟩
        have hsing := hinter hmem
        simpa using hsing
      have hstep : F^[m + 2] x = F (F^[m + 1] x) :=
        Function.iterate_succ_apply' F (m + 1) x
      have hxe : x = F mid := by
        rw [hstep, hmid_eq] at hxfixed
        exact hxfixed.symm
      have hFx : F x = F (F mid) := by rw [hxe]
      have hFxB : F x ∈ Set.Icc b1 b2 := by
        by_cases hm0 : m = 0
        · subst hm0
          have e1 : F^[0 + 1] x = F x := by rw [show (0 : ℕ) + 1 = 1 from rfl,
            Function.iterate_one]
          rw [← e1, hmid_eq]
          exact hmidB
        · have h1m : 1 ≤ m := by omega
          rcases eq_or_lt_of_le h1m with h1eq | h1lt
          · have hFm : F^[m] x ∈ F^[m] '' Set.Icc α β := ⟨x, hxJ, rfl⟩
            rw [hJmap] at hFm
            have e1 : F^[1] x = F x := by rw [Function.iterate_one]
            have em : F^[m] x = F x := by rw [← h1eq]; exact e1
            rw [← em]
            exact hVsub hFm
          · have hF1 : F^[1] x ∈ F^[1] '' Set.Icc α β := ⟨x, hxJ, rfl⟩
            have e1 : F^[1] x = F x := by rw [Function.iterate_one]
            rw [← e1]
            exact hJinter 1 h1lt hF1
      rw [hFx] at hFxB
      exact absurd hFxB hex

private theorem horseshoe_R (F : ℝ → ℝ) (hF : Continuous F) (l mid r : ℝ)
    (hlm : l < mid) (hmr : mid < r)
    (h1 : F l = mid) (h2 : F mid = r) (h3 : F r = l) :
    ∀ n : ℕ, 0 < n → ∃ y, Function.minimalPeriod F y = n := by
  apply horseshoe_main F hF l mid mid r
  · exact Set.mem_Icc.mpr ⟨hlm.le, le_rfl⟩
  · exact Set.mem_Icc.mpr ⟨le_rfl, hmr.le⟩
  · intro x hx
    obtain ⟨hxA, hxB⟩ := hx
    obtain ⟨_, hxA2⟩ := Set.mem_Icc.mp hxA
    obtain ⟨hxB1, _⟩ := Set.mem_Icc.mp hxB
    exact Set.mem_singleton_iff.mpr (le_antisymm hxA2 hxB1)
  · have hcov : Set.Icc (F l) (F mid) ⊆ F '' Set.Icc l mid :=
      intermediate_value_Icc hlm.le hF.continuousOn
    rw [h1, h2] at hcov
    exact hcov
  · have hcov : Set.Icc (F r) (F mid) ⊆ F '' Set.Icc mid r :=
      intermediate_value_Icc' hmr.le hF.continuousOn
    rw [h3, h2] at hcov
    intro x hx
    rcases hx with hxA | hxB
    · obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hxA
      exact hcov (Set.mem_Icc.mpr ⟨hx1, le_trans hx2 hmr.le⟩)
    · obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hxB
      exact hcov (Set.mem_Icc.mpr ⟨le_trans hlm.le hx1, hx2⟩)
  · rw [h2, h3]
    intro hcon
    obtain ⟨h1', _⟩ := Set.mem_Icc.mp hcon
    exact absurd h1' (not_le_of_gt hlm)

private theorem horseshoe_L (F : ℝ → ℝ) (hF : Continuous F) (l mid r : ℝ)
    (hlm : l < mid) (hmr : mid < r)
    (h1 : F l = r) (h2 : F mid = l) (h3 : F r = mid) :
    ∀ n : ℕ, 0 < n → ∃ y, Function.minimalPeriod F y = n := by
  apply horseshoe_main F hF mid r l mid
  · exact Set.mem_Icc.mpr ⟨le_rfl, hmr.le⟩
  · exact Set.mem_Icc.mpr ⟨hlm.le, le_rfl⟩
  · intro x hx
    obtain ⟨hxA, hxB⟩ := hx
    obtain ⟨hxA1, _⟩ := Set.mem_Icc.mp hxA
    obtain ⟨_, hxB2⟩ := Set.mem_Icc.mp hxB
    exact Set.mem_singleton_iff.mpr (le_antisymm hxB2 hxA1)
  · have hcov : Set.Icc (F mid) (F r) ⊆ F '' Set.Icc mid r :=
      intermediate_value_Icc hmr.le hF.continuousOn
    rw [h2, h3] at hcov
    exact hcov
  · have hcov : Set.Icc (F mid) (F l) ⊆ F '' Set.Icc l mid :=
      intermediate_value_Icc' hlm.le hF.continuousOn
    rw [h2, h1] at hcov
    intro x hx
    rcases hx with hxA | hxB
    · obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hxA
      exact hcov (Set.mem_Icc.mpr ⟨le_trans hlm.le hx1, hx2⟩)
    · obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hxB
      exact hcov (Set.mem_Icc.mpr ⟨hx1, le_trans hx2 hmr.le⟩)
  · rw [h2, h1]
    intro hcon
    obtain ⟨_, h2'⟩ := Set.mem_Icc.mp hcon
    exact absurd h2' (not_le_of_gt hmr)

private theorem liYorke_period_three_R (F : ℝ → ℝ) (hF : Continuous F)
    (h3 : ∃ a, Function.minimalPeriod F a = 3) :
    ∀ n : ℕ, 0 < n → ∃ y, Function.minimalPeriod F y = n := by
  obtain ⟨a, ha3⟩ := h3
  have hper3 : Function.IsPeriodicPt F 3 a := by
    have h := Function.isPeriodicPt_minimalPeriod F a
    rw [ha3] at h
    exact h
  have h3eq : F^[3] a = a := hper3
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := F) (x := a)
  rw [ha3] at hinj
  have hmem0 : (0 : ℕ) ∈ Set.Iio 3 := by decide
  have hmem1 : (1 : ℕ) ∈ Set.Iio 3 := by decide
  have hmem2 : (2 : ℕ) ∈ Set.Iio 3 := by decide
  have d01r : F^[0] a ≠ F^[1] a := fun h => absurd (hinj hmem0 hmem1 h) (by omega)
  have d02r : F^[0] a ≠ F^[2] a := fun h => absurd (hinj hmem0 hmem2 h) (by omega)
  have d12r : F^[1] a ≠ F^[2] a := fun h => absurd (hinj hmem1 hmem2 h) (by omega)
  have e0 : F^[0] a = a := Function.iterate_zero_apply F a
  have e1 : F^[1] a = F a := by rw [Function.iterate_one]
  have d01 : a ≠ F a := by rw [e0, e1] at d01r; exact d01r
  have d02 : a ≠ F^[2] a := by rw [e0] at d02r; exact d02r
  have d12 : F a ≠ F^[2] a := by rw [e1] at d12r; exact d12r
  have cyc2 : F (F a) = F^[2] a := by
    rw [← e1]
    exact (Function.iterate_succ_apply' F 1 a).symm
  have cyc3 : F (F^[2] a) = a := by
    have h := Function.iterate_succ_apply' F 2 a
    rw [show (2 : ℕ).succ = 3 from rfl] at h
    rw [← h, h3eq]
  intro n hn
  rcases lt_trichotomy a (F a) with h01 | h01 | h01
  · rcases lt_trichotomy (F a) (F^[2] a) with h12 | h12 | h12
    · exact horseshoe_R F hF a (F a) (F^[2] a) h01 h12 rfl cyc2 cyc3 n hn
    · exact absurd h12 d12
    · rcases lt_trichotomy a (F^[2] a) with h02 | h02 | h02
      · exact horseshoe_L F hF a (F^[2] a) (F a) h02 h12 rfl cyc3 cyc2 n hn
      · exact absurd h02 d02
      · exact horseshoe_R F hF (F^[2] a) a (F a) h02 h01 cyc3 rfl cyc2 n hn
  · exact absurd h01 d01
  · rcases lt_trichotomy (F a) (F^[2] a) with h12 | h12 | h12
    · rcases lt_trichotomy (F^[2] a) a with h20 | h20 | h20
      · exact horseshoe_R F hF (F a) (F^[2] a) a h12 h20 cyc2 cyc3 rfl n hn
      · exact absurd h20 d02.symm
      · exact horseshoe_L F hF (F a) a (F^[2] a) h01 h20 cyc2 rfl cyc3 n hn
    · exact absurd h12 d12
    · exact horseshoe_L F hF (F^[2] a) (F a) a h12 h01 cyc3 cyc2 rfl n hn

/--
**Li–Yorke theorem: period three implies all periods.** Let $f \colon [0, 1] \to [0, 1]$ be a
continuous map. If some point of $[0, 1]$ has minimal period $3$ under $f$, then for every
positive integer $n$ some point of $[0, 1]$ has minimal period $n$ under $f$.

Source: T.-Y. Li and J. A. Yorke, Period Three Implies Chaos, Amer. Math. Monthly 82 (1975),
985-992, DOI 10.2307/2318254.

Proves `Wanted` entry `liYorke_period_three_implies_periods`.
-/
theorem liYorke_period_three_implies_periods
    (f : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1)
    (hf : Continuous f)
    (h3 : ∃ x, Function.minimalPeriod f x = 3) :
    ∀ (n : ℕ), 0 < n → ∃ y, Function.minimalPeriod f y = n := by
  have hclamp : Continuous fun t : ℝ => max 0 (min t 1) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hclamp_mem : ∀ t : ℝ, max 0 (min t 1) ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    Set.mem_Icc.mpr ⟨le_max_left 0 _, max_le (by norm_num) (min_le_right t 1)⟩
  set F : ℝ → ℝ := fun t => ((f ⟨max 0 (min t 1),
    (Set.mem_Icc.mp (hclamp_mem t)).1, (Set.mem_Icc.mp (hclamp_mem t)).2⟩).val) with hFdef
  have hFt : ∀ t : ℝ, F t = ((f ⟨max 0 (min t 1),
    (Set.mem_Icc.mp (hclamp_mem t)).1, (Set.mem_Icc.mp (hclamp_mem t)).2⟩).val) :=
    fun t => rfl
  have hFcont : Continuous F := by
    rw [hFdef]
    exact continuous_subtype_val.comp
      (hf.comp (hclamp.subtype_mk (fun t => hclamp_mem t)))
  have hFmem : ∀ t : ℝ, F t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t
    rw [hFt]
    exact (f _).property
  have hclamp_id : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → max 0 (min t 1) = t := by
    intro t ht
    obtain ⟨h0, h1⟩ := Set.mem_Icc.mp ht
    rw [min_eq_left h1, max_eq_right h0]
  have hFagree : ∀ x : Set.Icc (0 : ℝ) 1, F x.val = (f x).val := by
    intro x
    rw [hFt]
    have hcl : max 0 (min x.val 1) = x.val := hclamp_id x.val x.property
    have hmx : (⟨max 0 (min x.val 1), (Set.mem_Icc.mp (hclamp_mem x.val)).1,
        (Set.mem_Icc.mp (hclamp_mem x.val)).2⟩ : Set.Icc (0 : ℝ) 1) = x :=
      Subtype.ext hcl
    rw [hmx]
  have hiter : ∀ (n : ℕ) (x : Set.Icc (0 : ℝ) 1),
      F^[n] x.val = ((f^[n] x).val) := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : F^[n + 1] x.val = F (F^[n] x.val) := Function.iterate_succ_apply' F n x
      have h2 : f^[n + 1] x = f (f^[n] x) := Function.iterate_succ_apply' f n x
      rw [h1, ih, h2]
      exact hFagree _
  obtain ⟨x0, hx03⟩ := h3
  have hx0per : Function.IsPeriodicPt f 3 x0 := by
    have h := Function.isPeriodicPt_minimalPeriod f x0
    rw [hx03] at h
    exact h
  have hx0eq : f^[3] x0 = x0 := hx0per
  have hF3 : F^[3] x0.val = x0.val := by rw [hiter 3 x0, hx0eq]
  have hFper : Function.IsPeriodicPt F 3 x0.val := hF3
  have hmpF_dvd : Function.minimalPeriod F x0.val ∣ 3 := hFper.minimalPeriod_dvd
  have hmpF13 : Function.minimalPeriod F x0.val = 1 ∨
      Function.minimalPeriod F x0.val = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp hmpF_dvd
  have hmpF3 : Function.minimalPeriod F x0.val = 3 := by
    rcases hmpF13 with h | h
    · exfalso
      have hfix : Function.IsFixedPt F x0.val :=
        Function.minimalPeriod_eq_one_iff_isFixedPt.mp h
      have hfixeq : F x0.val = x0.val := hfix
      have hfx0 : f x0 = x0 := by
        have e : F x0.val = (f x0).val := hFagree x0
        rw [hfixeq] at e
        exact Subtype.ext e.symm
      have hfx0' : Function.IsFixedPt f x0 := hfx0
      have h1 : Function.minimalPeriod f x0 = 1 :=
        Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfx0'
      omega
    · exact h
  have hall := liYorke_period_three_R F hFcont ⟨x0.val, hmpF3⟩
  intro n hn
  obtain ⟨y, hy⟩ := hall n hn
  have hmppos : 0 < Function.minimalPeriod F y := by rw [hy]; exact hn
  obtain ⟨k, hk⟩ : ∃ k, Function.minimalPeriod F y = k + 1 :=
    ⟨Function.minimalPeriod F y - 1, by omega⟩
  have hyeq : F^[Function.minimalPeriod F y] y = y :=
    Function.isPeriodicPt_minimalPeriod F y
  have hFk : F (F^[k] y) = y := by
    have h1 : F (F^[k] y) = F^[k + 1] y := (Function.iterate_succ_apply' F k y).symm
    rw [h1, ← hk]
    exact hyeq
  have hyI : y ∈ Set.Icc (0 : ℝ) 1 := by
    have hsub : F '' Set.univ ⊆ Set.Icc (0 : ℝ) 1 := by
      rintro _ ⟨t, _, rfl⟩
      exact hFmem t
    exact hsub ⟨F^[k] y, Set.mem_univ _, hFk⟩
  obtain ⟨hym0, hym1⟩ := Set.mem_Icc.mp hyI
  have hFn : F^[n] y = y := by rw [← hy]; exact hyeq
  have hfn : f^[n] ⟨y, hym0, hym1⟩ = ⟨y, hym0, hym1⟩ := by
    apply Subtype.ext
    change ((f^[n] ⟨y, hym0, hym1⟩).val) = y
    rw [← hiter n ⟨y, hym0, hym1⟩]
    exact hFn
  have hpern : Function.IsPeriodicPt f n ⟨y, hym0, hym1⟩ := hfn
  have hmpn_dvd : Function.minimalPeriod f ⟨y, hym0, hym1⟩ ∣ n := hpern.minimalPeriod_dvd
  have hFmp : F^[Function.minimalPeriod f ⟨y, hym0, hym1⟩] y = y := by
    have h1 : F^[Function.minimalPeriod f ⟨y, hym0, hym1⟩]
        (⟨y, hym0, hym1⟩ : Set.Icc (0 : ℝ) 1).val =
        ((f^[Function.minimalPeriod f ⟨y, hym0, hym1⟩] ⟨y, hym0, hym1⟩).val) :=
      hiter _ _
    have h2 : f^[Function.minimalPeriod f ⟨y, hym0, hym1⟩] ⟨y, hym0, hym1⟩ =
        ⟨y, hym0, hym1⟩ :=
      Function.isPeriodicPt_minimalPeriod f _
    change F^[Function.minimalPeriod f ⟨y, hym0, hym1⟩]
      (⟨y, hym0, hym1⟩ : Set.Icc (0 : ℝ) 1).val = y
    rw [h1, h2]
  have hn_dvd : n ∣ Function.minimalPeriod f ⟨y, hym0, hym1⟩ := by
    rw [← hy]
    exact Function.IsPeriodicPt.minimalPeriod_dvd hFmp
  have hfinal : Function.minimalPeriod f ⟨y, hym0, hym1⟩ = n :=
    Nat.dvd_antisymm hmpn_dvd hn_dvd
  exact ⟨⟨y, hym0, hym1⟩, hfinal⟩

end MathlibExt.Dynamics.Periodic.LiYorkeWanted
