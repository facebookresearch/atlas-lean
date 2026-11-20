/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Code.Universality.HexInfraReach
import Code.Universality.HexWall3

namespace StatMech.Universality

open HexWalk List Filter Topology
open scoped BigOperators Topology Real NNReal
















noncomputable def hexW3_anchor (h0 : ℤ) (b : HexBridge)
    (hpos : 0 < ⌊hexInfra_disp h0 b.content⌋₊) : HexBridge :=
  hexInfra_dispBridgeOfContent h0 b.content b.content_ne hpos

@[simp] theorem hexW3_anchor_content (h0 : ℤ) (b : HexBridge) (hpos) :
    (hexW3_anchor h0 b hpos).content = b.content := rfl

@[simp] theorem hexW3_anchor_width (h0 : ℤ) (b : HexBridge) (hpos) :
    (hexW3_anchor h0 b hpos).width = ⌊hexInfra_disp h0 b.content⌋₊ := rfl






theorem hexW3_anchor_isDispBridge (h0 : ℤ) (b : HexBridge) (hpos)
    (hd : 0 ≤ hexInfra_disp h0 b.content) :
    hexInfra_IsDispBridge h0 (hexW3_anchor h0 b hpos) :=
  hexInfra_dispBridgeOfContent_isDispBridge h0 b.content b.content_ne hpos hd












theorem hexW3_anchor_reaches (a : ℂ) (h0 : ℤ) (b : HexBridge) (hpos)
    (hd : 0 ≤ hexInfra_disp h0 b.content) :
    hexWall3_ReachesWidth a h0 (hexW3_anchor h0 b hpos).width
      (hexW3_anchor h0 b hpos).content :=
  hexInfra_reachesWidth_of_dispBridge a h0 (hexW3_anchor h0 b hpos)
    (hexW3_anchor_isDispBridge h0 b hpos hd)













noncomputable def hexW3_dispBridgeDecomp (h0 : ℤ) (γ : List (ℕ × ℤ)) (h : hexHW_WF γ)
    (hPos : ∀ b ∈ bridgeDecomp γ h, 0 < ⌊hexInfra_disp h0 b.content⌋₊) :
    List HexBridge :=
  (bridgeDecomp γ h).attach.map (fun b => hexW3_anchor h0 b.1 (hPos b.1 b.2))







theorem hexW3_bridgeDecomp_isDispBridge (h0 : ℤ) (γ : List (ℕ × ℤ)) (h : hexHW_WF γ)
    (hPos : ∀ b ∈ bridgeDecomp γ h, 0 < ⌊hexInfra_disp h0 b.content⌋₊)
    (hD : ∀ b ∈ bridgeDecomp γ h, 0 ≤ hexInfra_disp h0 b.content) :
    ∀ b' ∈ hexW3_dispBridgeDecomp h0 γ h hPos, hexInfra_IsDispBridge h0 b' := by
  intro b' hb'
  simp only [hexW3_dispBridgeDecomp, List.mem_map, List.mem_attach, true_and] at hb'
  obtain ⟨b, rfl⟩ := hb'
  exact hexW3_anchor_isDispBridge h0 b.1 (hPos b.1 b.2) (hD b.1 b.2)








theorem hexW3_bridgeDecomp_reaches (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ)) (h : hexHW_WF γ)
    (hPos : ∀ b ∈ bridgeDecomp γ h, 0 < ⌊hexInfra_disp h0 b.content⌋₊)
    (hD : ∀ b ∈ bridgeDecomp γ h, 0 ≤ hexInfra_disp h0 b.content) :
    ∀ b' ∈ hexW3_dispBridgeDecomp h0 γ h hPos,
      hexWall3_ReachesWidth a h0 b'.width b'.content := fun b' hb' =>
  hexInfra_reachesWidth_of_dispBridge a h0 b'
    (hexW3_bridgeDecomp_isDispBridge h0 γ h hPos hD b' hb')





























theorem hex_connective_constant_wall3closed
    (c : ℕ → ℝ)
    (hge : ∀ n, 1 ≤ c n) (hsub : Submultiplicative c)
    
    (a : ℕ → ℂ) (h0 : ℕ → ℤ)
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v)))
    (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    
    (hlamMono : ∀ v, 1 ≤ v → hexConnFinalLam B v ≤ hexConnFinalLam B (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < hexConnFinalUps B v)
    (hυnn : ∀ v, 0 ≤ hexConnFinalUps B v)
    (hτnn : ∀ v, 0 ≤ hexConnFinalTau B v)
    
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) =
      hexConnFinalLam B (v + 1) - hexConnFinalLam B v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = hexConnFinalUps B (v + 1))
    
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < hexConnFinalTau B v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = hexConnFinalUps B)
    
    (aB : ℂ) (h0B : ℤ)
    (hColsum : ∀ T, Summable (fun w : {ts // hexWall3_mem aB h0B T ts} =>
      hexChiE ^ (HexWalk.ofTurns aB h0B w.1).numVertices))
    (hColle : ∀ T, (∑' w : {ts // hexWall3_mem aB h0B T ts},
      hexChiE ^ (HexWalk.ofTurns aB h0B w.1).numVertices) ≤ 1)
    
    (Dn : ∀ x, 0 < x → x < hexChiE → ∀ N, Type)
    (Dn_fin : ∀ x hx hxlt N, Fintype (Dn x hx hxlt N))
    (wtγ : ∀ x hx hxlt N, Dn x hx hxlt N → ℝ)
    (wtγ_nn : ∀ x hx hxlt N, ∀ d, 0 ≤ wtγ x hx hxlt N d)
    (partial_eq : ∀ x hx hxlt N,
      (Finset.univ (α := Dn x hx hxlt N)).sum (wtγ x hx hxlt N)
        = ∑ n ∈ Finset.range N, c n * x ^ n)
    (lower upper : ∀ x hx hxlt N, Dn x hx hxlt N → List HexBridge)
    (hlo : ∀ x hx hxlt N, ∀ d, StrictDecreasingWidths (lower x hx hxlt N d))
    (hup : ∀ x hx hxlt N, ∀ d, StrictDecreasingWidths (upper x hx hxlt N d))
    (htwoEdge : ∀ x hx hxlt N, ∀ d, wtγ x hx hxlt N d * x ^ 2
        = ((lower x hx hxlt N d).map
              (fun b => x ^ (HexWalk.ofTurns aB h0B b.content).numVertices)).prod
          * ((upper x hx hxlt N d).map
              (fun b => x ^ (HexWalk.ofTurns aB h0B b.content).numVertices)).prod)
    (decomp_inj : ∀ x hx hxlt N, Function.Injective
      (fun d => (hbw_widthFinset (lower x hx hxlt N d),
                 hbw_widthFinset (upper x hx hxlt N d))))
    
    
    (hDispLo : ∀ x hx hxlt N, ∀ d, ∀ b ∈ lower x hx hxlt N d,
      hexInfra_IsDispBridge h0B b)
    (hDispUp : ∀ x hx hxlt N, ∀ d, ∀ b ∈ upper x hx hxlt N d,
      hexInfra_IsDispBridge h0B b)
    
    (hSAWLo : ∀ x hx hxlt N, ∀ d, ∀ b ∈ lower x hx hxlt N d,
      (HexWalk.ofTurns aB h0B b.content).IsLegalSAW)
    (hSAWUp : ∀ x hx hxlt N, ∀ d, ∀ b ∈ upper x hx hxlt N d,
      (HexWalk.ofTurns aB h0B b.content).IsLegalSAW) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) :=
  hex_connective_constant_2walls c hge hsub a h0 B hFa hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc aB h0B hColsum hColle
    Dn Dn_fin wtγ wtγ_nn partial_eq lower upper hlo hup htwoEdge decomp_inj
    
    (fun x hx hxlt N d b hb =>
      hexInfra_reachesWidth_of_dispBridge aB h0B b (hDispLo x hx hxlt N d b hb))
    (hSAWLo)
    (fun x hx hxlt N d b hb =>
      hexInfra_reachesWidth_of_dispBridge aB h0B b (hDispUp x hx hxlt N d b hb))
    (hSAWUp)











noncomputable def hexW3_witnessBridge : HexBridge :=
  hexW3_anchor 0 hexWall3_witnessBridge
    (by change 0 < ⌊hexInfra_disp 0 [(-1 : ℤ)]⌋₊
        rw [hexInfra_floor_disp_singleRight]; exact one_pos)

@[simp] theorem hexW3_witnessBridge_content : hexW3_witnessBridge.content = [(-1 : ℤ)] := rfl

@[simp] theorem hexW3_witnessBridge_width : hexW3_witnessBridge.width = 1 := by
  change ⌊hexInfra_disp 0 [(-1 : ℤ)]⌋₊ = 1
  rw [hexInfra_floor_disp_singleRight]




theorem hexW3_witness_isDispBridge :
    hexInfra_IsDispBridge 0 hexW3_witnessBridge :=
  hexW3_anchor_isDispBridge 0 hexWall3_witnessBridge _
    (by change 0 ≤ hexInfra_disp 0 [(-1 : ℤ)]
        exact le_trans (by norm_num) hexInfra_disp_singleRight_ge_one)




theorem hexW3_witness_reaches (a : ℂ) :
    hexWall3_ReachesWidth a 0 hexW3_witnessBridge.width hexW3_witnessBridge.content :=
  hexInfra_reachesWidth_of_dispBridge a 0 hexW3_witnessBridge hexW3_witness_isDispBridge











theorem hexW3_witnessRung_wf : hexHW_WF [((1 : ℕ), (-1 : ℤ))] := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp; exact one_pos



theorem hexW3_witnessRung_decomp :
    bridgeDecomp [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf
      = [(⟨1, one_pos, [(-1 : ℤ)], by simp⟩ : HexBridge)] := by
  rw [bridgeDecomp_cons ((1 : ℕ), (-1 : ℤ)) [] hexW3_witnessRung_wf]
  have hdrop : hexHW_dropRun ((1 : ℕ), (-1 : ℤ)) [] = [] := by
    simp [hexHW_dropRun]
  have hwfnil : hexHW_WF ([] : List (ℕ × ℤ)) := fun p hp => absurd hp (by simp)
  have htail : bridgeDecomp (hexHW_dropRun ((1 : ℕ), (-1 : ℤ)) [])
      (hexHW_WF_dropRun ((1 : ℕ), (-1 : ℤ)) [] hexW3_witnessRung_wf) = [] := by
    rw [bridgeDecomp_congr (hexHW_dropRun ((1 : ℕ), (-1 : ℤ)) []) []
      (hexHW_WF_dropRun ((1 : ℕ), (-1 : ℤ)) [] hexW3_witnessRung_wf) hwfnil hdrop]
    exact bridgeDecomp_nil _
  rw [htail]
  congr 1



theorem hexW3_witnessRung_hPos :
    ∀ b ∈ bridgeDecomp [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf,
      0 < ⌊hexInfra_disp 0 b.content⌋₊ := by
  rw [hexW3_witnessRung_decomp]
  intro b hb
  simp only [List.mem_singleton] at hb
  subst hb
  change 0 < ⌊hexInfra_disp 0 [(-1 : ℤ)]⌋₊
  rw [hexInfra_floor_disp_singleRight]; exact one_pos


theorem hexW3_witnessRung_hD :
    ∀ b ∈ bridgeDecomp [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf,
      0 ≤ hexInfra_disp 0 b.content := by
  rw [hexW3_witnessRung_decomp]
  intro b hb
  simp only [List.mem_singleton] at hb
  subst hb
  change 0 ≤ hexInfra_disp 0 [(-1 : ℤ)]
  exact le_trans (by norm_num) hexInfra_disp_singleRight_ge_one





theorem hexW3_witnessRung_dispBridge_nonempty_anchored :
    (hexW3_dispBridgeDecomp 0 [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf
        hexW3_witnessRung_hPos) ≠ []
      ∧ ∀ b' ∈ hexW3_dispBridgeDecomp 0 [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf
          hexW3_witnessRung_hPos, hexInfra_IsDispBridge 0 b' := by
  refine ⟨?_, hexW3_bridgeDecomp_isDispBridge 0 [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf
    hexW3_witnessRung_hPos hexW3_witnessRung_hD⟩
  simp only [hexW3_dispBridgeDecomp, ne_eq, List.map_eq_nil_iff, List.attach_eq_nil_iff]
  rw [hexW3_witnessRung_decomp]
  exact List.cons_ne_nil _ _

end StatMech.Universality
