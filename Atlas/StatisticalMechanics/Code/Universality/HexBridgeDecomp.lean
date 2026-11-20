/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Mathlib
import Code.Universality.HexLattice

namespace StatMech.Universality

open List











structure HexBridge where
  
  width : ℕ
  
  width_pos : 0 < width
  
  content : List ℤ
  
  content_ne : content ≠ []

namespace HexBridge




def rungs (b : HexBridge) : List (ℕ × ℤ) := b.content.map (fun t => (b.width, t))


theorem rungs_ne_nil (b : HexBridge) : b.rungs ≠ [] := by
  simp only [rungs, ne_eq, List.map_eq_nil_iff]
  exact b.content_ne


theorem mem_rungs_fst {b : HexBridge} {p : ℕ × ℤ} (hp : p ∈ b.rungs) : p.1 = b.width := by
  simp only [rungs, List.mem_map] at hp
  obtain ⟨t, _, rfl⟩ := hp
  rfl


@[simp]
theorem length_rungs (b : HexBridge) : b.rungs.length = b.content.length := by
  simp [rungs]

end HexBridge










def StrictDecreasingWidths (bs : List HexBridge) : Prop :=
  List.Pairwise (fun b c => b.width > c.width) bs

theorem strictDecreasingWidths_nil : StrictDecreasingWidths [] := List.Pairwise.nil

theorem strictDecreasingWidths_cons {b : HexBridge} {bs : List HexBridge} :
    StrictDecreasingWidths (b :: bs) ↔
      (∀ c ∈ bs, b.width > c.width) ∧ StrictDecreasingWidths bs := by
  unfold StrictDecreasingWidths
  exact List.pairwise_cons

theorem StrictDecreasingWidths.tail {b : HexBridge} {bs : List HexBridge}
    (h : StrictDecreasingWidths (b :: bs)) : StrictDecreasingWidths bs :=
  (strictDecreasingWidths_cons.mp h).2

theorem StrictDecreasingWidths.head_gt {b : HexBridge} {bs : List HexBridge}
    (h : StrictDecreasingWidths (b :: bs)) {c : HexBridge} (hc : c ∈ bs) :
    b.width > c.width :=
  (strictDecreasingWidths_cons.mp h).1 c hc









def bridgeRecompose (bs : List HexBridge) : List (ℕ × ℤ) :=
  (bs.map HexBridge.rungs).flatten

@[simp]
theorem bridgeRecompose_nil : bridgeRecompose [] = [] := rfl

@[simp]
theorem bridgeRecompose_cons (b : HexBridge) (bs : List HexBridge) :
    bridgeRecompose (b :: bs) = b.rungs ++ bridgeRecompose bs := by
  simp [bridgeRecompose]

theorem bridgeRecompose_append (bs cs : List HexBridge) :
    bridgeRecompose (bs ++ cs) = bridgeRecompose bs ++ bridgeRecompose cs := by
  simp [bridgeRecompose, List.flatten_append]



theorem mem_bridgeRecompose_fst {bs : List HexBridge} {p : ℕ × ℤ}
    (hp : p ∈ bridgeRecompose bs) : ∃ b ∈ bs, p.1 = b.width := by
  induction bs with
  | nil => simp [bridgeRecompose] at hp
  | cons b bs ih =>
    rw [bridgeRecompose_cons, List.mem_append] at hp
    rcases hp with hp | hp
    · exact ⟨b, List.mem_cons_self, HexBridge.mem_rungs_fst hp⟩
    · obtain ⟨c, hc, hpc⟩ := ih hp
      exact ⟨c, List.mem_cons_of_mem b hc, hpc⟩














def hexHW_leadRun (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  (p :: rest).takeWhile (fun q => q.1 == p.1)


def hexHW_dropRun (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  (p :: rest).dropWhile (fun q => q.1 == p.1)

theorem hexHW_lead_drop_append (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) :
    hexHW_leadRun p rest ++ hexHW_dropRun p rest = p :: rest := by
  simp [hexHW_leadRun, hexHW_dropRun, List.takeWhile_append_dropWhile]

theorem hexHW_dropRun_length_lt (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) :
    (hexHW_dropRun p rest).length < (p :: rest).length := by
  have hkey : (hexHW_leadRun p rest).length + (hexHW_dropRun p rest).length
      = (p :: rest).length := by
    have := hexHW_lead_drop_append p rest
    calc (hexHW_leadRun p rest).length + (hexHW_dropRun p rest).length
        = (hexHW_leadRun p rest ++ hexHW_dropRun p rest).length := by
          rw [List.length_append]
      _ = (p :: rest).length := by rw [this]
  have hlead_pos : 0 < (hexHW_leadRun p rest).length := by
    have : p ∈ hexHW_leadRun p rest := by
      simp only [hexHW_leadRun]
      rw [List.takeWhile_cons]
      simp
    exact List.length_pos_of_mem this
  omega

theorem hexHW_leadRun_ne_nil (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) :
    hexHW_leadRun p rest ≠ [] := by
  simp only [hexHW_leadRun, ne_eq]
  rw [List.takeWhile_cons]; simp

theorem hexHW_leadRun_content_ne (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) :
    (hexHW_leadRun p rest).map Prod.snd ≠ [] := by
  simp only [ne_eq, List.map_eq_nil_iff]
  exact hexHW_leadRun_ne_nil p rest

theorem hexHW_dropRun_sublist (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) :
    hexHW_dropRun p rest <+ p :: rest := by
  simp only [hexHW_dropRun]
  exact List.dropWhile_sublist _


theorem hexHW_leadRun_fst (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) {q : ℕ × ℤ}
    (hq : q ∈ hexHW_leadRun p rest) : q.1 = p.1 := by
  simp only [hexHW_leadRun] at hq
  simpa using List.mem_takeWhile_imp hq










def hexHW_WF (γ : List (ℕ × ℤ)) : Prop := ∀ p ∈ γ, 0 < p.1

theorem hexHW_WF_dropRun (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) (h : hexHW_WF (p :: rest)) :
    hexHW_WF (hexHW_dropRun p rest) :=
  fun q hq => h q ((hexHW_dropRun_sublist p rest).subset hq)






def bridgeDecomp : (γ : List (ℕ × ℤ)) → hexHW_WF γ → List HexBridge
  | [], _ => []
  | p :: rest, h =>
    let hwpos : 0 < p.1 := h p List.mem_cons_self
    (⟨p.1, hwpos, (hexHW_leadRun p rest).map Prod.snd, hexHW_leadRun_content_ne p rest⟩ :
        HexBridge)
      :: bridgeDecomp (hexHW_dropRun p rest) (hexHW_WF_dropRun p rest h)
  termination_by γ _ => γ.length
  decreasing_by exact hexHW_dropRun_length_lt p rest

@[simp]
theorem bridgeDecomp_nil (h : hexHW_WF []) : bridgeDecomp [] h = [] := by rw [bridgeDecomp]

theorem bridgeDecomp_cons (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) (h : hexHW_WF (p :: rest)) :
    bridgeDecomp (p :: rest) h =
      (⟨p.1, h p List.mem_cons_self, (hexHW_leadRun p rest).map Prod.snd,
          hexHW_leadRun_content_ne p rest⟩ : HexBridge)
        :: bridgeDecomp (hexHW_dropRun p rest) (hexHW_WF_dropRun p rest h) := by
  rw [bridgeDecomp]



theorem bridgeDecomp_congr (γ γ' : List (ℕ × ℤ)) (h : hexHW_WF γ) (h' : hexHW_WF γ')
    (he : γ = γ') : bridgeDecomp γ h = bridgeDecomp γ' h' := by
  subst he; rfl









theorem HexBridge.eq_of {b c : HexBridge} (hw : b.width = c.width)
    (hc : b.content = c.content) : b = c := by
  cases b; cases c; simp_all



theorem HexBridge.eq_of_rungs {b c : HexBridge} (h : b.rungs = c.rungs) : b = c := by
  have hwb : b.width = c.width := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ b.rungs_ne_nil
    have hpc : p ∈ c.rungs := h ▸ hp
    rw [← HexBridge.mem_rungs_fst hp, ← HexBridge.mem_rungs_fst hpc]
  have hcontent : b.content = c.content := by
    have : b.rungs.map Prod.snd = c.rungs.map Prod.snd := by rw [h]
    simpa [HexBridge.rungs, List.map_map, Function.comp] using this
  exact HexBridge.eq_of hwb hcontent


theorem hexHW_wf_bridgeRecompose (bs : List HexBridge) : hexHW_WF (bridgeRecompose bs) := by
  intro q hq
  obtain ⟨b, _, hqb⟩ := mem_bridgeRecompose_fst hq
  rw [hqb]; exact b.width_pos










theorem hexHW_recompose_decomp : ∀ (γ : List (ℕ × ℤ)) (h : hexHW_WF γ),
    bridgeRecompose (bridgeDecomp γ h) = γ
  | [], h => by rw [bridgeDecomp_nil]; rfl
  | p :: rest, h => by
    rw [bridgeDecomp_cons, bridgeRecompose_cons]
    
    have hbr : (HexBridge.mk p.1 (h p List.mem_cons_self)
        ((hexHW_leadRun p rest).map Prod.snd) (hexHW_leadRun_content_ne p rest)).rungs
          = hexHW_leadRun p rest := by
      simp only [HexBridge.rungs, List.map_map]
      conv_rhs => rw [← List.map_id (hexHW_leadRun p rest)]
      apply List.map_congr_left
      intro q hq
      ext
      · exact (hexHW_leadRun_fst p rest hq).symm
      · rfl
    rw [hbr]
    rw [hexHW_recompose_decomp (hexHW_dropRun p rest) (hexHW_WF_dropRun p rest h)]
    exact hexHW_lead_drop_append p rest
  termination_by γ _ => γ.length
  decreasing_by exact hexHW_dropRun_length_lt p rest










theorem hexHW_takeWhile_recompose (b : HexBridge) (bs : List HexBridge)
    (h : StrictDecreasingWidths (b :: bs)) :
    (bridgeRecompose (b :: bs)).takeWhile (fun q => q.1 == b.width) = b.rungs := by
  rw [bridgeRecompose_cons]
  have hb : ∀ a ∈ b.rungs, (a.1 == b.width) = true :=
    fun a ha => by simp [HexBridge.mem_rungs_fst ha]
  rw [List.takeWhile_append_of_pos hb]
  have htail : (bridgeRecompose bs).takeWhile (fun q => q.1 == b.width) = [] := by
    cases hbs : bridgeRecompose bs with
    | nil => simp
    | cons p rest =>
      rw [List.takeWhile_cons]
      obtain ⟨c, hc, hpc⟩ := mem_bridgeRecompose_fst
        (by rw [hbs]; exact List.mem_cons_self : p ∈ bridgeRecompose bs)
      have hlt : c.width < b.width := h.head_gt hc
      rw [if_neg (by simp; rw [hpc]; omega)]
  rw [htail, List.append_nil]




theorem hexHW_dropWhile_recompose (b : HexBridge) (bs : List HexBridge)
    (h : StrictDecreasingWidths (b :: bs)) :
    (bridgeRecompose (b :: bs)).dropWhile (fun q => q.1 == b.width) = bridgeRecompose bs := by
  rw [bridgeRecompose_cons]
  have hb : ∀ a ∈ b.rungs, (a.1 == b.width) = true :=
    fun a ha => by simp [HexBridge.mem_rungs_fst ha]
  rw [List.dropWhile_append_of_pos hb]
  cases hbs : bridgeRecompose bs with
  | nil => simp
  | cons p rest =>
    rw [List.dropWhile_cons]
    obtain ⟨c, hc, hpc⟩ := mem_bridgeRecompose_fst
      (by rw [hbs]; exact List.mem_cons_self : p ∈ bridgeRecompose bs)
    have hlt : c.width < b.width := h.head_gt hc
    rw [if_neg (by simp; rw [hpc]; omega)]














theorem hexHW_decomp_recompose : ∀ (bs : List HexBridge) (h : hexHW_WF (bridgeRecompose bs)),
    StrictDecreasingWidths bs → bridgeDecomp (bridgeRecompose bs) h = bs := by
  intro bs
  induction bs with
  | nil => intro h _; exact bridgeDecomp_nil h
  | cons b bs ih =>
    intro h hsdw
    obtain ⟨p0, rs, hpr0⟩ := List.exists_cons_of_ne_nil b.rungs_ne_nil
    have hrec_eq : bridgeRecompose (b :: bs) = p0 :: (rs ++ bridgeRecompose bs) := by
      rw [bridgeRecompose_cons, hpr0, List.cons_append]
    have hp01 : p0.1 = b.width := by
      apply HexBridge.mem_rungs_fst; rw [hpr0]; exact List.mem_cons_self
    rw [bridgeDecomp_congr _ _ h (hrec_eq ▸ h) hrec_eq, bridgeDecomp_cons]
    have hlead_eq : hexHW_leadRun p0 (rs ++ bridgeRecompose bs) = b.rungs := by
      simp only [hexHW_leadRun]
      rw [← hrec_eq]
      rw [show (fun q : ℕ × ℤ => q.1 == p0.1) = (fun q => q.1 == b.width) from by rw [hp01]]
      exact hexHW_takeWhile_recompose b bs hsdw
    have hdrop_eq : hexHW_dropRun p0 (rs ++ bridgeRecompose bs) = bridgeRecompose bs := by
      simp only [hexHW_dropRun]
      rw [← hrec_eq]
      rw [show (fun q : ℕ × ℤ => q.1 == p0.1) = (fun q => q.1 == b.width) from by rw [hp01]]
      exact hexHW_dropWhile_recompose b bs hsdw
    have hp0pos : 0 < p0.1 := by rw [hp01]; exact b.width_pos
    have hbhead : (⟨p0.1, hp0pos, (hexHW_leadRun p0 (rs ++ bridgeRecompose bs)).map Prod.snd,
        hexHW_leadRun_content_ne p0 (rs ++ bridgeRecompose bs)⟩ : HexBridge) = b := by
      apply HexBridge.eq_of
      · exact hp01
      · show (hexHW_leadRun p0 (rs ++ bridgeRecompose bs)).map Prod.snd = b.content
        rw [hlead_eq]
        simp [HexBridge.rungs, List.map_map]
    rw [hbhead]
    congr 1
    rw [bridgeDecomp_congr _ (bridgeRecompose bs) _ (hexHW_wf_bridgeRecompose bs) hdrop_eq]
    exact ih (hexHW_wf_bridgeRecompose bs) hsdw.tail










theorem hexHW_bridgeRecompose_injOn {bs cs : List HexBridge}
    (hb : StrictDecreasingWidths bs) (hc : StrictDecreasingWidths cs)
    (heq : bridgeRecompose bs = bridgeRecompose cs) : bs = cs := by
  have e1 : bridgeDecomp (bridgeRecompose bs) (hexHW_wf_bridgeRecompose bs) = bs :=
    hexHW_decomp_recompose bs _ hb
  have e2 : bridgeDecomp (bridgeRecompose cs) (hexHW_wf_bridgeRecompose cs) = cs :=
    hexHW_decomp_recompose cs _ hc
  rw [← e1, ← e2]
  exact bridgeDecomp_congr _ _ _ _ heq











def hexHW_IsValidWalk (γ : List (ℕ × ℤ)) : Prop :=
  ∃ bs, StrictDecreasingWidths bs ∧ bridgeRecompose bs = γ












noncomputable def hexHW_bridge_decomp :
    {bs : List HexBridge // StrictDecreasingWidths bs} ≃
      {γ : List (ℕ × ℤ) // hexHW_IsValidWalk γ} :=
  Equiv.ofBijective
    (fun bs => ⟨bridgeRecompose bs.1, bs.1, bs.2, rfl⟩)
    (by
      constructor
      · 
        intro bs cs heq
        apply Subtype.ext
        have : bridgeRecompose bs.1 = bridgeRecompose cs.1 := congrArg Subtype.val heq
        exact hexHW_bridgeRecompose_injOn bs.2 cs.2 this
      · 
        intro γ
        obtain ⟨bs, hbs, hrec⟩ := γ.2
        exact ⟨⟨bs, hbs⟩, by apply Subtype.ext; exact hrec⟩)



@[simp]
theorem hexHW_bridge_decomp_apply (bs : {bs : List HexBridge // StrictDecreasingWidths bs}) :
    (hexHW_bridge_decomp bs : List (ℕ × ℤ)) = bridgeRecompose bs.1 := rfl




theorem hexHW_bridge_decomp_symm_apply (γ : {γ : List (ℕ × ℤ) // hexHW_IsValidWalk γ}) :
    ((hexHW_bridge_decomp.symm γ : {bs : List HexBridge // StrictDecreasingWidths bs}) :
        List HexBridge)
      = bridgeDecomp γ.1 (by
          obtain ⟨bs, _, hrec⟩ := γ.2
          rw [← hrec]; exact hexHW_wf_bridgeRecompose bs) := by
  obtain ⟨bs, hbs, hrec⟩ := γ.2
  have hforward : hexHW_bridge_decomp ⟨bs, hbs⟩ = γ := by
    apply Subtype.ext
    simpa using hrec
  have hsymm : hexHW_bridge_decomp.symm γ = ⟨bs, hbs⟩ := by
    rw [← hforward, Equiv.symm_apply_apply]
  rw [hsymm]
  
  show bs = bridgeDecomp γ.1 _
  have hwf : hexHW_WF γ.1 := by rw [← hrec]; exact hexHW_wf_bridgeRecompose bs
  symm
  calc bridgeDecomp γ.1 hwf
      = bridgeDecomp (bridgeRecompose bs) (hexHW_wf_bridgeRecompose bs) :=
        bridgeDecomp_congr γ.1 (bridgeRecompose bs) hwf (hexHW_wf_bridgeRecompose bs) hrec.symm
    _ = bs := hexHW_decomp_recompose bs _ hbs










theorem hexHW_decomp_strictDecreasing (γ : List (ℕ × ℤ)) (h : hexHW_WF γ)
    (hv : hexHW_IsValidWalk γ) :
    StrictDecreasingWidths (bridgeDecomp γ h) := by
  obtain ⟨bs, hbs, hrec⟩ := hv
  have : bridgeDecomp γ h = bs := by
    rw [bridgeDecomp_congr γ (bridgeRecompose bs) h (hexHW_wf_bridgeRecompose bs) hrec.symm]
    exact hexHW_decomp_recompose bs _ hbs
  rw [this]; exact hbs





theorem hexHW_image_iff (bs : List HexBridge) :
    (∃ (γ : List (ℕ × ℤ)) (h : hexHW_WF γ), hexHW_IsValidWalk γ ∧ bridgeDecomp γ h = bs)
      ↔ StrictDecreasingWidths bs := by
  constructor
  · rintro ⟨γ, h, hv, hd⟩
    rw [← hd]; exact hexHW_decomp_strictDecreasing γ h hv
  · intro hbs
    refine ⟨bridgeRecompose bs, hexHW_wf_bridgeRecompose bs, ⟨bs, hbs, rfl⟩, ?_⟩
    exact hexHW_decomp_recompose bs _ hbs














def StrictIncreasingWidths (bs : List HexBridge) : Prop :=
  List.Pairwise (fun b c => b.width < c.width) bs



theorem hexHW_strictIncreasing_reverse (bs : List HexBridge) :
    StrictIncreasingWidths bs ↔ StrictDecreasingWidths bs.reverse := by
  unfold StrictIncreasingWidths StrictDecreasingWidths
  rw [List.pairwise_reverse]














noncomputable def hexHW_bridge_decomp_twoSided :
    ({lower : List HexBridge // StrictIncreasingWidths lower} ×
        {upper : List HexBridge // StrictDecreasingWidths upper}) ≃
      ({γL : List (ℕ × ℤ) // hexHW_IsValidWalk γL} ×
        {γU : List (ℕ × ℤ) // hexHW_IsValidWalk γU}) :=
  
  
  Equiv.prodCongr
    ((Equiv.subtypeEquiv
        (⟨List.reverse, List.reverse, List.reverse_reverse, List.reverse_reverse⟩ :
          List HexBridge ≃ List HexBridge)
        (fun lower => hexHW_strictIncreasing_reverse lower)).trans
      hexHW_bridge_decomp)
    hexHW_bridge_decomp

end StatMech.Universality
