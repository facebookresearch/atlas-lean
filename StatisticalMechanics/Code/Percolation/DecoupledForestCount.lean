/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Percolation.CanonForestCount























namespace StatMech.Percolation

open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}










def dfc_BoxOpenForestSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vset : Finset (Site d)) (_ : Nonempty (↑Vset : Type)) (F : SimpleGraph (↑Vset : Type))
    (_ : DecidableRel F.Adj) (vx : Site d → (↑Vset : Type)) (b : Site d → Fin 3 → (↑Vset : Type)),
    (∀ u v, F.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d)) ∧
    F.IsAcyclic ∧
    (∀ v : (↑Vset : Type), 1 ≤ F.degree v) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ((vx x : Site d) = x ∧
       (∀ i, F.Reachable (vx x) (b x i) ∧ b x i ≠ vx x) ∧
       (¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d)))) ∧
    (∀ v : (↑Vset : Type), F.degree v = 1 → (v : Site d) ∈ vertexBoundary d (n + 1))

open Classical in



theorem dfc_Tcount_le_boundary_succ_of_boxOpenForestSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : dfc_BoxOpenForestSucc ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
  classical
  obtain ⟨Vset, hVne, F, _, vx, b, hπ, hacyc, hmin, htriData, hleaf⟩ := h
  set Tf := tfc_trifFinset ω n with hTf
  have hdeg3 : ∀ x, x ∈ box d n → IsTrifurcation d ω x → 3 ≤ F.degree (vx x) := by
    intro x hxbox htri
    obtain ⟨hvx, hreach, hcut⟩ := htriData x hxbox htri
    exact bst_deg_ge_three_of_boxOpenForest hπ hxbox htri hvx hreach hcut
  have hvxinjOn : Set.InjOn vx Tf := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx hy
    have hx' : (vx x : Site d) = x := (htriData x hx.1 hx.2).1
    have hy' : (vx y : Site d) = y := (htriData y hy.1 hy.2).1
    rw [← hx', ← hy', hxy]
  set Tw : Finset (↑Vset : Type) := Tf.image vx with hTw
  have hcardTw : Tw.card = Tf.card := by rw [hTw, Finset.card_image_of_injOn hvxinjOn]
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ F.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨x, hxT, rfl⟩ := hw
    rw [tfc_mem_trifFinset] at hxT
    exact hdeg3 x hxT.1 hxT.2
  have h1 : Tf.card ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := by
    rw [← hcardTw]; exact flc2_trifImage_card_le_deg3 F Tw hTwdeg
  have h2 : (univ.filter (fun v => 3 ≤ F.degree v)).card
      ≤ (univ.filter (fun v => F.degree v = 1)).card :=
    flc2_forest_internal_le_leaves F hacyc hmin
  have h3 : (univ.filter (fun v => F.degree v = 1)).card ≤ boxSV_boundaryCard d (n + 1) := by
    rw [← tfc_boundaryFinset_card]
    apply Finset.card_le_card_of_injOn (fun v : (↑Vset : Type) => (v : Site d))
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, tfc_mem_boundaryFinset]
      exact hleaf v hv.2
    · intro u _ v _ huv; exact Subtype.val_injective huv
  calc Tcount d ω n = Tf.card := (tfc_trifFinset_card ω n).symm
    _ ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := h1
    _ ≤ (univ.filter (fun v => F.degree v = 1)).card := h2
    _ ≤ boxSV_boundaryCard d (n + 1) := h3











def dfc_ArmForestReachingSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (c : Site d → Fin 3 → Site d) (zr : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d (n + 1)) ∧
    (∃ v, spc_OnBPath T B v) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      (∀ i, T.Adj x (c x i)) ∧
      (¬ Connected d (removeSite x ω) (c x 0) (c x 1) ∧
       ¬ Connected d (removeSite x ω) (c x 0) (c x 2) ∧
       ¬ Connected d (removeSite x ω) (c x 1) (c x 2)) ∧
      (∀ i, zr x i ∈ B ∧ ∃ w : T.Walk (c x i) (zr x i), x ∉ w.support))


def dfc_SpanForestArmsSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (m : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d (n + 1)) ∧
    (∃ v, spc_OnBPath T B v) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      spc_OnBPath T B x ∧
      ((m x 0 ≠ m x 1 ∧ m x 0 ≠ m x 2 ∧ m x 1 ≠ m x 2) ∧
       (∀ i, T.Adj x (m x i) ∧ spc_OnBPath T B (m x i)) ∧
       (¬ Connected d (removeSite x ω) (m x 0) (m x 1) ∧
        ¬ Connected d (removeSite x ω) (m x 0) (m x 2) ∧
        ¬ Connected d (removeSite x ω) (m x 1) (m x 2))))


theorem dfc_spanForestArmsSucc_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : dfc_ArmForestReachingSucc ω n) : dfc_SpanForestArmsSucc ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ := h
  refine ⟨Vall, T, hTdec, B, c, hTac, hTopen, hTsupp, hBbd, hRne, ?_⟩
  intro x hxbox htri
  obtain ⟨hadj, hcut, hreach⟩ := hData x hxbox htri
  obtain ⟨hcut01, hcut02, hcut12⟩ := hcut
  have hne01 : c x 0 ≠ c x 1 := fun h => hcut01 (h ▸ connected_refl _ _)
  have hne02 : c x 0 ≠ c x 2 := fun h => hcut02 (h ▸ connected_refl _ _)
  have hne12 : c x 1 ≠ c x 2 := fun h => hcut12 (h ▸ connected_refl _ _)
  obtain ⟨hz0, w0, hw0x⟩ := hreach 0
  obtain ⟨hz1, w1, hw1x⟩ := hreach 1
  obtain ⟨hz2, w2, hw2x⟩ := hreach 2
  obtain ⟨hxsurv, hc0surv, hc1surv⟩ :=
    sfa_onBPath_of_arms ω T hTopen B (hadj 0) (hadj 1) w0 hw0x hz0 w1 hw1x hz1 hcut01
  obtain ⟨_, _, hc2surv⟩ :=
    sfa_onBPath_of_arms ω T hTopen B (hadj 0) (hadj 2) w0 hw0x hz0 w2 hw2x hz2 hcut02
  refine ⟨hxsurv, ⟨hne01, hne02, hne12⟩, ?_, hcut01, hcut02, hcut12⟩
  intro i
  refine ⟨hadj i, ?_⟩
  fin_cases i
  · exact hc0surv
  · exact hc1surv
  · exact hc2surv

open Classical in



theorem dfc_boxOpenForestSucc_of_spanForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : dfc_SpanForestArmsSucc ω n) : dfc_BoxOpenForestSucc ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, m, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ := h
  have hRfin : {v | spc_OnBPath T B v}.Finite := by
    apply Set.Finite.subset (Vall.finite_toSet)
    intro v hv
    obtain ⟨w, hadj, _⟩ := spc_survivor_has_neighbor T B v hv
    exact hTsupp v w hadj
  set Vset : Finset (Site d) := hRfin.toFinset with hVset
  have hmemVset : ∀ v, v ∈ Vset ↔ spc_OnBPath T B v := by
    intro v; rw [hVset, Set.Finite.mem_toFinset]; rfl
  have hVne : Nonempty (↥Vset) := by
    obtain ⟨v, hv⟩ := hRne; exact ⟨⟨v, (hmemVset v).mpr hv⟩⟩
  set F₀ : SimpleGraph (↥Vset) := T.comap (fun (u : ↥Vset) => (u : Site d)) with hF₀
  haveI hF₀dec : DecidableRel F₀.Adj := fun a b => by rw [hF₀, comap_adj]; infer_instance
  have hF₀adj : ∀ u v : ↥Vset, F₀.Adj u v ↔ T.Adj (u : Site d) (v : Site d) := by
    intro u v; rw [hF₀, comap_adj]
  have hF₀ac : F₀.IsAcyclic :=
    hTac.comap ⟨(fun (u : ↥Vset) => (u : Site d)), fun {a b} h => h⟩ (fun a b h => Subtype.ext h)
  have hlift : ∀ v, spc_OnBPath T B v → v ∈ Vset := fun v hv => (hmemVset v).mpr hv
  let dflt : ↥Vset := hVne.some
  set vx : Site d → ↥Vset := fun x =>
    if hx : spc_OnBPath T B x then ⟨x, hlift x hx⟩ else dflt with hvxdef
  set bb : Site d → Fin 3 → ↥Vset := fun x i =>
    if hx : spc_OnBPath T B (m x i) then ⟨m x i, hlift _ hx⟩ else dflt with hbbdef
  refine ⟨Vset, hVne, F₀, hF₀dec, vx, bb, ?_, hF₀ac, ?_, ?_, ?_⟩
  · 
    intro u v huv
    rw [hF₀adj] at huv; exact hTopen _ _ huv
  · 
    intro v
    have hvR : spc_OnBPath T B (v : Site d) := (hmemVset (v : Site d)).mp v.2
    obtain ⟨w, hadjw, hwR⟩ := spc_survivor_has_neighbor T B (v : Site d) hvR
    exact spc_deg_ge_one F₀ v ⟨w, hlift w hwR⟩ (by rw [hF₀adj]; exact hadjw)
  · 
    intro x hxbox htri
    obtain ⟨hxR, hmne, hmadj, hmsep⟩ := hData x hxbox htri
    have hvxval : (vx x : Site d) = x := by simp only [hvxdef, dif_pos hxR]
    refine ⟨hvxval, ?_, ?_⟩
    · intro i
      have hmi := hmadj i
      have hbbval : (bb x i : Site d) = m x i := by simp only [hbbdef, dif_pos hmi.2]
      refine ⟨?_, ?_⟩
      · refine Adj.reachable ?_
        rw [hF₀adj, hvxval, hbbval]; exact hmi.1
      · intro hh
        have hval : (bb x i : Site d) = (vx x : Site d) :=
          congrArg (fun (u : ↥Vset) => (u : Site d)) hh
        rw [hbbval, hvxval] at hval
        exact (T.ne_of_adj hmi.1) hval.symm
    · have h0 : (bb x 0 : Site d) = m x 0 := by simp only [hbbdef, dif_pos (hmadj 0).2]
      have h1 : (bb x 1 : Site d) = m x 1 := by simp only [hbbdef, dif_pos (hmadj 1).2]
      have h2 : (bb x 2 : Site d) = m x 2 := by simp only [hbbdef, dif_pos (hmadj 2).2]
      rw [h0, h1, h2]; exact hmsep
  · 
    intro v hv
    have hvR : spc_OnBPath T B (v : Site d) := (hmemVset (v : Site d)).mp v.2
    by_cases hvB : (v : Site d) ∈ B
    · exact hBbd hvB
    · exfalso
      obtain ⟨w₁, w₂, hw12, ha1, ha2, hr1, hr2⟩ :=
        spc_interior_two_neighbors T B (v : Site d) hvR hvB
      have hdeg2 : 2 ≤ F₀.degree v :=
        spc_deg_ge_two F₀ v ⟨w₁, hlift w₁ hr1⟩ ⟨w₂, hlift w₂ hr2⟩
          (fun hh => hw12 (Subtype.ext_iff.mp hh))
          (by rw [hF₀adj]; exact ha1) (by rw [hF₀adj]; exact ha2)
      omega






theorem dfc_armForestReachingSucc_of_canonical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
    (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
    dfc_ArmForestReachingSucc ω n := by
  classical
  have harms : arc_TrifArmsRemoveSiteInfinite ω n :=
    ctc2_armsRemoveSiteInfinite_of_canonical ω n hcanon
  have hdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
        (∀ i, (cfc_T ω (n + 1)).Adj x (c i)) ∧
        (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
         ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
         ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
        (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧
          ∃ w : (cfc_T ω (n + 1)).Walk (c i) (zr i), x ∉ w.support) := by
    intro x hxbox htri
    obtain ⟨c0, hadj, hne, hcut, hinf⟩ := harms x hxbox htri
    have hcbox : ∀ i, c0 i ∈ box d (n + 1) := fun i =>
      arc_neighbour_in_box_succ hxbox (hadj i).1
    have hxbox1 : x ∈ box d (n + 1) := box_subset_succ d n hxbox
    exact cfc_trif_data ω (n + 1) (by omega) hxbox1 c0 hadj hne hcbox hcut hinf
  choose! c zr hcadj hccut hcreach using hdata
  set B : Set (Site d) := vertexBoundary d (n + 1) with hBdef
  obtain ⟨x0, hx0box, hx0tri⟩ := hexists
  have hc0reach := hcreach x0 hx0box hx0tri
  obtain ⟨hz0, w0, hw0x⟩ := hc0reach 0
  obtain ⟨hz1, w1, hw1x⟩ := hc0reach 1
  have hcut01 := (hccut x0 hx0box hx0tri).1
  obtain ⟨hxsurv, _, _⟩ :=
    sfa_onBPath_of_arms ω (cfc_T ω (n + 1)) (cfc_T_open ω (n + 1)) B
      (hcadj x0 hx0box hx0tri 0) (hcadj x0 hx0box hx0tri 1)
      w0 hw0x hz0 w1 hw1x hz1 hcut01
  refine ⟨boxFinsetBK d (n + 2), cfc_T ω (n + 1), Classical.decRel _, B, c, zr,
    cfc_T_acyclic ω (n + 1), cfc_T_open ω (n + 1), ?_, le_refl _, ⟨x0, hxsurv⟩, ?_⟩
  · intro u v huv
    rw [boxFinsetBK, Set.Finite.mem_toFinset]
    exact cfc_T_support ω (n + 1) u v huv
  · intro x hxbox htri
    exact ⟨hcadj x hxbox htri, hccut x hxbox htri, hcreach x hxbox htri⟩









theorem dfc_Tcount_le_boundary_succ_of_canonical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) :
    Tcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
  classical
  by_cases hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x
  · exact dfc_Tcount_le_boundary_succ_of_boxOpenForestSucc ω n
      (dfc_boxOpenForestSucc_of_spanForestArms ω n
        (dfc_spanForestArmsSucc_of_armForestReaching ω n
          (dfc_armForestReachingSucc_of_canonical ω n hn hcanon hexists)))
  · have h0 : Tcount d ω n = 0 := by
      unfold Tcount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      rw [boxFinsetBK, Set.Finite.mem_toFinset] at hx
      exact fun htri => hexists ⟨x, hx, htri⟩
    rw [h0]; exact Nat.zero_le _




theorem dfc_canonTcount_le_boundary_succ_of_canonical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d (n + 1) :=
  le_trans (ctc2_canonTcount_le_Tcount ω n)
    (dfc_Tcount_le_boundary_succ_of_canonical ω n hn hcanon)












def dfc_CanonBoxOpenForestSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vset : Finset (Site d)) (_ : Nonempty (↑Vset : Type)) (F : SimpleGraph (↑Vset : Type))
    (_ : DecidableRel F.Adj) (vx : Site d → (↑Vset : Type)) (b : Site d → Fin 3 → (↑Vset : Type)),
    (∀ u v, F.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d)) ∧
    F.IsAcyclic ∧
    (∀ v : (↑Vset : Type), 1 ≤ F.degree v) ∧
    (∀ x, x ∈ box d n → IsCanonicalTrifurcation d ω x →
      ((vx x : Site d) = x ∧
       (∀ i, F.Reachable (vx x) (b x i) ∧ b x i ≠ vx x) ∧
       (¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d)))) ∧
    (∀ v : (↑Vset : Type), F.degree v = 1 → (v : Site d) ∈ vertexBoundary d (n + 1))

open Classical in

theorem dfc_canonTcount_le_boundary_succ_of_canonBoxOpenForestSucc
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : dfc_CanonBoxOpenForestSucc ω n) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
  classical
  obtain ⟨Vset, hVne, F, _, vx, b, hπ, hacyc, hmin, htriData, hleaf⟩ := h
  set Cf : Finset (Site d) := (boxFinsetBK d n).filter (fun x => IsCanonicalTrifurcation d ω x)
    with hCf
  have hmemCf : ∀ x, x ∈ Cf ↔ x ∈ box d n ∧ IsCanonicalTrifurcation d ω x := by
    intro x; rw [hCf, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]
  have hCfcard : Cf.card = ctc2_canonTcount d ω n := rfl
  have hdeg3 : ∀ x, x ∈ box d n → IsCanonicalTrifurcation d ω x → 3 ≤ F.degree (vx x) := by
    intro x hxbox htri
    obtain ⟨hvx, hreach, hcut⟩ := htriData x hxbox htri
    exact bst_deg_ge_three_of_boxOpenForest hπ hxbox (ctc2_isTrifurcation_of_canonical htri) hvx
      hreach hcut
  have hvxinjOn : Set.InjOn vx Cf := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hmemCf] at hx hy
    have hx' : (vx x : Site d) = x := (htriData x hx.1 hx.2).1
    have hy' : (vx y : Site d) = y := (htriData y hy.1 hy.2).1
    rw [← hx', ← hy', hxy]
  set Cw : Finset (↑Vset : Type) := Cf.image vx with hCw
  have hcardCw : Cw.card = Cf.card := by rw [hCw, Finset.card_image_of_injOn hvxinjOn]
  have hCwdeg : ∀ w ∈ Cw, 3 ≤ F.degree w := by
    intro w hw
    rw [hCw, Finset.mem_image] at hw
    obtain ⟨x, hxC, rfl⟩ := hw
    rw [hmemCf] at hxC
    exact hdeg3 x hxC.1 hxC.2
  have h1 : Cf.card ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := by
    rw [← hcardCw]; exact flc2_trifImage_card_le_deg3 F Cw hCwdeg
  have h2 : (univ.filter (fun v => 3 ≤ F.degree v)).card
      ≤ (univ.filter (fun v => F.degree v = 1)).card :=
    flc2_forest_internal_le_leaves F hacyc hmin
  have h3 : (univ.filter (fun v => F.degree v = 1)).card ≤ boxSV_boundaryCard d (n + 1) := by
    rw [← tfc_boundaryFinset_card]
    apply Finset.card_le_card_of_injOn (fun v : (↑Vset : Type) => (v : Site d))
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, tfc_mem_boundaryFinset]
      exact hleaf v hv.2
    · intro u _ v _ huv; exact Subtype.val_injective huv
  calc ctc2_canonTcount d ω n = Cf.card := hCfcard.symm
    _ ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := h1
    _ ≤ (univ.filter (fun v => F.degree v = 1)).card := h2
    _ ≤ boxSV_boundaryCard d (n + 1) := h3


def dfc_CanonArmForestReachingSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (c : Site d → Fin 3 → Site d) (zr : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d (n + 1)) ∧
    (∃ v, spc_OnBPath T B v) ∧
    (∀ x, x ∈ box d n → IsCanonicalTrifurcation d ω x →
      (∀ i, T.Adj x (c x i)) ∧
      (¬ Connected d (removeSite x ω) (c x 0) (c x 1) ∧
       ¬ Connected d (removeSite x ω) (c x 0) (c x 2) ∧
       ¬ Connected d (removeSite x ω) (c x 1) (c x 2)) ∧
      (∀ i, zr x i ∈ B ∧ ∃ w : T.Walk (c x i) (zr x i), x ∉ w.support))


def dfc_CanonSpanForestArmsSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (m : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d (n + 1)) ∧
    (∃ v, spc_OnBPath T B v) ∧
    (∀ x, x ∈ box d n → IsCanonicalTrifurcation d ω x →
      spc_OnBPath T B x ∧
      ((m x 0 ≠ m x 1 ∧ m x 0 ≠ m x 2 ∧ m x 1 ≠ m x 2) ∧
       (∀ i, T.Adj x (m x i) ∧ spc_OnBPath T B (m x i)) ∧
       (¬ Connected d (removeSite x ω) (m x 0) (m x 1) ∧
        ¬ Connected d (removeSite x ω) (m x 0) (m x 2) ∧
        ¬ Connected d (removeSite x ω) (m x 1) (m x 2))))


theorem dfc_canonSpanForestArmsSucc_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : dfc_CanonArmForestReachingSucc ω n) : dfc_CanonSpanForestArmsSucc ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ := h
  refine ⟨Vall, T, hTdec, B, c, hTac, hTopen, hTsupp, hBbd, hRne, ?_⟩
  intro x hxbox htri
  obtain ⟨hadj, hcut, hreach⟩ := hData x hxbox htri
  obtain ⟨hcut01, hcut02, hcut12⟩ := hcut
  have hne01 : c x 0 ≠ c x 1 := fun h => hcut01 (h ▸ connected_refl _ _)
  have hne02 : c x 0 ≠ c x 2 := fun h => hcut02 (h ▸ connected_refl _ _)
  have hne12 : c x 1 ≠ c x 2 := fun h => hcut12 (h ▸ connected_refl _ _)
  obtain ⟨hz0, w0, hw0x⟩ := hreach 0
  obtain ⟨hz1, w1, hw1x⟩ := hreach 1
  obtain ⟨hz2, w2, hw2x⟩ := hreach 2
  obtain ⟨hxsurv, hc0surv, hc1surv⟩ :=
    sfa_onBPath_of_arms ω T hTopen B (hadj 0) (hadj 1) w0 hw0x hz0 w1 hw1x hz1 hcut01
  obtain ⟨_, _, hc2surv⟩ :=
    sfa_onBPath_of_arms ω T hTopen B (hadj 0) (hadj 2) w0 hw0x hz0 w2 hw2x hz2 hcut02
  refine ⟨hxsurv, ⟨hne01, hne02, hne12⟩, ?_, hcut01, hcut02, hcut12⟩
  intro i
  refine ⟨hadj i, ?_⟩
  fin_cases i
  · exact hc0surv
  · exact hc1surv
  · exact hc2surv

open Classical in

theorem dfc_canonBoxOpenForestSucc_of_spanForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : dfc_CanonSpanForestArmsSucc ω n) : dfc_CanonBoxOpenForestSucc ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, m, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ := h
  have hRfin : {v | spc_OnBPath T B v}.Finite := by
    apply Set.Finite.subset (Vall.finite_toSet)
    intro v hv
    obtain ⟨w, hadj, _⟩ := spc_survivor_has_neighbor T B v hv
    exact hTsupp v w hadj
  set Vset : Finset (Site d) := hRfin.toFinset with hVset
  have hmemVset : ∀ v, v ∈ Vset ↔ spc_OnBPath T B v := by
    intro v; rw [hVset, Set.Finite.mem_toFinset]; rfl
  have hVne : Nonempty (↥Vset) := by
    obtain ⟨v, hv⟩ := hRne; exact ⟨⟨v, (hmemVset v).mpr hv⟩⟩
  set F₀ : SimpleGraph (↥Vset) := T.comap (fun (u : ↥Vset) => (u : Site d)) with hF₀
  haveI hF₀dec : DecidableRel F₀.Adj := fun a b => by rw [hF₀, comap_adj]; infer_instance
  have hF₀adj : ∀ u v : ↥Vset, F₀.Adj u v ↔ T.Adj (u : Site d) (v : Site d) := by
    intro u v; rw [hF₀, comap_adj]
  have hF₀ac : F₀.IsAcyclic :=
    hTac.comap ⟨(fun (u : ↥Vset) => (u : Site d)), fun {a b} h => h⟩ (fun a b h => Subtype.ext h)
  have hlift : ∀ v, spc_OnBPath T B v → v ∈ Vset := fun v hv => (hmemVset v).mpr hv
  let dflt : ↥Vset := hVne.some
  set vx : Site d → ↥Vset := fun x =>
    if hx : spc_OnBPath T B x then ⟨x, hlift x hx⟩ else dflt with hvxdef
  set bb : Site d → Fin 3 → ↥Vset := fun x i =>
    if hx : spc_OnBPath T B (m x i) then ⟨m x i, hlift _ hx⟩ else dflt with hbbdef
  refine ⟨Vset, hVne, F₀, hF₀dec, vx, bb, ?_, hF₀ac, ?_, ?_, ?_⟩
  · intro u v huv
    rw [hF₀adj] at huv; exact hTopen _ _ huv
  · intro v
    have hvR : spc_OnBPath T B (v : Site d) := (hmemVset (v : Site d)).mp v.2
    obtain ⟨w, hadjw, hwR⟩ := spc_survivor_has_neighbor T B (v : Site d) hvR
    exact spc_deg_ge_one F₀ v ⟨w, hlift w hwR⟩ (by rw [hF₀adj]; exact hadjw)
  · intro x hxbox htri
    obtain ⟨hxR, hmne, hmadj, hmsep⟩ := hData x hxbox htri
    have hvxval : (vx x : Site d) = x := by simp only [hvxdef, dif_pos hxR]
    refine ⟨hvxval, ?_, ?_⟩
    · intro i
      have hmi := hmadj i
      have hbbval : (bb x i : Site d) = m x i := by simp only [hbbdef, dif_pos hmi.2]
      refine ⟨?_, ?_⟩
      · refine Adj.reachable ?_
        rw [hF₀adj, hvxval, hbbval]; exact hmi.1
      · intro hh
        have hval : (bb x i : Site d) = (vx x : Site d) :=
          congrArg (fun (u : ↥Vset) => (u : Site d)) hh
        rw [hbbval, hvxval] at hval
        exact (T.ne_of_adj hmi.1) hval.symm
    · have h0 : (bb x 0 : Site d) = m x 0 := by simp only [hbbdef, dif_pos (hmadj 0).2]
      have h1 : (bb x 1 : Site d) = m x 1 := by simp only [hbbdef, dif_pos (hmadj 1).2]
      have h2 : (bb x 2 : Site d) = m x 2 := by simp only [hbbdef, dif_pos (hmadj 2).2]
      rw [h0, h1, h2]; exact hmsep
  · intro v hv
    have hvR : spc_OnBPath T B (v : Site d) := (hmemVset (v : Site d)).mp v.2
    by_cases hvB : (v : Site d) ∈ B
    · exact hBbd hvB
    · exfalso
      obtain ⟨w₁, w₂, hw12, ha1, ha2, hr1, hr2⟩ :=
        spc_interior_two_neighbors T B (v : Site d) hvR hvB
      have hdeg2 : 2 ≤ F₀.degree v :=
        spc_deg_ge_two F₀ v ⟨w₁, hlift w₁ hr1⟩ ⟨w₂, hlift w₂ hr2⟩
          (fun hh => hw12 (Subtype.ext_iff.mp hh))
          (by rw [hF₀adj]; exact ha1) (by rw [hF₀adj]; exact ha2)
      omega





theorem dfc_canonArmForestReachingSucc (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hexists : ∃ x, x ∈ box d n ∧ IsCanonicalTrifurcation d ω x) :
    dfc_CanonArmForestReachingSucc ω n := by
  classical
  have hdata : ∀ x, x ∈ box d n → IsCanonicalTrifurcation d ω x →
      ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
        (∀ i, (cfc_T ω (n + 1)).Adj x (c i)) ∧
        (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
         ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
         ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
        (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧
          ∃ w : (cfc_T ω (n + 1)).Walk (c i) (zr i), x ∉ w.support) := by
    intro x hxbox htri
    obtain ⟨a₁, a₂, a₃, _hne3, hadj3, hinf3, hsep3⟩ := htri
    refine cfc_trif_data ω (n + 1) (by omega) (box_subset_succ d n hxbox) ![a₁, a₂, a₃] ?_ ?_ ?_
      ?_ ?_
    · intro i; fin_cases i
      · exact hadj3.1
      · exact hadj3.2.1
      · exact hadj3.2.2
    · intro i; fin_cases i
      · exact ((openSubgraph d ω).ne_of_adj hadj3.1).symm
      · exact ((openSubgraph d ω).ne_of_adj hadj3.2.1).symm
      · exact ((openSubgraph d ω).ne_of_adj hadj3.2.2).symm
    · intro i; fin_cases i
      · exact arc_neighbour_in_box_succ hxbox hadj3.1.1
      · exact arc_neighbour_in_box_succ hxbox hadj3.2.1.1
      · exact arc_neighbour_in_box_succ hxbox hadj3.2.2.1
    · exact ⟨hsep3.1, hsep3.2.1, hsep3.2.2⟩
    · intro i; fin_cases i
      · exact hinf3.1
      · exact hinf3.2.1
      · exact hinf3.2.2
  choose! c zr hcadj hccut hcreach using hdata
  set B : Set (Site d) := vertexBoundary d (n + 1) with hBdef
  obtain ⟨x0, hx0box, hx0tri⟩ := hexists
  have hc0reach := hcreach x0 hx0box hx0tri
  obtain ⟨hz0, w0, hw0x⟩ := hc0reach 0
  obtain ⟨hz1, w1, hw1x⟩ := hc0reach 1
  have hcut01 := (hccut x0 hx0box hx0tri).1
  obtain ⟨hxsurv, _, _⟩ :=
    sfa_onBPath_of_arms ω (cfc_T ω (n + 1)) (cfc_T_open ω (n + 1)) B
      (hcadj x0 hx0box hx0tri 0) (hcadj x0 hx0box hx0tri 1)
      w0 hw0x hz0 w1 hw1x hz1 hcut01
  refine ⟨boxFinsetBK d (n + 2), cfc_T ω (n + 1), Classical.decRel _, B, c, zr,
    cfc_T_acyclic ω (n + 1), cfc_T_open ω (n + 1), ?_, le_refl _, ⟨x0, hxsurv⟩, ?_⟩
  · intro u v huv
    rw [boxFinsetBK, Set.Finite.mem_toFinset]
    exact cfc_T_support ω (n + 1) u v huv
  · intro x hxbox htri
    exact ⟨hcadj x hxbox htri, hccut x hxbox htri, hcreach x hxbox htri⟩







theorem dfc_canonTcount_le_boundary_succ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
  classical
  by_cases hexists : ∃ x, x ∈ box d n ∧ IsCanonicalTrifurcation d ω x
  · exact dfc_canonTcount_le_boundary_succ_of_canonBoxOpenForestSucc ω n
      (dfc_canonBoxOpenForestSucc_of_spanForestArms ω n
        (dfc_canonSpanForestArmsSucc_of_armForestReaching ω n
          (dfc_canonArmForestReachingSucc ω n hn hexists)))
  · have h0 : ctc2_canonTcount d ω n = 0 := by
      unfold ctc2_canonTcount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      rw [boxFinsetBK, Set.Finite.mem_toFinset] at hx
      exact fun htri => hexists ⟨x, hx, htri⟩
    rw [h0]; exact Nat.zero_le _

end StatMech.Percolation
