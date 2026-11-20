/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexConnEndgame
import Code.Universality.HexBridge
import Code.Universality.HexInjections
import Code.Universality.HexBridgeDecomp
import Code.Universality.HexBridgeRecon

namespace StatMech.Universality

open Complex HexWalk List Filter
open scoped Topology BigOperators
















theorem hexVerticesAux_take_prefix (m : ℂ) (h : ℤ) (ts : List ℤ) (cp : ℕ) :
    (verticesAux m h (ts.take cp)) <+: (verticesAux m h ts) := by
  induction ts generalizing m h cp with
  | nil => simp
  | cons t ts ih =>
    cases cp with
    | zero =>
      simp only [List.take_zero, verticesAux_nil, verticesAux_cons]
      exact ⟨_, rfl⟩
    | succ cp =>
      simp only [List.take_succ_cons, verticesAux_cons]
      exact (prefix_cons_inj _).mpr (ih (m + halfStep h + halfStep (h + t)) (h + t) cp)








theorem hexVerticesAux_drop (m : ℂ) (h : ℤ) (ts : List ℤ) (cp : ℕ) (hcp : cp ≤ ts.length) :
    ∃ m', (verticesAux m h ts).drop cp = verticesAux m' (h + (ts.take cp).sum) (ts.drop cp) := by
  induction cp generalizing m h ts with
  | zero => exact ⟨m, by simp⟩
  | succ cp ih =>
    cases ts with
    | nil => simp at hcp
    | cons t ts =>
      simp only [List.length_cons] at hcp
      obtain ⟨m', hm'⟩ := ih (m + halfStep h + halfStep (h + t)) (h + t) ts (by omega)
      refine ⟨m', ?_⟩
      simp only [verticesAux_cons, List.drop_succ_cons, List.take_succ_cons, List.sum_cons]
      rw [hm', show h + (t + (ts.take cp).sum) = h + t + (ts.take cp).sum from by ring]








theorem hexCut_legal_take (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hleg : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns a h0 (ts.take cp)).IsLegalSAW := by
  obtain ⟨hturns, hsaw⟩ := hleg
  refine ⟨fun t ht => hturns t (List.mem_of_mem_take ht), ?_⟩
  unfold IsSAW vertices ofTurns at hsaw ⊢
  simp only at hsaw ⊢
  exact hsaw.sublist (hexVerticesAux_take_prefix a h0 ts cp).sublist





noncomputable def hexDropMid (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ) : ℂ :=
  if hcp : cp ≤ ts.length then (hexVerticesAux_drop a h0 ts cp hcp).choose else a











theorem hexCut_legal_drop (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ) (hcp : cp ≤ ts.length)
    (hleg : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns (hexDropMid a h0 ts cp) (h0 + (ts.take cp).sum) (ts.drop cp)).IsLegalSAW := by
  obtain ⟨hturns, hsaw⟩ := hleg
  refine ⟨fun t ht => hturns t (List.mem_of_mem_drop ht), ?_⟩
  unfold IsSAW vertices ofTurns at hsaw ⊢
  simp only at hsaw ⊢
  unfold hexDropMid
  rw [dif_pos hcp, ← (hexVerticesAux_drop a h0 ts cp hcp).choose_spec]
  exact hsaw.sublist (List.drop_sublist cp _)














noncomputable def hexHighestCutClosed (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (memD : List ℤ → Prop)
    (B : Type)
    (wtB : B → ℝ) (wtB_nn : ∀ b, 0 ≤ wtB b)
    (cpos : {ts // memD ts} → ℕ)
    (hcp : ∀ d : {ts // memD ts}, cpos d ≤ d.1.length)
    (split : {ts // memD ts} → B × B)
    (hwtB1 : ∀ d, wtB (split d).1 = hexSAWwt a h0 x (d.1.take (cpos d)))
    (hwtB2 : ∀ d, wtB (split d).2 =
      hexSAWwt (hexDropMid a h0 d.1 (cpos d)) (h0 + (d.1.take (cpos d)).sum) x
        (d.1.drop (cpos d)))
    (split_inj : Function.Injective split)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1))
    (hBsum : Summable wtB) :
    HexHighestCut x⁻¹ :=
  hexHighestCutRecon a h0 hx memD B wtB wtB_nn cpos
    (fun d => hexDropMid a h0 d.1 (cpos d))
    (fun d => h0 + (d.1.take (cpos d)).sum)
    hcp
    (fun d hleg => hexCut_legal_take a h0 d.1 (cpos d) hleg)
    (fun d hleg => hexCut_legal_drop a h0 d.1 (cpos d) (hcp d) hleg)
    split hwtB1 hwtB2 split_inj hDsum hBsum








theorem hexZ_chi_div_seams_closed (c lam tau ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = ups) :
    ¬ Summable (fun n => c n * hexChiE ^ n) :=
  hexZ_chi_div_from_geometry_recon c lam tau ups hbdry hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc















theorem hexSeams_powerset_range_tendsto :
    Tendsto (fun N => (Finset.range N).powerset) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro s
  refine ⟨(s.sup (fun t => t.sup id)) + 1, fun M hM => ?_⟩
  intro t ht
  rw [Finset.mem_powerset]
  intro i hi
  rw [Finset.mem_range]
  have h1 : i ≤ t.sup id := Finset.le_sup (f := id) hi
  have h2 : t.sup id ≤ s.sup (fun t => t.sup id) := Finset.le_sup ht
  omega



theorem hexSeams_prod_one_add_mono (f : ℕ → ℝ) (hnn : ∀ i, 0 ≤ f i) :
    Monotone (fun N => ∏ i ∈ Finset.range N, (1 + f i)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Finset.prod_range_succ]
  have hp : (0 : ℝ) ≤ ∏ i ∈ Finset.range n, (1 + f i) :=
    Finset.prod_nonneg (fun i _ => by have := hnn i; linarith)
  nlinarith [hnn n]



theorem hexSeams_prod_one_add_le_tprod (f : ℕ → ℝ) (hnn : ∀ i, 0 ≤ f i)
    (hm : Multipliable (fun i => 1 + f i)) (N : ℕ) :
    ∏ i ∈ Finset.range N, (1 + f i) ≤ ∏' i, (1 + f i) :=
  Monotone.ge_of_tendsto (hexSeams_prod_one_add_mono f hnn)
    (Multipliable.tendsto_prod_tprod_nat hm) N





theorem hexSeams_summable_finset_prod (f : ℕ → ℝ) (hnn : ∀ i, 0 ≤ f i)
    (hm : Multipliable (fun i => 1 + f i)) :
    Summable (fun t : Finset ℕ => ∏ i ∈ t, f i) := by
  apply summable_of_sum_le (c := ∏' i, (1 + f i))
  · intro t; exact Finset.prod_nonneg (fun i _ => hnn i)
  · intro s
    obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp hexSeams_powerset_range_tendsto) s
    have hsub : s ≤ (Finset.range N).powerset := hN N le_rfl
    calc ∑ t ∈ s, ∏ i ∈ t, f i
        ≤ ∑ t ∈ (Finset.range N).powerset, ∏ i ∈ t, f i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun t _ _ => Finset.prod_nonneg (fun i _ => hnn i))
      _ = ∏ i ∈ Finset.range N, (1 + f i) := (Finset.prod_one_add _).symm
      _ ≤ ∏' i, (1 + f i) := hexSeams_prod_one_add_le_tprod f hnn hm N
















theorem tsum_finset_prod_eq_tprod (f : ℕ → ℝ) (hnn : ∀ i, 0 ≤ f i)
    (hm : Multipliable (fun i => 1 + f i)) :
    (∑' t : Finset ℕ, ∏ i ∈ t, f i) = ∏' i, (1 + f i) := by
  have hsum := hexSeams_summable_finset_prod f hnn hm
  have hHS := hsum.hasSum
  have ht1 : Tendsto (fun N => ∑ t ∈ (Finset.range N).powerset, ∏ i ∈ t, f i) atTop
      (𝓝 (∑' t : Finset ℕ, ∏ i ∈ t, f i)) := by
    have := hHS.comp hexSeams_powerset_range_tendsto
    convert this using 1
  have heq : (fun N => ∑ t ∈ (Finset.range N).powerset, ∏ i ∈ t, f i)
      = (fun N => ∏ i ∈ Finset.range N, (1 + f i)) := by
    funext N; exact (Finset.prod_one_add _).symm
  rw [heq] at ht1
  exact tendsto_nhds_unique ht1 (Multipliable.tendsto_prod_tprod_nat hm)













def hexCanonBridge (T : ℕ) (hT : 0 < T) : HexBridge := ⟨T, hT, [0], by simp⟩





noncomputable def bridgeSeqOfFinset (s : Finset ℕ) (hs : ∀ T ∈ s, 0 < T) : List HexBridge :=
  (s.sort (· ≤ ·)).reverse.pmap (fun T (hT : 0 < T) => hexCanonBridge T hT)
    (by
      intro T hT
      rw [List.mem_reverse, Finset.mem_sort] at hT
      exact hs T hT)


theorem bridgeSeqOfFinset_widths (s : Finset ℕ) (hs : ∀ T ∈ s, 0 < T) :
    (bridgeSeqOfFinset s hs).map HexBridge.width = (s.sort (· ≤ ·)).reverse := by
  unfold bridgeSeqOfFinset
  rw [List.map_pmap, List.pmap_eq_map_attach]
  simp [hexCanonBridge]



theorem hexSeams_sort_reverse_strictDecr (s : Finset ℕ) :
    ((s.sort (· ≤ ·)).reverse).Pairwise (· > ·) := by
  rw [List.pairwise_reverse]
  have hs : (s.sort (· ≤ ·)).Pairwise (· ≤ ·) := Finset.pairwise_sort s (· ≤ ·)
  have hn : (s.sort (· ≤ ·)).Nodup := Finset.sort_nodup s (· ≤ ·)
  rw [List.pairwise_iff_get] at hs ⊢
  intro i j hij
  have hle := hs i j hij
  have hne := (List.nodup_iff_injective_get.mp hn).ne (Fin.ne_of_lt hij)
  omega







theorem bridgeSeqOfFinset_strictDecr (s : Finset ℕ) (hs : ∀ T ∈ s, 0 < T) :
    StrictDecreasingWidths (bridgeSeqOfFinset s hs) := by
  unfold StrictDecreasingWidths
  rw [← List.pairwise_map (R := (· > ·)) (f := HexBridge.width), bridgeSeqOfFinset_widths]
  exact hexSeams_sort_reverse_strictDecr s











theorem bridgeSeq_prod (s : Finset ℕ) (hs : ∀ T ∈ s, 0 < T) (υ : ℕ → ℝ) :
    ((bridgeSeqOfFinset s hs).map (fun b => υ b.width)).prod = ∏ T ∈ s, υ T := by
  have hmap : (bridgeSeqOfFinset s hs).map (fun b => υ b.width)
      = ((bridgeSeqOfFinset s hs).map HexBridge.width).map υ := by
    rw [List.map_map]; rfl
  rw [hmap, bridgeSeqOfFinset_widths, List.map_reverse, List.prod_reverse,
    ← Finset.prod_map_toList s υ]
  exact (List.Perm.map υ (Finset.sort_perm_toList s (· ≤ ·))).prod_eq













noncomputable def hexHWDataClosed (c : ℕ → ℝ) (υ : ℕ → ℝ) (x : ℝ) (N : ℕ)
    (hυnn : ∀ T, 0 ≤ υ T)
    (hmul : Multipliable (fun T => 1 + υ T))
    (Dn : Type) [Fintype Dn]
    (wtγ : Dn → ℝ) (wtγ_nn : ∀ d, 0 ≤ wtγ d)
    (partial_eq : ∑ d, wtγ d = ∑ n ∈ Finset.range N, c n * x ^ n)
    (decomp : Dn → Finset ℕ × Finset ℕ)
    (decomp_inj : Function.Injective decomp)
    (weight_bound : ∀ d, wtγ d ≤ (x ^ 2)⁻¹ *
      ((∏ T ∈ (decomp d).1, υ T) * (∏ T ∈ (decomp d).2, υ T))) :
    HexHWDataRecon c υ x N where
  S := Finset ℕ
  Dn := Dn
  Dn_fintype := inferInstance
  wtγ := wtγ
  wtS := fun s => ∏ T ∈ s, υ T
  wtγ_nn := wtγ_nn
  wtS_nn := fun _ => Finset.prod_nonneg (fun T _ => hυnn T)
  S_summable := hexSeams_summable_finset_prod υ hυnn hmul
  partial_eq := partial_eq
  half_sum_eq := tsum_finset_prod_eq_tprod υ hυnn hmul
  decomp := decomp
  decomp_inj := decomp_inj
  weight_bound := weight_bound









theorem hexZ_conv_seams_closed (c : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hlt : x < hexChiE) (hc : ∀ n, 0 ≤ c n)
    (C : ∀ T, HexColumn T hexChiE)
    (H : ∀ N, HexHWDataRecon c (fun T => (C T).colSum x) x N) :
    Summable (fun n => c n * x ^ n) :=
  hexZ_conv_recon_from_geometry c x hx hlt hc C H

end StatMech.Universality
