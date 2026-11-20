/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































































import Code.Universality.HexW2Cut
import Code.Universality.HexFiniteStripClose
import Code.Universality.HexInfraDisplacement
import Code.Universality.HexInfraWinding
import Code.Universality.HexWall3
import Code.Universality.HexHalfEdgeClose

namespace StatMech.Universality

open HexWalk List
open scoped BigOperators












theorem hcm_vertex_is_prefix_last (a : ℂ) (h0 : ℤ) (ts : List ℤ) (v : ℂ)
    (hv : v ∈ verticesAux a h0 ts) :
    ∃ k ≤ ts.length, v = hexInfra_midAccum a h0 (ts.take k)
      + HexWalk.halfStep (hexInfra_headAccum h0 (ts.take k)) := by
  induction ts generalizing a h0 with
  | nil =>
    rw [verticesAux_nil, List.mem_singleton] at hv
    exact ⟨0, by simp, by simp [hv]⟩
  | cons t ts ih =>
    rw [verticesAux_cons, List.mem_cons] at hv
    rcases hv with h | h
    · exact ⟨0, by simp, by simp [h]⟩
    · obtain ⟨k, hk, hkv⟩ := ih (a + halfStep h0 + halfStep (h0 + t)) (h0 + t) h
      refine ⟨k + 1, by simp; omega, ?_⟩
      rw [List.take_succ_cons, hexInfra_midAccum_cons, hexInfra_headAccum_cons]
      exact hkv






theorem hcm_vertex_re_le_cutDisp (a : ℂ) (h0 : ℤ) (ts : List ℤ) (v : ℂ)
    (hv : v ∈ verticesAux a h0 ts) :
    v.re ≤ a.re + hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts) := by
  obtain ⟨k, hk, hkv⟩ := hcm_vertex_is_prefix_last a h0 ts v hv
  rw [hkv, hexInfra_ofTurns_last_re a h0 (ts.take k)]
  have hmax := hexW2_cutPos_max h0 ts k hk
  unfold hexW2_partialDisp at hmax ⊢
  linarith





theorem hcm_stMid_eq_midAccum (m : ℂ) (h : ℤ) (ts : List ℤ) :
    hfs_stMid m h ts = hexInfra_midAccum m h ts := by
  induction ts generalizing m h with
  | nil => simp [hfs_stMid, hexInfra_midAccum]
  | cons t ts ih => simp [hfs_stMid, hexInfra_midAccum, ih]



theorem hcm_stHead_eq_headAccum (h : ℤ) (ts : List ℤ) :
    hfs_stHead h ts = hexInfra_headAccum h ts := by
  induction ts generalizing h with
  | nil => simp [hfs_stHead, hexInfra_headAccum]
  | cons t ts ih => simp [hfs_stHead, hexInfra_headAccum, ih]


theorem hcm_first_vertex_mem (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    a + halfStep h0 ∈ verticesAux a h0 ts := by
  cases ts with
  | nil => rw [verticesAux_nil]; exact List.mem_singleton.mpr rfl
  | cons x xs => rw [verticesAux_cons]; exact List.mem_cons_self






theorem hcm_dropStart_re (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ) :
    (hfs_stMid a h0 (ts.take cp)).re
      + (HexWalk.halfStep (hfs_stHead h0 (ts.take cp))).re
      = a.re + hexW2_partialDisp h0 ts cp := by
  rw [hcm_stMid_eq_midAccum, hcm_stHead_eq_headAccum, hexInfra_midAccum_re]
  unfold hexW2_partialDisp
  ring












def hcm_SpansWidth (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) : Prop :=
  ∃ u ∈ (HexWalk.ofTurns a h0 ts).vertices, ∃ w ∈ (HexWalk.ofTurns a h0 ts).vertices,
    (T : ℝ) ≤ w.re - u.re



theorem hcm_verticesAux_translate (δ : ℂ) (m : ℂ) (h : ℤ) (ts : List ℤ) :
    verticesAux (m + δ) h ts = (verticesAux m h ts).map (· + δ) := by
  induction ts generalizing m h with
  | nil => simp [verticesAux_nil]; ring
  | cons t ts ih =>
    rw [verticesAux_cons, verticesAux_cons, List.map_cons, List.cons.injEq]
    refine ⟨by ring, ?_⟩
    rw [show m + δ + halfStep h + halfStep (h + t)
          = (m + halfStep h + halfStep (h + t)) + δ by ring]
    exact ih _ _







theorem hcm_spans_transl (m m' : ℂ) (h : ℤ) (T : ℕ) (ts : List ℤ) :
    hcm_SpansWidth m h T ts ↔ hcm_SpansWidth m' h T ts := by
  have hkey : m' = m + (m' - m) := by ring
  unfold hcm_SpansWidth HexWalk.ofTurns HexWalk.vertices
  simp only
  constructor
  · rintro ⟨u, hu, w, hw, hgap⟩
    rw [hkey, hcm_verticesAux_translate]
    refine ⟨u + (m' - m), List.mem_map_of_mem hu, w + (m' - m), List.mem_map_of_mem hw, ?_⟩
    simp only [Complex.add_re]; linarith
  · rintro ⟨u, hu, w, hw, hgap⟩
    rw [hkey, hcm_verticesAux_translate] at hu hw
    rw [List.mem_map] at hu hw
    obtain ⟨u0, hu0, hu0e⟩ := hu
    obtain ⟨w0, hw0, hw0e⟩ := hw
    refine ⟨u0, hu0, w0, hw0, ?_⟩
    rw [← hu0e, ← hw0e] at hgap
    simp only [Complex.add_re] at hgap; linarith







def hcm_BridgeContent (a0 : ℂ) (T : ℕ) (ts : List ℤ) : Prop :=
  ∃ h : ℤ, hcm_SpansWidth a0 h T ts












theorem hcm_take_spans (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) (cp : ℕ)
    (hT : (T : ℝ) ≤ hexW2_partialDisp h0 ts cp - (HexWalk.halfStep h0).re) :
    hcm_SpansWidth a h0 T (ts.take cp) := by
  refine ⟨a + halfStep h0, hcm_first_vertex_mem a h0 (ts.take cp),
    hexInfra_midAccum a h0 (ts.take cp) + halfStep (hexInfra_headAccum h0 (ts.take cp)), ?_, ?_⟩
  · exact hexInfra_verticesAux_getLast_mem a h0 (ts.take cp)
  · rw [hexInfra_ofTurns_last_re a h0 (ts.take cp), Complex.add_re]
    unfold hexW2_partialDisp at hT
    linarith












theorem hcm_drop_first_is_max (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hcp : cp = hexW2_cutPos h0 ts) (hcple : cp ≤ ts.length) :
    ∀ v ∈ (HexWalk.ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp))
        (ts.drop cp)).vertices,
      v.re ≤ (hfs_stMid a h0 (ts.take cp)).re
        + (HexWalk.halfStep (hfs_stHead h0 (ts.take cp))).re := by
  intro v hvmem
  rw [show (HexWalk.ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp))
      (ts.drop cp)).vertices = (verticesAux a h0 ts).drop cp from ?_] at hvmem
  · have hvfull : v ∈ verticesAux a h0 ts := List.mem_of_mem_drop hvmem
    have hbound := hcm_vertex_re_le_cutDisp a h0 ts v hvfull
    have hstart := hcm_dropStart_re a h0 ts cp
    rw [← hcp] at hbound
    rw [hstart]; linarith
  · unfold HexWalk.ofTurns HexWalk.vertices
    simp only
    exact hfs_verticesAux_drop a h0 ts cp (hcp ▸ hcple)








theorem hcm_drop_not_reaches (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (cp : ℕ) (hcp : cp = hexW2_cutPos h0 ts) (hcple : cp ≤ ts.length) (T : ℕ) (hT : 1 ≤ T) :
    ¬ hexWall3_ReachesWidth (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp))
        T (ts.drop cp) := by
  rintro ⟨v, hvmem, hvre⟩
  have hmax := hcm_drop_first_is_max a h0 ts cp hcp hcple v hvmem
  have hhalf := hexInfra_halfStep_re_le (hfs_stHead h0 (ts.take cp))
  have hTr : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  
  linarith







theorem hcm_drop_spans (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) (cp : ℕ)
    (hdescend : (T : ℝ)
      ≤ (HexWalk.halfStep (hexInfra_headAccum h0 (ts.take cp))).re
        - (hexInfra_stepReSum (hexInfra_headAccum h0 (ts.take cp)) (ts.drop cp)
            + (HexWalk.halfStep
                (hexInfra_headAccum (hexInfra_headAccum h0 (ts.take cp)) (ts.drop cp))).re)) :
    hcm_SpansWidth (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp)) T (ts.drop cp) := by
  set m := hfs_stMid a h0 (ts.take cp) with hmdef
  set h := hfs_stHead h0 (ts.take cp) with hhdef
  have hh : h = hexInfra_headAccum h0 (ts.take cp) := hcm_stHead_eq_headAccum h0 (ts.take cp)
  have hm : m.re = a.re + hexInfra_stepReSum h0 (ts.take cp) := by
    rw [hmdef, hcm_stMid_eq_midAccum]; rw [hexInfra_midAccum_re]
  refine ⟨hexInfra_midAccum m h (ts.drop cp) + halfStep (hexInfra_headAccum h (ts.drop cp)), ?_,
          m + halfStep h, ?_, ?_⟩
  · unfold HexWalk.ofTurns HexWalk.vertices; simp only
    exact hexInfra_verticesAux_getLast_mem m h (ts.drop cp)
  · unfold HexWalk.ofTurns HexWalk.vertices; simp only; exact hcm_first_vertex_mem m h (ts.drop cp)
  · rw [Complex.add_re, Complex.add_re, hexInfra_midAccum_re, hm, hh]
    linarith [hdescend]














def hcm_CutReaches (h0 : ℤ) (T : ℕ) (memD : List ℤ → Prop) : Prop :=
  ∀ d : {ts // memD ts},
    (T : ℝ) ≤ hexW2_partialDisp h0 d.1 (hexW2_cutPos h0 d.1) - (HexWalk.halfStep h0).re





def hcm_DropDescends (h0 : ℤ) (T : ℕ) (memD : List ℤ → Prop) : Prop :=
  ∀ d : {ts // memD ts},
    (T : ℝ)
      ≤ (HexWalk.halfStep (hexInfra_headAccum h0 (d.1.take (hexW2_cutPos h0 d.1)))).re
        - (hexInfra_stepReSum (hexInfra_headAccum h0 (d.1.take (hexW2_cutPos h0 d.1)))
              (d.1.drop (hexW2_cutPos h0 d.1))
            + (HexWalk.halfStep
                (hexInfra_headAccum (hexInfra_headAccum h0 (d.1.take (hexW2_cutPos h0 d.1)))
                  (d.1.drop (hexW2_cutPos h0 d.1)))).re)
















def hcm_halvesInColumn_of_descends (a0 : ℂ) (h0 : ℤ) (T : ℕ) (memD : List ℤ → Prop)
    (hreach : hcm_CutReaches h0 T memD)
    (hdesc : hcm_DropDescends h0 T memD) :
    HexHalvesInColumn h0 memD (hcm_BridgeContent a0 T) where
  htake := fun d => ⟨h0, hcm_take_spans a0 h0 T d.1 (hexW2_cutPos h0 d.1) (hreach d)⟩
  hdrop := fun d => by
    refine ⟨hfs_stHead h0 (d.1.take (hexW2_cutPos h0 d.1)), ?_⟩
    
    
    have hspan := hcm_drop_spans a0 h0 T d.1 (hexW2_cutPos h0 d.1) (hdesc d)
    exact (hcm_spans_transl (hfs_stMid a0 h0 (d.1.take (hexW2_cutPos h0 d.1))) a0
      (hfs_stHead h0 (d.1.take (hexW2_cutPos h0 d.1))) T
      (d.1.drop (hexW2_cutPos h0 d.1))).mp hspan
















noncomputable def hcm_halfClass_of_descends (a0 : ℂ) (h0 : ℤ) (x : ℝ) (T : ℕ)
    (memD : List ℤ → Prop)
    (hreach : hcm_CutReaches h0 T memD) (hdesc : hcm_DropDescends h0 T memD) :
    HexHalfClass a0 h0 x memD (hcm_BridgeContent a0 T) :=
  hhe_halfClass_of_halves a0 h0 x memD (hcm_BridgeContent a0 T)
    (hcm_halvesInColumn_of_descends a0 h0 T memD hreach hdesc)












theorem hcm_hexZ_chi_div_of_descends (c : ℕ → ℝ) (a0 : ℂ) (h0 : ℤ)
    (memA : ℕ → List ℤ → Prop)
    (tau : ℕ → ℝ)
    (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
    (hreach : ∀ v, hcm_CutReaches h0 (v + 1) (fun ts => memA (v + 1) ts ∧ ¬ memA v ts))
    (hdesc : ∀ v, hcm_DropDescends h0 (v + 1) (fun ts => memA (v + 1) ts ∧ ¬ memA v ts))
    (hDsum : ∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} =>
      hexSAWwt a0 h0 hexChiE d.1))
    (hBsum : ∀ v, Summable (fun b : {ts // hcm_BridgeContent a0 (v + 1) ts} =>
      hexSAWwt a0 h0 hexChiE b.1))
    (hAsum : ∀ v, Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a0 h0 hexChiE n.1))
    (hbdry : ∀ v, 1 ≤ v → hexCl * hpb_lamS a0 h0 hexChiE (memA v)
        + hexCt * tau v + hpb_upsS a0 h0 hexChiE (hcm_BridgeContent a0 v) = 1)
    (hlamMono : ∀ v, 1 ≤ v → hpb_lamS a0 h0 hexChiE (memA v)
        ≤ hpb_lamS a0 h0 hexChiE (memA (v + 1)))
    (hυpos : ∀ v, 1 ≤ v → 0 < hpb_upsS a0 h0 hexChiE (hcm_BridgeContent a0 v))
    (hτnn : ∀ v, 0 ≤ tau v)
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = fun v => hpb_upsS a0 h0 hexChiE (hcm_BridgeContent a0 v)) :
    ¬ Summable (fun n => c n * hexChiE ^ n) :=
  hhe_hexZ_chi_div c a0 h0 memA (fun v => hcm_BridgeContent a0 v) tau hsub
    (fun v => hcm_halvesInColumn_of_descends a0 h0 (v + 1)
      (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (hreach v) (hdesc v))
    hDsum hBsum hAsum hbdry hlamMono hυpos hτnn Eτ hEτ hτdiv Eυ hEυ hEυc














theorem hcm_singleRight_spans (a : ℂ) :
    hcm_SpansWidth a 0 0 [(-1 : ℤ)] := by
  have hdisp : ((0 : ℕ) : ℝ) ≤ hexW2_partialDisp 0 [(-1 : ℤ)] 1 - (HexWalk.halfStep 0).re := by
    rw [hexW2_singleRight_partialDisp_one]
    have hm1 : (HexWalk.halfStep (-1)).re = Real.sqrt 3 / 4 := by
      unfold HexWalk.halfStep hexUnit
      rw [show (Complex.I * ((Real.pi : ℂ) / 6 + (((-1 : ℤ) : ℝ)) * ((Real.pi : ℂ) / 3)))
            = ((Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by
              push_cast; ring]
      rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
      push_cast
      rw [show Real.pi / 6 + (-1 : ℝ) * (Real.pi / 3) = -(Real.pi / 6) by ring, Real.cos_neg,
        Real.cos_pi_div_six]
      norm_num; ring
    rw [hm1]
    have : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    push_cast; linarith
  have := hcm_take_spans a 0 0 [(-1 : ℤ)] 1 hdisp
  rwa [show [(-1 : ℤ)].take 1 = [(-1 : ℤ)] from rfl] at this




theorem hcm_singleRight_bridgeContent (a : ℂ) :
    hcm_BridgeContent a 0 [(-1 : ℤ)] :=
  ⟨0, hcm_singleRight_spans a⟩

end StatMech.Universality
