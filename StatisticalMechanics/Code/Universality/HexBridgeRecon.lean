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

namespace StatMech.Universality

open Filter Topology Complex
open scoped Topology BigOperators







lemma hexChiE_inv_pos : 0 < hexChiE⁻¹ := inv_pos.mpr hexChiE_pos















theorem hexCut_numVertices_sum (a₁ a₂ : ℂ) (h1 h2 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hcp : cp ≤ ts.length) :
    (HexWalk.ofTurns a₁ h1 (ts.take cp)).numVertices
      + (HexWalk.ofTurns a₂ h2 (ts.drop cp)).numVertices
      = (HexWalk.ofTurns a₁ h1 ts).numVertices + 1 := by
  simp only [HexWalk.numVertices, HexWalk.ofTurns,
    List.length_take, List.length_drop, min_eq_left hcp]
  omega






theorem hexCut_pow_factor (a₁ a₂ : ℂ) (h1 h2 : ℤ) (x : ℝ) (hx : 0 < x)
    (ts : List ℤ) (cp : ℕ) (hcp : cp ≤ ts.length) :
    x ^ (HexWalk.ofTurns a₁ h1 ts).numVertices
      = x⁻¹ * (x ^ (HexWalk.ofTurns a₁ h1 (ts.take cp)).numVertices
                * x ^ (HexWalk.ofTurns a₂ h2 (ts.drop cp)).numVertices) := by
  have hsum := hexCut_numVertices_sum a₁ a₂ h1 h2 ts cp hcp
  rw [← pow_add, hsum, pow_succ,
    mul_comm (x ^ (HexWalk.ofTurns a₁ h1 ts).numVertices) x,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hx), one_mul]











theorem hexHighestCut_weight_bound_literal (a a₂ : ℂ) (h0 h2 : ℤ) (x : ℝ) (hx : 0 < x)
    (ts : List ℤ) (cp : ℕ) (hcp : cp ≤ ts.length)
    (hleg1 : (HexWalk.ofTurns a h0 ts).IsLegalSAW →
      (HexWalk.ofTurns a h0 (ts.take cp)).IsLegalSAW)
    (hleg2 : (HexWalk.ofTurns a h0 ts).IsLegalSAW →
      (HexWalk.ofTurns a₂ h2 (ts.drop cp)).IsLegalSAW) :
    hexSAWwt a h0 x ts
      ≤ x⁻¹ * (hexSAWwt a h0 x (ts.take cp) * hexSAWwt a₂ h2 x (ts.drop cp)) := by
  by_cases hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW
  · rw [hexSAWwt_of_isLegalSAW a h0 x hleg,
        hexSAWwt_of_isLegalSAW a h0 x (hleg1 hleg),
        hexSAWwt_of_isLegalSAW a₂ h2 x (hleg2 hleg)]
    exact le_of_eq (hexCut_pow_factor a a₂ h0 h2 x hx ts cp hcp)
  · unfold hexSAWwt
    rw [if_neg hleg]
    exact mul_nonneg (by positivity)
      (mul_nonneg (hexSAWwt_nonneg a h0 (le_of_lt hx) (ts.take cp))
        (hexSAWwt_nonneg a₂ h2 (le_of_lt hx) (ts.drop cp)))














noncomputable def hexHighestCutRecon (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (memD : List ℤ → Prop)
    (B : Type)
    (wtB : B → ℝ) (wtB_nn : ∀ b, 0 ≤ wtB b)
    (cpos : {ts // memD ts} → ℕ)
    (a2 : {ts // memD ts} → ℂ) (h2 : {ts // memD ts} → ℤ)
    (hcp : ∀ d : {ts // memD ts}, cpos d ≤ d.1.length)
    (hleg1 : ∀ d : {ts // memD ts}, (HexWalk.ofTurns a h0 d.1).IsLegalSAW →
      (HexWalk.ofTurns a h0 (d.1.take (cpos d))).IsLegalSAW)
    (hleg2 : ∀ d : {ts // memD ts}, (HexWalk.ofTurns a h0 d.1).IsLegalSAW →
      (HexWalk.ofTurns (a2 d) (h2 d) (d.1.drop (cpos d))).IsLegalSAW)
    (split : {ts // memD ts} → B × B)
    (hwtB1 : ∀ d, wtB (split d).1 = hexSAWwt a h0 x (d.1.take (cpos d)))
    (hwtB2 : ∀ d, wtB (split d).2 = hexSAWwt (a2 d) (h2 d) x (d.1.drop (cpos d)))
    (split_inj : Function.Injective split)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1))
    (hBsum : Summable wtB) :
    HexHighestCut x⁻¹ where
  D := {ts // memD ts}
  B := B
  wtγ := fun d => hexSAWwt a h0 x d.1
  wtB := wtB
  wtB_nn := wtB_nn
  wtγ_nn := fun d => hexSAWwt_nonneg a h0 (le_of_lt hx) d.1
  split := split
  split_inj := split_inj
  weight_bound := by
    intro d
    rw [hwtB1 d, hwtB2 d]
    exact hexHighestCut_weight_bound_literal a (a2 d) h0 (h2 d) x hx d.1 (cpos d)
      (hcp d) (hleg1 d) (hleg2 d)
  D_summable := hDsum
  B_summable := hBsum






theorem hexRec_term_of_cut_recon (lam ups : ℕ → ℝ) (v : ℕ)
    (Cut : HexHighestCut hexChiE⁻¹)
    (hD : (∑' d, Cut.wtγ d) = lam (v + 1) - lam v)
    (hB : (∑' b, Cut.wtB b) = ups (v + 1)) :
    lam (v + 1) - lam v ≤ hexChiE⁻¹ * (ups (v + 1)) ^ 2 := by
  have hrb := Cut.recursion_bound (le_of_lt hexChiE_inv_pos)
  rw [hD, hB] at hrb
  exact hrb










theorem hexZ_chi_div_recon (c lam tau ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE⁻¹ * (ups (v + 1)) ^ 2)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable (fun n => c n * hexChiE ^ n))
    (hυemb : Summable (fun n => c n * hexChiE ^ n) → Summable ups) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  by_cases hτ : ∃ v, 1 ≤ v ∧ 0 < tau v
  · 
    exact hτcol hτ
  · 
    push Not at hτ
    have hτ0 : ∀ v, 1 ≤ v → tau v = 0 := fun v hv =>
      le_antisymm (hτ v hv) (hτnn v)
    have hbd2 : ∀ v, 1 ≤ v → hexCl * lam v + ups v = 1 := by
      intro v hv
      have h := hbdry v hv
      rw [hτ0 v hv, mul_zero, add_zero] at h
      exact h
    
    have hdefect : ∀ v, 1 ≤ v →
        ups v - ups (v + 1) ≤ (hexCl * hexChiE⁻¹) * (ups (v + 1)) ^ 2 := by
      intro v hv
      have e1 := hbd2 v hv
      have e2 := hbd2 (v + 1) (by omega)
      have hr := hrec v hv
      have hmul : hexCl * (lam (v + 1) - lam v) ≤ hexCl * (hexChiE⁻¹ * (ups (v + 1)) ^ 2) :=
        mul_le_mul_of_nonneg_left hr (le_of_lt hexCl_pos)
      nlinarith [hmul, e1, e2]
    have hυmono : ∀ v, 1 ≤ v → ups (v + 1) ≤ ups v := by
      intro v hv
      have e1 := hbd2 v hv
      have e2 := hbd2 (v + 1) (by omega)
      have hmono := hlamMono v hv
      nlinarith [mul_le_mul_of_nonneg_left hmono (le_of_lt hexCl_pos)]
    set C := hexCl * hexChiE⁻¹ with hCdef
    have hCpos : 0 < C := mul_pos hexCl_pos hexChiE_inv_pos
    have hrecip := hex_recip_induction ups C hCpos hυpos hυmono hdefect
    set m := min (ups 1) (1 / C) with hmdef
    have hmpos : 0 < m := lt_min (hυpos 1 le_rfl) (by positivity)
    have hlower : ∀ v, 1 ≤ v → m / v ≤ ups v := by
      intro v hv
      have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
      have huv := hυpos v hv
      have h := hrecip v hv
      rw [div_le_div_iff₀ huv hmpos] at h
      rw [div_le_iff₀ hvpos]
      nlinarith [h]
    have hυdiv : ¬ Summable ups :=
      hex_div_of_lower_bound ups m hmpos hυnn hlower
    intro hZ
    exact hυdiv (hυemb hZ)








theorem hexZ_chi_div_from_geometry_recon (c lam tau ups : ℕ → ℝ)
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
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  
  have hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE⁻¹ * (ups (v + 1)) ^ 2 :=
    fun v hv => hexRec_term_of_cut_recon lam ups v (Cut v) (hCutD v hv) (hCutB v hv)
  have hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable (fun n => c n * hexChiE ^ n) := by
    intro hex
    have := Eτ.not_summable_of_not_summable (hτdiv hex)
    rw [hEτ] at this
    exact this
  have hυemb : Summable (fun n => c n * hexChiE ^ n) → Summable ups := by
    intro hZ
    rw [← hEυ] at hZ
    have := Eυ.fiberSum_summable hZ
    rw [hEυc] at this
    exact this
  exact hexZ_chi_div_recon c lam tau ups hbdry hrec hlamMono hυpos hυnn hτnn hτcol hυemb

















theorem hexHW_two_overcount_pow_factor (x : ℝ) (hx : 0 < x) (g m n : ℕ)
    (hmn : m + n = g + 2) :
    x ^ g = (x ^ 2)⁻¹ * (x ^ m * x ^ n) := by
  rw [← pow_add, hmn, pow_add]
  field_simp







structure HexHWDataRecon (c : ℕ → ℝ) (υ : ℕ → ℝ) (x : ℝ) (N : ℕ) where
  
  S : Type
  
  Dn : Type
  
  Dn_fintype : Fintype Dn
  
  wtγ : Dn → ℝ
  
  wtS : S → ℝ
  
  wtγ_nn : ∀ d, 0 ≤ wtγ d
  
  wtS_nn : ∀ s, 0 ≤ wtS s
  
  S_summable : Summable wtS
  
  partial_eq : ∑ d, wtγ d = ∑ n ∈ Finset.range N, c n * x ^ n
  
  half_sum_eq : (∑' s, wtS s) = ∏' T, (1 + υ T)
  
  decomp : Dn → S × S
  
  decomp_inj : Function.Injective decomp
  
  weight_bound : ∀ d, wtγ d ≤ (x ^ 2)⁻¹ * (wtS (decomp d).1 * wtS (decomp d).2)

attribute [instance] HexHWDataRecon.Dn_fintype

namespace HexHWDataRecon

variable {c υ : ℕ → ℝ} {x : ℝ} {N : ℕ}







theorem partial_bound_recon (H : HexHWDataRecon c υ x N) :
    ∑ n ∈ Finset.range N, c n * x ^ n ≤ 2 * (x ^ 2)⁻¹ * (∏' T, (1 + υ T)) ^ 2 := by
  classical
  have hx2nn : (0 : ℝ) ≤ (x ^ 2)⁻¹ := by positivity
  
  have hprodSumm : Summable (fun p : H.S × H.S => H.wtS p.1 * H.wtS p.2) :=
    H.S_summable.mul_of_nonneg H.S_summable H.wtS_nn H.wtS_nn
  have hprodEq : (∑' p : H.S × H.S, H.wtS p.1 * H.wtS p.2) = (∑' s, H.wtS s) ^ 2 := by
    rw [sq, ← H.S_summable.tsum_mul_tsum H.S_summable hprodSumm]
  
  have hcap : (∑ d, H.wtγ d) ≤ (x ^ 2)⁻¹ * (∑' s, H.wtS s) ^ 2 := by
    calc (∑ d, H.wtγ d)
        ≤ ∑ d : H.Dn, (x ^ 2)⁻¹ * (H.wtS (H.decomp d).1 * H.wtS (H.decomp d).2) :=
          Finset.sum_le_sum (fun d _ => H.weight_bound d)
      _ = (x ^ 2)⁻¹ * ∑ d : H.Dn, (H.wtS (H.decomp d).1 * H.wtS (H.decomp d).2) := by
          rw [Finset.mul_sum]
      _ = (x ^ 2)⁻¹ * ∑ p ∈ Finset.univ.image H.decomp, H.wtS p.1 * H.wtS p.2 := by
          rw [Finset.sum_image (fun a _ b _ h => H.decomp_inj h)]
      _ ≤ (x ^ 2)⁻¹ * ∑' p : H.S × H.S, H.wtS p.1 * H.wtS p.2 := by
          apply mul_le_mul_of_nonneg_left _ hx2nn
          exact Summable.sum_le_tsum _
            (fun p _ => mul_nonneg (H.wtS_nn _) (H.wtS_nn _)) hprodSumm
      _ = (x ^ 2)⁻¹ * (∑' s, H.wtS s) ^ 2 := by rw [hprodEq]
  rw [← H.partial_eq]
  calc (∑ d, H.wtγ d) ≤ (x ^ 2)⁻¹ * (∑' s, H.wtS s) ^ 2 := hcap
    _ = (x ^ 2)⁻¹ * (∏' T, (1 + υ T)) ^ 2 := by rw [H.half_sum_eq]
    _ ≤ 2 * (x ^ 2)⁻¹ * (∏' T, (1 + υ T)) ^ 2 := by
        nlinarith [mul_nonneg hx2nn (sq_nonneg (∏' T, (1 + υ T)))]

end HexHWDataRecon










theorem hexZ_conv_recon (c upsx : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hc : ∀ n, 0 ≤ c n)
    (hbridge : ∀ N, ∑ n ∈ Finset.range N, c n * x ^ n
        ≤ 2 * (x ^ 2)⁻¹ * (∏' T, (1 + upsx T)) ^ 2) :
    Summable (fun n => c n * x ^ n) := by
  refine summable_of_sum_range_le
    (f := fun n => c n * x ^ n) (c := 2 * (x ^ 2)⁻¹ * (∏' T, (1 + upsx T)) ^ 2) ?_ ?_
  · intro n; exact mul_nonneg (hc n) (pow_nonneg (le_of_lt hx) n)
  · intro N; exact hbridge N









theorem hexZ_conv_recon_from_geometry (c : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hlt : x < hexChiE) (hc : ∀ n, 0 ≤ c n)
    (C : ∀ T, HexColumn T hexChiE)
    (H : ∀ N, HexHWDataRecon c (fun T => (C T).colSum x) x N) :
    Summable (fun n => c n * x ^ n) := by
  set upsx : ℕ → ℝ := fun T => (C T).colSum x with hupsx
  
  
  
  
  have hυnn : ∀ T, 0 ≤ upsx T := fun T => (C T).colSum_nonneg (le_of_lt hx)
  have hυle : ∀ T, upsx T ≤ (x / hexChiE) ^ T :=
    fun T => (C T).colSum_le_pow (le_of_lt hx) hexChiE_pos (le_of_lt hlt)
  have hsum : Summable upsx := hex_ups_summable upsx x (le_of_lt hx) hlt hυnn hυle
  have _hmul : Multipliable (fun T => 1 + upsx T) := hex_bridge_multipliable upsx hsum
  refine hexZ_conv_recon c upsx x hx hc ?_
  intro N
  exact (H N).partial_bound_recon

end StatMech.Universality
