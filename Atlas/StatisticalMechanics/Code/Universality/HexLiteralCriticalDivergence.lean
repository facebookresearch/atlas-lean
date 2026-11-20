/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Code.Universality.HexCoefficientAggregation
import Code.Universality.HexInjections
import Code.Universality.HexBridgeRecon
import Code.Universality.HexColumnMembershipClose
import Code.Universality.HexMirrorPairFromReflection
import Code.Universality.HexMirrorOrbitBoundary

namespace StatMech.Universality

open HexWalk
open scoped BigOperators





theorem hlcd_not_summable_iff (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    (¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n)) ↔
      ¬ Summable (fun ts : List ℤ => hexSAWwt a h0 x ts) := by
  simpa only [hlc_sawCountR] using
    (not_congr (hlc_summable_iff a h0 hx)).symm



theorem hlcd_not_summable_of_literal (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (hdiv : ¬ Summable (fun ts : List ℤ => hexSAWwt a h0 x ts)) :
    ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) :=
  (hlcd_not_summable_iff a h0 hx).2 hdiv




noncomputable def hlcd_columnSum (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) : ℝ :=
  (hexColumnEmbOfPred a h0 (le_of_lt hexChiE_pos) P scale).fiberSum v


theorem hlcd_columnSum_nonneg (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) :
    0 ≤ hlcd_columnSum a h0 P scale v := by
  unfold hlcd_columnSum HexColumnEmb.fiberSum
  exact tsum_nonneg (fun _ => hexSAWwt_nonneg a h0 (le_of_lt hexChiE_pos) _)



theorem hlcd_columnSum_summable (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ)
    (hwalk : Summable (fun ts : List ℤ => hexSAWwt a h0 hexChiE ts)) :
    Summable (hlcd_columnSum a h0 P scale) := by
  exact (hexColumnEmbOfPred a h0 (le_of_lt hexChiE_pos) P scale).fiberSum_summable hwalk







structure HexLiteralSideFibers (a : ℂ) (h0 : ℤ) where
  
  Index : ℕ → Type*
  
  turns : ∀ T, Index T → List ℤ
  
  turns_injective : ∀ T, Function.Injective (turns T)
  
  height : ∀ T, Index T → ℕ

namespace HexLiteralSideFibers



noncomputable def columnEmb {a : ℂ} {h0 : ℤ}
    (S : HexLiteralSideFibers a h0) (T : ℕ) :
    HexColumnEmb (List ℤ) (S.Index T) where
  wtSAW := hexSAWwt a h0 hexChiE
  emb := S.turns T
  emb_inj := S.turns_injective T
  wtSAW_nn := hexSAWwt_nonneg a h0 (le_of_lt hexChiE_pos)
  scale := S.height T



def sidePred {a : ℂ} {h0 : ℤ} (S : HexLiteralSideFibers a h0)
    (T L : ℕ) (ts : List ℤ) : Prop :=
  ∃ i : S.Index T, S.height T i = L ∧ S.turns T i = ts


theorem sidePred_height_unique {a : ℂ} {h0 : ℤ}
    (S : HexLiteralSideFibers a h0) (T L L' : ℕ) (ts : List ℤ)
    (hL : S.sidePred T L ts) (hL' : S.sidePred T L' ts) : L = L' := by
  obtain ⟨i, hiL, hits⟩ := hL
  obtain ⟨j, hjL, hjts⟩ := hL'
  have hij : i = j := S.turns_injective T (hits.trans hjts.symm)
  subst j
  exact hiL.symm.trans hjL

end HexLiteralSideFibers




structure HexLiteralSideLimits (a : ℂ) (h0 : ℤ) (tau : ℕ → ℝ) where
  fibers : HexLiteralSideFibers a h0
  tendsto_tau : ∀ T,
    Filter.Tendsto (fibers.columnEmb T).fiberSum
      Filter.atTop (nhds (tau T))





theorem hlcd_side_limit_forces_literal_divergence
    {a : ℂ} {h0 : ℤ} {tau : ℕ → ℝ}
    (S : HexLiteralSideLimits a h0 tau)
    (hpos : ∃ T, 1 ≤ T ∧ 0 < tau T) :
    ¬ Summable (fun ts : List ℤ => hexSAWwt a h0 hexChiE ts) := by
  rintro hwalk
  obtain ⟨T, _, hTpos⟩ := hpos
  have hfib : Summable (S.fibers.columnEmb T).fiberSum :=
    (S.fibers.columnEmb T).fiberSum_summable hwalk
  have hzero := hfib.tendsto_atTop_zero
  have : tau T = 0 := tendsto_nhds_unique (S.tendsto_tau T) hzero
  exact (ne_of_gt hTpos) this





def hlcd_atScale (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) (ts : List ℤ) : Prop :=
  ∃ h : P ts, scale ⟨ts, h⟩ = v



noncomputable def hlcd_atScaleEquiv (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) :
    {ts : List ℤ // hlcd_atScale P scale v ts} ≃
      {i : {ts : List ℤ // P ts} // scale i = v} where
  toFun i := ⟨⟨i.1, i.2.choose⟩, i.2.choose_spec⟩
  invFun i := ⟨i.1.1, ⟨i.1.2, i.2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)



theorem hlcd_ups_atScale_eq_columnSum (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) :
    hpb_upsS a h0 hexChiE (hlcd_atScale P scale v) =
      hlcd_columnSum a h0 P scale v := by
  unfold hpb_upsS hlcd_columnSum HexColumnEmb.fiberSum
  change (∑' b : {ts : List ℤ // hlcd_atScale P scale v ts},
      hexSAWwt a h0 hexChiE b.1) =
    ∑' i : {i : {ts : List ℤ // P ts} // scale i = v},
      hexSAWwt a h0 hexChiE i.1.1
  rw [← (hlcd_atScaleEquiv P scale v).tsum_eq
    (fun i => hexSAWwt a h0 hexChiE i.1.1)]
  rfl






theorem hlcd_boundary_of_reflected_pairing
    {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {C : HexFiniteStripBoundaryCore R h0 D P}
    (S : HexFiniteStripReflectedPairing (ι := I) C)
    (A : S.DCSAngles) (lam tau ups : ℝ)
    (hlam : lam = HexFiniteStripMirrorPairedData.dcsLam S.toMirrorPairedData
      (A.toClassification S))
    (htau : tau = HexFiniteStripMirrorPairedData.dcsTau S.toMirrorPairedData
      (A.toClassification S))
    (hups : ups = HexFiniteStripMirrorPairedData.dcsUps S.toMirrorPairedData
      (A.toClassification S)) :
    hexCl * lam + hexCt * tau + ups = 1 := by
  rw [hlam, htau, hups]
  exact S.normalized_dcs_identity A



theorem hlcd_boundary_of_mirror_orbits
    {I K V : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {C : HexFiniteStripBoundaryCore R h0 D P}
    (S : HexFiniteStripMirrorOrbitData (I := I) (K := K) C)
    (A : S.DCSClassification) (lam tau ups : ℝ)
    (hlam : lam = S.dcsLam A)
    (htau : tau = S.dcsTau A)
    (hups : ups = S.dcsUps A) :
    hexCl * lam + hexCt * tau + ups = 1 := by
  rw [hlam, htau, hups]
  exact S.normalized_dcs_identity A











theorem hlcd_critical_divergence_of_recurrence
    (a : ℂ) (h0 : ℤ)
    (lam tau : ℕ → ℝ)
    (Pcol : List ℤ → Prop)
    (scale : {ts : List ℤ // Pcol ts} → ℕ)
    (S : HexLiteralSideLimits a h0 tau)
    (hbdry : ∀ v, 1 ≤ v →
      hexCl * lam v + hexCt * tau v + hlcd_columnSum a h0 Pcol scale v = 1)
    (hrec : ∀ v, 1 ≤ v →
      lam (v + 1) - lam v ≤
        hexChiE⁻¹ * (hlcd_columnSum a h0 Pcol scale (v + 1)) ^ 2)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hcolPos : ∀ v, 1 ≤ v → 0 < hlcd_columnSum a h0 Pcol scale v)
    (hτnn : ∀ v, 0 ≤ tau v) :
    ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
  have hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) →
      ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
    intro hpos
    exact hlcd_not_summable_of_literal a h0 (le_of_lt hexChiE_pos)
      (hlcd_side_limit_forces_literal_divergence S hpos)
  have hcolEmb :
      Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) →
        Summable (hlcd_columnSum a h0 Pcol scale) := by
    intro hcoeff
    have hwalk : Summable (fun ts : List ℤ => hexSAWwt a h0 hexChiE ts) := by
      have h := (hlc_summable_iff a h0 (le_of_lt hexChiE_pos)).mpr
        (show Summable (fun n : ℕ => (hlc_sawCount a h0 n : ℝ) * hexChiE ^ n) by
          simpa only [hlc_sawCountR] using hcoeff)
      exact h
    exact hlcd_columnSum_summable a h0 Pcol scale hwalk
  exact hexZ_chi_div_recon (hlc_sawCountR a h0) lam tau
    (hlcd_columnSum a h0 Pcol scale) hbdry hrec hlamMono hcolPos
    (hlcd_columnSum_nonneg a h0 Pcol scale) hτnn hτcol hcolEmb




theorem hlcd_critical_divergence_of_cuts
    (a : ℂ) (h0 : ℤ)
    (lam tau : ℕ → ℝ)
    (Pcol : List ℤ → Prop)
    (scale : {ts : List ℤ // Pcol ts} → ℕ)
    (S : HexLiteralSideLimits a h0 tau)
    (hbdry : ∀ v, 1 ≤ v →
      hexCl * lam v + hexCt * tau v + hlcd_columnSum a h0 Pcol scale v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hcolPos : ∀ v, 1 ≤ v → 0 < hlcd_columnSum a h0 Pcol scale v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v →
      (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
    (hCutB : ∀ v, 1 ≤ v →
      (∑' b, (Cut v).wtB b) = hlcd_columnSum a h0 Pcol scale (v + 1)) :
    ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
  apply hlcd_critical_divergence_of_recurrence a h0 lam tau Pcol scale S
    hbdry
  · intro v hv
    exact hexRec_term_of_cut_recon lam (hlcd_columnSum a h0 Pcol scale) v
      (Cut v) (hCutD v hv) (hCutB v hv)
  · exact hlamMono
  · exact hcolPos
  · exact hτnn










theorem hlcd_critical_divergence_of_half_classes
    (a : ℂ) (h0 : ℤ)
    (memA : ℕ → List ℤ → Prop)
    (Pcol : List ℤ → Prop)
    (scale : {ts : List ℤ // Pcol ts} → ℕ)
    (tau : ℕ → ℝ)
    (S : HexLiteralSideLimits a h0 tau)
    (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
    (HC : ∀ v, HexHalfClass a h0 hexChiE
      (fun ts => memA (v + 1) ts ∧ ¬ memA v ts)
      (hlcd_atScale Pcol scale (v + 1)))
    (hDsum : ∀ v, Summable
      (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} =>
        hexSAWwt a h0 hexChiE d.1))
    (hBsum : ∀ v, Summable
      (fun b : {ts // hlcd_atScale Pcol scale (v + 1) ts} =>
        hexSAWwt a h0 hexChiE b.1))
    (hAsum : ∀ v, Summable
      (fun n : {ts // memA (v + 1) ts} => hexSAWwt a h0 hexChiE n.1))
    (hbdry : ∀ v, 1 ≤ v →
      hexCl * hpb_lamS a h0 hexChiE (memA v) + hexCt * tau v +
        hlcd_columnSum a h0 Pcol scale v = 1)
    (hlamMono : ∀ v, 1 ≤ v →
      hpb_lamS a h0 hexChiE (memA v) ≤
        hpb_lamS a h0 hexChiE (memA (v + 1)))
    (hcolPos : ∀ v, 1 ≤ v → 0 < hlcd_columnSum a h0 Pcol scale v)
    (hτnn : ∀ v, 0 ≤ tau v) :
    ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
  let Cut : ℕ → HexHighestCut hexChiE⁻¹ := fun v =>
    hpb_cut a h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts)
      (hlcd_atScale Pcol scale (v + 1)) (HC v) (hDsum v) (hBsum v)
  apply hlcd_critical_divergence_of_cuts a h0
    (fun v => hpb_lamS a h0 hexChiE (memA v)) tau Pcol scale S
    hbdry hlamMono hcolPos hτnn Cut
  · intro v _
    exact hpb_cut_wtγ_eq_diff a h0 memA
      (hlcd_atScale Pcol scale (v + 1)) v (hsub v) (HC v)
      (hDsum v) (hBsum v) (hAsum v)
  · intro v _
    calc
      (∑' b, (Cut v).wtB b) =
          hpb_upsS a h0 hexChiE (hlcd_atScale Pcol scale (v + 1)) :=
        hpb_cut_wtB_sum a h0
          (fun ts => memA (v + 1) ts ∧ ¬ memA v ts)
          (hlcd_atScale Pcol scale (v + 1)) (HC v) (hDsum v) (hBsum v)
      _ = hlcd_columnSum a h0 Pcol scale (v + 1) :=
        hlcd_ups_atScale_eq_columnSum a h0 Pcol scale (v + 1)





theorem hlcd_critical_divergence_of_halves
    (a : ℂ) (h0 : ℤ)
    (memA : ℕ → List ℤ → Prop)
    (Pcol : List ℤ → Prop)
    (scale : {ts : List ℤ // Pcol ts} → ℕ)
    (tau : ℕ → ℝ)
    (S : HexLiteralSideLimits a h0 tau)
    (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
    (HIC : ∀ v, HexHalvesInColumn h0
      (fun ts => memA (v + 1) ts ∧ ¬ memA v ts)
      (hlcd_atScale Pcol scale (v + 1)))
    (hDsum : ∀ v, Summable
      (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} =>
        hexSAWwt a h0 hexChiE d.1))
    (hBsum : ∀ v, Summable
      (fun b : {ts // hlcd_atScale Pcol scale (v + 1) ts} =>
        hexSAWwt a h0 hexChiE b.1))
    (hAsum : ∀ v, Summable
      (fun n : {ts // memA (v + 1) ts} => hexSAWwt a h0 hexChiE n.1))
    (hbdry : ∀ v, 1 ≤ v →
      hexCl * hpb_lamS a h0 hexChiE (memA v) + hexCt * tau v +
        hlcd_columnSum a h0 Pcol scale v = 1)
    (hlamMono : ∀ v, 1 ≤ v →
      hpb_lamS a h0 hexChiE (memA v) ≤
        hpb_lamS a h0 hexChiE (memA (v + 1)))
    (hcolPos : ∀ v, 1 ≤ v → 0 < hlcd_columnSum a h0 Pcol scale v)
    (hτnn : ∀ v, 0 ≤ tau v) :
    ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
  apply hlcd_critical_divergence_of_half_classes a h0 memA Pcol scale tau S
    hsub
    (fun v => hhe_halfClass_of_halves a h0 hexChiE
      (fun ts => memA (v + 1) ts ∧ ¬ memA v ts)
      (hlcd_atScale Pcol scale (v + 1)) (HIC v))
    hDsum hBsum hAsum hbdry hlamMono hcolPos hτnn

end StatMech.Universality
