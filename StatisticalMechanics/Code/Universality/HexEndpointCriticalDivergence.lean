/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexEndpointAggregation
import Code.Universality.HexBridgeRecon

namespace StatMech.Universality

open HexWalk

noncomputable section



noncomputable def hexEndpointColumnEmbOfPred
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) (scale : {ts : List ℤ // P ts} → ℕ) :
    HexColumnEmb (List ℤ) {ts : List ℤ // P ts} where
  wtSAW := hexEndpointSAWwt a h0 x
  emb := fun s => s.1
  emb_inj := Subtype.val_injective
  wtSAW_nn := hexEndpointSAWwt_nonneg a h0 hx
  scale := scale


noncomputable def hecd_columnSum
    (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) : ℝ :=
  (hexEndpointColumnEmbOfPred a h0 (le_of_lt hexChiE_pos) P scale).fiberSum v

theorem hecd_columnSum_nonneg
    (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) :
    0 ≤ hecd_columnSum a h0 P scale v := by
  unfold hecd_columnSum HexColumnEmb.fiberSum
  exact tsum_nonneg
    (fun _ => hexEndpointSAWwt_nonneg a h0 (le_of_lt hexChiE_pos) _)

theorem hecd_columnSum_summable
    (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ)
    (hwalk : Summable (hexEndpointSAWwt a h0 hexChiE)) :
    Summable (hecd_columnSum a h0 P scale) :=
  (hexEndpointColumnEmbOfPred a h0 (le_of_lt hexChiE_pos) P scale).fiberSum_summable
    hwalk


structure HexEndpointSideFibers (a : ℂ) (h0 : ℤ) where
  Index : ℕ → Type*
  turns : ∀ T, Index T → List ℤ
  turns_injective : ∀ T, Function.Injective (turns T)
  height : ∀ T, Index T → ℕ

namespace HexEndpointSideFibers

noncomputable def columnEmb {a : ℂ} {h0 : ℤ}
    (S : HexEndpointSideFibers a h0) (T : ℕ) :
    HexColumnEmb (List ℤ) (S.Index T) where
  wtSAW := hexEndpointSAWwt a h0 hexChiE
  emb := S.turns T
  emb_inj := S.turns_injective T
  wtSAW_nn := hexEndpointSAWwt_nonneg a h0 (le_of_lt hexChiE_pos)
  scale := S.height T

def sidePred {a : ℂ} {h0 : ℤ} (S : HexEndpointSideFibers a h0)
    (T L : ℕ) (ts : List ℤ) : Prop :=
  ∃ i : S.Index T, S.height T i = L ∧ S.turns T i = ts

theorem sidePred_height_unique {a : ℂ} {h0 : ℤ}
    (S : HexEndpointSideFibers a h0) (T L L' : ℕ) (ts : List ℤ)
    (hL : S.sidePred T L ts) (hL' : S.sidePred T L' ts) : L = L' := by
  obtain ⟨i, hiL, hits⟩ := hL
  obtain ⟨j, hjL, hjts⟩ := hL'
  have hij : i = j := S.turns_injective T (hits.trans hjts.symm)
  subst j
  exact hiL.symm.trans hjL

end HexEndpointSideFibers



structure HexEndpointSideLimits
    (a : ℂ) (h0 : ℤ) (tau : ℕ → ℝ) where
  fibers : HexEndpointSideFibers a h0
  tendsto_tau : ∀ T,
    Filter.Tendsto (fibers.columnEmb T).fiberSum
      Filter.atTop (nhds (tau T))



theorem hecd_side_limit_forces_walk_divergence
    {a : ℂ} {h0 : ℤ} {tau : ℕ → ℝ}
    (S : HexEndpointSideLimits a h0 tau)
    (hpos : ∃ T, 1 ≤ T ∧ 0 < tau T) :
    ¬ Summable (hexEndpointSAWwt a h0 hexChiE) := by
  rintro hwalk
  obtain ⟨T, _, hTpos⟩ := hpos
  have hfib : Summable (S.fibers.columnEmb T).fiberSum :=
    (S.fibers.columnEmb T).fiberSum_summable hwalk
  have hzero := hfib.tendsto_atTop_zero
  have : tau T = 0 := tendsto_nhds_unique (S.tendsto_tau T) hzero
  exact (ne_of_gt hTpos) this




theorem hecd_critical_divergence_of_recurrence
    (a : ℂ) (h0 : ℤ)
    (lam tau : ℕ → ℝ)
    (Pcol : List ℤ → Prop)
    (scale : {ts : List ℤ // Pcol ts} → ℕ)
    (S : HexEndpointSideLimits a h0 tau)
    (hbdry : ∀ v, 1 ≤ v →
      hexCl * lam v + hexCt * tau v +
        hecd_columnSum a h0 Pcol scale v = 1)
    (hrec : ∀ v, 1 ≤ v →
      lam (v + 1) - lam v ≤
        hexChiE⁻¹ * (hecd_columnSum a h0 Pcol scale (v + 1)) ^ 2)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hcolPos : ∀ v, 1 ≤ v → 0 < hecd_columnSum a h0 Pcol scale v)
    (hτnn : ∀ v, 0 ≤ tau v) :
    ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
  have hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) →
      ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) := by
    intro hpos
    exact hexEndpoint_hlc_not_summable_of_walk a h0 hexChiE_pos
      (hecd_side_limit_forces_walk_divergence S hpos)
  have hcolEmb :
      Summable (fun n : ℕ => hlc_sawCountR a h0 n * hexChiE ^ n) →
        Summable (hecd_columnSum a h0 Pcol scale) := by
    intro hcoeff
    have hwalk : Summable (hexEndpointSAWwt a h0 hexChiE) :=
      (hexEndpoint_walk_summable_iff_hlc a h0 hexChiE_pos).2 hcoeff
    exact hecd_columnSum_summable a h0 Pcol scale hwalk
  exact hexZ_chi_div_recon (hlc_sawCountR a h0) lam tau
    (hecd_columnSum a h0 Pcol scale) hbdry hrec hlamMono hcolPos
    (hecd_columnSum_nonneg a h0 Pcol scale) hτnn hτcol hcolEmb

end

end StatMech.Universality
