/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Sharpness.MeanfieldIsingMass
import Code.Sharpness.CToOneLattice
import Code.Sharpness.EpsToZeroLattice
import Code.Sharpness.TildeBc
import Code.Percolation.DctItem2

open Finset SimpleGraph
open scoped BigOperators

namespace StatMech
namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


noncomputable def sctCutSites {d n : ℕ} (T : Finset (sctBox d n)) :
    Finset (Site d) :=
  T.image Subtype.val

@[simp]
theorem mem_sctCutSites {d n : ℕ} {T : Finset (sctBox d n)} {x : sctBox d n} :
    x.1 ∈ sctCutSites T ↔ x ∈ T := by
  classical
  constructor
  · intro hx
    rw [sctCutSites, Finset.mem_image] at hx
    obtain ⟨y, hy, hv⟩ := hx
    have : y = x := Subtype.ext hv
    rwa [← this]
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩



noncomputable def sctCutVertexEquiv {d n : ℕ} (T : Finset (sctBox d n)) :
    {x : sctBox d n // x ∈ T} ≃ {z : Site d // z ∈ sctCutSites T} :=
  Equiv.ofBijective
    (fun x => (⟨x.1.1, mem_sctCutSites.mpr x.2⟩ :
      {z : Site d // z ∈ sctCutSites T}))
    ⟨by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {z : Site d // z ∈ sctCutSites T} => z.1) h,
    by
      intro z
      have hz : z.1 ∈ T.image Subtype.val := z.2
      rw [Finset.mem_image] at hz
      obtain ⟨x, hx, hv⟩ := hz
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      exact hv⟩



theorem sctCutVertexEquiv_adj {d n : ℕ} (T : Finset (sctBox d n))
    (a b : {x : sctBox d n // x ∈ T}) :
    ((sctBoxGraph d n).comap
        (Subtype.val : {x : sctBox d n // x ∈ T} → sctBox d n)).Adj a b ↔
      (graphS d (sctCutSites T)).Adj
        (sctCutVertexEquiv T a) (sctCutVertexEquiv T b) := by
  rfl




theorem sct_localCorr_eq_corrOriginInner {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) {x : sctBox d n}
    (ho : sctBoxOrigin d n ∈ T) (hx : x ∈ T)
    (hox : sctBoxOrigin d n ≠ x) :
    expectationJ (sctBoxGraph d n) beta (couplingIn (fun _ => 1) T)
        {sctBoxOrigin d n, x} =
      corrOriginInner d beta (sctCutSites T) x.1 := by
  classical
  let oT : {z : sctBox d n // z ∈ T} := ⟨sctBoxOrigin d n, ho⟩
  let xT : {z : sctBox d n // z ∈ T} := ⟨x, hx⟩
  have hbase := expectationJ_couplingIn_one_eq_induced
    (sctBoxGraph d n) beta T ho hx
  have hrel := Ising.isingExpectation_spinProd_relabel
    ((sctBoxGraph d n).comap
      (Subtype.val : {z : sctBox d n // z ∈ T} → sctBox d n))
    (graphS d (sctCutSites T)) (sctCutVertexEquiv T)
    (sctCutVertexEquiv_adj T) beta 0 ({oT, xT} : Finset _)
  have hmap : ({oT, xT} : Finset _).map (sctCutVertexEquiv T).toEmbedding =
      ({⟨origin d, mem_sctCutSites.mpr ho⟩,
        ⟨x.1, mem_sctCutSites.mpr hx⟩} :
          Finset {z : Site d // z ∈ sctCutSites T}) := by
    have horigin : (sctBoxOrigin d n).1 = origin d := rfl
    ext z
    simp [oT, xT, sctCutVertexEquiv, horigin]
  rw [hmap] at hrel
  rw [hbase, hrel]
  have ho' : origin d ∈ sctCutSites T := by
    exact Finset.mem_image.mpr ⟨sctBoxOrigin d n, ho, rfl⟩
  have hx' : x.1 ∈ sctCutSites T := mem_sctCutSites.mpr hx
  unfold corrOriginInner
  rw [dif_pos ho', dif_pos hx']
  unfold freeCorr
  rw [if_neg]
  intro heq
  apply hox
  apply Subtype.ext
  exact congrArg (fun z : {z : Site d // z ∈ sctCutSites T} => z.1) heq



theorem sct_corrOriginInner_origin {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) (ho : sctBoxOrigin d n ∈ T) :
    corrOriginInner d beta (sctCutSites T) (origin d) = 1 := by
  classical
  have ho' : origin d ∈ sctCutSites T := by
    exact Finset.mem_image.mpr ⟨sctBoxOrigin d n, ho, rfl⟩
  unfold corrOriginInner
  rw [dif_pos ho', dif_pos ho']
  exact freeCorr_self d beta (sctCutSites T) _


noncomputable def sctCurrentCutMass (d : ℕ) (beta h : ℝ) (n : ℕ)
    (T : Finset (sctBox d n)) : ℝ :=
  isingCutMass (withGhost (sctBoxGraph d n)) beta
    (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)



noncomputable def sctOrientedCutMass (d : ℕ) (beta h : ℝ) (n : ℕ)
    (x y : sctBox d n) : ℝ :=
  ∑ T : Finset (sctBox d n),
    if sctBoxOrigin d n ∈ T ∧ x ∈ T ∧ y ∉ T then
      corrOriginInner d beta (sctCutSites T) x.1 *
        sctCurrentCutMass d beta h n T
    else 0



theorem sct_normalizedDeltaLowerMass_eq_orientedCutMass
    {d n : ℕ} (beta h : ℝ) {x y : sctBox d n}
    (hox : sctBoxOrigin d n ≠ x) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      isingDeltaLowerMass (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1))
        (some (sctBoxOrigin d n)) (some x) (some y) none =
      sctOrientedCutMass d beta h n x y := by
  rw [normalizedDeltaLowerMass_fieldGhost (sctBoxGraph d n) beta h hox]
  unfold sctOrientedCutMass sctCurrentCutMass
  apply Finset.sum_congr rfl
  intro T _
  by_cases ho : sctBoxOrigin d n ∈ T <;> by_cases hx : x ∈ T <;>
    by_cases hy : y ∉ T
  · rw [if_pos ⟨ho, hx, hy⟩, if_pos ⟨ho, hx, hy⟩,
      sct_localCorr_eq_corrOriginInner beta T ho hx hox]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]



theorem sct_normalizedDeltaSelfLowerMass_eq_orientedCutMass
    {d n : ℕ} (beta h : ℝ) (y : sctBox d n) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      isingDeltaSelfLowerMass (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1))
        (some (sctBoxOrigin d n)) (some y) none =
      sctOrientedCutMass d beta h n (sctBoxOrigin d n) y := by
  rw [normalizedDeltaSelfLowerMass_fieldGhost
    (sctBoxGraph d n) beta h (sctBoxOrigin d n) y]
  unfold sctOrientedCutMass sctCurrentCutMass
  apply Finset.sum_congr rfl
  intro T _
  by_cases ho : sctBoxOrigin d n ∈ T <;> by_cases hy : y ∉ T
  · simp only [ho, hy, not_false_eq_true, and_self, and_true, if_true]
    have hc : corrOriginInner d beta (sctCutSites T) (sctBoxOrigin d n).1 = 1 := by
      simpa using sct_corrOriginInner_origin beta T ho
    rw [hc, one_mul]
  · simp [ho, hy]
  · simp [ho, hy]
  · simp [ho, hy]


theorem sctLatticeC_le_siteRatio {d n : ℕ} (beta h : ℝ)
    (y : sctBox d n) :
    sctLatticeC d beta h n ≤
      sctOriginMag d beta h n / sctBoxMag d beta h n y := by
  unfold sctLatticeC sct_cInfDep sctBoxSites
  exact Finset.inf'_le _ (Finset.mem_univ y)


theorem sctLatticeC_nonneg {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) :
    0 ≤ sctLatticeC d beta h n := by
  unfold sctLatticeC sct_cInfDep sctBoxSites
  apply Finset.le_inf' (sctBoxSites_nonempty d n)
  intro y _
  exact div_nonneg (sctOriginMag_pos d beta h hbeta hh n).le
    (sctBoxMag_pos d beta h hbeta hh n y).le


theorem sctLatticeC_mul_siteMag_le_origin {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) (y : sctBox d n) :
    sctLatticeC d beta h n * sctBoxMag d beta h n y ≤
      sctOriginMag d beta h n := by
  have hr := sctLatticeC_le_siteRatio beta h y
  have hy := sctBoxMag_pos d beta h hbeta hh n y
  rwa [le_div_iff₀ hy] at hr



theorem sct_nonincidentBondDelta_bound {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) {x y : sctBox d n}
    (hox : sctBoxOrigin d n ≠ x) (hoy : sctBoxOrigin d n ≠ y)
    (hxy : x ≠ y) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      (sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
          (sctBoxOrigin d n) s(x, y)) ≥
      sctLatticeC d beta h n *
        (sctOrientedCutMass d beta h n x y +
          sctOrientedCutMass d beta h n y x) := by
  let K := sctBoxGraph d n
  let o := sctBoxOrigin d n
  let Jg : Sym2 (Option (sctBox d n)) → ℝ :=
    ghostCoupling h beta (fun _ => 1)
  let Zinv := (currentSum (withGhost K) beta Jg ∅)⁻¹ ^ 2
  let dxy := isingDeltaPairSum (withGhost K) beta Jg
    (some o) (some x) (some y) none
  let dyx := isingDeltaPairSum (withGhost K) beta Jg
    (some o) (some y) (some x) none
  let Lxy := isingDeltaLowerMass (withGhost K) beta Jg
    (some o) (some x) (some y) none
  let Lyx := isingDeltaLowerMass (withGhost K) beta Jg
    (some o) (some y) (some x) none
  have hJg : ∀ e : Sym2 (Option (sctBox d n)), 0 ≤ Jg e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b => cases a <;> cases b <;> simp [Jg, ghostCoupling, hh.le]
  have hdxy : 0 ≤ dxy :=
    isingDeltaPairSum_nonneg (withGhost K) beta Jg hbeta.le hJg _ _ _ _
  have hdyx : 0 ≤ dyx :=
    isingDeltaPairSum_nonneg (withGhost K) beta Jg hbeta.le hJg _ _ _ _
  have hbxy : Lxy ≤ sctBoxMag d beta h n y * dxy := by
    have hb := isingDeltaPair_field_bound K beta h hbeta.le hh.le hox hoy hxy
    have hspin : spinProd ({y} : Finset (sctBox d n)) =
        (fun s => spin s y) := by funext s; simp [spinProd]
    rw [hspin] at hb
    simpa [K, o, Jg, dxy, Lxy, sctBoxMag] using hb
  have hbyx : Lyx ≤ sctBoxMag d beta h n x * dyx := by
    have hb := isingDeltaPair_field_bound K beta h hbeta.le hh.le hoy hox hxy.symm
    have hspin : spinProd ({x} : Finset (sctBox d n)) =
        (fun s => spin s x) := by funext s; simp [spinProd]
    rw [hspin] at hb
    simpa [K, o, Jg, dyx, Lyx, sctBoxMag] using hb
  have hc : 0 ≤ sctLatticeC d beta h n :=
    sctLatticeC_nonneg beta h hbeta hh
  have hcx := sctLatticeC_mul_siteMag_le_origin beta h hbeta hh x
  have hcy := sctLatticeC_mul_siteMag_le_origin beta h hbeta hh y
  have hxy' : sctLatticeC d beta h n * Lxy ≤
      sctOriginMag d beta h n * dxy := by
    calc
      sctLatticeC d beta h n * Lxy ≤
          sctLatticeC d beta h n *
            (sctBoxMag d beta h n y * dxy) :=
        mul_le_mul_of_nonneg_left hbxy hc
      _ = (sctLatticeC d beta h n * sctBoxMag d beta h n y) * dxy := by ring
      _ ≤ sctOriginMag d beta h n * dxy :=
        mul_le_mul_of_nonneg_right hcy hdxy
  have hyx' : sctLatticeC d beta h n * Lyx ≤
      sctOriginMag d beta h n * dyx := by
    calc
      sctLatticeC d beta h n * Lyx ≤
          sctLatticeC d beta h n *
            (sctBoxMag d beta h n x * dyx) :=
        mul_le_mul_of_nonneg_left hbyx hc
      _ = (sctLatticeC d beta h n * sctBoxMag d beta h n x) * dyx := by ring
      _ ≤ sctOriginMag d beta h n * dyx :=
        mul_le_mul_of_nonneg_right hcx hdyx
  have hsplit := hcaBondDelta_nonincident_eq_deltaPair_add K beta h hox hoy hxy
  have hsum : sctLatticeC d beta h n * (Lxy + Lyx) ≤
      sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta K beta h o s(x, y) := by
    rw [hsplit]
    calc
      sctLatticeC d beta h n * (Lxy + Lyx) =
          sctLatticeC d beta h n * Lxy +
            sctLatticeC d beta h n * Lyx := by ring
      _ ≤ sctOriginMag d beta h n * dxy +
          sctOriginMag d beta h n * dyx := add_le_add hxy' hyx'
      _ = sctOriginMag d beta h n * (dxy + dyx) := by ring
  have hZ : 0 ≤ Zinv := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hsum hZ
  have hcutxy := sct_normalizedDeltaLowerMass_eq_orientedCutMass
    beta h (x := x) (y := y) hox
  have hcutyx := sct_normalizedDeltaLowerMass_eq_orientedCutMass
    beta h (x := y) (y := x) hoy
  change Zinv * (sctOriginMag d beta h n *
      HcovAssembly.hcaBondDelta K beta h o s(x, y)) ≥ _
  calc
    sctLatticeC d beta h n *
        (sctOrientedCutMass d beta h n x y +
          sctOrientedCutMass d beta h n y x) =
        Zinv * (sctLatticeC d beta h n * (Lxy + Lyx)) := by
      rw [← hcutxy, ← hcutyx]
      dsimp [Zinv, Lxy, Lyx, K, Jg, o]
      ring
    _ ≤ Zinv * (sctOriginMag d beta h n *
          HcovAssembly.hcaBondDelta K beta h o s(x, y)) := hscaled



theorem sct_incidentBondDelta_bound {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) (y : sctBox d n)
    (hoy : sctBoxOrigin d n ≠ y) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      (sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
          (sctBoxOrigin d n) s(sctBoxOrigin d n, y)) ≥
      sctLatticeC d beta h n *
        sctOrientedCutMass d beta h n (sctBoxOrigin d n) y := by
  let K := sctBoxGraph d n
  let o := sctBoxOrigin d n
  let Jg : Sym2 (Option (sctBox d n)) → ℝ :=
    ghostCoupling h beta (fun _ => 1)
  let Zinv := (currentSum (withGhost K) beta Jg ∅)⁻¹ ^ 2
  let L := isingDeltaSelfLowerMass (withGhost K) beta Jg (some o) (some y) none
  have hb : L ≤ sctBoxMag d beta h n y *
      HcovAssembly.hcaBondDelta K beta h o s(o, y) := by
    have hb' := hcaBondDelta_incident_bound K beta h hbeta.le hh.le o y hoy
    have hspin : spinProd ({y} : Finset (sctBox d n)) =
        (fun s => spin s y) := by funext s; simp [spinProd]
    rw [hspin] at hb'
    simpa [K, o, Jg, L, sctBoxMag] using hb'
  have hc : 0 ≤ sctLatticeC d beta h n :=
    sctLatticeC_nonneg beta h hbeta hh
  have hcy := sctLatticeC_mul_siteMag_le_origin beta h hbeta hh y
  have hd : 0 ≤ HcovAssembly.hcaBondDelta K beta h o s(o, y) :=
    HcovAssembly.hcaBondDelta_nonneg K beta h hbeta.le hh.le o s(o, y)
  have hraw : sctLatticeC d beta h n * L ≤
      sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta K beta h o s(o, y) := by
    calc
      sctLatticeC d beta h n * L ≤
          sctLatticeC d beta h n *
            (sctBoxMag d beta h n y *
              HcovAssembly.hcaBondDelta K beta h o s(o, y)) :=
        mul_le_mul_of_nonneg_left hb hc
      _ = (sctLatticeC d beta h n * sctBoxMag d beta h n y) *
          HcovAssembly.hcaBondDelta K beta h o s(o, y) := by ring
      _ ≤ sctOriginMag d beta h n *
          HcovAssembly.hcaBondDelta K beta h o s(o, y) :=
        mul_le_mul_of_nonneg_right hcy hd
  have hscaled := mul_le_mul_of_nonneg_left hraw (sq_nonneg _ : 0 ≤ Zinv)
  have hcut := sct_normalizedDeltaSelfLowerMass_eq_orientedCutMass beta h y
  change Zinv * (sctOriginMag d beta h n *
      HcovAssembly.hcaBondDelta K beta h o s(o, y)) ≥ _
  calc
    sctLatticeC d beta h n *
        sctOrientedCutMass d beta h n o y =
      Zinv * (sctLatticeC d beta h n * L) := by
        rw [← hcut]
        dsimp [Zinv, L, K, Jg, o]
        ring
    _ ≤ Zinv * (sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta K beta h o s(o, y)) := hscaled



noncomputable def sctEdgeCutMass (d : ℕ) (beta h : ℝ) (n : ℕ) :
    Sym2 (sctBox d n) → ℝ :=
  Sym2.lift ⟨fun x y =>
    sctOrientedCutMass d beta h n x y +
      sctOrientedCutMass d beta h n y x, by
    intro x y
    ring⟩

@[simp]
theorem sctEdgeCutMass_mk (d : ℕ) (beta h : ℝ) (n : ℕ)
    (x y : sctBox d n) :
    sctEdgeCutMass d beta h n s(x, y) =
      sctOrientedCutMass d beta h n x y +
        sctOrientedCutMass d beta h n y x := rfl



theorem sctOrientedCutMass_to_origin_zero {d n : ℕ} (beta h : ℝ)
    (x : sctBox d n) :
    sctOrientedCutMass d beta h n x (sctBoxOrigin d n) = 0 := by
  unfold sctOrientedCutMass
  apply Finset.sum_eq_zero
  intro T _
  by_cases ho : sctBoxOrigin d n ∈ T <;> simp [ho]



theorem sct_bondDelta_bound {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) (e : Sym2 (sctBox d n))
    (he : e ∈ (sctBoxGraph d n).edgeFinset) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      (sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
          (sctBoxOrigin d n) e) ≥
      sctLatticeC d beta h n * sctEdgeCutMass d beta h n e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hadj : (sctBoxGraph d n).Adj x y := by
        simpa using (SimpleGraph.mem_edgeFinset.mp he)
      have hxy : x ≠ y := (sctBoxGraph d n).ne_of_adj hadj
      by_cases hox : sctBoxOrigin d n = x
      · subst x
        rw [sctEdgeCutMass_mk, sctOrientedCutMass_to_origin_zero, add_zero]
        exact sct_incidentBondDelta_bound beta h hbeta hh y hxy
      · by_cases hoy : sctBoxOrigin d n = y
        · subst y
          rw [sctEdgeCutMass_mk, sctOrientedCutMass_to_origin_zero, zero_add]
          rw [Sym2.eq_swap]
          exact sct_incidentBondDelta_bound beta h hbeta hh x hxy.symm
        · exact sct_nonincidentBondDelta_bound beta h hbeta hh hox hoy hxy



theorem sct_sum_bondDelta_bound {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      (sctOriginMag d beta h n *
        ∑ e ∈ (sctBoxGraph d n).edgeFinset,
          HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
            (sctBoxOrigin d n) e) ≥
      sctLatticeC d beta h n *
        ∑ e ∈ (sctBoxGraph d n).edgeFinset,
          sctEdgeCutMass d beta h n e := by
  have hs :
      (∑ e ∈ (sctBoxGraph d n).edgeFinset,
        sctLatticeC d beta h n * sctEdgeCutMass d beta h n e) ≤
      ∑ e ∈ (sctBoxGraph d n).edgeFinset,
        (currentSum (withGhost (sctBoxGraph d n)) beta
            (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
          (sctOriginMag d beta h n *
            HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
              (sctBoxOrigin d n) e) := by
    apply Finset.sum_le_sum
    intro e he
    exact sct_bondDelta_bound (d := d) (n := n) beta h hbeta hh e he
  calc
    sctLatticeC d beta h n *
        ∑ e ∈ (sctBoxGraph d n).edgeFinset,
          sctEdgeCutMass d beta h n e =
      ∑ e ∈ (sctBoxGraph d n).edgeFinset,
        sctLatticeC d beta h n * sctEdgeCutMass d beta h n e := by
          rw [Finset.mul_sum]
    _ ≤ ∑ e ∈ (sctBoxGraph d n).edgeFinset,
        (currentSum (withGhost (sctBoxGraph d n)) beta
            (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
          (sctOriginMag d beta h n *
            HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
              (sctBoxOrigin d n) e) := hs
    _ = (currentSum (withGhost (sctBoxGraph d n)) beta
          (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
        (sctOriginMag d beta h n *
          ∑ e ∈ (sctBoxGraph d n).edgeFinset,
            HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
              (sctBoxOrigin d n) e) := by
      rw [Finset.mul_sum, Finset.mul_sum]



noncomputable def sctEdgeBoundaryCorr {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) : Sym2 (sctBox d n) → ℝ :=
  Sym2.lift ⟨fun x y =>
    if x ∈ T ∧ y ∉ T then corrOriginInner d beta (sctCutSites T) x.1
    else if y ∈ T ∧ x ∉ T then corrOriginInner d beta (sctCutSites T) y.1
    else 0, by
      intro x y
      by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp [hx, hy]⟩


noncomputable def sctInternalBoundaryCorr (d : ℕ) (beta : ℝ) (n : ℕ)
    (T : Finset (sctBox d n)) : ℝ :=
  ∑ e ∈ (sctBoxGraph d n).edgeFinset, sctEdgeBoundaryCorr beta T e



theorem sctEdgeCutMass_eq_sum_boundary {d n : ℕ} (beta h : ℝ)
    (e : Sym2 (sctBox d n)) :
    sctEdgeCutMass d beta h n e =
      ∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T then
          sctEdgeBoundaryCorr beta T e * sctCurrentCutMass d beta h n T
        else 0 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [sctEdgeCutMass_mk]
      unfold sctOrientedCutMass
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T _
      by_cases ho : sctBoxOrigin d n ∈ T <;>
        by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;>
        simp [ho, hx, hy, sctEdgeBoundaryCorr] <;> ring



theorem sct_sum_edgeCutMass_eq_sum_internalBoundary {d n : ℕ} (beta h : ℝ) :
    (∑ e ∈ (sctBoxGraph d n).edgeFinset, sctEdgeCutMass d beta h n e) =
      ∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T then
          sctInternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
        else 0 := by
  simp_rw [sctEdgeCutMass_eq_sum_boundary beta h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  by_cases ho : sctBoxOrigin d n ∈ T
  · rw [if_pos ho]
    unfold sctInternalBoundaryCorr
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    rw [if_pos ho]
  · rw [if_neg ho]
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg ho]


theorem sctCutSites_subset_box {d n : ℕ} (T : Finset (sctBox d n)) :
    (sctCutSites T : Set (Site d)) ⊆ box d n := by
  intro z hz
  change z ∈ sctCutSites T at hz
  rw [sctCutSites, Finset.mem_image] at hz
  obtain ⟨x, _, rfl⟩ := hz
  exact x.2



noncomputable def sctBoxize (d n : ℕ) (z : Site d) : sctBox d n :=
  if hz : z ∈ box d n then ⟨z, hz⟩ else sctBoxOrigin d n

@[simp]
theorem sctBoxize_val {d n : ℕ} {z : Site d} (hz : z ∈ box d n) :
    (sctBoxize d n z).1 = z := by
  simp [sctBoxize, hz]


def sctCrossesCut {d n : ℕ} (T : Finset (sctBox d n)) :
    Sym2 (sctBox d n) → Prop :=
  Sym2.lift ⟨fun x y => (x ∈ T ∧ y ∉ T) ∨ (y ∈ T ∧ x ∉ T), by
    intro x y
    apply propext
    tauto⟩

noncomputable instance instDecidableSctCrossesCut {d n : ℕ}
    (T : Finset (sctBox d n)) : DecidablePred (sctCrossesCut T) :=
  Classical.decPred _



theorem sctInternalBoundaryCorr_eq_ambient {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) :
    sctInternalBoundaryCorr d beta n T =
      ∑ e ∈ (boundaryEdges d (sctCutSites T)).filter
          (fun e => e.2 ∈ box d n),
        corrOriginInner d beta (sctCutSites T) e.1 := by
  classical
  let C := (sctBoxGraph d n).edgeFinset.filter (sctCrossesCut T)
  let B := (boundaryEdges d (sctCutSites T)).filter (fun e => e.2 ∈ box d n)
  let i : Site d × Site d → Sym2 (sctBox d n) := fun e =>
    s(sctBoxize d n e.1, sctBoxize d n e.2)
  have hrestrict : sctInternalBoundaryCorr d beta n T =
      ∑ e ∈ C, sctEdgeBoundaryCorr beta T e := by
    unfold sctInternalBoundaryCorr C
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hc : sctCrossesCut T e
    · rw [if_pos hc]
    · rw [if_neg hc]
      induction e using Sym2.inductionOn with
      | _ x y =>
          unfold sctCrossesCut at hc
          simp only [Sym2.lift_mk] at hc
          by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;>
            simp [sctEdgeBoundaryCorr, hx, hy] at hc ⊢
  have hbij :
      (∑ e ∈ B, corrOriginInner d beta (sctCutSites T) e.1) =
        ∑ e ∈ C, sctEdgeBoundaryCorr beta T e := by
    apply Finset.sum_bij (fun e _ => i e)
    · intro e he
      have heB := Finset.mem_filter.mp he
      obtain ⟨_, _, h1S, h2S, _⟩ := boundaryEdges_outer heB.1
      have h1box := sctCutSites_subset_box T h1S
      have h2box := heB.2
      have hxT : sctBoxize d n e.1 ∈ T := by
        apply mem_sctCutSites.mp
        simpa [sctBoxize_val h1box] using h1S
      have hyT : sctBoxize d n e.2 ∉ T := by
        intro hy
        apply h2S
        have := mem_sctCutSites.mpr hy
        simpa [sctBoxize_val h2box] using this
      rw [Finset.mem_filter]
      constructor
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        simpa [sctBoxGraph, SimpleGraph.induce_adj, sctBoxize_val h1box,
          sctBoxize_val h2box] using boundaryEdges_adj heB.1
      · simp [sctCrossesCut, i, hxT, hyT]
    · intro a ha b hb hab
      have haB := (Finset.mem_filter.mp ha).1
      have hbB := (Finset.mem_filter.mp hb).1
      have ha2 := (Finset.mem_filter.mp ha).2
      have hb2 := (Finset.mem_filter.mp hb).2
      obtain ⟨_, _, ha1S, _, _⟩ := boundaryEdges_outer haB
      obtain ⟨_, _, hb1S, _, _⟩ := boundaryEdges_outer hbB
      have ha1box := sctCutSites_subset_box T ha1S
      have hb1box := sctCutSites_subset_box T hb1S
      have hamb : (s(a.1, a.2) : Sym2 (Site d)) = s(b.1, b.2) := by
        have hm := congrArg (Sym2.map (fun z : sctBox d n => z.1)) hab
        simpa [i, sctBoxize_val ha1box, sctBoxize_val ha2,
          sctBoxize_val hb1box, sctBoxize_val hb2] using hm
      exact boundaryEdges_sym2_injOn (sctCutSites T) haB hbB hamb
    · intro e he
      have heC := Finset.mem_filter.mp he
      induction e using Sym2.inductionOn with
      | _ x y =>
          have hadj : (sctBoxGraph d n).Adj x y := by
            simpa using SimpleGraph.mem_edgeFinset.mp heC.1
          have hlat : (hypercubicLattice d).Adj x.1 y.1 := by
            simpa [sctBoxGraph, SimpleGraph.induce_adj] using hadj
          have hcross := heC.2
          change (x ∈ T ∧ y ∉ T) ∨ (y ∈ T ∧ x ∉ T) at hcross
          rcases hcross with hxy | hyx
          · refine ⟨(x.1, y.1), ?_, ?_⟩
            · rw [Finset.mem_filter]
              exact ⟨mem_boundaryEdges_of_adj (sctCutSites T)
                (mem_sctCutSites.mpr hxy.1)
                (fun hy => hxy.2 (mem_sctCutSites.mp hy)) hlat, y.2⟩
            · have hxz : sctBoxize d n x.1 = x :=
                Subtype.ext (sctBoxize_val x.2)
              have hyz : sctBoxize d n y.1 = y :=
                Subtype.ext (sctBoxize_val y.2)
              simp [i, hxz, hyz]
          · refine ⟨(y.1, x.1), ?_, ?_⟩
            · rw [Finset.mem_filter]
              exact ⟨mem_boundaryEdges_of_adj (sctCutSites T)
                (mem_sctCutSites.mpr hyx.1)
                (fun hx => hyx.2 (mem_sctCutSites.mp hx)) hlat.symm, x.2⟩
            · have hxz : sctBoxize d n x.1 = x :=
                Subtype.ext (sctBoxize_val x.2)
              have hyz : sctBoxize d n y.1 = y :=
                Subtype.ext (sctBoxize_val y.2)
              simp [i, hxz, hyz, Sym2.eq_swap]
    · intro e he
      have heB := Finset.mem_filter.mp he
      obtain ⟨_, _, h1S, h2S, _⟩ := boundaryEdges_outer heB.1
      have h1box := sctCutSites_subset_box T h1S
      have h2box := heB.2
      have hxT : sctBoxize d n e.1 ∈ T := by
        apply mem_sctCutSites.mp
        simpa [sctBoxize_val h1box] using h1S
      have hyT : sctBoxize d n e.2 ∉ T := by
        intro hy
        apply h2S
        have := mem_sctCutSites.mpr hy
        simpa [sctBoxize_val h2box] using this
      simp [i, sctEdgeBoundaryCorr, hxT, hyT, sctBoxize_val h1box]
  rw [hrestrict, ← hbij]


noncomputable def sctExternalBoundaryCorr (d : ℕ) (beta : ℝ) (n : ℕ)
    (T : Finset (sctBox d n)) : ℝ :=
  ∑ e ∈ (boundaryEdges d (sctCutSites T)).filter
      (fun e => e.2 ∉ box d n),
    corrOriginInner d beta (sctCutSites T) e.1



theorem sct_boundaryCorr_split {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) :
    (∑ e ∈ boundaryEdges d (sctCutSites T),
      corrOriginInner d beta (sctCutSites T) e.1) =
      sctInternalBoundaryCorr d beta n T +
        sctExternalBoundaryCorr d beta n T := by
  rw [sctInternalBoundaryCorr_eq_ambient]
  unfold sctExternalBoundaryCorr
  rw [← Finset.sum_filter_add_sum_filter_not
    (boundaryEdges d (sctCutSites T)) (fun e => e.2 ∈ box d n)]



theorem sct_phiIsing_eq_tanh_mul_boundaryCorr {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) :
    phiIsing d beta (sctCutSites T) =
      Real.tanh beta *
        ∑ e ∈ boundaryEdges d (sctCutSites T),
          corrOriginInner d beta (sctCutSites T) e.1 := by
  rfl



theorem tanh_le_self_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    Real.tanh beta ≤ beta := by
  let f : ℝ → ℝ := fun x => x * Real.cosh x - Real.sinh x
  have hfderiv : ∀ x : ℝ, deriv f x = x * Real.sinh x := by
    intro x
    have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x)
    simpa [f] using hd.deriv
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    · exact ((continuous_id.mul Real.continuous_cosh).sub
        Real.continuous_sinh).continuousOn
    · exact ((differentiable_id.mul Real.differentiable_cosh).sub
        Real.differentiable_sinh).differentiableOn
    · intro x hx
      rw [interior_Ici] at hx
      rw [hfderiv]
      exact mul_nonneg (le_of_lt hx) (Real.sinh_nonneg_iff.mpr (le_of_lt hx))
  have hf := hmono (by simp) hbeta hbeta
  have hgap : Real.sinh beta ≤ beta * Real.cosh beta := by
    simpa [f] using hf
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos beta)]
  exact hgap


theorem sct_sum_currentCutMass {d n : ℕ} (beta h : ℝ) :
    (∑ T : Finset (sctBox d n),
      if sctBoxOrigin d n ∈ T then sctCurrentCutMass d beta h n T else 0) =
      1 - (sctOriginMag d beta h n) ^ 2 := by
  have hs := sum_baseCutMass_eq_one_sub_mag_sq
    (sctBoxGraph d n) beta h (sctBoxOrigin d n)
  have hspin : spinProd ({sctBoxOrigin d n} : Finset (sctBox d n)) =
      (fun s => spin s (sctBoxOrigin d n)) := by
    funext s
    simp [spinProd]
  rw [hspin] at hs
  simpa [sctCurrentCutMass, sctOriginMag, sctBoxMag] using hs


noncomputable def sctCurrentBoundaryError (d : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  ∑ T : Finset (sctBox d n),
    if sctBoxOrigin d n ∈ T then
      sctExternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
    else 0




theorem sct_internalBoundaryMass_lower {d n : ℕ} (beta h infphi : ℝ)
    (hbeta : 0 < beta) (hh : 0 ≤ h)
    (hinf : ∀ S : Finset (Site d), origin d ∈ S → infphi ≤ phiIsing d beta S) :
    (∑ T : Finset (sctBox d n),
      if sctBoxOrigin d n ∈ T then
        sctInternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
      else 0) ≥
      (1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
        sctCurrentBoundaryError d beta h n := by
  have hJ : ∀ e : Sym2 (Option (sctBox d n)),
      0 ≤ ghostCoupling h beta (fun _ => 1) e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b => cases a <;> cases b <;> simp [ghostCoupling, hh]
  have hmass (T : Finset (sctBox d n)) : 0 ≤ sctCurrentCutMass d beta h n T :=
    isingCutMass_nonneg (withGhost (sctBoxGraph d n)) beta
      (ghostCoupling h beta (fun _ => 1)) hbeta.le hJ none (T.map someEmb)
  let full : Finset (sctBox d n) → ℝ := fun T =>
    ∑ e ∈ boundaryEdges d (sctCutSites T),
      corrOriginInner d beta (sctCutSites T) e.1
  have hfull (T : Finset (sctBox d n)) (ho : sctBoxOrigin d n ∈ T) :
      (1 / beta) * infphi ≤ full T := by
    have hoS : origin d ∈ sctCutSites T := by
      exact Finset.mem_image.mpr ⟨sctBoxOrigin d n, ho, rfl⟩
    have hi := hinf (sctCutSites T) hoS
    have hphi : phiIsing d beta (sctCutSites T) = Real.tanh beta * full T := rfl
    have hcorr : 0 ≤ full T := by
      apply Finset.sum_nonneg
      intro e _
      exact corrOriginInner_nonneg d hbeta.le (sctCutSites T) e.1
    have htanh := tanh_le_self_of_nonneg hbeta.le
    have hupper : phiIsing d beta (sctCutSites T) ≤ beta * full T := by
      rw [hphi]
      exact mul_le_mul_of_nonneg_right htanh hcorr
    have : infphi ≤ beta * full T := hi.trans hupper
    calc
      (1 / beta) * infphi = infphi / beta := by ring
      _ ≤ full T := (div_le_iff₀ hbeta).2 (by simpa [mul_comm] using this)
  have hweighted :
      (1 / beta) * infphi *
          (∑ T : Finset (sctBox d n),
            if sctBoxOrigin d n ∈ T then sctCurrentCutMass d beta h n T else 0) ≤
        ∑ T : Finset (sctBox d n),
          if sctBoxOrigin d n ∈ T then full T * sctCurrentCutMass d beta h n T
          else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro T _
    by_cases ho : sctBoxOrigin d n ∈ T
    · rw [if_pos ho, if_pos ho]
      exact mul_le_mul_of_nonneg_right (hfull T ho) (hmass T)
    · simp [ho]
  rw [sct_sum_currentCutMass] at hweighted
  unfold sctCurrentBoundaryError
  calc
    (1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          (∑ T : Finset (sctBox d n),
            if sctBoxOrigin d n ∈ T then
              sctExternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
            else 0) =
        ((1 / beta) * infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          (∑ T : Finset (sctBox d n),
            if sctBoxOrigin d n ∈ T then
              sctExternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
            else 0) := by ring
    _ ≤ (∑ T : Finset (sctBox d n),
          if sctBoxOrigin d n ∈ T then full T * sctCurrentCutMass d beta h n T
          else 0) -
        (∑ T : Finset (sctBox d n),
          if sctBoxOrigin d n ∈ T then
            sctExternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
          else 0) := sub_le_sub_right hweighted _
    _ = ∑ T : Finset (sctBox d n),
          if sctBoxOrigin d n ∈ T then
            sctInternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
          else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro T _
      by_cases ho : sctBoxOrigin d n ∈ T
      · rw [if_pos ho, if_pos ho, if_pos ho]
        dsimp [full]
        rw [sct_boundaryCorr_split beta T]
        ring
      · simp [ho]





theorem sct_finite_meanfield_inequality {d n : ℕ} (beta h infphi : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h)
    (hinf : ∀ S : Finset (Site d), origin d ∈ S → infphi ≤ phiIsing d beta S) :
    deriv (fun b => (sctOriginMag d b h n) ^ 2) beta ≥
      2 * sctLatticeC d beta h n *
        ((1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          sctCurrentBoundaryError d beta h n) := by
  let K := sctBoxGraph d n
  let o := sctBoxOrigin d n
  let Jg : Sym2 (Option (sctBox d n)) → ℝ :=
    ghostCoupling h beta (fun _ => 1)
  let Zinv := (currentSum (withGhost K) beta Jg ∅)⁻¹ ^ 2
  let bondSum := ∑ e ∈ K.edgeFinset,
    HcovAssembly.hcaBondDelta K beta h o e
  let fieldSum := ∑ z,
    HcovAssembly.hcaFieldDelta K beta h o z
  have hd := HcovAssembly.hca_deriv_magnetization_eq_currentDelta K beta h o
  change HasDerivAt (fun b => sctOriginMag d b h n)
    ((1 / (currentSum (withGhost K) beta Jg ∅) ^ 2) *
      (bondSum + h * fieldSum)) beta at hd
  have hd2 := hd.pow 2
  have hderiv : deriv (fun b => (sctOriginMag d b h n) ^ 2) beta =
      2 * sctOriginMag d beta h n * Zinv * (bondSum + h * fieldSum) := by
    change deriv ((fun b => sctOriginMag d b h n) ^ 2) beta = _
    rw [hd2.deriv]
    dsimp [Zinv]
    have hZ : currentSum (withGhost K) beta Jg ∅ ≠ 0 :=
      ne_of_gt (Ising.acr_currentSum_empty_pos (withGhost K) beta Jg)
    field_simp
  have hfield : 0 ≤ fieldSum := by
    unfold fieldSum
    apply Finset.sum_nonneg
    intro z _
    exact HcovAssembly.hcaFieldDelta_nonneg K beta h hbeta.le hh.le o z
  have hm : 0 ≤ sctOriginMag d beta h n :=
    (sctOriginMag_pos d beta h hbeta hh n).le
  have hZinv : 0 ≤ Zinv := sq_nonneg _
  have hdrop :
      2 * sctOriginMag d beta h n * Zinv * bondSum ≤
        2 * sctOriginMag d beta h n * Zinv * (bondSum + h * fieldSum) := by
    have hext : 0 ≤ h * fieldSum := mul_nonneg hh.le hfield
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hext)
      (mul_nonneg (mul_nonneg (by norm_num) hm) hZinv)
  have hbond := sct_sum_bondDelta_bound (d := d) (n := n) beta h hbeta hh
  have hedge :
      sctLatticeC d beta h n *
          (∑ e ∈ K.edgeFinset, sctEdgeCutMass d beta h n e) ≤
        Zinv * (sctOriginMag d beta h n * bondSum) := by
    simpa [K, o, Jg, Zinv, bondSum] using hbond
  have hreassemble := sct_sum_edgeCutMass_eq_sum_internalBoundary
    (d := d) (n := n) beta h
  have hmain := sct_internalBoundaryMass_lower
    (d := d) (n := n) beta h infphi hbeta hh.le hinf
  have hc : 0 ≤ sctLatticeC d beta h n :=
    sctLatticeC_nonneg beta h hbeta hh
  have hmainc := mul_le_mul_of_nonneg_left hmain hc
  rw [← hreassemble] at hmainc
  rw [hderiv]
  calc
    2 * sctLatticeC d beta h n *
        ((1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          sctCurrentBoundaryError d beta h n) =
      2 * (sctLatticeC d beta h n *
        ((1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          sctCurrentBoundaryError d beta h n)) := by ring
    _ ≤ 2 * (sctLatticeC d beta h n *
        ∑ e ∈ K.edgeFinset, sctEdgeCutMass d beta h n e) :=
      mul_le_mul_of_nonneg_left hmainc (by norm_num)
    _ ≤ 2 * (Zinv * (sctOriginMag d beta h n * bondSum)) :=
      mul_le_mul_of_nonneg_left hedge (by norm_num)
    _ = 2 * sctOriginMag d beta h n * Zinv * bondSum := by ring
    _ ≤ 2 * sctOriginMag d beta h n * Zinv * (bondSum + h * fieldSum) := hdrop





noncomputable def sctExternalBoxPairs (d n : ℕ) :
    Finset (sctBox d n × Site d) :=
  (Finset.univ : Finset (sctBox d n)).biUnion fun x =>
    (sctExteriorNeighbours d n x.1).image fun y => (x, y)

theorem mem_sctExternalBoxPairs {d n : ℕ} {p : sctBox d n × Site d} :
    p ∈ sctExternalBoxPairs d n ↔ p.2 ∈ sctExteriorNeighbours d n p.1.1 := by
  classical
  constructor
  · intro hp
    rw [sctExternalBoxPairs, Finset.mem_biUnion] at hp
    obtain ⟨x, _, hp⟩ := hp
    rw [Finset.mem_image] at hp
    obtain ⟨y, hy, hyp⟩ := hp
    rw [← hyp]
    exact hy
  · intro hp
    rw [sctExternalBoxPairs, Finset.mem_biUnion]
    refine ⟨p.1, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨p.2, hp, rfl⟩



theorem sctExternalBoundaryCorr_eq_sum_vertices {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) :
    sctExternalBoundaryCorr d beta n T =
      ∑ x : sctBox d n,
        if x ∈ T then
          ((sctExteriorNeighbours d n x.1).card : ℝ) *
            corrOriginInner d beta (sctCutSites T) x.1
        else 0 := by
  classical
  let B := (boundaryEdges d (sctCutSites T)).filter (fun e => e.2 ∉ box d n)
  let P := (sctExternalBoxPairs d n).filter (fun p => p.1 ∈ T)
  let i : Site d × Site d → sctBox d n × Site d := fun e =>
    (sctBoxize d n e.1, e.2)
  have hbij :
      (∑ e ∈ B, corrOriginInner d beta (sctCutSites T) e.1) =
        ∑ p ∈ P, corrOriginInner d beta (sctCutSites T) p.1.1 := by
    apply Finset.sum_bij (fun e _ => i e)
    · intro e he
      have heB := Finset.mem_filter.mp he
      obtain ⟨_, _, h1S, h2S, _⟩ := boundaryEdges_outer heB.1
      have h1box := sctCutSites_subset_box T h1S
      have hxT : sctBoxize d n e.1 ∈ T := by
        apply mem_sctCutSites.mp
        simpa [sctBoxize_val h1box] using h1S
      rw [Finset.mem_filter]
      refine ⟨?_, hxT⟩
      rw [mem_sctExternalBoxPairs]
      rw [sctExteriorNeighbours, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      constructor
      · simpa [i, sctBoxize_val h1box] using boundaryEdges_adj heB.1
      · exact heB.2
    · intro a ha b hb hab
      have haB := (Finset.mem_filter.mp ha).1
      have hbB := (Finset.mem_filter.mp hb).1
      obtain ⟨_, _, ha1S, _, _⟩ := boundaryEdges_outer haB
      obtain ⟨_, _, hb1S, _, _⟩ := boundaryEdges_outer hbB
      have ha1box := sctCutSites_subset_box T ha1S
      have hb1box := sctCutSites_subset_box T hb1S
      apply Prod.ext
      · have hv := congrArg (fun p : sctBox d n × Site d => p.1.1) hab
        simpa [i, sctBoxize_val ha1box, sctBoxize_val hb1box] using hv
      · exact congrArg (fun p : sctBox d n × Site d => p.2) hab
    · intro p hp
      have hpP := Finset.mem_filter.mp hp
      have hpExt := mem_sctExternalBoxPairs.mp hpP.1
      have hadj : (hypercubicLattice d).Adj p.1.1 p.2 := by
        rw [sctExteriorNeighbours, Finset.mem_filter,
          SimpleGraph.mem_neighborFinset] at hpExt
        exact hpExt.1
      have hybox : p.2 ∉ box d n := by
        rw [sctExteriorNeighbours, Finset.mem_filter] at hpExt
        exact hpExt.2
      have hyS : p.2 ∉ sctCutSites T := fun hy =>
        hybox (sctCutSites_subset_box T hy)
      refine ⟨(p.1.1, p.2), ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨mem_boundaryEdges_of_adj (sctCutSites T)
          (mem_sctCutSites.mpr hpP.2) hyS hadj, hybox⟩
      · have hpboxize : sctBoxize d n p.1.1 = p.1 :=
          Subtype.ext (sctBoxize_val p.1.2)
        simp [i, hpboxize]
    · intro e he
      have heB := Finset.mem_filter.mp he
      obtain ⟨_, _, h1S, _, _⟩ := boundaryEdges_outer heB.1
      have h1box := sctCutSites_subset_box T h1S
      simp [i, sctBoxize_val h1box]
  have hpairwise : ((Finset.univ : Finset (sctBox d n)) : Set (sctBox d n)).PairwiseDisjoint
      (fun x => (sctExteriorNeighbours d n x.1).image fun y => (x, y)) := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpx hpy
    rw [Finset.mem_image] at hpx hpy
    obtain ⟨_, _, rfl⟩ := hpx
    obtain ⟨_, _, hp⟩ := hpy
    exact hxy (congrArg (fun p : sctBox d n × Site d => p.1) hp).symm
  have hregroup :
      (∑ p ∈ P, corrOriginInner d beta (sctCutSites T) p.1.1) =
        ∑ x : sctBox d n,
          if x ∈ T then
            ((sctExteriorNeighbours d n x.1).card : ℝ) *
              corrOriginInner d beta (sctCutSites T) x.1
          else 0 := by
    unfold P sctExternalBoxPairs
    rw [Finset.sum_filter]
    rw [Finset.sum_biUnion hpairwise]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ T
    · rw [if_pos hx]
      rw [Finset.sum_image]
      · simp [hx]
      · intro a _ b _ hab
        exact congrArg (fun p : sctBox d n × Site d => p.2) hab
    · rw [if_neg hx]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨y, _, rfl⟩ := hp
      simp [hx]
  unfold sctExternalBoundaryCorr
  change (∑ e ∈ B, corrOriginInner d beta (sctCutSites T) e.1) = _
  rw [hbij, hregroup]



theorem sct_sum_cutCorr_eq_covariance {d n : ℕ} (beta h : ℝ)
    (x : sctBox d n) (hox : sctBoxOrigin d n ≠ x) :
    (∑ T : Finset (sctBox d n),
      if sctBoxOrigin d n ∈ T ∧ x ∈ T then
        corrOriginInner d beta (sctCutSites T) x.1 *
          sctCurrentCutMass d beta h n T
      else 0) =
      sctBoxCovariance d beta h n x := by
  have hc := sum_localCorr_baseCutMass_eq_fieldCovariance
    (sctBoxGraph d n) beta h hox
  have hlhs :
      (∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T ∧ x ∈ T then
          expectationJ (sctBoxGraph d n) beta
              (couplingIn (fun _ => 1) T) {sctBoxOrigin d n, x} *
            sctCurrentCutMass d beta h n T
        else 0) =
      ∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T ∧ x ∈ T then
          corrOriginInner d beta (sctCutSites T) x.1 *
            sctCurrentCutMass d beta h n T
        else 0 := by
    apply Finset.sum_congr rfl
    intro T _
    by_cases ho : sctBoxOrigin d n ∈ T <;> by_cases hx : x ∈ T
    · rw [if_pos ⟨ho, hx⟩, if_pos ⟨ho, hx⟩,
        sct_localCorr_eq_corrOriginInner beta T ho hx hox]
    · simp [ho, hx]
    · simp [ho, hx]
    · simp [ho, hx]
  rw [← hlhs]
  unfold sctCurrentCutMass
  rw [hc]
  unfold sctBoxCovariance sctOriginMag sctBoxMag
  have hpair : spinProd ({sctBoxOrigin d n, x} : Finset (sctBox d n)) =
      (fun s => spin s (sctBoxOrigin d n) * spin s x) := by
    funext s
    rw [spinProd, Finset.prod_pair hox]
  have hoSpin : spinProd ({sctBoxOrigin d n} : Finset (sctBox d n)) =
      (fun s => spin s (sctBoxOrigin d n)) := by funext s; simp [spinProd]
  have hxSpin : spinProd ({x} : Finset (sctBox d n)) =
      (fun s => spin s x) := by funext s; simp [spinProd]
  rw [hpair, hoSpin, hxSpin]



theorem sctCurrentBoundaryError_eq_boundaryCovarianceError
    {d n : ℕ} (beta h : ℝ) (hn : 1 ≤ n) :
    sctCurrentBoundaryError d beta h n =
      sctBoundaryCovarianceError d beta h n := by
  unfold sctCurrentBoundaryError
  simp_rw [sctExternalBoundaryCorr_eq_sum_vertices beta]
  have hexpand :
      (∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T then
          (∑ x : sctBox d n,
            if x ∈ T then
              ((sctExteriorNeighbours d n x.1).card : ℝ) *
                corrOriginInner d beta (sctCutSites T) x.1
            else 0) * sctCurrentCutMass d beta h n T
        else 0) =
      ∑ T : Finset (sctBox d n), ∑ x : sctBox d n,
        if sctBoxOrigin d n ∈ T ∧ x ∈ T then
          ((sctExteriorNeighbours d n x.1).card : ℝ) *
            (corrOriginInner d beta (sctCutSites T) x.1 *
              sctCurrentCutMass d beta h n T)
        else 0 := by
    apply Finset.sum_congr rfl
    intro T _
    by_cases ho : sctBoxOrigin d n ∈ T
    · rw [if_pos ho, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ T <;> simp [ho, hx] <;> ring
    · rw [if_neg ho]
      symm
      apply Finset.sum_eq_zero
      intro x _
      simp [ho]
  rw [hexpand, Finset.sum_comm]
  unfold sctBoundaryCovarianceError
  apply Finset.sum_congr rfl
  intro x _
  by_cases hox : sctBoxOrigin d n = x
  · subst x
    have horigin : (sctBoxOrigin d n).1 ∈ box d (n - 1) := by
      intro i
      simp [sctBoxOrigin]
    rw [sctExteriorNeighbours_eq_empty_of_mem_pred hn horigin]
    simp
  · calc
      (∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T ∧ x ∈ T then
          ((sctExteriorNeighbours d n x.1).card : ℝ) *
            (corrOriginInner d beta (sctCutSites T) x.1 *
              sctCurrentCutMass d beta h n T)
        else 0) =
          ((sctExteriorNeighbours d n x.1).card : ℝ) *
            ∑ T : Finset (sctBox d n),
              if sctBoxOrigin d n ∈ T ∧ x ∈ T then
                corrOriginInner d beta (sctCutSites T) x.1 *
                  sctCurrentCutMass d beta h n T
              else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        by_cases ho : sctBoxOrigin d n ∈ T <;> by_cases hx : x ∈ T <;>
          simp [ho, hx] <;> ring
      _ = ((sctExteriorNeighbours d n x.1).card : ℝ) *
          sctBoxCovariance d beta h n x := by
        rw [sct_sum_cutCorr_eq_covariance beta h x hox]





theorem sct_finite_meanfield_inequality_concrete {d n : ℕ}
    (beta h infphi : ℝ) (hn : 1 ≤ n)
    (hbeta : 0 < beta) (hh : 0 < h)
    (hinf : ∀ S : Finset (Site d), origin d ∈ S →
      infphi ≤ phiIsing d beta S) :
    deriv (fun b => (sctOriginMag d b h n) ^ 2) beta ≥
      2 * sctLatticeC d beta h n *
        ((1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          sctBoundaryCovarianceError d beta h n) := by
  rw [← sctCurrentBoundaryError_eq_boundaryCovarianceError beta h hn]
  exact sct_finite_meanfield_inequality beta h infphi hbeta hh hinf

end Sharpness
end StatMech
