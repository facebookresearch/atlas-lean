/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.Universality.HexLiteralHWDepth
import Code.Universality.HexTaggedColumnBound
import Code.Universality.HexCorrectedStripColumn
import Code.Universality.HexContentHalfBound

namespace StatMech.Universality

open HexWalk
open scoped BigOperators

noncomputable section



structure HLHDBridgeOrigin (b : HexBridge) where
  turns : List ℤ
  legal : (ofTurns hexAWStart 1 turns).IsLegalSAW
  halfSpace : HLHDLiteralHalfSpace turns legal
  interval : ℕ × ℕ
  interval_mem : interval ∈ hlhd_intervals turns legal
  bridge_eq : b = hlhd_bridge turns legal halfSpace
    ⟨interval, interval_mem⟩

theorem hlhdt_bridge_eq_of_width_content {b c : HexBridge}
    (hwidth : b.width = c.width) (hcontent : b.content = c.content) :
    b = c := by
  rcases b with ⟨bw, hbpos, bc, hbc⟩
  rcases c with ⟨cw, hcpos, cc, hcc⟩
  simp only at hwidth hcontent
  subst cw
  subst cc
  rfl

theorem HLHDBridgeOrigin.width_eq {b : HexBridge}
    (o : HLHDBridgeOrigin b) :
    b.width = hlhd_width o.turns o.legal o.interval := by
  have h := congrArg HexBridge.width o.bridge_eq
  simpa [hlhd_bridge] using h

theorem HLHDBridgeOrigin.content_eq {b : HexBridge}
    (o : HLHDBridgeOrigin b) :
    b.content = hlhd_intervalRaw o.turns o.interval := by
  have h := congrArg HexBridge.content o.bridge_eq
  simpa [hlhd_bridge, hlhd_intervalRaw] using h

theorem hlhdt_contentHalf_bridge_origin (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    {b : HexBridge} (hb : b ∈ (hlhd_contentHalf ts hleg hhalf).1) :
    Nonempty (HLHDBridgeOrigin b) := by
  change b ∈ hlhd_bridgeList ts hleg hhalf at hb
  unfold hlhd_bridgeList at hb
  rw [List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  exact ⟨{
    turns := ts
    legal := hleg
    halfSpace := hhalf
    interval := p.1
    interval_mem := p.2
    bridge_eq := rfl
  }⟩

noncomputable def hlhdt_contentHalfImage
    (D : Type*) [Fintype D]
    (turns : D → List ℤ)
    (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
    (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d)) :
    Finset HexHWContentHalf := by
  classical
  exact Finset.univ.image (fun d =>
    hlhd_contentHalf (turns d) (legal d) (halfSpace d))

theorem hlhdt_contentHalfImage_origin
    (D : Type*) [Fintype D]
    (turns : D → List ℤ)
    (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
    (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
    (b : HexBridge)
    (hb : b ∈ hchb_bridges
      (hlhdt_contentHalfImage D turns legal halfSpace)) :
    Nonempty (HLHDBridgeOrigin b) := by
  classical
  unfold hchb_bridges at hb
  rw [Finset.mem_biUnion] at hb
  obtain ⟨s, hs, hbs⟩ := hb
  unfold hlhdt_contentHalfImage at hs
  rw [Finset.mem_image] at hs
  obtain ⟨d, _, rfl⟩ := hs
  exact hlhdt_contentHalf_bridge_origin (turns d) (legal d)
    (halfSpace d) (List.mem_toFinset.mp hbs)



noncomputable def hlhdt_originCode {b : HexBridge}
    (o : HLHDBridgeOrigin b) (T : ℕ) (hT : 0 < T)
    (hbT : b.width = T) :
    HLHDColumnTag ×
      {ws : List ℤ // HexCSTopWalkAtWidth T hT ws} :=
  let hwidth : hlhd_width o.turns o.legal o.interval = T :=
    o.width_eq.symm.trans hbT
  (hlhd_intervalTag o.turns o.legal o.halfSpace
      o.interval o.interval_mem,
    ⟨hlhd_intervalEndpoint o.turns o.legal o.halfSpace
        o.interval o.interval_mem,
      by
        have hmem := hlhd_intervalEndpoint_mem_topAtWidth
          o.turns o.legal o.halfSpace o.interval o.interval_mem
        simpa only [hwidth] using hmem⟩)

theorem hlhdt_originCode_decode {b : HexBridge}
    (o : HLHDBridgeOrigin b) (T : ℕ) (hT : 0 < T)
    (hbT : b.width = T) :
    hlhd_decodeColumn (hlhdt_originCode o T hT hbT).1
        (hlhdt_originCode o T hT hbT).2.1 = b.content := by
  rw [hlhdt_originCode]
  exact (hlhd_interval_decode o.turns o.legal o.halfSpace
    o.interval o.interval_mem).trans o.content_eq.symm

noncomputable def hlhdt_widthFiber
    (S : Finset HexHWContentHalf) (T : ℕ) : Finset HexBridge :=
  (hchb_bridges S).filter (fun b => b.width = T)

noncomputable def hlhdt_pickOrigin
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (b : {b // b ∈ hlhdt_widthFiber S T}) :
    HLHDBridgeOrigin b.1 :=
  Classical.choice (horigin b.1 (Finset.mem_filter.mp b.2).1)

noncomputable def hlhdt_fiberCode
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T)
    (b : {b // b ∈ hlhdt_widthFiber S T}) :
    HLHDColumnTag ×
      {ws : List ℤ // HexCSTopWalkAtWidth T hT ws} :=
  hlhdt_originCode (hlhdt_pickOrigin S horigin T b) T hT
    (Finset.mem_filter.mp b.2).2

theorem hlhdt_fiberCode_decode
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T)
    (b : {b // b ∈ hlhdt_widthFiber S T}) :
    hlhd_decodeColumn (hlhdt_fiberCode S horigin T hT b).1
        (hlhdt_fiberCode S horigin T hT b).2.1 = b.1.content :=
  hlhdt_originCode_decode (hlhdt_pickOrigin S horigin T b) T hT
    (Finset.mem_filter.mp b.2).2

theorem hlhdt_fiberCode_injective
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T) :
    Function.Injective (hlhdt_fiberCode S horigin T hT) := by
  intro b c hcode
  have hcontent := congrArg
    (fun code => hlhd_decodeColumn code.1 code.2.1) hcode
  change hlhd_decodeColumn (hlhdt_fiberCode S horigin T hT b).1
      (hlhdt_fiberCode S horigin T hT b).2.1 =
    hlhd_decodeColumn (hlhdt_fiberCode S horigin T hT c).1
      (hlhdt_fiberCode S horigin T hT c).2.1 at hcontent
  rw [hlhdt_fiberCode_decode S horigin T hT b,
    hlhdt_fiberCode_decode S horigin T hT c] at hcontent
  apply Subtype.ext
  apply hlhdt_bridge_eq_of_width_content
  · exact (Finset.mem_filter.mp b.2).2.trans
      (Finset.mem_filter.mp c.2).2.symm
  · exact hcontent

theorem hlhdt_fiber_raw_weight_le
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T) {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1)
    (b : {b // b ∈ hlhdt_widthFiber S T}) :
    hhc_bridgeWeight x b.1 ≤
      x⁻¹ * x ^ (hlhdt_fiberCode S horigin T hT b).2.1.length := by
  let o := hlhdt_pickOrigin S horigin T b
  have hpow := raw_pow_le_inv_mul_endpoint_pow hx hxone
    (hlhd_intervalRaw o.turns o.interval).length
    (hlhd_intervalEndpoint o.turns o.legal o.halfSpace
      o.interval o.interval_mem).length
    (hlhd_intervalEndpoint_length o.turns o.legal o.halfSpace
      o.interval o.interval_mem)
  have hcontent : b.1.content = hlhd_intervalRaw o.turns o.interval :=
    o.content_eq
  simpa only [hhc_bridgeWeight, hcontent, hlhdt_fiberCode,
    hlhdt_originCode, o] using hpow



theorem hlhdt_bridgeMass_le_eight_inv_colSum
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T) {x : ℝ}
    (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x ≤ hexChiE)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
    hchb_bridgeMass S x T ≤
      8 * x⁻¹ * (hexCSTopColumn T hT hlocal hwindow).colSum x := by
  classical
  let F := hlhdt_widthFiber S T
  let C := hexCSTopColumn T hT hlocal hwindow
  have hcolsum : Summable
      (fun w : {ws : List ℤ // HexCSTopWalkAtWidth T hT ws} =>
        x ^ w.1.length) := by
    have hs := C.colSum_summable (le_of_lt hx) hexChiE_pos hxchi
    simpa only [C, hexCSTopColumn, HexWalk.endpointNumVertices_eq,
      ofTurns_turns] using hs
  have hbound := finiteTagged_sum_le_card_mul_tsum
    (Finset.univ : Finset {b // b ∈ F})
    (hlhdt_fiberCode S horigin T hT)
    (hlhdt_fiberCode_injective S horigin T hT).injOn
    (fun b => hhc_bridgeWeight x b.1)
    (fun w : {ws : List ℤ // HexCSTopWalkAtWidth T hT ws} =>
      x ^ w.1.length)
    x⁻¹ (inv_nonneg.mpr (le_of_lt hx))
    (fun w => pow_nonneg (le_of_lt hx) _)
    hcolsum
    (fun b _ => hlhdt_fiber_raw_weight_le
      S horigin T hT hx hxone b)
  have hcol :
      (∑' w : {ws : List ℤ // HexCSTopWalkAtWidth T hT ws},
          x ^ w.1.length) = C.colSum x := by
    rw [hexCSTopColumn_colSum]
    simp only [HexWalk.endpointNumVertices_eq, ofTurns_turns]
  calc
    hchb_bridgeMass S x T =
        ∑ b : {b // b ∈ F}, hhc_bridgeWeight x b.1 := by
      unfold hchb_bridgeMass
      rw [← Finset.sum_attach, Finset.attach_eq_univ]
      rfl
    _ ≤ x⁻¹ * Fintype.card HLHDColumnTag *
          ∑' w : {ws : List ℤ // HexCSTopWalkAtWidth T hT ws},
            x ^ w.1.length := hbound
    _ = 8 * x⁻¹ * C.colSum x := by
      rw [hlhd_columnTag_card, hcol]
      ring

theorem hlhdt_bridgeMass_le_eight_inv_pow
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T) {x : ℝ}
    (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x ≤ hexChiE)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
    hchb_bridgeMass S x T ≤ 8 * x⁻¹ * (x / hexChiE) ^ T := by
  let C := hexCSTopColumn T hT hlocal hwindow
  calc
    hchb_bridgeMass S x T ≤ 8 * x⁻¹ * C.colSum x :=
      hlhdt_bridgeMass_le_eight_inv_colSum S horigin T hT hx hxone
        hxchi hlocal hwindow
    _ ≤ 8 * x⁻¹ * (x / hexChiE) ^ T := by
      apply mul_le_mul_of_nonneg_left
      · exact C.colSum_le_pow (le_of_lt hx) hexChiE_pos hxchi
      · positivity

theorem hlhdt_contentHalfImage_bridgeMass_le
    (D : Type*) [Fintype D]
    (turns : D → List ℤ)
    (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
    (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
    (T : ℕ) (hT : 0 < T) {x : ℝ}
    (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x ≤ hexChiE)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
    hchb_bridgeMass (hlhdt_contentHalfImage D turns legal halfSpace) x T ≤
      8 * x⁻¹ * (x / hexChiE) ^ T := by
  exact hlhdt_bridgeMass_le_eight_inv_pow
    (hlhdt_contentHalfImage D turns legal halfSpace)
    (hlhdt_contentHalfImage_origin D turns legal halfSpace)
    T hT hx hxone hxchi hlocal hwindow

def hlhdt_taggedMajorant (x : ℝ) (T : ℕ) : ℝ :=
  if T = 0 then 0 else 8 * x⁻¹ * (x / hexChiE) ^ T

theorem hlhdt_taggedMajorant_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ∀ T, 0 ≤ hlhdt_taggedMajorant x T := by
  intro T
  unfold hlhdt_taggedMajorant
  split
  · exact le_rfl
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr hx))
      (pow_nonneg (div_nonneg hx hexChiE_pos.le) _)

theorem hlhdt_taggedMajorant_summable {x : ℝ}
    (hx : 0 < x) (hxchi : x < hexChiE) :
    Summable (hlhdt_taggedMajorant x) := by
  let r := x / hexChiE
  let K := 8 * x⁻¹
  have hr0 : 0 ≤ r := div_nonneg hx.le hexChiE_pos.le
  have hr1 : r < 1 := (div_lt_one hexChiE_pos).2 hxchi
  have hK : 0 ≤ K := by positivity
  have hgeom : Summable (fun T : ℕ => K * r ^ T) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left K
  apply hgeom.of_nonneg_of_le (hlhdt_taggedMajorant_nonneg hx.le)
  intro T
  unfold hlhdt_taggedMajorant
  split
  · exact mul_nonneg hK (pow_nonneg hr0 _)
  · rfl

theorem hlhdt_bridgeMass_zero
    (S : Finset HexHWContentHalf) (x : ℝ) :
    hchb_bridgeMass S x 0 = 0 := by
  unfold hchb_bridgeMass
  apply Finset.sum_eq_zero
  intro b hb
  simp only [Finset.mem_filter] at hb
  exact (Nat.ne_of_gt b.width_pos hb.2).elim

theorem hlhdt_contentHalfImage_bridgeMass_le_majorant
    (D : Type*) [Fintype D]
    (turns : D → List ℤ)
    (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
    (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
    {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x ≤ hexChiE)
    (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
    (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
    ∀ T,
      hchb_bridgeMass (hlhdt_contentHalfImage D turns legal halfSpace) x T ≤
        hlhdt_taggedMajorant x T := by
  intro T
  cases T with
  | zero =>
      rw [hlhdt_bridgeMass_zero]
      simp [hlhdt_taggedMajorant]
  | succ T =>
      have hT : 0 < T + 1 := by omega
      rw [hlhdt_taggedMajorant, if_neg (Nat.ne_of_gt hT)]
      exact hlhdt_contentHalfImage_bridgeMass_le D turns legal halfSpace
        (T + 1) hT hx hxone hxchi (hlocal (T + 1) hT)
          (hwindow (T + 1) hT)

theorem hlhdt_contentHalfImage_sum_le_tprod
    (D : Type*) [Fintype D]
    (turns : D → List ℤ)
    (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
    (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
    {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x < hexChiE)
    (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
    (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
    ∑ s ∈ hlhdt_contentHalfImage D turns legal halfSpace,
        hhc_halfWeight x s ≤
      ∏' T, (1 + hlhdt_taggedMajorant x T) := by
  exact hchb_sum_halfWeight_le_tprod
    (hlhdt_contentHalfImage D turns legal halfSpace) hx.le
    (hlhdt_taggedMajorant x) (hlhdt_taggedMajorant_nonneg hx.le)
    (hex_bridge_multipliable _ (hlhdt_taggedMajorant_summable hx hxchi))
    (hlhdt_contentHalfImage_bridgeMass_le_majorant D turns legal
      halfSpace hx hxone hxchi.le hlocal hwindow)






structure HLHDTaggedTwoHalfData (a : ℂ) (h0 : ℤ) (N extra : ℕ) where
  lower : hhc_Dn a h0 N → List ℤ
  upper : hhc_Dn a h0 N → List ℤ
  lower_legal : ∀ d, (ofTurns hexAWStart 1 (lower d)).IsLegalSAW
  upper_legal : ∀ d, (ofTurns hexAWStart 1 (upper d)).IsLegalSAW
  lower_halfSpace : ∀ d, HLHDLiteralHalfSpace (lower d) (lower_legal d)
  upper_halfSpace : ∀ d, HLHDLiteralHalfSpace (upper d) (upper_legal d)
  pair_injective : Function.Injective (fun d => (lower d, upper d))
  length_add : ∀ d,
    (lower d).length + (upper d).length = d.1.length + extra

namespace HLHDTaggedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N extra : ℕ}

noncomputable def lowerHalf
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    (d : hhc_Dn a h0 N) : HexHWContentHalf :=
  hlhd_contentHalf (H.lower d) (H.lower_legal d) (H.lower_halfSpace d)

noncomputable def upperHalf
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    (d : hhc_Dn a h0 N) : HexHWContentHalf :=
  hlhd_contentHalf (H.upper d) (H.upper_legal d) (H.upper_halfSpace d)

@[simp] theorem lowerHalf_turns
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    (d : hhc_Dn a h0 N) :
    hhc_halfTurns (H.lowerHalf d) = H.lower d :=
  hlhd_contentHalf_turns _ (H.lower_legal d) (H.lower_halfSpace d)

@[simp] theorem upperHalf_turns
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    (d : hhc_Dn a h0 N) :
    hhc_halfTurns (H.upperHalf d) = H.upper d :=
  hlhd_contentHalf_turns _ (H.upper_legal d) (H.upper_halfSpace d)

noncomputable def contentPair
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    (d : hhc_Dn a h0 N) : HexHWContentHalf × HexHWContentHalf :=
  (H.lowerHalf d, H.upperHalf d)

theorem contentPair_injective
    (H : HLHDTaggedTwoHalfData a h0 N extra) :
    Function.Injective H.contentPair := by
  intro d e hpair
  apply H.pair_injective
  apply Prod.ext
  · have h := congrArg
      (fun p : HexHWContentHalf × HexHWContentHalf => hhc_halfTurns p.1)
      hpair
    simpa [contentPair] using h
  · have h := congrArg
      (fun p : HexHWContentHalf × HexHWContentHalf => hhc_halfTurns p.2)
      hpair
    simpa [contentPair] using h

noncomputable def lowerImage
    (H : HLHDTaggedTwoHalfData a h0 N extra) :
    Finset HexHWContentHalf :=
  hlhdt_contentHalfImage (hhc_Dn a h0 N) H.lower H.lower_legal
    H.lower_halfSpace

noncomputable def upperImage
    (H : HLHDTaggedTwoHalfData a h0 N extra) :
    Finset HexHWContentHalf :=
  hlhdt_contentHalfImage (hhc_Dn a h0 N) H.upper H.upper_legal
    H.upper_halfSpace

theorem source_weight_factor
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    (x : ℝ) (hx : 0 < x) (d : hhc_Dn a h0 N) :
    x ^ d.1.length = (x ^ extra)⁻¹ *
      (hhc_halfWeight x (H.lowerHalf d) *
        hhc_halfWeight x (H.upperHalf d)) := by
  rw [hhc_halfWeight_eq_pow, hhc_halfWeight_eq_pow,
    H.lowerHalf_turns, H.upperHalf_turns, ← pow_add, H.length_add d,
    pow_add]
  have hpow : x ^ extra ≠ 0 := pow_ne_zero _ (ne_of_gt hx)
  calc
    x ^ d.1.length = 1 * x ^ d.1.length := by ring
    _ = ((x ^ extra)⁻¹ * x ^ extra) * x ^ d.1.length := by
      rw [inv_mul_cancel₀ hpow]
    _ = (x ^ extra)⁻¹ * (x ^ d.1.length * x ^ extra) := by ring

noncomputable def pairImage
    (H : HLHDTaggedTwoHalfData a h0 N extra) :
    Finset (HexHWContentHalf × HexHWContentHalf) := by
  classical
  exact Finset.univ.image H.contentPair

theorem sum_eq_pairImage
    (H : HLHDTaggedTwoHalfData a h0 N extra) (x : ℝ) :
    ∑ d : hhc_Dn a h0 N,
        hhc_halfWeight x (H.lowerHalf d) *
          hhc_halfWeight x (H.upperHalf d) =
      ∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
  classical
  rw [pairImage, Finset.sum_image
    (fun d _ e _ hde => H.contentPair_injective hde)]
  rfl

theorem pairImage_subset_product
    (H : HLHDTaggedTwoHalfData a h0 N extra) :
    H.pairImage ⊆ H.lowerImage ×ˢ H.upperImage := by
  classical
  intro p hp
  rw [pairImage, Finset.mem_image] at hp
  obtain ⟨d, _, rfl⟩ := hp
  rw [Finset.mem_product]
  exact ⟨Finset.mem_image_of_mem H.lowerHalf (Finset.mem_univ d),
    Finset.mem_image_of_mem H.upperHalf (Finset.mem_univ d)⟩

theorem pair_sum_le_product
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    {x : ℝ} (hx : 0 ≤ x) :
    (∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2) ≤
      (∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
        (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
  classical
  calc
    (∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2) ≤
        ∑ p ∈ H.lowerImage ×ˢ H.upperImage,
          hhc_halfWeight x p.1 * hhc_halfWeight x p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg H.pairImage_subset_product
        (fun p _ _ => mul_nonneg (hhc_halfWeight_nonneg hx p.1)
          (hhc_halfWeight_nonneg hx p.2))
    _ = (∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]


theorem finite_partial_bound
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (x ^ extra)⁻¹ *
        ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s)) := by
  rw [← hhc_partial_eq a h0 x N]
  calc
    (∑ d : hhc_Dn a h0 N, x ^ d.1.length) =
        (x ^ extra)⁻¹ *
          ∑ d : hhc_Dn a h0 N,
            hhc_halfWeight x (H.lowerHalf d) *
              hhc_halfWeight x (H.upperHalf d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      exact H.source_weight_factor x hx d
    _ = (x ^ extra)⁻¹ *
        ∑ p ∈ H.pairImage,
          hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
      rw [H.sum_eq_pairImage x]
    _ ≤ (x ^ extra)⁻¹ *
        ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s)) :=
      mul_le_mul_of_nonneg_left (H.pair_sum_le_product hx.le)
        (inv_nonneg.mpr (pow_nonneg hx.le _))



theorem finite_partial_bound_tagged
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x < hexChiE)
    (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
    (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (x ^ extra)⁻¹ *
        (∏' T, (1 + hlhdt_taggedMajorant x T)) ^ 2 := by
  let P := ∏' T, (1 + hlhdt_taggedMajorant x T)
  have hlo :
      (∑ s ∈ H.lowerImage, hhc_halfWeight x s) ≤ P := by
    simpa only [lowerImage, P] using
      hlhdt_contentHalfImage_sum_le_tprod
        (hhc_Dn a h0 N) H.lower H.lower_legal H.lower_halfSpace
        hx hxone hxchi hlocal hwindow
  have hup :
      (∑ s ∈ H.upperImage, hhc_halfWeight x s) ≤ P := by
    simpa only [upperImage, P] using
      hlhdt_contentHalfImage_sum_le_tprod
        (hhc_Dn a h0 N) H.upper H.upper_legal H.upper_halfSpace
        hx hxone hxchi hlocal hwindow
  have hupper_nn :
      0 ≤ ∑ s ∈ H.upperImage, hhc_halfWeight x s :=
    Finset.sum_nonneg fun s _ => hhc_halfWeight_nonneg hx.le s
  have hmul : Multipliable
      (fun T => 1 + hlhdt_taggedMajorant x T) :=
    hex_bridge_multipliable _ (hlhdt_taggedMajorant_summable hx hxchi)
  have hP_one : 1 ≤ P := by
    have h := hexSeams_prod_one_add_le_tprod
      (hlhdt_taggedMajorant x) (hlhdt_taggedMajorant_nonneg hx.le) hmul 0
    simpa [P] using h
  calc
    (∑ n ∈ Finset.range N,
        (hlc_sawCount a h0 n : ℝ) * x ^ n) ≤
        (x ^ extra)⁻¹ *
          ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
            (∑ s ∈ H.upperImage, hhc_halfWeight x s)) :=
      H.finite_partial_bound hx
    _ ≤ (x ^ extra)⁻¹ * (P * P) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul hlo hup hupper_nn (le_trans (by norm_num) hP_one)
      · positivity
    _ = (x ^ extra)⁻¹ * P ^ 2 := by ring



theorem summable_of_taggedTwoHalfData
    (H : ∀ N, HLHDTaggedTwoHalfData a h0 N extra)
    {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x < hexChiE)
    (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
    (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
    Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
  apply summable_of_sum_range_le
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.le _)
  · intro N
    simpa [hlc_sawCountR] using
      (H N).finite_partial_bound_tagged hx hxone hxchi hlocal hwindow

end HLHDTaggedTwoHalfData

end

end StatMech.Universality
