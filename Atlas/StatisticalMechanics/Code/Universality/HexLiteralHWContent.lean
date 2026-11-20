/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Mathlib
import Code.Universality.HexBridgeDecomp
import Code.Universality.HexBridgeWeight
import Code.Universality.HexLiteralCountLaws
import Code.Universality.HexW2Cut

namespace StatMech.Universality

open HexWalk
open scoped BigOperators





def HexHWContentHalf : Type :=
  {bs : List HexBridge // StrictDecreasingWidths bs}


def hhc_halfTurns (s : HexHWContentHalf) : List ℤ :=
  (s.1.map HexBridge.content).flatten


noncomputable def hhc_widths (s : HexHWContentHalf) : Finset ℕ :=
  hbw_widthFinset s.1


theorem hhc_widthList_nodup (s : HexHWContentHalf) :
    (s.1.map HexBridge.width).Nodup :=
  hbw_widthlist_nodup s.1 s.2


theorem hhc_card_widths (s : HexHWContentHalf) :
    (hhc_widths s).card = s.1.length := by
  classical
  unfold hhc_widths hbw_widthFinset
  simpa using List.toFinset_card_of_nodup (hhc_widthList_nodup s)



private def hhc_plusBridge : HexBridge where
  width := 1
  width_pos := one_pos
  content := [1]
  content_ne := by simp

private def hhc_minusBridge : HexBridge where
  width := 1
  width_pos := one_pos
  content := [-1]
  content_ne := by simp

private def hhc_plusHalf : HexHWContentHalf :=
  ⟨[hhc_plusBridge], by simp [StrictDecreasingWidths]⟩

private def hhc_minusHalf : HexHWContentHalf :=
  ⟨[hhc_minusBridge], by simp [StrictDecreasingWidths]⟩

private theorem hhc_plusHalf_ne_minusHalf : hhc_plusHalf ≠ hhc_minusHalf := by
  intro h
  have hv : ([hhc_plusBridge] : List HexBridge) = [hhc_minusBridge] :=
    congrArg Subtype.val h
  have hb : hhc_plusBridge = hhc_minusBridge := by simpa using hv
  have hc := congrArg HexBridge.content hb
  simp [hhc_plusBridge, hhc_minusBridge] at hc




theorem hhc_width_projection_not_injective :
    ¬ Function.Injective hhc_widths := by
  intro hinj
  apply hhc_plusHalf_ne_minusHalf
  apply hinj
  simp [hhc_widths, hbw_widthFinset, hhc_plusHalf, hhc_minusHalf,
    hhc_plusBridge, hhc_minusBridge]




theorem hhc_sum_grouped_by_widths (S : Finset HexHWContentHalf)
    (w : HexHWContentHalf → ℝ) :
    ∑ s ∈ S, w s =
      ∑ widths ∈ S.image hhc_widths,
        ∑ s ∈ S with hhc_widths s = widths, w s := by
  classical
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun s hs => Finset.mem_image_of_mem hhc_widths hs) w





def hhc_bridgeWeight (x : ℝ) (b : HexBridge) : ℝ :=
  x ^ b.content.length


def hhc_halfWeight (x : ℝ) (s : HexHWContentHalf) : ℝ :=
  (s.1.map (hhc_bridgeWeight x)).prod



theorem hhc_halfWeight_eq_pow (x : ℝ) (s : HexHWContentHalf) :
    hhc_halfWeight x s = x ^ (hhc_halfTurns s).length := by
  rcases s with ⟨bs, hbs⟩
  induction bs with
  | nil => simp [hhc_halfWeight, hhc_halfTurns]
  | cons b bs ih =>
      let tail : HexHWContentHalf := ⟨bs, (strictDecreasingWidths_cons.mp hbs).2⟩
      have hi := ih (hbs := (strictDecreasingWidths_cons.mp hbs).2)
      simp only [hhc_halfWeight, hhc_halfTurns, List.map_cons, List.flatten_cons,
        List.prod_cons, hhc_bridgeWeight, List.length_append, pow_add]
      simpa [hhc_halfWeight, hhc_halfTurns, tail] using
        congrArg (fun z => x ^ b.content.length * z) hi


theorem hhc_halfWeight_nonneg {x : ℝ} (hx : 0 ≤ x) (s : HexHWContentHalf) :
    0 ≤ hhc_halfWeight x s := by
  rw [hhc_halfWeight_eq_pow]
  positivity







structure HexHWContentDecomp (D : Type) where
  
  turns : D → List ℤ
  
  turns_inj : Function.Injective turns
  
  lower : D → HexHWContentHalf
  
  upper : D → HexHWContentHalf
  
  reconstruct : ∀ d, turns d = hhc_halfTurns (lower d) ++ hhc_halfTurns (upper d)

namespace HexHWContentDecomp

variable {D : Type}


def pair (H : HexHWContentDecomp D) (d : D) :
    HexHWContentHalf × HexHWContentHalf :=
  (H.lower d, H.upper d)



theorem pair_injective (H : HexHWContentDecomp D) :
    Function.Injective H.pair := by
  intro d e hde
  apply H.turns_inj
  rw [H.reconstruct d, H.reconstruct e]
  exact congrArg (fun p : HexHWContentHalf × HexHWContentHalf =>
    hhc_halfTurns p.1 ++ hhc_halfTurns p.2) hde



theorem weight_factor (H : HexHWContentDecomp D) (x : ℝ) (d : D) :
    x ^ (H.turns d).length =
      hhc_halfWeight x (H.lower d) * hhc_halfWeight x (H.upper d) := by
  rw [H.reconstruct d, List.length_append, pow_add,
    hhc_halfWeight_eq_pow, hhc_halfWeight_eq_pow]

section Finite

variable [Fintype D]


noncomputable def lowerImage (H : HexHWContentDecomp D) : Finset HexHWContentHalf :=
  by
    classical
    exact Finset.univ.image H.lower


noncomputable def upperImage (H : HexHWContentDecomp D) : Finset HexHWContentHalf :=
  by
    classical
    exact Finset.univ.image H.upper


noncomputable def pairImage (H : HexHWContentDecomp D) :
    Finset (HexHWContentHalf × HexHWContentHalf) :=
  by
    classical
    exact Finset.univ.image H.pair



theorem sum_eq_pairImage (H : HexHWContentDecomp D) (x : ℝ) :
    ∑ d : D, x ^ (H.turns d).length =
      ∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
  classical
  rw [pairImage, Finset.sum_image (fun a _ b _ hab => H.pair_injective hab)]
  apply Finset.sum_congr rfl
  intro d _
  exact H.weight_factor x d


theorem pairImage_subset_product (H : HexHWContentDecomp D) :
    H.pairImage ⊆ H.lowerImage ×ˢ H.upperImage := by
  classical
  intro p hp
  rw [pairImage, Finset.mem_image] at hp
  obtain ⟨d, _, rfl⟩ := hp
  rw [Finset.mem_product]
  exact ⟨Finset.mem_image_of_mem H.lower (Finset.mem_univ d),
    Finset.mem_image_of_mem H.upper (Finset.mem_univ d)⟩





theorem finite_content_bound (H : HexHWContentDecomp D) {x : ℝ} (hx : 0 ≤ x) :
    ∑ d : D, x ^ (H.turns d).length ≤
      (∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
        (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
  classical
  rw [H.sum_eq_pairImage x]
  calc
    (∑ p ∈ H.pairImage, hhc_halfWeight x p.1 * hhc_halfWeight x p.2)
        ≤ ∑ p ∈ H.lowerImage ×ˢ H.upperImage,
            hhc_halfWeight x p.1 * hhc_halfWeight x p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg H.pairImage_subset_product
        (fun p _ _ => mul_nonneg (hhc_halfWeight_nonneg hx p.1)
          (hhc_halfWeight_nonneg hx p.2))
    _ = (∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
      rw [Finset.sum_product]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]

end Finite

end HexHWContentDecomp





def hhc_Dn (a : ℂ) (h0 : ℤ) (N : ℕ) : Type :=
  hzc_Dn a h0 (N + 1)

noncomputable instance hhc_Dn_fintype (a : ℂ) (h0 : ℤ) (N : ℕ) :
    Fintype (hhc_Dn a h0 N) := by
  unfold hhc_Dn
  infer_instance


theorem hhc_Dn_spec (a : ℂ) (h0 : ℤ) (N : ℕ) (d : hhc_Dn a h0 N) :
    (ofTurns a h0 d.1).IsLegalSAW ∧ d.1.length < N := by
  have h := (hzc_mem_truncFinset a h0 (N + 1) d.1).mp d.2
  refine ⟨h.1, ?_⟩
  simpa [numVertices] using h.2



theorem hhc_partial_eq (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ d : hhc_Dn a h0 N, x ^ d.1.length =
      ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n := by
  classical
  rw [show (∑ d : hhc_Dn a h0 N, x ^ d.1.length) =
      ∑ ts ∈ hzc_truncFinset a h0 (N + 1), x ^ ts.length from
        Finset.sum_coe_sort (hzc_truncFinset a h0 (N + 1)) (fun ts => x ^ ts.length)]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range N)
      (g := List.length) ?_]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range] at hn
    rw [Finset.sum_congr rfl (g := fun _ => x ^ n)
      (fun ts hts => by simp only [Finset.mem_filter] at hts; rw [hts.2])]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard :
        ((hzc_truncFinset a h0 (N + 1)).filter (fun ts => ts.length = n)).card =
          hlc_sawCount a h0 n := by
      rw [← hlc_card_sawFinset a h0 n]
      congr 1
      ext ts
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨htr, hlen⟩
        rw [hlc_mem_sawFinset]
        exact ⟨(hzc_mem_truncFinset a h0 (N + 1) ts).mp htr |>.1, hlen⟩
      · intro hsaw
        have hs := (hlc_mem_sawFinset a h0 n ts).mp hsaw
        refine ⟨?_, hs.2⟩
        rw [hzc_mem_truncFinset]
        refine ⟨hs.1, ?_⟩
        simp [numVertices, hs.2]
        omega
    rw [hcard]
  · intro ts hts
    simp only [Finset.mem_range]
    have h := (hzc_mem_truncFinset a h0 (N + 1) ts).mp hts
    simpa [numVertices] using h.2



noncomputable def hhc_literalDecomp (a : ℂ) (h0 : ℤ) (N : ℕ)
    (lower upper : hhc_Dn a h0 N → HexHWContentHalf)
    (hreconstruct : ∀ d, d.1 = hhc_halfTurns (lower d) ++ hhc_halfTurns (upper d)) :
    HexHWContentDecomp (hhc_Dn a h0 N) where
  turns := Subtype.val
  turns_inj := Subtype.val_injective
  lower := lower
  upper := upper
  reconstruct := hreconstruct





theorem hhc_literal_partial_bound (a : ℂ) (h0 : ℤ) (N : ℕ)
    (lower upper : hhc_Dn a h0 N → HexHWContentHalf)
    (hreconstruct : ∀ d, d.1 = hhc_halfTurns (lower d) ++ hhc_halfTurns (upper d))
    {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (∑ s ∈ (hhc_literalDecomp a h0 N lower upper hreconstruct).lowerImage,
          hhc_halfWeight x s) *
        (∑ s ∈ (hhc_literalDecomp a h0 N lower upper hreconstruct).upperImage,
          hhc_halfWeight x s) := by
  rw [← hhc_partial_eq a h0 x N]
  exact (hhc_literalDecomp a h0 N lower upper hreconstruct).finite_content_bound hx




















def hhc_bridgeOfNonempty (ts : List ℤ) (hne : ts ≠ []) : HexBridge where
  width := ts.length
  width_pos := List.length_pos_iff.mpr hne
  content := ts
  content_ne := hne

@[simp] theorem hhc_bridgeOfNonempty_width (ts : List ℤ) (hne : ts ≠ []) :
    (hhc_bridgeOfNonempty ts hne).width = ts.length := rfl

@[simp] theorem hhc_bridgeOfNonempty_content (ts : List ℤ) (hne : ts ≠ []) :
    (hhc_bridgeOfNonempty ts hne).content = ts := rfl



noncomputable def hhc_halfOfList (ts : List ℤ) : HexHWContentHalf := by
  classical
  by_cases hne : ts = []
  · exact ⟨[], strictDecreasingWidths_nil⟩
  · exact ⟨[hhc_bridgeOfNonempty ts hne], by
      simp [StrictDecreasingWidths]⟩


@[simp] theorem hhc_halfTurns_halfOfList (ts : List ℤ) :
    hhc_halfTurns (hhc_halfOfList ts) = ts := by
  classical
  unfold hhc_halfOfList
  split
  · next h => simp [hhc_halfTurns, h]
  · next h => simp [hhc_halfTurns, hhc_bridgeOfNonempty]



theorem hhc_halfOfList_strict (ts : List ℤ) :
    StrictDecreasingWidths (hhc_halfOfList ts).1 :=
  (hhc_halfOfList ts).2



theorem hhc_bridge_decomp_retains_turns (s : HexHWContentHalf) :
    (hexHW_bridge_decomp s : List (ℕ × ℤ)).map Prod.snd = hhc_halfTurns s := by
  rcases s with ⟨bs, hbs⟩
  simp only [hexHW_bridge_decomp_apply, bridgeRecompose, hhc_halfTurns,
    List.map_flatten]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  simp [HexBridge.rungs, Function.comp_def, List.map_map]



noncomputable def hhc_literalLower (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) : HexHWContentHalf :=
  hhc_halfOfList (d.1.take (hexW2_cutPos h0 d.1))



noncomputable def hhc_literalUpper (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) : HexHWContentHalf :=
  hhc_halfOfList (d.1.drop (hexW2_cutPos h0 d.1))

@[simp] theorem hhc_literalLower_turns (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    hhc_halfTurns (hhc_literalLower a h0 N d) =
      d.1.take (hexW2_cutPos h0 d.1) := by
  simp [hhc_literalLower]

@[simp] theorem hhc_literalUpper_turns (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    hhc_halfTurns (hhc_literalUpper a h0 N d) =
      d.1.drop (hexW2_cutPos h0 d.1) := by
  simp [hhc_literalUpper]




theorem hhc_literalHighest_reconstruct (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    d.1 = hhc_halfTurns (hhc_literalLower a h0 N d) ++
      hhc_halfTurns (hhc_literalUpper a h0 N d) := by
  rw [hhc_literalLower_turns, hhc_literalUpper_turns]
  exact (List.take_append_drop (hexW2_cutPos h0 d.1) d.1).symm




theorem hhc_literalHighest_bridgeDecomp_reconstruct (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    d.1 =
      (hexHW_bridge_decomp (hhc_literalLower a h0 N d) : List (ℕ × ℤ)).map Prod.snd ++
      (hexHW_bridge_decomp (hhc_literalUpper a h0 N d) : List (ℕ × ℤ)).map Prod.snd := by
  rw [hhc_bridge_decomp_retains_turns, hhc_bridge_decomp_retains_turns]
  exact hhc_literalHighest_reconstruct a h0 N d



theorem hhc_literalHighest_cut_spec (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    hexW2_cutPos h0 d.1 ≤ d.1.length ∧
      (∀ k ≤ d.1.length,
        hexW2_partialDisp h0 d.1 k ≤
          hexW2_partialDisp h0 d.1 (hexW2_cutPos h0 d.1)) ∧
      (∀ k, k < hexW2_cutPos h0 d.1 →
        hexW2_partialDisp h0 d.1 k <
          hexW2_partialDisp h0 d.1 (hexW2_cutPos h0 d.1)) :=
  ⟨hexW2_cutPos_le h0 d.1, hexW2_cutPos_max h0 d.1,
    hexW2_cutPos_first h0 d.1⟩



theorem hhc_literalHighest_halves_legal (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    (ofTurns a h0 (hhc_halfTurns (hhc_literalLower a h0 N d))).IsLegalSAW ∧
      (ofTurns (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
        (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum)
        (hhc_halfTurns (hhc_literalUpper a h0 N d))).IsLegalSAW := by
  have hleg := (hhc_Dn_spec a h0 N d).1
  rw [hhc_literalLower_turns, hhc_literalUpper_turns]
  exact ⟨hexW2_prefix_legal a h0 d.1 hleg,
    hexW2_suffix_legal a h0 d.1 hleg⟩


noncomputable def hhc_literalHighestDecomp (a : ℂ) (h0 : ℤ) (N : ℕ) :
    HexHWContentDecomp (hhc_Dn a h0 N) :=
  hhc_literalDecomp a h0 N (hhc_literalLower a h0 N)
    (hhc_literalUpper a h0 N) (hhc_literalHighest_reconstruct a h0 N)




theorem hhc_literalHighest_partial_bound (a : ℂ) (h0 : ℤ) (N : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (∑ s ∈ (hhc_literalHighestDecomp a h0 N).lowerImage,
          hhc_halfWeight x s) *
        (∑ s ∈ (hhc_literalHighestDecomp a h0 N).upperImage,
          hhc_halfWeight x s) := by
  rw [← hhc_partial_eq a h0 x N]
  exact (hhc_literalHighestDecomp a h0 N).finite_content_bound hx






def hhc_retagBridge (b : HexBridge) (T : ℕ) (hT : 0 < T) : HexBridge where
  width := T
  width_pos := hT
  content := b.content
  content_ne := b.content_ne

@[simp] theorem hhc_retagBridge_width (b : HexBridge) (T : ℕ) (hT : 0 < T) :
    (hhc_retagBridge b T hT).width = T := rfl

@[simp] theorem hhc_retagBridge_content (b : HexBridge) (T : ℕ) (hT : 0 < T) :
    (hhc_retagBridge b T hT).content = b.content := rfl



theorem hhc_same_content_distinct_widths (b : HexBridge) :
    ∃ b₁ b₂ : HexBridge,
      b₁.content = b₂.content ∧ b₁.width ≠ b₂.width := by
  refine ⟨hhc_retagBridge b 1 one_pos, hhc_retagBridge b 2 (by omega), rfl, ?_⟩
  simp

end StatMech.Universality
