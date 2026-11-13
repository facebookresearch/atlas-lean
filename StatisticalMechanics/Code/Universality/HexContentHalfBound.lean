/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.Universality.HexContentChoiceBound
import Code.Universality.HexLiteralHWContent
import Code.Universality.HexSurgerySeams

namespace StatMech.Universality

open scoped BigOperators

noncomputable section

private instance : Std.Irrefl
    (fun b c : HexBridge => b.width > c.width) where
  irrefl b := lt_irrefl b.width

private instance : Std.Antisymm
    (fun b c : HexBridge => b.width > c.width) where
  antisymm _ _ hab hba := (lt_asymm hab hba).elim



theorem hchb_eq_of_mem_iff (s t : HexHWContentHalf)
    (hmem : forall b : HexBridge, b ∈ s.1 ↔ b ∈ t.1) : s = t := by
  apply Subtype.ext
  exact s.2.eq_of_mem_iff t.2 hmem


def hchb_find (s : HexHWContentHalf) (T : ℕ) : Option HexBridge :=
  s.1.find? (fun b => decide (b.width = T))

private theorem hchb_find_eq_some_of_mem
    {l : List HexBridge}
    (hl : l.Pairwise (fun b c => b.width > c.width))
    {b : HexBridge} (hb : b ∈ l) :
    l.find? (fun c => decide (c.width = b.width)) = some b := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
      rw [List.pairwise_cons] at hl
      rcases List.mem_cons.mp hb with rfl | hb
      · simp
      · have hne : a.width ≠ b.width := by
          intro heq
          have hab := hl.1 b hb
          omega
        simp only [List.find?, decide_eq_true_eq, hne, Bool.false_eq_true,
          ↓reduceIte]
        exact ih hl.2 hb


theorem hchb_find_eq_some_iff (s : HexHWContentHalf) (T : ℕ)
    (b : HexBridge) :
    hchb_find s T = some b ↔ b ∈ s.1 ∧ b.width = T := by
  constructor
  · intro h
    have h' := h
    unfold hchb_find at h'
    have hp : decide (b.width = T) = true :=
      @List.find?_some HexBridge (fun c => decide (c.width = T)) b s.1 h'
    exact ⟨List.mem_of_find?_eq_some h',
      of_decide_eq_true hp⟩
  · rintro ⟨hb, rfl⟩
    exact hchb_find_eq_some_of_mem s.2 hb


noncomputable def hchb_bridges
    (S : Finset HexHWContentHalf) : Finset HexBridge := by
  classical
  exact S.biUnion (fun s => s.1.toFinset)


noncomputable def hchb_active (S : Finset HexHWContentHalf) : Finset ℕ :=
  S.biUnion hhc_widths



noncomputable def hchb_choices (S : Finset HexHWContentHalf) (T : ℕ) :
    Finset (Option HexBridge) := by
  classical
  exact insert none
    (((hchb_bridges S).filter (fun b => b.width = T)).image some)


def hchb_choiceWeight (x : ℝ) (_T : ℕ) : Option HexBridge → ℝ
  | none => 1
  | some b => hhc_bridgeWeight x b


noncomputable def hchb_bridgeMass
    (S : Finset HexHWContentHalf) (x : ℝ) (T : ℕ) : ℝ := by
  classical
  exact ∑ b ∈ (hchb_bridges S).filter (fun b => b.width = T),
    hhc_bridgeWeight x b

private theorem hchb_widths_subset_active {S : Finset HexHWContentHalf}
    {s : HexHWContentHalf} (hs : s ∈ S) :
    hhc_widths s ⊆ hchb_active S := by
  intro T hT
  exact Finset.mem_biUnion.mpr ⟨s, hs, hT⟩

private theorem hchb_mem_bridges {S : Finset HexHWContentHalf}
    {s : HexHWContentHalf} (hs : s ∈ S) {b : HexBridge} (hb : b ∈ s.1) :
    b ∈ hchb_bridges S := by
  classical
  rw [hchb_bridges, Finset.mem_biUnion]
  exact ⟨s, hs, by simpa using hb⟩

private theorem hchb_width_mem {s : HexHWContentHalf} {b : HexBridge}
    (hb : b ∈ s.1) : b.width ∈ hhc_widths s := by
  simpa [hhc_widths, hbw_widthFinset] using
    (List.mem_map_of_mem (f := HexBridge.width) hb)


theorem hchb_encode_mem_pi (S : Finset HexHWContentHalf)
    (s : HexHWContentHalf) (hs : s ∈ S) :
    (fun T (_hT : T ∈ hchb_active S) => hchb_find s T) ∈
      (hchb_active S).pi (hchb_choices S) := by
  classical
  rw [Finset.mem_pi]
  intro T hT
  cases hfind : hchb_find s T with
  | none => simp [hchb_choices]
  | some b =>
      have hb := (hchb_find_eq_some_iff s T b).mp hfind
      rw [hchb_choices, Finset.mem_insert]
      right
      rw [Finset.mem_image]
      exact ⟨b, by
        rw [Finset.mem_filter]
        exact ⟨hchb_mem_bridges hs hb.1, hb.2⟩, rfl⟩




theorem hchb_encode_injOn (S : Finset HexHWContentHalf) :
    Set.InjOn (fun s => fun T (_hT : T ∈ hchb_active S) => hchb_find s T)
      (S : Set HexHWContentHalf) := by
  classical
  intro s hs t ht hst
  apply hchb_eq_of_mem_iff
  intro b
  constructor
  · intro hb
    have hT : b.width ∈ hchb_active S :=
      hchb_widths_subset_active hs (hchb_width_mem hb)
    have heq := congrArg (fun f => f b.width hT) hst
    change hchb_find s b.width = hchb_find t b.width at heq
    have hsfind : hchb_find s b.width = some b :=
      (hchb_find_eq_some_iff s b.width b).2 ⟨hb, rfl⟩
    have htfind : hchb_find t b.width = some b := by
      rw [← heq]
      exact hsfind
    exact (hchb_find_eq_some_iff t b.width b).1 htfind |>.1
  · intro hb
    have hT : b.width ∈ hchb_active S :=
      hchb_widths_subset_active ht (hchb_width_mem hb)
    have heq := congrArg (fun f => f b.width hT) hst
    change hchb_find s b.width = hchb_find t b.width at heq
    have htfind : hchb_find t b.width = some b :=
      (hchb_find_eq_some_iff t b.width b).2 ⟨hb, rfl⟩
    have hsfind : hchb_find s b.width = some b := by
      rw [heq]
      exact htfind
    exact (hchb_find_eq_some_iff s b.width b).1 hsfind |>.1



theorem hchb_halfWeight_eq_widthProd (x : ℝ) (s : HexHWContentHalf) :
    hhc_halfWeight x s =
      ∏ T ∈ hhc_widths s, hchb_choiceWeight x T (hchb_find s T) := by
  let f : ℕ → ℝ := fun T => hchb_choiceWeight x T (hchb_find s T)
  have hprod := hbw_prod_eq_finsetProd s.1 s.2 f
  change hhc_halfWeight x s = ∏ T ∈ hbw_widthFinset s.1, f T
  rw [← hprod]
  unfold hhc_halfWeight
  congr 1
  apply List.map_congr_left
  intro b hb
  have hfind : hchb_find s b.width = some b :=
    (hchb_find_eq_some_iff s b.width b).2 ⟨hb, rfl⟩
  simp [f, hchb_choiceWeight, hfind]



theorem hchb_halfWeight_eq_activeProd
    (S : Finset HexHWContentHalf) (x : ℝ)
    (s : HexHWContentHalf) (hs : s ∈ S) :
    hhc_halfWeight x s =
      ∏ T ∈ hchb_active S, hchb_choiceWeight x T (hchb_find s T) := by
  rw [hchb_halfWeight_eq_widthProd]
  apply Finset.prod_subset (hchb_widths_subset_active hs)
  intro T hTactive hTnot
  cases hfind : hchb_find s T with
  | none => rfl
  | some b =>
      exfalso
      apply hTnot
      have hb := (hchb_find_eq_some_iff s T b).1 hfind
      simpa [hb.2] using hchb_width_mem hb.1



theorem hchb_sum_choices (S : Finset HexHWContentHalf) (x : ℝ) (T : ℕ) :
    ∑ o ∈ hchb_choices S T, hchb_choiceWeight x T o =
      1 + hchb_bridgeMass S x T := by
  classical
  unfold hchb_choices hchb_bridgeMass
  rw [Finset.sum_insert]
  · rw [Finset.sum_image]
    · rfl
    · intro a _ b _ hab
      simpa using hab
  · simp




theorem hchb_sum_halfWeight_le_prod
    (S : Finset HexHWContentHalf) {x : ℝ} (hx : 0 ≤ x) :
    ∑ s ∈ S, hhc_halfWeight x s ≤
      ∏ T ∈ hchb_active S, (1 + hchb_bridgeMass S x T) := by
  classical
  have h := finiteChoice_sum_le_prod
    (active := hchb_active S) (choices := hchb_choices S)
    (objects := S)
    (encode := fun s T _ => hchb_find s T)
    (hencode := hchb_encode_mem_pi S)
    (hinjective := hchb_encode_injOn S)
    (choiceWeight := hchb_choiceWeight x)
    (objectWeight := hhc_halfWeight x)
    (hweight := by
      intro s hs
      rw [hchb_halfWeight_eq_activeProd S x s hs]
      exact (Finset.prod_attach (hchb_active S)
        (fun T => hchb_choiceWeight x T (hchb_find s T))).symm)
    (hnonneg := by
      intro p hp
      apply Finset.prod_nonneg
      intro T hT
      cases hopt : p T.1 T.2 with
      | none => simp [hchb_choiceWeight]
      | some b =>
          simp only [hchb_choiceWeight]
          exact pow_nonneg hx _)
  simpa only [hchb_sum_choices] using h



theorem hchb_sum_halfWeight_le_tprod
    (S : Finset HexHWContentHalf) {x : ℝ} (hx : 0 ≤ x)
    (ups : ℕ → ℝ) (hups : ∀ T, 0 ≤ ups T)
    (hmul : Multipliable (fun T => 1 + ups T))
    (hmass : ∀ T, hchb_bridgeMass S x T ≤ ups T) :
    ∑ s ∈ S, hhc_halfWeight x s ≤ ∏' T, (1 + ups T) := by
  calc
    ∑ s ∈ S, hhc_halfWeight x s ≤
        ∏ T ∈ hchb_active S, (1 + hchb_bridgeMass S x T) :=
      hchb_sum_halfWeight_le_prod S hx
    _ ≤ ∏ T ∈ hchb_active S, (1 + ups T) := by
      apply Finset.prod_le_prod
      · intro T hT
        have : 0 ≤ hchb_bridgeMass S x T := by
          unfold hchb_bridgeMass
          exact Finset.sum_nonneg fun b _ => pow_nonneg hx _
        linarith
      · intro T hT
        linarith [hmass T]
    _ ≤ ∏' T, (1 + ups T) := by
      obtain ⟨N, hsub⟩ := Finset.exists_nat_subset_range (hchb_active S)
      calc
        (∏ T ∈ hchb_active S, (1 + ups T)) ≤
            ∏ T ∈ Finset.range N, (1 + ups T) := by
          apply Finset.prod_le_prod_of_subset_of_one_le hsub
          · intro T hT
            linarith [hups T]
          · intro T hT hTnot
            linarith [hups T]
        _ ≤ ∏' T, (1 + ups T) :=
          hexSeams_prod_one_add_le_tprod ups hups hmul N

end

end StatMech.Universality
