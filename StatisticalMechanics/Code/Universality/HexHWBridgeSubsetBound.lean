/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexContentChoiceBound
import Code.Universality.HexLiteralHWContent

namespace StatMech.Universality

open scoped BigOperators



theorem strictDecreasingWidths_eq_of_mem_iff
    {xs ys : List HexBridge}
    (hx : StrictDecreasingWidths xs) (hy : StrictDecreasingWidths ys)
    (hmem : ∀ b, b ∈ xs ↔ b ∈ ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          exfalso
          have := (hmem y).mpr (by simp)
          simpa using this
  | cons x xs ih =>
      cases ys with
      | nil =>
          exfalso
          have := (hmem x).mp (by simp)
          simpa using this
      | cons y ys =>
          have hxmem : x = y ∨ x ∈ ys := by
            simpa using (hmem x).mp (by simp)
          have hymem : y = x ∨ y ∈ xs := by
            simpa using (hmem y).mpr (by simp)
          have hxy : x = y := by
            by_contra hne
            have hxys : x ∈ ys := hxmem.resolve_left hne
            have hyxs : y ∈ xs := hymem.resolve_left (Ne.symm hne)
            have hxyw := hx.head_gt hyxs
            have hyxw := hy.head_gt hxys
            omega
          subst y
          congr 1
          apply ih hx.tail hy.tail
          intro b
          constructor
          · intro hb
            have hall : b ∈ x :: ys := (hmem b).mp (by simp [hb])
            rcases List.mem_cons.mp hall with hbx | hbys
            · subst b
              exact False.elim (Nat.lt_irrefl _ (hx.head_gt hb))
            · exact hbys
          · intro hb
            have hall : b ∈ x :: xs := (hmem b).mpr (by simp [hb])
            rcases List.mem_cons.mp hall with hbx | hbxs
            · subst b
              exact False.elim (Nat.lt_irrefl _ (hy.head_gt hb))
            · exact hbxs

theorem strictDecreasingWidths_nodup {bs : List HexBridge}
    (hbs : StrictDecreasingWidths bs) : bs.Nodup := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      rw [List.nodup_cons]
      refine ⟨?_, ih hbs.tail⟩
      intro hb
      exact Nat.lt_irrefl _ (hbs.head_gt hb)



noncomputable def hhs_activeBridges
    (S : Finset HexHWContentHalf) : Finset HexBridge := by
  classical
  exact S.biUnion (fun s => s.1.toFinset)

theorem hhs_mem_activeBridges
    {S : Finset HexHWContentHalf} {s : HexHWContentHalf}
    (hs : s ∈ S) {b : HexBridge} (hb : b ∈ s.1) :
    b ∈ hhs_activeBridges S := by
  classical
  rw [hhs_activeBridges, Finset.mem_biUnion]
  exact ⟨s, hs, List.mem_toFinset.mpr hb⟩

noncomputable def hhs_bridgeEncoding
    (S : Finset HexHWContentHalf) (s : HexHWContentHalf) :
    ∀ b, b ∈ hhs_activeBridges S → Bool := by
  classical
  exact fun b _ => decide (b ∈ s.1)

theorem hhs_bridgeEncoding_injective
    (S : Finset HexHWContentHalf) :
    Set.InjOn (hhs_bridgeEncoding S) (S : Set HexHWContentHalf) := by
  classical
  intro s hs t ht heq
  apply Subtype.ext
  apply strictDecreasingWidths_eq_of_mem_iff s.2 t.2
  intro b
  constructor
  · intro hb
    have hactive := hhs_mem_activeBridges hs hb
    have hv := congrFun (congrFun heq b) hactive
    change decide (b ∈ s.1) = decide (b ∈ t.1) at hv
    have hsbool : decide (b ∈ s.1) = true := by simp [hb]
    have htbool : decide (b ∈ t.1) = true := by
      rw [← hv]
      exact hsbool
    exact of_decide_eq_true htbool
  · intro hb
    have hactive := hhs_mem_activeBridges ht hb
    have hv := congrFun (congrFun heq b) hactive
    change decide (b ∈ s.1) = decide (b ∈ t.1) at hv
    have htbool : decide (b ∈ t.1) = true := by simp [hb]
    have hsbool : decide (b ∈ s.1) = true := by
      rw [hv]
      exact htbool
    exact of_decide_eq_true hsbool

private def hhs_boolWeight (x : ℝ) (b : HexBridge) (q : Bool) : ℝ :=
  if q then hhc_bridgeWeight x b else 1

theorem hhs_encoding_weight
    (S : Finset HexHWContentHalf) (x : ℝ)
    (s : HexHWContentHalf) (hs : s ∈ S) :
    hhc_halfWeight x s =
      ∏ b ∈ (hhs_activeBridges S).attach,
        hhs_boolWeight x b.1 (hhs_bridgeEncoding S s b.1 b.2) := by
  classical
  have hsub : s.1.toFinset ⊆ hhs_activeBridges S := by
    intro b hb
    exact hhs_mem_activeBridges hs (List.mem_toFinset.mp hb)
  rw [hhc_halfWeight]
  rw [← List.prod_toFinset (hhc_bridgeWeight x)
    (strictDecreasingWidths_nodup s.2)]
  simp only [hhs_boolWeight, hhs_bridgeEncoding, decide_eq_true_eq]
  change (∏ b ∈ s.1.toFinset, hhc_bridgeWeight x b) =
    ∏ b ∈ (hhs_activeBridges S).attach,
      if b.1 ∈ s.1 then hhc_bridgeWeight x b.1 else 1
  rw [Finset.prod_attach (hhs_activeBridges S)
    (fun b => if b ∈ s.1 then hhc_bridgeWeight x b else 1)]
  symm
  simp_rw [← List.mem_toFinset]
  rw [Finset.prod_ite_mem]
  rw [Finset.inter_eq_right.mpr hsub]



theorem hhs_half_sum_le_bridge_product
    (S : Finset HexHWContentHalf) {x : ℝ} (hx : 0 ≤ x) :
    ∑ s ∈ S, hhc_halfWeight x s ≤
      ∏ b ∈ hhs_activeBridges S, (1 + hhc_bridgeWeight x b) := by
  classical
  let active := hhs_activeBridges S
  let choices : HexBridge → Finset Bool := fun _ => Finset.univ
  let encode := hhs_bridgeEncoding S
  let choiceWeight := hhs_boolWeight x
  have hbound := finiteChoice_sum_le_prod active choices S encode
    (fun s hs => by simp [choices])
    (hhs_bridgeEncoding_injective S)
    choiceWeight (hhc_halfWeight x)
    (fun s hs => hhs_encoding_weight S x s hs)
    (fun p hp => by
      apply Finset.prod_nonneg
      intro b hb
      cases hq : p b.1 b.2 <;>
        simp [choiceWeight, hhs_boolWeight, hq, hhc_bridgeWeight,
          pow_nonneg hx])
  simpa [active, choices, choiceWeight, hhs_boolWeight, add_comm] using hbound



theorem hhs_half_sum_le_exp_bridge_sum
    (S : Finset HexHWContentHalf) {x : ℝ} (hx : 0 ≤ x) :
    ∑ s ∈ S, hhc_halfWeight x s ≤
      Real.exp (∑ b ∈ hhs_activeBridges S, hhc_bridgeWeight x b) := by
  calc
    ∑ s ∈ S, hhc_halfWeight x s ≤
        ∏ b ∈ hhs_activeBridges S, (1 + hhc_bridgeWeight x b) :=
      hhs_half_sum_le_bridge_product S hx
    _ ≤ ∏ b ∈ hhs_activeBridges S,
        Real.exp (hhc_bridgeWeight x b) := by
      apply Finset.prod_le_prod
      · intro b hb
        exact add_nonneg zero_le_one
          (by exact pow_nonneg hx _)
      · intro b hb
        simpa [add_comm] using Real.add_one_le_exp (hhc_bridgeWeight x b)
    _ = Real.exp (∑ b ∈ hhs_activeBridges S,
        hhc_bridgeWeight x b) := by
      rw [← Real.exp_sum]

end StatMech.Universality
