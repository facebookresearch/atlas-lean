/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/CapSet/README.md` (leansolving/SqueezeBench):
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The dimension-four statement uses Mathlib's additive Roth number for the value tabulated at
commit e2e19eef093a77882da57f348def029533ec2d5e.
-/
module

public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.Abel

/-!
# Largest cap set in dimension four

The largest cap in the four-dimensional affine space over the field of three elements has
20 points. In a hypothetical 21-point cap, some midpoint is shared by four pairs. Putting
these pairs in standard coordinates leaves two configurations. A finite search bounds their
extensions by grouping points that cannot both be added to a cap. The nonzero solutions of
`x₀² + x₁² + x₂² = x₃²` give the matching lower bound.
-/

namespace MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted
namespace CapSetDimFour

open Finset

attribute [local instance 2000] Finset.decidableDforallFinset

private abbrev Space := Fin 4 → ZMod 3

private def axis (i : Fin 4) : Space := Pi.single i 1

private def paired (s : Finset Space) := s.filter fun x => -x ∈ s

private def flat (k : ℕ) : Finset Space :=
  univ.filter fun x => ∀ j : Fin 4, k ≤ j.val → x j = 0

private lemma twice (x : Space) : x + x = -x := by
  funext j
  exact (by decide : ∀ z : ZMod 3, z + z = -z) (x j)

private lemma third_not_mem {s : Finset Space} (hs : ThreeAPFree (s : Set Space))
    {a b : Space} (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) : -(a + b) ∉ s := by
  intro hc
  have h := hs ha hc hb (by rw [twice, neg_neg])
  have he : a + b = a + a := by
    rw [twice]
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  exact hne (add_left_cancel he).symm

-- Count ordered pairs by their midpoint. Translating a large fiber to the origin
-- gives a cap with at least seven points whose negatives also belong to the cap.
private lemma center {s : Finset Space} (hc : s.card = 21) (hs : ThreeAPFree (s : Set Space)) :
    ∃ t : Finset Space, t.card = 21 ∧ ThreeAPFree (t : Set Space) ∧ 6 < (paired t).card := by
  let mid (p : Space × Space) := -(p.1 + p.2)
  obtain ⟨m, _, hm⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := s.offDiag) (t := univ \ s) (f := mid) (n := 6) (fun p hp => by
      obtain ⟨hl, hr, hn⟩ := mem_offDiag.mp hp
      exact mem_sdiff.mpr ⟨mem_univ _, third_not_mem hs hl hr hn⟩)
    (by rw [card_sdiff_of_subset (subset_univ _), offDiag_card, hc]; decide)
  let t := s.image (· - m)
  have hmem {x : Space} : x ∈ t ↔ x + m ∈ s := by
    simp only [t, mem_image]
    exact ⟨fun ⟨a, ha, e⟩ => (sub_eq_iff_eq_add.mp e) ▸ ha,
      fun h => ⟨_, h, add_sub_cancel_right _ _⟩⟩
  refine ⟨t, (card_image_of_injective _ (sub_left_injective (b := m))).trans hc, ?_, hm.trans_le ?_⟩
  · intro a ha b hb c hcx he
    apply add_right_cancel (b := m)
    apply hs (hmem.mp ha) (hmem.mp hb) (hmem.mp hcx)
    rw [add_add_add_comm, he, add_add_add_comm]
  · apply card_le_card_of_injOn (fun p => p.1 - m)
    · intro p hp
      obtain ⟨hp, he⟩ := mem_filter.mp hp
      obtain ⟨ha, hb, _⟩ := mem_offDiag.mp hp
      refine mem_filter.mpr ⟨mem_image_of_mem _ ha, hmem.mpr ?_⟩
      have hsum : p.1 + p.2 = -m := neg_eq_iff_eq_neg.mp he
      have : -(p.1 - m) + m = p.2 := by
        rw [show -(p.1 - m) + m = m + m - p.1 by abel, twice, ← hsum]
        abel
      exact this.symm ▸ hb
    · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq he
      have hac : a = c := sub_left_injective he
      subst c
      have heq := (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
      exact Prod.ext rfl (add_left_cancel (neg_injective heq))

-- Replace the kth coordinate vector by a given vector outside the preceding coordinate
-- subspace, keeping the preceding coordinate vectors fixed.
private lemma pivot {k : Fin 4} {x : Space} (hx : x ∉ flat k) :
    ∃ e : Space ≃+ Space, e (axis k) = x ∧ ∀ i : Fin 4, i < k → e (axis i) = axis i := by
  obtain ⟨j, hj, hn⟩ : ∃ j : Fin 4, k ≤ j ∧ x j ≠ 0 := by
    simpa [flat] using hx
  let σ := Equiv.swap k j
  let f (z : Space) := z + z j • (x - axis j)
  have axis_self : axis j j = 1 := by simp [axis]
  have fj (z : Space) : f z j = z j * x j := by
    change z j + z j * (x j - axis j j) = _
    rw [axis_self, mul_sub, mul_one]; abel
  have inj : Function.Injective f := by
    intro u v he
    have he' := congrFun he j
    rw [fj, fj] at he'
    exact add_right_cancel (show u + u j • (x - axis j) = v + u j • (x - axis j) by
      simpa only [f, mul_right_cancel₀ hn he'] using he)
  let g : Space →+ Space := {
    toFun := fun z => f (z ∘ σ)
    map_zero' := by simp [f, Function.comp_def]; rfl
    map_add' := fun a b => by
      change (a ∘ σ + b ∘ σ) + (a (σ j) + b (σ j)) • _ = _ + _
      simp only [add_smul, f, Function.comp_apply]; abel }
  have hg : Function.Injective g := fun u v h => σ.surjective.injective_comp_right (inj h)
  let e := AddEquiv.ofBijective g (Finite.injective_iff_bijective.mp hg)
  have swap_axis (a : Fin 4) : axis a ∘ σ = axis (σ a) := by
    funext l
    simp [axis, Pi.single_apply, σ, Equiv.swap_apply_eq_iff]
  refine ⟨e, ?_, ?_⟩
  · change f (axis k ∘ σ) = x
    rw [swap_axis, show σ k = j from Equiv.swap_apply_left ..]
    simp [f, axis_self]
  · intro i hi
    have hij : i ≠ j := (hi.trans_le hj).ne
    change f (axis i ∘ σ) = axis i
    rw [swap_axis, show σ i = i from Equiv.swap_apply_of_ne_of_ne hi.ne hij]
    simp [f, axis, Pi.single_eq_of_ne hij.symm]

private structure Frame (n : ℕ) (s : Finset Space) : Prop where
  card : s.card = 21
  free : ThreeAPFree (s : Set Space)
  pairs : 6 < (paired s).card
  axes : ∀ i : Fin 4, i.val < n → axis i ∈ paired s

private lemma pull {s : Finset Space} {n : ℕ} (h : Frame n s) (e : Space ≃+ Space)
    (fixes : ∀ i : Fin 4, i.val < n → e (axis i) = axis i) :
    Frame n (s.map e.symm.toEquiv.toEmbedding) := by
  let t := s.map e.symm.toEquiv.toEmbedding
  have mem (x : Space) : x ∈ t ↔ e x ∈ s := mem_map_equiv
  have pmem (x : Space) : x ∈ paired t ↔ e x ∈ paired s := by
    simp only [paired, mem_filter, mem, map_neg]
  refine ⟨(card_map _).trans h.card, ?_, ?_, ?_⟩
  · intro a ha b hb c hc he
    exact e.injective (h.free ((mem _).mp ha) ((mem _).mp hb) ((mem _).mp hc)
      (by simpa only [map_add] using congrArg e he))
  · have he : paired t = (paired s).map e.symm.toEquiv.toEmbedding := by
      ext x
      exact (pmem x).trans (mem_map_equiv (f := e.symm.toEquiv)).symm
    change 6 < (paired t).card
    rw [he, card_map]
    exact h.pairs
  · intro i hi
    exact (pmem _).mpr ((fixes i hi).symm ▸ h.axes i hi)

private lemma extend_frame {s : Finset Space} {k : Fin 4} (hk : k.val ≤ 2)
    (h : Frame k.val s) : ∃ t, Frame (k.val + 1) t := by
  have bound : addRothNumber (flat 2) < 5 :=
    addRothNumber_lt_of_forall_not_threeAPFree (by decide +kernel)
  obtain ⟨x, hx, hout⟩ : ∃ x ∈ paired s, x ∉ flat k := by
    by_contra! hin
    have hsub : paired s ⊆ flat 2 := fun x hx => mem_filter.mpr
      ⟨mem_univ _, fun j hj => (mem_filter.mp (hin x hx)).2 j (hk.trans hj)⟩
    have hl := ((h.free.mono (filter_subset ..)).le_addRothNumber hsub).trans_lt bound
    exact (not_lt_of_ge h.pairs.le) (show (paired s).card < 6 from hl.trans (by decide))
  obtain ⟨e, he, hfix⟩ := pivot hout
  let t := s.map e.symm.toEquiv.toEmbedding
  have ht := pull h e hfix
  refine ⟨t, { ht with axes := ?_ }⟩
  intro i hi
  obtain hi | heq := (Nat.le_of_lt_succ hi).lt_or_eq
  · exact ht.axes i hi
  · obtain rfl := Fin.ext heq
    simpa [paired, t, mem_map_equiv, he] using hx

private def pairedAxes : Finset Space := {axis 0, -axis 0, axis 1, -axis 1, axis 2, -axis 2}

private lemma pairedAxes_subset {s : Finset Space} (h : Frame 3 s) : pairedAxes ⊆ s := by
  have mem (i : Fin 4) (hi : i < 3) : axis i ∈ s ∧ -axis i ∈ s :=
    mem_filter.mp (h.axes i hi)
  simp only [pairedAxes, insert_subset_iff, singleton_subset_iff]
  exact ⟨(mem 0 (by decide)).1, (mem 0 (by decide)).2, (mem 1 (by decide)).1,
    (mem 1 (by decide)).2, mem 2 (by decide)⟩

private def seeds := insert (axis 3) pairedAxes

private lemma normalized {s : Finset Space} (hc : s.card = 21) (hs : ThreeAPFree (s : Set Space)) :
    ∃ t : Finset Space, Frame 3 t ∧ seeds ⊆ t := by
  obtain ⟨a, ha, hf, hp⟩ := center hc hs
  have h₀ : Frame 0 a := ⟨ha, hf, hp, by simp⟩
  obtain ⟨b, h₁⟩ := extend_frame (k := 0) (by decide) h₀
  obtain ⟨c, h₂⟩ := extend_frame (k := 1) (by decide) h₁
  obtain ⟨d, h₃⟩ := extend_frame (k := 2) (by decide) h₂
  have hsub := pairedAxes_subset h₃
  obtain ⟨x, hx, hout⟩ : ∃ x ∈ d, x ∉ flat 3 := by
    by_contra! hin
    let room := (flat 3).filter fun p => ∀ y ∈ pairedAxes, ∀ z ∈ pairedAxes, y ≠ z → -(y + z) ≠ p
    have le : d.card ≤ room.card := card_le_card fun p hp => mem_filter.mpr
      ⟨hin p hp, fun y hy z hz hne he => third_not_mem h₃.free (hsub hy) (hsub hz) hne (he ▸ hp)⟩
    have : room.card < 21 := by decide +kernel
    have := h₃.card
    omega
  obtain ⟨e, he, hfix⟩ := pivot (k := 3) hout
  have ht := pull h₃ e hfix
  exact ⟨_, ht, insert_subset (mem_map_equiv.mpr (show e (axis 3) ∈ d from he.symm ▸ hx))
    (pairedAxes_subset ht)⟩

private def corner : Space := axis 0 + axis 1 + axis 2

private def flipSigns (x : Space) : Space ≃+ Space where
  toFun z i := if x i = 2 then -z i else z i
  invFun z i := if x i = 2 then -z i else z i
  left_inv z := by funext i; dsimp; split <;> simp
  right_inv z := by funext i; dsimp; split <;> simp
  map_add' z w := by funext i; dsimp; split <;> simp [add_comm]

private def independentPairs := insert (-axis 3) seeds
private def dependentPairs := insert corner (insert (-corner) seeds)

-- A fourth pair either extends the three independent directions or lies in their span.
-- Inside that span the only available points other than the axes are the eight corners.
private lemma four_pairs {s : Finset Space} (hc : s.card = 21) (hs : ThreeAPFree (s : Set Space)) :
    ∃ t : Finset Space, t.card = 21 ∧ ThreeAPFree (t : Set Space) ∧
      (independentPairs ⊆ t ∨ dependentPairs ⊆ t) := by
  obtain ⟨a, ha, hseed⟩ := normalized hc hs
  by_cases hout : ∃ x ∈ paired a, x ∉ flat 3
  · obtain ⟨x, hx, hflat⟩ := hout
    obtain ⟨e, he, hfix⟩ := pivot (k := 3) hflat
    have ht := pull ha e hfix
    refine ⟨_, ht.card, ht.free, Or.inl (insert_subset (mem_map_equiv.mpr ?_)
      (insert_subset (mem_map_equiv.mpr ?_) (pairedAxes_subset ht)))⟩
    · change e (-axis 3) ∈ a
      simpa only [map_neg, he] using (mem_filter.mp hx).2
    · exact he.symm ▸ (mem_filter.mp hx).1
  · push Not at hout
    obtain ⟨x, hx, hother⟩ : ∃ x ∈ paired a, x ∉ pairedAxes := by
      by_contra! hin
      have := card_le_card hin
      have : pairedAxes.card = 6 := by decide +kernel
      have := ha.pairs
      omega
    have geo : ∀ x ∈ flat 3, x ∉ pairedAxes →
        (∀ y ∈ pairedAxes, ∀ z ∈ pairedAxes, y ≠ z → -(y + z) ≠ x) →
        flipSigns x corner = x ∧ ∀ y ∈ seeds, flipSigns x y ∈ seeds := by decide +kernel
    have haxes := pairedAxes_subset ha
    obtain ⟨hcorner, hseeds⟩ := geo x (hout x hx) hother (fun y hy z hz hn he =>
      third_not_mem ha.free (haxes hy) (haxes hz) hn (he ▸ (mem_filter.mp hx).1))
    let e := flipSigns x
    let t := a.map e.symm.toEquiv.toEmbedding
    have mem (z : Space) : z ∈ t ↔ e z ∈ a := mem_map_equiv
    refine ⟨t, (card_map _).trans ha.card, ?_, Or.inr ?_⟩
    · intro u hu v hv w hw he
      exact e.injective (ha.free ((mem _).mp hu) ((mem _).mp hv) ((mem _).mp hw)
        (by simpa only [map_add] using congrArg e he))
    · refine insert_subset ?_ (insert_subset ?_ (fun y hy => (mem _).mpr (hseed (hseeds y hy))))
      · exact (mem _).mpr (hcorner.symm ▸ (mem_filter.mp hx).1)
      · exact (mem _).mpr (by simpa only [map_neg, e, hcorner] using (mem_filter.mp hx).2)

-- Base-three indices let a single natural number represent a set of points.
private abbrev Index := Fin 81

private def decode (i : Index) : Space := fun j => ((i.val / 3 ^ j.val : ℕ) : ZMod 3)

private def encode (x : Space) : Index :=
  Fin.ofNat 81 ((x 0).val + 3 * (x 1).val + 9 * (x 2).val + 27 * (x 3).val)

private def coords : Space ≃ Index where
  toFun := encode
  invFun := decode
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def third (i j : Index) : Index := encode (-(decode i + decode j))

private lemma decode_third (i j : Index) : decode (third i j) = -(decode i + decode j) :=
  coords.left_inv _

private structure Row where
  point : Index
  blocked : ℕ

private def bit (v : Index) : ℕ := 2 ^ v.val

private lemma bit_mem (i j : Index) : (bit i).testBit j = decide (i = j) := by
  simp [bit, Nat.testBit_two_pow, Fin.ext_iff]

-- A row marks all points which would complete a line with its point and one already chosen.
-- Greedily remove one class of mutually incompatible points. A cap takes at most one.
private def peel (mask : ℕ) : List Row → List Row
  | [] => []
  | r :: rs =>
    if mask &&& r.blocked = mask then peel (mask ||| bit r.point) rs
    else r :: peel mask rs

private def remainder : ℕ → List Row → List Row
  | 0, rs => rs
  | n + 1, rs => remainder n (peel 0 rs)

private def consistent (t : Finset Index) (rs : List Row) : Prop :=
  ∀ r ∈ rs, r.point ∈ t → ∀ x ∈ t, r.blocked.testBit x.val = false

private def hits (t : Finset Index) (mask : ℕ) : Bool := decide (∃ x ∈ t, mask.testBit x.val = true)

private def weight (t : Finset Index) (rs : List Row) : ℕ :=
  rs.countP fun r => r.point ∈ t

private lemma peel_sub (mask : ℕ) (rs : List Row) : peel mask rs ⊆ rs := by
  induction rs generalizing mask with
  | nil => rfl
  | cons r rs ih =>
    rw [peel]
    split
    · exact fun _ h => List.mem_cons_of_mem _ (ih _ h)
    · exact List.cons_subset_cons _ (ih _)

private lemma peel_bound {t : Finset Index} (rs : List Row) (hc : consistent t rs) (m : ℕ) :
    weight t rs + (hits t m).toNat ≤ weight t (peel m rs) + 1 := by
  induction rs generalizing m with
  | nil => simp [weight, peel, Bool.toNat_le]
  | cons r rs ih =>
    have ht : consistent t rs := fun v hv => hc v (List.mem_cons_of_mem _ hv)
    have inc : (hits t m).toNat ≤ (hits t (m ||| bit r.point)).toNat := by
      cases he : hits t m
      · simp
      · obtain ⟨x, hx, hb⟩ := of_decide_eq_true he
        have hh : hits t (m ||| bit r.point) = true :=
          decide_eq_true ⟨x, hx, by simp [hb]⟩
        simp [hh]
    simp only [peel]
    split <;> rename_i h
    · have ih' := ih ht (m ||| bit r.point)
      by_cases hr : r.point ∈ t
      · have hzero : hits t m = false := by
          apply Bool.eq_false_iff.mpr
          intro hh
          obtain ⟨x, hx, hbit⟩ := of_decide_eq_true hh
          have eq := congrArg (fun n : ℕ => n.testBit x) h
          simp [Nat.testBit_and, hc r (.head _) hr x hx, hbit] at eq
        have hone : hits t (m ||| bit r.point) = true :=
          decide_eq_true ⟨r.point, hr, by simp [bit_mem]⟩
        simpa [weight, hr, hzero, hone, Nat.add_comm] using ih'
      · simp [weight, hr] at ih' ⊢
        omega
    · have ih' := ih ht m
      simp [weight, List.countP_cons] at ih' ⊢
      omega

private lemma remainder_bound {t : Finset Index} (k : ℕ) (rs : List Row) (hc : consistent t rs) :
    weight t rs ≤ weight t (remainder k rs) + k := by
  induction k generalizing rs with
  | zero => simp [remainder]
  | succ k ih =>
    have h₁ := peel_bound rs hc 0
    have h₂ := ih (peel 0 rs) (fun r hr => hc r (peel_sub _ _ hr))
    simp only [remainder]
    omega

-- Including a vertex rules out its incompatible neighbors. For each surviving row,
-- mark the third point on the line through that row and the new vertex.
private def includePoint (v : Index) (rs : List Row) : List Row :=
  (rs.filter fun r => !r.blocked.testBit v).map fun r =>
    {r with blocked := r.blocked ||| bit (third v r.point)}

private def ruledOut : ℕ → ℕ → List Row → Bool
  | 0, _, _ => false
  | fuel + 1, k, rs => Id.run do
    if k = 0 then return false
    if rs.length < k then return true
    match (remainder (k - 1) rs).getLast? with
    | none => return true
    | some r =>
      let tail := rs.filter fun q => q.point != r.point
      return ruledOut fuel k tail && ruledOut fuel (k - 1) (includePoint r.point tail)

private def contained (t : Finset Index) (rs : List Row) : Prop :=
  ∀ x ∈ t, ∃ r ∈ rs, r.point = x

private lemma card_le_weight {t : Finset Index} {rs : List Row} (hc : contained t rs) :
    t.card ≤ weight t rs := by
  let xs := (rs.filter fun r => r.point ∈ t).map Row.point
  have he : t ⊆ xs.toFinset := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hc x hx
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨r, List.mem_filter.mpr ⟨hr, decide_eq_true hx⟩, rfl⟩)
  simpa [weight, List.countP_eq_length_filter, xs] using
    (card_le_card he).trans xs.toFinset_card_le

private def noLine (t : Finset Index) : Prop :=
  ∀ x ∈ t, ∀ y ∈ t, third x y ∈ t → x = third x y

private lemma ruledOut_sound (fuel k : ℕ) (rs : List Row) {t : Finset Index}
    (hf : noLine t) (hc : consistent t rs) (hin : contained t rs)
    (he : ruledOut fuel k rs = true) : t.card < k := by
  induction fuel generalizing k rs t with
  | zero => simp [ruledOut] at he
  | succ fuel ih =>
    simp only [ruledOut, Id.run, pure] at he
    split at he
    · contradiction
    rename_i hk
    split at he
    · exact (card_le_weight hin).trans_lt (List.countP_le_length.trans_lt ‹_›)
    split at he
    · rename_i hn
      have h := remainder_bound (k - 1) rs hc
      rw [List.getLast?_eq_none_iff.mp hn] at h
      simp only [weight, List.countP_nil, zero_add] at h
      exact lt_of_le_of_lt ((card_le_weight hin).trans h) (by omega)
    · rename_i r hr
      obtain ⟨hexcl, hincl⟩ := Bool.and_eq_true_iff.mp he
      let tail := rs.filter fun q => q.point != r.point
      have htail : tail ⊆ rs := fun _ h => (List.mem_filter.mp h).1
      by_cases hp : r.point ∈ t
      · let u := t.erase r.point
        have hsub : u ⊆ t := erase_subset ..
        have hfu : noLine u := fun x hx y hy hz => hf x (hsub hx) y (hsub hy) (hsub hz)
        have hcu : consistent u (includePoint r.point tail) := by
          intro q hq hx y hy
          obtain ⟨p, hmem, rfl⟩ := List.mem_map.mp hq
          have hm := htail (List.mem_filter.mp hmem).1
          have hne : third r.point p.point ≠ y := by
            rintro rfl
            exact (ne_of_mem_erase hy) (hf r.point hp p.point (hsub hx) (hsub hy)).symm
          simp [hc p hm (hsub hx) y (hsub hy), bit_mem, hne]
        have hiu : contained u (includePoint r.point tail) := by
          intro x hx
          obtain ⟨q, hq, hqx⟩ := hin x (hsub hx)
          have hqt : q ∈ tail := List.mem_filter.mpr
            ⟨hq, by simpa [hqx] using ne_of_mem_erase hx⟩
          apply Exists.intro _
          exact ⟨List.mem_map_of_mem (List.mem_filter.mpr
            ⟨hqt, by simp [hc q hq (hqx ▸ hsub hx) r.point hp]⟩), hqx⟩
        have hlt := ih _ _ hfu hcu hiu hincl
        have heq := card_erase_add_one hp
        change (t.erase r.point).card < k - 1 at hlt
        omega
      · apply ih k tail hf (fun q hq => hc q (htail hq)) _ hexcl
        intro x hx
        obtain ⟨q, hq, rfl⟩ := hin x hx
        exact ⟨q, List.mem_filter.mpr ⟨hq, by simpa using ne_of_mem_of_not_mem hx hp⟩, rfl⟩

private def maskOf : List Index → ℕ
  | [] => 0
  | i :: is => bit i ||| maskOf is

private lemma maskOf_mem (i : Index) (xs : List Index) :
    (maskOf xs).testBit i.val = true ↔ i ∈ xs := by
  induction xs with
  | nil => simp [maskOf]
  | cons x xs ih =>
    rw [maskOf, Nat.testBit_or, Bool.or_eq_true, bit_mem, decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

private def initial (a : Finset Index) : List Row :=
  let chosen := (List.finRange 81).filter fun x => x ∈ a
  ((List.finRange 81).filter fun i => i ∉ a ∧ ∀ x ∈ a, ∀ y ∈ a, x ≠ y → third x y ≠ i).map
    fun i => ⟨i, maskOf (chosen.map (third i))⟩

private lemma extension_bound {s a : Finset Space} (hs : ThreeAPFree (s : Set Space)) (ha : a ⊆ s)
    {k : ℕ} (hc : ruledOut 81 k (initial (a.map coords.toEmbedding)) = true) :
    s.card - a.card < k := by
  let cap := s.map coords.toEmbedding
  let base := a.map coords.toEmbedding
  have hbase : base ⊆ cap := map_subset_map.mpr ha
  let t := cap \ base
  have mem (i : Index) : i ∈ cap ↔ decode i ∈ s := mem_map_equiv
  have free : noLine cap := by
    intro x hx y hy hz
    apply coords.symm.injective
    exact hs ((mem _).mp hx) ((mem _).mp hz) ((mem _).mp hy)
      (by
        change _ = decode (third x y) + decode (third x y)
        rw [twice, decode_third, neg_neg])
  have distinct {x y : Index} (hx : x ∈ cap) (hy : y ∈ cap) (hne : x ≠ y) : third x y ∉ cap := by
    intro h
    have eq : third x y = third y x := by simp [third, add_comm]
    exact hne ((free x hx y hy h).trans (eq.trans (free y hy x hx (eq ▸ h)).symm))
  have hft : noLine t := fun x hx y hy hz => free x (sdiff_subset hx) y
    (sdiff_subset hy) (sdiff_subset hz)
  have consis : consistent t (initial base) := by
    intro r hr hx y hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    apply Bool.eq_false_iff.mpr
    intro hbit
    obtain ⟨j, hj, he⟩ := List.mem_map.mp ((maskOf_mem y _).mp hbit)
    have hj' : j ∈ base := of_decide_eq_true (List.mem_filter.mp hj).2
    exact distinct (sdiff_subset hx) (hbase hj') (fun h => (mem_sdiff.mp hx).2 (h ▸ hj'))
      (he ▸ sdiff_subset hy)
  have incl : contained t (initial base) := by
    intro i hi
    obtain ⟨hcap, hnot⟩ := mem_sdiff.mp hi
    refine ⟨_, List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true ?_⟩),
      rfl⟩
    exact ⟨hnot, fun x hx y hy hne he => distinct (hbase hx) (hbase hy) hne (he ▸ hcap)⟩
  simpa [t, card_sdiff_of_subset hbase, cap, base] using ruledOut_sound 81 k _ hft consis incl hc

private lemma no_twenty_one {s : Finset Space} (hc : s.card = 21)
    (hs : ThreeAPFree (s : Set Space)) : False := by
  obtain ⟨t, ht, hf, ha | ha⟩ := four_pairs hc hs
  · have he : ruledOut 81 13 (initial (independentPairs.map coords.toEmbedding)) = true := by
      decide +kernel
    have h := extension_bound hf ha he
    have : independentPairs.card = 8 := by decide +kernel
    omega
  · have he : ruledOut 81 12 (initial (dependentPairs.map coords.toEmbedding)) = true := by
      decide +kernel
    have h := extension_bound hf ha he
    have : dependentPairs.card = 9 := by decide +kernel
    omega

end CapSetDimFour

open CapSetDimFour

/-- **Largest cap set in dimension four.** Let $\mathbb{F}_3$ be the field with three elements.
The largest subset of $\mathbb{F}_3^4$ containing no three-term arithmetic progression, that is,
no elements $a, b, c$ of the subset with $a + c = 2b$ and $a \neq b$, has exactly $20$ elements.

Over $\mathbb{F}_3$ these subsets are exactly the caps: sets with no three distinct collinear
points.

Source: G. Pellegrino, *Sul massimo ordine delle calotte in S₄,₃*, Matematiche
(Catania) 25 (1970), 149–157; OEIS A090245; listed in SqueezeBench
`SqueezeBench/Problems/CapSet/README.md`. -/
public theorem capSet_dim_four :
    addRothNumber (Finset.univ : Finset (Fin 4 → ZMod 3)) = 20 := by
  apply le_antisymm
  · apply Nat.le_of_lt_succ
    apply addRothNumber_lt_of_forall_not_threeAPFree
    intro t ht
    exact no_twenty_one (Finset.mem_powersetCard.mp ht).2
  · let quadric := Finset.univ.filter fun x : Space =>
      x ≠ 0 ∧ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = x 3 ^ 2
    have hs : ThreeAPFree (quadric : Set Space) := by decide +kernel
    have hcard : quadric.card = 20 := by decide +kernel
    exact hcard ▸ hs.le_addRothNumber (Finset.subset_univ _)

end MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted
