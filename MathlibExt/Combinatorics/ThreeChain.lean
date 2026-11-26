/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Segment
public import MathlibExt.Combinatorics.ThreeArmedV
import all MathlibExt.Combinatorics.ThreeArmedV
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Plane regions cut by three-piece chains

The maximum number of complementary regions of `n` three-piece chains is
`1 + 2 * n + 9 * n.choose 2`. We bound the increase from each new chain by cutting along its
two rays and then its segment. For attainment we construct three supporting lines per chain.
All pairwise crossings lie on the retained pieces, and extending those pieces to full lines
adds at most four regions per chain.

The construction follows the narrow chains and the extension to complete lines in Section 8 of
Cutler, Karlsson and Sloane, *Cutting a Pancake with an Exotic Knife*.
-/

namespace MetaMathlibExt.isGreatest_planeRegionCount_threeChain

open Set isGreatest_planeRegionCount_threeArmedV

-- The blocked interval D containing 1 cannot contain the left endpoint of a gap inside [0, 1].
private theorem axis_segment_bound {ι : Type*} [Fintype ι] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (T : ι → Set ℝ) (hT : ∀ i, (T i).OrdConnected)
    (D : Set ℝ) (hD : D.OrdConnected) (h₁ : 1 ∈ D) (h₀ : axis 0 ∉ U)
    (hTeq : (axis ⁻¹' U)ᶜ = (⋃ i, T i) ∪ D) :
    (regions (U \ axis '' Icc 0 1)).encard ≤ (regions U).encard + Fintype.card ι := by
  have hn₁ : 1 ∈ (axis ⁻¹' U)ᶜ := hTeq ▸ Or.inr h₁
  have heq : axis '' Icc 0 1 = axisCut (Icc 0 1) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨hx, hx.1⟩, rfl⟩
    · intro h
      exact ⟨z.1, h.1.1, Prod.ext rfl h.2.symm⟩
  rw [heq]
  apply axis_union_bound hU T hT
  · rintro J ⟨t, ht, rfl⟩ ⟨y, hy, hy₀, hy₁⟩ x hx
    have hc : IsPreconnected (connectedComponentIn (axis ⁻¹' U) t) :=
      isPreconnected_connectedComponentIn
    have hsub := connectedComponentIn_subset (axis ⁻¹' U) t
    refine ⟨le_of_not_gt fun hlt => h₀ ?_, le_of_not_gt fun hlt => hn₁ ?_⟩
    · exact hsub (hc.ordConnected.out hx hy ⟨hlt.le, hy₀⟩)
    · exact hsub (hc.ordConnected.out hy hx ⟨hy₁, hlt.le⟩)
  · exact hTeq ▸ subset_union_left
  · rintro J ⟨t, ht, rfl⟩ hsub hinf
    have hm := mem_connectedComponentIn ht
    have hbb : BddBelow (connectedComponentIn (axis ⁻¹' U) t) :=
      ⟨0, fun _ hx => (hsub hx).1⟩
    rcases (hTeq ▸ hinf : sInf (connectedComponentIn (axis ⁻¹' U) t) ∈ (⋃ i, T i) ∪ D)
      with h | h
    · exact h
    · have htD := hD.out h h₁ ⟨csInf_le hbb hm, (hsub hm).2⟩
      exact ((hTeq ▸ Or.inr htD : t ∈ (axis ⁻¹' U)ᶜ) ht).elim

private theorem convex_trace (p u : ℝ × ℝ) {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) :
    ((fun t : ℝ => p + t • u) ⁻¹' S).OrdConnected := by
  rw [← convex_iff_ordConnected, ← coe_ray_lineMap]
  exact hS.affine_preimage _

private theorem segment_bound {ι : Type*} [Fintype ι] {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (p q : ℝ × ℝ) (hp : p ∉ U) (B : ι → Set (ℝ × ℝ)) (hB : ∀ i, Convex ℝ (B i))
    (D : Set (ℝ × ℝ)) (hD : Convex ℝ D) (hq : q ∈ D) (hK : Uᶜ = (⋃ i, B i) ∪ D) :
    (regions (U \ segment ℝ p q)).encard ≤ (regions U).encard + Fintype.card ι := by
  by_cases heq : q = p
  · subst q
    rw [segment_same, sdiff_singleton_eq_self hp]
    exact le_self_add
  let v := q - p
  obtain ⟨e, he⟩ := exists_ray_homeomorph p v (sub_ne_zero.mpr heq)
  let W := e ⁻¹' U
  let g (t : ℝ) := p + t • v
  have hg : axis ⁻¹' W = g ⁻¹' U := by ext t; simp [W, g, he]
  have hWW := axis_segment_bound (U := W) (hU.preimage e.continuous) (fun i => g ⁻¹' B i)
    (fun i => convex_trace p v (hB i)) (g ⁻¹' D) (convex_trace p v hD)
    (by simpa [g, v, add_comm p] using hq)
    (by simpa [W, he] using hp)
    (by rw [hg, ← preimage_compl, hK, preimage_union, preimage_iUnion])
  have him : e '' W = U := e.surjective.image_preimage _
  have hseg : e '' (axis '' Icc 0 1) = segment ℝ p q := by
    rw [segment_eq_image', image_image]
    simp only [he, v]
  have hcut : e '' (W \ axis '' Icc 0 1) = U \ segment ℝ p q := by
    rw [image_sdiff e.injective, him, hseg]
  rw [← hcut, ← him, regions_encard_image, regions_encard_image]
  exact hWW

private def chain (p q u v : ℝ × ℝ) := ray p u ∪ segment ℝ p q ∪ ray q v

private def piece (p q u v : ℝ × ℝ) (j : Fin 3) := ![ray p u, segment ℝ p q, ray q v] j

private theorem piece_convex (p q u v : ℝ × ℝ) (j : Fin 3) : Convex ℝ (piece p q u v j) := by
  fin_cases j
  · exact ray_convex p u
  · exact convex_segment p q
  · exact ray_convex q v

private theorem piece_closed (p q u v : ℝ × ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (j : Fin 3) :
    IsClosed (piece p q u v j) := by
  fin_cases j
  · exact ray_closed _ _ hu
  · change IsClosed (segment ℝ p q)
    exact IsCompact.isClosed (by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop))
  · exact ray_closed _ _ hv

private theorem pieces_eq (p q u v : ℝ × ℝ) : (⋃ j, piece p q u v j) = chain p q u v := by
  simp [piece, chain, iUnion_fin_add_one_eq_iUnion_succ, union_assoc]

private theorem added_chain_bound {ι : Type*} [Fintype ι] (B : ι → Set (ℝ × ℝ))
    (hB : ∀ i, Convex ℝ (B i)) (hc : ∀ i, IsClosed (B i))
    (p q u v : ℝ × ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    (regions ((⋃ i, B i) ∪ chain p q u v)ᶜ).encard ≤
      (regions (⋃ i, B i)ᶜ).encard + (3 * Fintype.card ι + 2 : ℕ) := by
  let K := ⋃ i, B i
  let B' : Option ι → Set (ℝ × ℝ) := fun i => i.elim (ray p u) B
  have hB' : ∀ i, Convex ℝ (B' i) := by
    rintro (_ | i)
    · exact ray_convex _ _
    · exact hB i
  have hK : IsClosed K := isClosed_iUnion_of_finite hc
  have hK' := hK.union (ray_closed p u hu)
  have hK'' := hK'.union (ray_closed q v hv)
  have hB'eq : K ∪ ray p u = ⋃ i, B' i := by rw [iUnion_option]; exact union_comm _ _
  have h₀ := ray_union_bound hK.isOpen_compl p u hu B (fun i => convex_trace p u (hB i))
    (compl_compl K)
  have h₁ := ray_union_bound hK'.isOpen_compl q v hv B' (fun i => convex_trace q v (hB' i))
    ((compl_compl _).trans hB'eq)
  have h₂ := segment_bound hK''.isOpen_compl p q (fun h => h (Or.inl (Or.inr (tip_mem_ray p u))))
    B' hB' (ray q v) (ray_convex q v) (tip_mem_ray q v)
    (by rw [compl_compl, hB'eq])
  have hs (K S : Set (ℝ × ℝ)) : Kᶜ \ S = (K ∪ S)ᶜ := by ext; simp
  rw [hs] at h₀ h₁ h₂
  rw [show K ∪ chain p q u v = K ∪ ray p u ∪ ray q v ∪ segment ℝ p q by
    dsimp [chain]; ac_rfl]
  refine h₂.trans ((add_le_add_left h₁ _).trans
    ((add_le_add_left (add_le_add_left h₀ _) _).trans ?_))
  simp only [Fintype.card_option, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  exact le_of_eq (by ring)

private theorem all_chains_bound {n : ℕ} (p q u v : Fin n → ℝ × ℝ)
    (hu : ∀ i, u i ≠ 0 ∧ v i ≠ 0) :
    (regions (⋃ i, chain (p i) (q i) (u i) (v i))ᶜ).encard ≤ (1 + 2 * n + 9 * n.choose 2 : ℕ) := by
  classical
  let K (s : Finset (Fin n)) := ⋃ i ∈ s, chain (p i) (q i) (u i) (v i)
  have hbase : regions (univ : Set (ℝ × ℝ)) = {univ} := by
    ext x
    simp [regions, connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
  have h (s : Finset (Fin n)) :
      (regions (K s)ᶜ).encard ≤ (1 + 2 * s.card + 9 * s.card.choose 2 : ℕ) := by
    induction s using Finset.induction_on with
    | empty => simp [K, hbase]
    | @insert i s his ih =>
      let B (a : s × Fin 3) := piece (p a.1) (q a.1) (u a.1) (v a.1) a.2
      have heq : (⋃ a, B a) = K s := by
        simp only [B, K, iUnion_prod', pieces_eq, iUnion_subtype]
      have hKi : K (insert i s) = K s ∪ chain (p i) (q i) (u i) (v i) := by
        change (⋃ a ∈ insert i s, chain (p a) (q a) (u a) (v a)) =
          (⋃ a ∈ s, chain (p a) (q a) (u a) (v a)) ∪ chain (p i) (q i) (u i) (v i)
        rw [Finset.set_biUnion_insert, union_comm]
      have hi := added_chain_bound B (fun a => piece_convex _ _ _ _ _) (fun a =>
        piece_closed _ _ _ _ (hu a.1).1 (hu a.1).2 _) (p i) (q i) (u i) (v i) (hu i).1 (hu i).2
      rw [heq, ← hKi, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hi
      refine hi.trans ((add_le_add_left ih _).trans ?_)
      rw [← Nat.cast_add, Finset.card_insert_of_notMem his, Nat.choose_succ_succ' _ 1,
        Nat.choose_one_right, Nat.cast_le]
      simp only [show 1 + 1 = 2 from rfl]
      omega
  simpa [K] using h Finset.univ

/-! ## Regions of a simple arrangement of supporting lines -/

open Filter Topology

private def lineSet (b m : ℝ) : Set (ℝ × ℝ) := {z | z.1 = b + z.2 * m}

private def side {α : Type*} (b m : α → ℝ) (i : α) (z : ℝ × ℝ) : ℝ :=
  z.1 - lineAt b m i z.2

-- At a point on a line, the direction breaks the tie by selecting a side of the line.
private def label {α : Type*} (b m : α → ℝ) (z d : ℝ × ℝ) : Set α :=
  {i | 0 < side b m i z ∨ side b m i z = 0 ∧ d.2 * m i < d.1}

private theorem weak_sign {α : Type*} {b m : α → ℝ} {i : α} {z d : ℝ × ℝ} :
    (i ∈ label b m z d → lineAt b m i z.2 ≤ z.1) ∧
      (i ∉ label b m z d → z.1 ≤ lineAt b m i z.2) := by
  simp only [label, mem_ofPred_eq, side]
  constructor <;> intro h
  · rcases h with h | ⟨h, _⟩ <;> linarith
  · exact le_of_not_gt (fun hl => h (Or.inl (sub_pos.2 hl)))

private theorem label_region {α : Type*} [Finite α] (b m : α → ℝ) (z d : ℝ × ℝ)
    (hd : ∀ i, side b m i z = 0 → d.1 ≠ d.2 * m i) :
    ∃ C ∈ regions (⋃ i, lineSet (b i) (m i))ᶜ,
      ∀ p ∈ C, ∀ i, (0 < side b m i p ↔ i ∈ label b m z d) := by
  let f (t : ℝ) := z + t • d
  have step (i : α) (t : ℝ) :
      side b m i (f t) = side b m i z + t * (d.1 - d.2 * m i) := by
    simp [side, lineAt, f]
    ring
  have hev (i : α) : ∀ᶠ t in 𝓝[>] (0 : ℝ), side b m i (f t) ≠ 0 ∧
      (0 < side b m i (f t) ↔ i ∈ label b m z d) := by
    have hc : Continuous (fun t => side b m i (f t)) := by
      dsimp [side, lineAt, f]; fun_prop
    have hf : f 0 = z := by simp [f]
    rcases lt_trichotomy (side b m i z) 0 with h | h | h
    · have ht := hc.continuousAt.eventually_lt (g := fun _ => 0) continuousAt_const (hf ▸ h)
      filter_upwards [ht.filter_mono nhdsWithin_le_nhds] with t ht
      simp [ht.ne, not_lt_of_gt ht, label, h.ne, not_lt_of_gt h]
    · have hne := hd i h
      filter_upwards [self_mem_nhdsWithin (s := Ioi 0) (a := (0 : ℝ))] with t ht
      rw [step, h, zero_add]
      have ht' : 0 < t := ht
      simp [label, h, ht'.ne', sub_ne_zero.mpr hne, mul_pos_iff_of_pos_left ht']
    · have ht := continuousAt_const.eventually_lt hc.continuousAt (hf ▸ h)
      filter_upwards [ht.filter_mono nhdsWithin_le_nhds] with t ht
      simp [ht, ht.ne', label, h]
  obtain ⟨t, ht⟩ := (eventually_all.2 hev).exists
  let U := (⋃ i, lineSet (b i) (m i))ᶜ
  have nz {p : ℝ × ℝ} : p ∈ U ↔ ∀ i, side b m i p ≠ 0 := by
    simp [U, lineSet, side, lineAt, sub_ne_zero]
  have hp := nz.2 (fun i => (ht i).1)
  refine ⟨connectedComponentIn U (f t), region_at hp, ?_⟩
  intro p hp' i
  rw [← (ht i).2]
  have eqsign {x y : ℝ × ℝ} (hx : x ∈ connectedComponentIn U (f t))
      (hy : y ∈ connectedComponentIn U (f t)) (h : 0 < side b m i x) :
      0 < side b m i y := by
    by_contra! hn
    have hc : Continuous (side b m i) := by unfold side lineAt; fun_prop
    obtain ⟨w, hw, he⟩ := isPreconnected_connectedComponentIn.intermediate_value
      hy hx hc.continuousOn (show 0 ∈ Icc (side b m i y) (side b m i x) from ⟨hn, h.le⟩)
    exact nz.1 (connectedComponentIn_subset _ _ hw) i he
  exact ⟨eqsign hp' (mem_connectedComponentIn hp), eqsign (mem_connectedComponentIn hp) hp'⟩

private abbrev Cross {α : Type*} (m : α → ℝ) := {a : α × α // m a.1 < m a.2}

-- Each crossing labels the region just above it, between its two lines. The regions at
-- the bottom are indexed by the line immediately to their left, or by the empty prefix.
private theorem line_arrangement_lower {α : Type*} [Fintype α] (b m : α → ℝ)
    (hm : Function.Injective m) (z : Cross m → ℝ × ℝ) (t₀ : ℝ)
    (ht : ∀ a, t₀ < (z a).2) (hl : ∀ a, lineAt b m a.val.1 (z a).2 = (z a).1)
    (hr : ∀ a, lineAt b m a.val.2 (z a).2 = (z a).1)
    (htwo : ∀ a i, lineAt b m i (z a).2 = (z a).1 → i = a.val.1 ∨ i = a.val.2)
    (hb : Function.Injective (fun i => lineAt b m i t₀)) :
    ((1 + Fintype.card α + (Fintype.card α).choose 2 : ℕ) : ℕ∞) ≤
      (regions (⋃ i, lineSet (b i) (m i))ᶜ).encard := by
  classical
  let d (a : Cross m) : ℝ × ℝ := ((m a.val.1 + m a.val.2) / 2, 1)
  let L (a : Cross m) := label b m (z a) (d a)
  have hlmem (a : Cross m) : a.val.1 ∈ L a := by
    have h := a.2
    simp [L, label, side, hl, d]; linarith
  have hrmem (a : Cross m) : a.val.2 ∉ L a := by
    have h := a.2
    simp [L, label, side, hr, d]; linarith
  have squeeze {a : Cross m} {w e : ℝ × ℝ} (he : L a = label b m w e) :
      lineAt b m a.val.1 w.2 ≤ w.1 ∧ w.1 ≤ lineAt b m a.val.2 w.2 :=
    ⟨weak_sign.1 (he ▸ hlmem a), weak_sign.2 (he ▸ hrmem a)⟩
  have height {a : Cross m} {w e : ℝ × ℝ} (he : L a = label b m w e) : (z a).2 ≤ w.2 :=
    weakGap_height a.2 ((hl a).trans (hr a).symm) (squeeze he)
  have hLi : Function.Injective L := by
    intro a c he
    have hy := le_antisymm (height (a := a) he) (height (a := c) he.symm)
    obtain ⟨h₁, h₂⟩ := squeeze (a := c) (w := z a) he.symm
    rw [hy, hl] at h₁
    rw [hy, hr] at h₂
    have hz : z a = z c := Prod.ext (le_antisymm h₂ h₁) hy
    have ha := htwo c a.val.1 (hz ▸ hl a)
    have hb' := htwo c a.val.2 (hz ▸ hr a)
    have h := a.2
    have h' := c.2
    apply Subtype.ext
    rcases ha with h₁ | h₁ <;> rcases hb' with h₂ | h₂
    all_goals first | exact Prod.ext h₁ h₂ | exfalso; rw [h₁, h₂] at h; linarith
  let x (a : α) := lineAt b m a t₀
  obtain ⟨lo, hlo⟩ := Finite.bddBelow_range x
  let base (a : Option α) : ℝ × ℝ := (a.elim (lo - 1) x, t₀)
  let B (a : Option α) := label b m (base a) (1, 0)
  have hB (a : Option α) (i : α) : i ∈ B a ↔ x i ≤ (base a).1 := by
    simp only [B, label, mem_ofPred_eq, side, base, zero_mul, zero_lt_one, and_true]
    change 0 < _ - x i ∨ _ - x i = 0 ↔ _
    grind
  have hBi : Function.Injective B := by
    intro a c he
    have hh (i : α) := (hB a i).symm.trans ((Set.ext_iff.1 he i).trans (hB c i))
    cases a with
    | none =>
      cases c with
      | none => rfl
      | some c =>
        have h : x c ≤ lo - 1 := (hh c).2 le_rfl
        linarith [hlo (mem_range_self c)]
    | some a =>
      cases c with
      | none =>
        have h : x a ≤ lo - 1 := (hh a).1 le_rfl
        linarith [hlo (mem_range_self a)]
      | some c => exact congrArg some (hb (le_antisymm ((hh a).1 le_rfl) ((hh c).2 le_rfl)))
  let I := Option α ⊕ Cross m
  let anchor : I → ℝ × ℝ := Sum.elim base z
  let direction : I → ℝ × ℝ := Sum.elim (fun _ => (1, 0)) d
  let S (i : I) := label b m (anchor i) (direction i)
  have hSi : Function.Injective S := by
    rintro (a | a) (c | c) he
    · exact congrArg Sum.inl (hBi he)
    · exact ((ht c).not_ge (height (a := c) (w := base a) he.symm)).elim
    · exact ((ht a).not_ge (height (a := a) (w := base c) he)).elim
    · exact congrArg Sum.inr (hLi he)
  have hreg (i : I) := label_region b m (anchor i) (direction i) (by
    cases i with
    | inl a => simp [direction]
    | inr a =>
      intro k hk
      rcases htwo a k (sub_eq_zero.1 hk).symm with rfl | rfl <;>
        simp [direction, d] <;> linarith [a.2])
  choose C hC hsign using hreg
  let f (i : I) : regions (⋃ a, lineSet (b a) (m a))ᶜ := ⟨C i, hC i⟩
  have hfi : Function.Injective f := by
    intro i j he
    have hCeq : C i = C j := congrArg Subtype.val he
    obtain ⟨p, hp, hpC⟩ := hC i
    have hp' : p ∈ C i := hpC.ge (mem_connectedComponentIn hp)
    exact hSi (Set.ext fun k => ((hsign i p hp' k).symm.trans (hsign j p (hCeq ▸ hp') k)))
  let := LinearOrder.lift' m hm
  have hc : Fintype.card (Cross m) = (Fintype.card α).choose 2 := by
    change Fintype.card {p : α × α // p.1 < p.2} = _
    rw [Fintype.card_subtype, Fintype.card_product_filter_lt]
  have h := ENat.card_le_card_of_injective hfi
  rw [ENat.card_eq_coe_fintype_card] at h
  simpa [I, Fintype.card_option, hc, add_comm, add_left_comm] using h

/-! ## An arrangement of thin chains -/

-- In group i the three lines have slopes 4i, 4i + 1 and 4i + 2 as functions of height.
-- Their intercept offsets 1, 0 and 1 put their bends at heights -1 and 1 and their
-- self-crossing at height 0. All three pieces cover the entire strip between the bends.
private abbrev Strand (n : ℕ) := Fin n × Fin 3
private def slope {n : ℕ} (a : Strand n) : ℝ := (4 * a.1.val + a.2.val : ℕ)
private def offset (j : Fin 3) : ℝ := (j.val - 1 : ℝ) ^ 2

private theorem slope_inj {n : ℕ} : Function.Injective (@slope n) := by
  intro a b he
  have h : 4 * a.1.val + a.2.val = 4 * b.1.val + b.2.val := by
    unfold slope at he
    exact_mod_cast he
  apply Prod.ext <;> apply Fin.ext <;> omega

open Polynomial in
private noncomputable def ordinate {n : ℕ} (a : Strand n) : ℝ[X] :=
  X ^ (a.1.val + 1) + C (offset a.2)

open Polynomial in
private noncomputable def determinant {n : ℕ} (a b c : Strand n) : ℝ[X] :=
  ordinate a * C (slope b - slope c) + ordinate b * C (slope c - slope a) +
    ordinate c * C (slope a - slope b)

open Polynomial in
private theorem determinant_ne {n : ℕ} (a b c : Strand n) (hab : a ≠ b) (hbc : b ≠ c)
    (hca : c ≠ a) : determinant a b c ≠ 0 := by
  have coef (a b c : Strand n) (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) :
      (determinant a b c).coeff (a.1.val + 1) = slope b - slope c := by
    have hb : a.1.val ≠ b.1.val := fun he => hab (Fin.ext he)
    have hc : a.1.val ≠ c.1.val := fun he => hac (Fin.ext he)
    simp only [determinant, ordinate, coeff_add, coeff_mul_C, coeff_X_pow]
    simp [hb, hc]
  have single (a b c : Strand n) (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b ≠ c) :
      determinant a b c ≠ 0 := by
    intro he
    have h := coef a b c hab hac
    rw [he, coeff_zero, eq_comm, sub_eq_zero] at h
    exact hbc (slope_inj h)
  have cyc (a b c : Strand n) : determinant a b c = determinant b c a := by
    unfold determinant
    abel
  by_cases ha : a.1 = b.1
  · by_cases hb : b.1 = c.1
    · obtain ⟨i, j⟩ := a
      obtain ⟨i', k⟩ := b
      obtain ⟨i'', l⟩ := c
      change i = i' at ha
      change i' = i'' at hb
      subst i'; subst i''
      intro he
      have h := congrArg (fun f : ℝ[X] => f.eval 0) he
      have h₁ : (j.val : ℝ) ≠ k.val := fun he => hab (Prod.ext rfl (Fin.ext (by exact_mod_cast he)))
      have h₂ : (k.val : ℝ) ≠ l.val := fun he => hbc (Prod.ext rfl (Fin.ext (by exact_mod_cast he)))
      have h₃ : (l.val : ℝ) ≠ j.val := fun he => hca (Prod.ext rfl (Fin.ext (by exact_mod_cast he)))
      apply mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h₁) (sub_ne_zero.mpr h₂)) (sub_ne_zero.mpr h₃)
      simp [determinant, ordinate, slope, offset] at h
      linear_combination -h
    · rw [cyc, cyc b]
      exact single c a b (by simpa [ha] using Ne.symm hb) (Ne.symm hb) hab
  · by_cases hc : a.1 = c.1
    · rw [cyc]
      exact single b c a (hc ▸ Ne.symm ha) (Ne.symm ha) hca
    · exact single a b c ha hc hbc

private def intercept {n : ℕ} (s : ℝ) (a : Strand n) : ℝ := s ^ (a.1.val + 1) + offset a.2

-- The parameter s shifts group i horizontally by s^(i+1). A triple concurrence forces s
-- to be a root of a nonzero determinant polynomial, excluding only finitely many values.
open Polynomial in
private theorem choose_intercepts (n : ℕ) :
    ∃ s ∈ Ioo (0 : ℝ) 1, ∀ (a b c : Strand n) (t : ℝ),
      a ≠ b → lineAt (intercept s) slope a t = lineAt (intercept s) slope b t →
      lineAt (intercept s) slope c t = lineAt (intercept s) slope a t → c = a ∨ c = b := by
  classical
  let fs := (Finset.univ : Finset (Strand n × Strand n × Strand n)).image
    (fun x => determinant x.1 x.2.1 x.2.2)
  let bad := ⋃ f ∈ (fs.erase 0 : Finset ℝ[X]), {x | f.IsRoot x}
  have hbad : bad.Finite := (fs.erase 0).finite_toSet.biUnion (fun f hf =>
    finite_setOfPred_isRoot (Finset.mem_erase.1 hf).1)
  obtain ⟨s, hs, hs'⟩ := (Ioo_infinite (zero_lt_one : (0 : ℝ) < 1)).exists_notMem_finite hbad
  refine ⟨s, hs, ?_⟩
  intro a b c t hab h₁ h₂
  by_contra! h
  have hf : determinant a b c ∈ fs.erase 0 := Finset.mem_erase.mpr
    ⟨determinant_ne a b c hab h.2.symm h.1,
      Finset.mem_image.mpr ⟨(a, b, c), Finset.mem_univ _, rfl⟩⟩
  apply hs' (mem_iUnion₂_of_mem hf ?_)
  change (determinant a b c).eval s = 0
  simp only [determinant, ordinate, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  dsimp [lineAt, intercept] at h₁ h₂
  linear_combination (slope a - slope c) * h₁ + (slope a - slope b) * h₂

private theorem cross_height {n : ℕ} {s : ℝ} (hs : s ∈ Ioo 0 1) {a b : Strand n} (hab : a ≠ b)
    {t : ℝ} (he : lineAt (intercept s) slope a t = lineAt (intercept s) slope b t) :
    t ∈ Icc (-1) 1 := by
  have hpos (i : Fin n) : 0 < s ^ (i.val + 1) := pow_pos hs.1 _
  have hlt (i : Fin n) : s ^ (i.val + 1) < 1 := pow_lt_one₀ hs.1.le hs.2 (by omega)
  have hoff (j : Fin 3) : offset j = 0 ∨ offset j = 1 := by
    fin_cases j <;> norm_num [offset, Fin.isValue]
  have hsep (a b : Strand n) (hh : a.1 < b.1) : slope a + 2 ≤ slope b := by
    change ↑(4 * a.1.val + a.2.val) + (2 : ℝ) ≤ ↑(4 * b.1.val + b.2.val)
    exact_mod_cast (show 4 * a.1.val + a.2.val + 2 ≤ 4 * b.1.val + b.2.val by
      change a.1.val < b.1.val at hh
      omega)
  have hdiff (a b : Strand n) : intercept s a - intercept s b < 2 := by
    rcases hoff a.2 with ha | ha <;> rcases hoff b.2 with hb | hb <;>
      simp only [intercept, ha, hb] <;> linarith [hpos b.1, hlt a.1]
  have different_groups (a b : Strand n) (hh : a.1 < b.1)
      (he : lineAt (intercept s) slope a t = lineAt (intercept s) slope b t) :
      t ∈ Icc (-1) 1 := by
    dsimp [lineAt] at he
    have hg := hsep a b hh
    constructor
    · by_contra! hn
      nlinarith [hdiff b a, mul_neg_of_neg_of_pos (show t + 1 < 0 by linarith)
        (show 0 < slope b - slope a by linarith)]
    · by_contra! hn
      nlinarith [hdiff a b, mul_pos (show 0 < t - 1 by linarith)
        (show 0 < slope b - slope a by linarith)]
  rcases lt_trichotomy a.1 b.1 with hh | hh | hh
  · exact different_groups a b hh he
  · obtain ⟨i, j⟩ := a
    obtain ⟨i', k⟩ := b
    change i = i' at hh
    subst i'
    fin_cases j <;> fin_cases k <;> first | exact (hab rfl).elim |
      (norm_num [lineAt, intercept, offset, slope, Fin.isValue] at he; constructor <;> linarith)
  · exact different_groups b a hh he.symm

private def atHeight {n : ℕ} (s : ℝ) (a : Strand n) (t : ℝ) : ℝ × ℝ :=
  (lineAt (intercept s) slope a t, t)

private theorem full_lower {n : ℕ} {s : ℝ} (hs : s ∈ Ioo 0 1)
    (hsimple : ∀ (a b c : Strand n) (t : ℝ),
      a ≠ b → lineAt (intercept s) slope a t = lineAt (intercept s) slope b t →
      lineAt (intercept s) slope c t = lineAt (intercept s) slope a t → c = a ∨ c = b) :
    ((1 + n * 3 + (n * 3).choose 2 : ℕ) : ℕ∞) ≤
      (regions (⋃ a : Strand n, lineSet (intercept s a) (slope a))ᶜ).encard := by
  let t (e : Cross (@slope n)) :=
    (intercept s e.val.1 - intercept s e.val.2) / (slope e.val.2 - slope e.val.1)
  let z (e : Cross (@slope n)) := atHeight s e.val.1 (t e)
  have he (e : Cross (@slope n)) :
      lineAt (intercept s) slope e.val.1 (t e) = lineAt (intercept s) slope e.val.2 (t e) := by
    have h := div_mul_cancel₀ (intercept s e.val.1 - intercept s e.val.2) (sub_pos.2 e.2).ne'
    dsimp [lineAt, t]
    linear_combination -h
  have hne (e : Cross (@slope n)) : e.val.1 ≠ e.val.2 := fun h => e.2.ne (congrArg slope h)
  have h := line_arrangement_lower (intercept s) slope slope_inj z (-2)
    (fun e => by change (-2 : ℝ) < t e; linarith [(cross_height hs (hne e) (he e)).1])
    (fun _ => rfl) (fun e => (he e).symm)
    (fun e c hc => hsimple _ _ c _ (hne e) (he e) hc)
    (fun a b h => by
      by_contra hh
      have h' := (cross_height hs hh h).1
      norm_num at h')
  simpa [Strand, Fintype.card_prod] using h

private theorem free_ray_bound {K : Set (ℝ × ℝ)} (hK : IsClosed K) (p u : ℝ × ℝ)
    (hu : u ≠ 0) (hp : p ∈ K) (hfree : ∀ t : ℝ, 0 < t → p + t • u ∉ K) :
    (regions (K ∪ ray p u)ᶜ).encard ≤ (regions Kᶜ).encard + 1 := by
  obtain ⟨e, he⟩ := exists_ray_homeomorph p u hu
  let W := e ⁻¹' Kᶜ
  have hW : IsOpen W := hK.isOpen_compl.preimage e.continuous
  have hsub : Ioi 0 ⊆ axis ⁻¹' W := by
    intro x hx
    change e (axis x) ∉ K
    rw [he]
    exact hfree x hx
  have hcl : closure (Ioi 0) ∩ axis ⁻¹' W ⊆ Ioi 0 := by
    rw [closure_Ioi]
    rintro x ⟨hx, hxW⟩
    refine lt_of_le_of_ne hx ?_
    rintro rfl
    exact hxW (by simpa [he] using hp : e (axis 0) ∈ K)
  have h := axis_cut_region_bound hW isOpen_Ioi isPreconnected_Ioi nonempty_Ioi hsub hcl
  have him : e '' W = Kᶜ := e.surjective.image_preimage _
  have heq : axisCut (closure (Ioi 0)) = axisCut univ := by simp [axisCut, closure_Ioi]
  have hcut : e '' (W \ axisCut (closure (Ioi 0))) = (K ∪ ray p u)ᶜ := by
    rw [heq, image_sdiff e.injective, him, ray_image_axisCut p u e he]
    ext x; simp
  rw [← hcut, ← him, regions_encard_image, regions_encard_image]
  have hn : ¬ ((Ioi (0 : ℝ)) ∩ Iio 0).Nonempty := fun ⟨_, ha, hb⟩ => ha.not_ge hb.le
  simpa [hn] using h

private theorem extend_rays {α : Type*} [Fintype α] (K : Set (ℝ × ℝ)) (hK : IsClosed K)
    (p u : α → ℝ × ℝ) (hu : ∀ i, u i ≠ 0) (hp : ∀ i, p i ∈ K)
    (hfree : ∀ i (t : ℝ), 0 < t → p i + t • u i ∉ K)
    (hpair : ∀ i j, i ≠ j → ∀ t : ℝ, 0 < t → p i + t • u i ∉ ray (p j) (u j)) :
    (regions (K ∪ ⋃ i, ray (p i) (u i))ᶜ).encard ≤ (regions Kᶜ).encard + Fintype.card α := by
  classical
  let A (s : Finset α) := K ∪ ⋃ j ∈ s, ray (p j) (u j)
  have hs (s : Finset α) :
      (regions (A s)ᶜ).encard ≤ (regions Kᶜ).encard + (s.card : ℕ∞) := by
    induction s using Finset.induction_on with
    | empty => simp [A]
    | @insert a s ha ih =>
      have hcl : IsClosed (A s) := hK.union (isClosed_biUnion_finset (fun j _ =>
        ray_closed _ _ (hu j)))
      have h := free_ray_bound hcl (p a) (u a) (hu a) (Or.inl (hp a)) (by
        intro t ht
        rintro (hk | hs)
        · exact hfree a t ht hk
        · obtain ⟨j, hj, hmem⟩ := mem_iUnion₂.1 hs
          exact hpair a j (fun he => ha (he ▸ hj)) t ht hmem)
      have heq : A (insert a s) = A s ∪ ray (p a) (u a) := by
        simp [A, union_left_comm, union_comm]
      rw [heq, Finset.card_insert_of_notMem ha, Nat.cast_add_one]
      exact h.trans ((add_le_add_left ih _).trans_eq (add_assoc ..))
  simpa [A] using hs Finset.univ

private def stroke {n : ℕ} (s : ℝ) (a : Strand n) (D : Set ℝ) : Set (ℝ × ℝ) :=
  lineSet (intercept s a) (slope a) ∩ Prod.snd ⁻¹' D

private def domain (j : Fin 3) : Set ℝ := ![Iic 1, Icc (-1) 1, Ici (-1)] j

private def core {n : ℕ} (s : ℝ) := ⋃ a : Strand n, stroke s a (domain a.2)

private theorem closed_core (n : ℕ) (s : ℝ) : IsClosed (@core n s) := by
  apply isClosed_iUnion_of_finite
  intro a
  apply IsClosed.inter (isClosed_eq continuous_fst (by fun_prop))
  apply IsClosed.preimage continuous_snd
  obtain ⟨i, j⟩ := a
  fin_cases j
  · exact isClosed_Iic
  · exact isClosed_Icc
  · exact isClosed_Ici

private def sign (b : Bool) : ℝ := if b then 1 else -1
private def reach (b : Bool) (h : ℝ) : Set ℝ := if b then Ici h else Iic h

private theorem along {n : ℕ} (s : ℝ) (a : Strand n) (h r : ℝ) (b : Bool) :
    atHeight s a h + r • (sign b • (slope a, (1 : ℝ))) =
      atHeight s a (h + r * sign b) := by
  apply Prod.ext <;> simp [atHeight, lineAt]
  ring

private theorem ray_eq_stroke {n : ℕ} (s : ℝ) (a : Strand n) (h : ℝ) (b : Bool) :
    ray (atHeight s a h) (sign b • (slope a, (1 : ℝ))) = stroke s a (reach b h) := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp only [along]
    refine ⟨rfl, ?_⟩
    change h + r * sign b ∈ reach b h
    cases b <;> simpa [reach, sign] using hr
  · rintro ⟨hz, ht⟩
    change z.1 = intercept s a + z.2 * slope a at hz
    have heq : atHeight s a z.2 = z := Prod.ext hz.symm rfl
    cases b
    · refine ⟨h - z.2, sub_nonneg.2 (show z.2 ≤ h from ht), ?_⟩
      simp only [along]; simpa [sign] using heq
    · refine ⟨z.2 - h, sub_nonneg.2 (show h ≤ z.2 from ht), ?_⟩
      simp only [along]; simpa [sign] using heq

private theorem segment_eq_stroke {n : ℕ} (s : ℝ) (a : Strand n) :
    segment ℝ (atHeight s a (-1)) (atHeight s a 1) = stroke s a (Icc (-1) 1) := by
  rw [segment_eq_image']
  ext z
  constructor
  · rintro ⟨t, ⟨ht, ht'⟩, rfl⟩
    constructor
    · change _ + _ * (_ - _) = _ + (_ + _ * (_ - _)) * _
      dsimp [atHeight, lineAt]
      ring
    · change -1 ≤ -1 + t * (1 - -1) ∧ -1 + t * (1 - -1) ≤ (1 : ℝ)
      constructor <;> linarith
  · rintro ⟨hz, ht⟩
    change z.1 = intercept s a + z.2 * slope a at hz
    obtain ⟨h₁, h₂⟩ := ht
    refine ⟨(z.2 + 1) / 2, ⟨by change -1 ≤ z.2 at h₁; linarith,
      by change z.2 ≤ 1 at h₂; linarith⟩, ?_⟩
    apply Prod.ext <;> simp [atHeight, lineAt, hz] <;> ring

private def lowerTip {n : ℕ} (s : ℝ) (i : Fin n) := atHeight s (i, 1) (-1)
private def upperTip {n : ℕ} (s : ℝ) (i : Fin n) := atHeight s (i, 1) 1
private def rising {n : ℕ} (i : Fin n) : ℝ × ℝ := (slope (i, 2), 1)
private def falling {n : ℕ} (i : Fin n) : ℝ × ℝ := -(slope (i, 0), 1)

private theorem core_eq_chains (n : ℕ) (s : ℝ) : @core n s =
    ⋃ i : Fin n, chain (lowerTip s i) (upperTip s i) (rising i) (falling i) := by
  rw [core, iUnion_prod']
  congr 1; funext i
  have hp : lowerTip s i = atHeight s (i, 2) (-1) := by
    refine Prod.ext ?_ rfl
    simp [lowerTip, atHeight, lineAt, intercept, slope, offset]; ring
  have hq : upperTip s i = atHeight s (i, 0) 1 := by
    refine Prod.ext ?_ rfl
    simp [upperTip, atHeight, lineAt, intercept, slope, offset]; ring
  have ha := ray_eq_stroke s (i, 2) (-1) true
  have hb := ray_eq_stroke s (i, 0) 1 false
  simp only [sign, ↓reduceIte, one_smul, neg_smul, Bool.false_eq_true] at ha hb
  change _ = ray (lowerTip s i) (rising i) ∪ segment ℝ (lowerTip s i) (upperTip s i) ∪
    ray (upperTip s i) (falling i)
  rw [show ray (lowerTip s i) (rising i) = stroke s (i, 2) (Ici (-1)) from hp ▸ ha,
    show ray (upperTip s i) (falling i) = stroke s (i, 0) (Iic 1) from hq ▸ hb,
    lowerTip, upperTip, segment_eq_stroke]
  calc
    _ = stroke s (i, 0) (Iic 1) ∪
        (stroke s (i, 1) (Icc (-1) 1) ∪ stroke s (i, 2) (Ici (-1))) := by
      simp [iUnion_fin_add_one_eq_iUnion_succ, domain]
    _ = _ := by ac_rfl

private abbrev Tail (n : ℕ) := Fin n × Bool × Fin 2
private def strand {n : ℕ} (a : Tail n) : Strand n :=
  (a.1, if a.2.1 then a.2.2.castSucc else a.2.2.succ)
private def tailTip {n : ℕ} (s : ℝ) (a : Tail n) := atHeight s (strand a) (sign a.2.1)
private def tailDir {n : ℕ} (a : Tail n) := sign a.2.1 • (slope (strand a), (1 : ℝ))

private theorem tail_dir_ne {n : ℕ} (a : Tail n) : tailDir a ≠ 0 := by
  intro hz
  have h := congrArg Prod.snd hz
  rcases a with ⟨i, b, k⟩
  cases b <;> norm_num [tailDir, sign] at h

private theorem core_and_tails (n : ℕ) (s : ℝ) :
    @core n s ∪ ⋃ a : Tail n, ray (tailTip s a) (tailDir a) =
      ⋃ a : Strand n, lineSet (intercept s a) (slope a) := by
  have htail (a : Tail n) := ray_eq_stroke s (strand a) (sign a.2.1) a.2.1
  ext p
  constructor
  · rintro (h | h)
    · obtain ⟨a, ha⟩ := mem_iUnion.1 h
      exact mem_iUnion_of_mem a ha.1
    · obtain ⟨a, ha⟩ := mem_iUnion.1 h
      exact mem_iUnion_of_mem (strand a) ((htail a) ▸ ha : p ∈ stroke _ _ _).1
  · rintro hp
    obtain ⟨⟨i, j⟩, hi⟩ := mem_iUnion.1 hp
    by_cases h : p.2 ∈ domain j
    · exact Or.inl (mem_iUnion_of_mem (i, j) ⟨hi, h⟩)
    · refine Or.inr ?_
      have hh (b : Bool) (k : Fin 2) (hj : strand (i, b, k) = (i, j))
          (ht : p.2 ∈ reach b (sign b)) : p ∈ ⋃ a : Tail n, ray (tailTip s a) (tailDir a) :=
        mem_iUnion_of_mem (i, b, k) ((htail (i, b, k)).ge ⟨hj ▸ hi, ht⟩)
      fin_cases j
      · exact hh true 0 rfl (le_of_not_ge h)
      · change ¬ (-1 ≤ p.2 ∧ p.2 ≤ 1) at h
        rcases le_or_gt (-1) p.2 with h' | h'
        · exact hh true 1 rfl (le_of_not_ge fun h'' => h ⟨h', h''⟩)
        · exact hh false 0 rfl h'.le
      · exact hh false 1 rfl (le_of_not_ge h)

-- Outside the strip there are no intersections between different supporting lines. Each
-- missing ray starts on its chain and can increase the component count by at most one.
private theorem tails_bound {n : ℕ} {s : ℝ} (hs : s ∈ Ioo 0 1) :
    (regions (⋃ a : Strand n, lineSet (intercept s a) (slope a))ᶜ).encard ≤
      (regions (@core n s)ᶜ).encard + ↑(4 * n : ℕ) := by
  have hout (a : Tail n) (r : ℝ) (hr : 0 < r) :
      sign a.2.1 + r * sign a.2.1 ∉ Icc (-1) 1 := by
    rcases a with ⟨i, b, k⟩
    rintro ⟨hl, hu⟩
    cases b <;> simp [sign] at hl hu <;> linarith
  have htrace (a : Tail n) (r : ℝ) (hr : 0 < r) (c : Strand n)
      (hc : tailTip s a + r • tailDir a ∈ lineSet (intercept s c) (slope c)) : strand a = c := by
    change atHeight s (strand a) (sign a.2.1) + r • _ ∈ _ at hc
    rw [tailDir, along] at hc
    by_contra h
    exact hout a r hr (cross_height hs h hc)
  have h := extend_rays (@core n s) (closed_core n s) (tailTip s) tailDir tail_dir_ne (by
    intro a
    apply mem_iUnion_of_mem (strand a)
    refine ⟨rfl, ?_⟩
    rcases a with ⟨i, b, k⟩
    cases b <;> fin_cases k <;> norm_num [strand, sign, domain, tailTip, atHeight, Fin.isValue])
    (by
      intro a r hr hk
      obtain ⟨c, hc⟩ := mem_iUnion.1 hk
      have he := htrace a r hr c hc.1
      subst c
      have ht := hc.2
      change (sign a.2.1 + r * (sign a.2.1 * 1)) ∈ domain (strand a).2 at ht
      rcases a with ⟨i, b, k⟩
      cases b <;> fin_cases k <;> simp [sign, strand, domain, Fin.isValue] at ht <;> linarith)
    (by
      intro a b hab r hr hmem
      rw [show ray (tailTip s b) (tailDir b) = _ from
        ray_eq_stroke s (strand b) (sign b.2.1) b.2.1] at hmem
      have he := htrace a r hr (strand b) hmem.1
      have ht := hmem.2
      change sign a.2.1 + r * (sign a.2.1 * 1) ∈ reach b.2.1 (sign b.2.1) at ht
      obtain ⟨i, b₁, k⟩ := a
      obtain ⟨j, b₂, l⟩ := b
      have hi : i = j := congrArg Prod.fst he
      subst j
      have hj := congrArg Prod.snd he
      cases b₁ <;> cases b₂
      · exact hab (congrArg (fun k : Fin 2 => (i, false, k)) (Fin.succ_inj.mp hj))
      · simp [sign, reach] at ht; linarith
      · simp [sign, reach] at ht; linarith
      · exact hab (congrArg (fun k : Fin 2 => (i, true, k)) (Fin.castSucc_inj.mp hj)))
  rw [core_and_tails] at h
  simpa [Tail, Fintype.card_prod, mul_comm, mul_assoc] using h

private theorem attained (n : ℕ) : ∃ (p q u v : Fin n → ℝ × ℝ),
    (∀ i, u i ≠ 0 ∧ v i ≠ 0) ∧
    1 + 2 * n + 9 * n.choose 2 = planeRegionCount (⋃ i, chain (p i) (q i) (u i) (v i)) := by
  obtain ⟨s, hs, hsimple⟩ := choose_intercepts n
  have hdir (i : Fin n) : rising i ≠ 0 ∧ falling i ≠ 0 := by
    constructor <;> intro h <;> have he := congrArg Prod.snd h <;> norm_num [rising, falling] at he
  refine ⟨lowerTip s, upperTip s, rising, falling, hdir, ?_⟩
  have hupper := all_chains_bound (lowerTip s) (upperTip s) rising falling hdir
  have hlower := (full_lower hs hsimple).trans (tails_bound hs)
  have doubleChoose (k : ℕ) : 2 * k.choose 2 + k = k ^ 2 := by
    induction k with
    | zero => decide
    | succ k ih => rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]; nlinarith
  have harith : 1 + n * 3 + (n * 3).choose 2 = (1 + 2 * n + 9 * n.choose 2) + 4 * n := by
    nlinarith [doubleChoose n, doubleChoose (n * 3)]
  rw [harith, Nat.cast_add] at hlower
  have h := (ENat.add_le_add_iff_right (ENat.natCast_ne_top _)).1 hlower
  rw [core_eq_chains] at h
  simpa only [planeRegionCount, regions, Set.ncard, ENat.toNat_natCast] using
    congrArg ENat.toNat (le_antisymm h hupper)

end MetaMathlibExt.isGreatest_planeRegionCount_threeChain

namespace MetaMathlibExt

open isGreatest_planeRegionCount_threeChain isGreatest_planeRegionCount_threeArmedV in
/-- **Maximum region count for 3-chains.** For points $p, q \in \mathbb{R}^2$ and nonzero vectors
$u, v \in \mathbb{R}^2$, the 3-chain is the union of the ray $\{p + s u : s \ge 0\}$, the segment
$[p, q]$ and the ray $\{q + s v : s \ge 0\}$; the directions are arbitrary and the 3-chain may
intersect itself. For every natural number $n$, the largest number of regions into which the
union of $n$ 3-chains can divide the plane is $(9n^2 - 5n + 2)/2$.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Theorem 1
(`jis-2026-26.4.5-thm-1`), with the definition in the section *The k-chain*. -/
public theorem isGreatest_planeRegionCount_threeChain (n : ℕ) :
    IsGreatest {N : ℕ | ∃ (p q u v : Fin n → ℝ × ℝ), (∀ i, u i ≠ 0 ∧ v i ≠ 0) ∧
        N = planeRegionCount (⋃ i, ((fun s : ℝ => p i + s • u i) '' Set.Ici 0 ∪
          segment ℝ (p i) (q i) ∪ (fun s : ℝ => q i + s • v i) '' Set.Ici 0))}
      ((9 * n ^ 2 - 5 * n + 2) / 2) := by
  rw [← max_count_nat]
  constructor
  · exact attained n
  · rintro N ⟨p, q, u, v, hu, rfl⟩
    have h := all_chains_bound p q u v hu
    have hf := Set.encard_lt_top_iff.1 (h.trans_lt (ENat.natCast_lt_top _))
    rw [← hf.cast_ncard_eq, Nat.cast_le] at h
    exact h

end MetaMathlibExt
