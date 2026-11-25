/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Finset.Sym
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Edmonds' matching polytope theorem

`matchingPolytope_eq` describes the convex hull of the incidence vectors of matchings by the
vertex degree and odd-set inequalities, together with nonnegativity.

The proof studies nonnegative edge weights for which every matching has weight at most one.
At an extreme point of this set, it suffices to identify a degree or odd-set inequality tight on
all maximum-weight matchings of the positive-weight edges. If no vertex is always covered, two
vertices are related when they are equal or cannot both be missed by an optimal matching.
Exchanging parts of two optimal matchings proves transitivity. The class containing the endpoints
of a positive-weight edge then supplies a tight odd set.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MatchingPolytopeWanted

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open Classical in
/-- **Incidence vector of a subgraph's edges.** The vector in `ℝ^E` (indexed by the edges of `G`)
that is `1` on the edges of `M` and `0` elsewhere (Schrijver, *A Course in Combinatorial
Optimization*, §5.4, footnote 18). -/
noncomputable def edgeIncidence (M : G.Subgraph) : G.edgeSet → ℝ :=
  fun e => if (e : Sym2 V) ∈ M.edgeSet then 1 else 0

/-- **Matching polytope.** The convex hull in `ℝ^E` of the incidence vectors of the matchings of
`G` (Schrijver, *A Course in Combinatorial Optimization*, §5.4, eq. (29)). -/
def matchingPolytope : Set (G.edgeSet → ℝ) :=
  convexHull ℝ {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = edgeIncidence G M}

/-- **Perfect matching polytope.** The convex hull in `ℝ^E` of the incidence vectors of the perfect
matchings of `G` (Schrijver, *A Course in Combinatorial Optimization*, §5.4, eq. (26)). -/
def perfectMatchingPolytope : Set (G.edgeSet → ℝ) :=
  convexHull ℝ {x | ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = edgeIncidence G M}

namespace WeightProof

variable {V E : Type*} (ends : E → Finset V)

private abbrev covered [DecidableEq V] (M : Finset E) := M.biUnion ends

private abbrev matching (M : Finset E) := (M : Set E).PairwiseDisjoint ends

private def inside [DecidableEq V] (M : Finset E) (U : Finset V) := M.filter (fun e => ends e ⊆ U)

private def closedOn (M : Finset E) (U : Finset V) :=
  ∀ e ∈ M, ∀ v ∈ ends e, v ∈ U → ends e ⊆ U

private theorem covered_inside [DecidableEq V] {M : Finset E} {S : Finset V}
    (hc : closedOn ends M S) :
    covered ends (inside ends M S) = covered ends M ∩ S := by
  ext v
  simp only [inside, covered, mem_biUnion, mem_filter, mem_inter]
  constructor
  · rintro ⟨e, ⟨he, hs⟩, hv⟩
    exact ⟨⟨e, he, hv⟩, hs hv⟩
  · rintro ⟨⟨e, he, hv⟩, hs⟩
    exact ⟨e, ⟨he, hc e he v hv hs⟩, hv⟩

private theorem covered_card [DecidableEq V] (h₂ : ∀ e, (ends e).card = 2) {M : Finset E}
    (hm : matching ends M) : (covered ends M).card = M.card * 2 := by
  rw [covered, card_biUnion hm]
  simp [h₂]

-- A largest set containing the starting vertex and at least |S| − 1 internal edges is closed
-- under both edge sets. Adding the other endpoint of a crossing edge preserves the count.
private theorem exists_closed_set [Finite V] [DecidableEq V]
    (h₂ : ∀ e, (ends e).card = 2) (A B : Finset E) (v : V) :
    ∃ S : Finset V, v ∈ S ∧ closedOn ends A S ∧ closedOn ends B S ∧
      S.card ≤ (inside ends A S).card + (inside ends B S).card + 1 := by
  classical
  let _ := Fintype.ofFinite V
  let P (s : Finset V) := v ∈ s ∧ s.card ≤ (inside ends A s).card + (inside ends B s).card + 1
  have hstart : P {v} := ⟨by simp, by simp⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (univ.filter P) Finset.card
    ⟨{v}, mem_filter.mpr ⟨mem_univ _, hstart⟩⟩
  obtain ⟨hv, hsize⟩ := (mem_filter.mp hS).2
  have grow (M N : Finset E) (hne : S.card ≤ (inside ends M S).card + (inside ends N S).card + 1)
      (horder : ∀ s, (inside ends M s).card + (inside ends N s).card =
        (inside ends A s).card + (inside ends B s).card) : closedOn ends M S := by
    intro e he u hue hu z hz
    by_contra hzs
    have huz : u ≠ z := fun h => hzs (h ▸ hu)
    have hpair : ends e = {u, z} :=
      (Finset.eq_of_subset_of_card_le (by simpa [insert_subset_iff] using And.intro hue hz :
        ({u, z} : Finset V) ⊆ ends e) (by simp [h₂, huz])).symm
    let s := insert z S
    have hin (F : Finset E) : inside ends F S ⊆ inside ends F s :=
      fun i hi => mem_filter.mpr ⟨(mem_filter.mp hi).1,
        (mem_filter.mp hi).2.trans (subset_insert z S)⟩
    have hlt : (inside ends M S).card < (inside ends M s).card := by
      apply card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hin M, fun heq => hzs ?_⟩
      have him : e ∈ inside ends M s :=
        mem_filter.mpr ⟨he, by simp [s, hpair, hu, insert_subset_iff]⟩
      have := (mem_filter.mp (heq.symm ▸ him : e ∈ inside ends M S)).2
      exact this hz
    have hns := card_le_card (hin N)
    have hsc : s.card = S.card + 1 := card_insert_of_notMem hzs
    have hp : P s := ⟨mem_insert_of_mem hv, by rw [← horder]; omega⟩
    have := hmax s (mem_filter.mpr ⟨mem_univ _, hp⟩)
    omega
  exact ⟨S, hv, grow A B hsize (fun _ => rfl),
    grow B A (by omega) (fun _ => Nat.add_comm ..), hsize⟩

private theorem swap_matching [DecidableEq V] [DecidableEq E] {A B : Finset E} {S : Finset V}
    (ha : matching ends A) (hb : matching ends B) (hca : closedOn ends A S) :
    matching ends ((A \ inside ends A S) ∪ inside ends B S) := by
  intro e he f hf hne
  rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
  · exact ha (mem_sdiff.mp he).1 (mem_sdiff.mp hf).1 hne
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨he, hno⟩ := mem_sdiff.mp he
    exact hno (mem_filter.mpr ⟨he, hca e he v hv ((mem_filter.mp hf).2 hw)⟩)
  · apply Finset.disjoint_right.mpr
    intro v hv hw
    obtain ⟨hf, hno⟩ := mem_sdiff.mp hf
    exact hno (mem_filter.mpr ⟨hf, hca f hf v hv ((mem_filter.mp he).2 hw)⟩)
  · exact hb (mem_filter.mp he).1 (mem_filter.mp hf).1 hne

private theorem swap_covered [DecidableEq V] [DecidableEq E] {A B : Finset E} {S : Finset V}
    (hca : closedOn ends A S) (hcb : closedOn ends B S) :
    covered ends ((A \ inside ends A S) ∪ inside ends B S) =
      (covered ends A \ S) ∪ (covered ends B ∩ S) := by
  rw [covered, union_biUnion, ← covered_inside ends hcb]
  congr 1
  ext v
  simp only [covered, mem_biUnion, mem_sdiff, inside, mem_filter]
  constructor
  · rintro ⟨e, ⟨he, hno⟩, hv⟩
    exact ⟨⟨e, he, hv⟩, fun hs => hno ⟨he, hca e he v hv hs⟩⟩
  · rintro ⟨⟨e, he, hv⟩, hno⟩
    exact ⟨e, ⟨he, fun h => hno (h.2 hv)⟩, hv⟩

private theorem swap_sum [DecidableEq V] [DecidableEq E]
    (A B : Finset E) (S : Finset V) (w : E → ℝ) :
    ∑ e ∈ ((A \ inside ends A S) ∪ inside ends B S), w e =
      ∑ e ∈ A, w e - ∑ e ∈ inside ends A S, w e + ∑ e ∈ inside ends B S, w e := by
  rw [sum_union, sum_sdiff_eq_sub (show inside ends A S ⊆ A from filter_subset ..)]
  apply Finset.disjoint_left.mpr
  intro e he hb
  exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨(mem_sdiff.mp he).1, (mem_filter.mp hb).2⟩)

private def best (pos : Finset E) (w : E → ℝ) (M : Finset E) :=
  M ⊆ pos ∧ matching ends M ∧
    ∀ N ⊆ pos, matching ends N → ∑ e ∈ N, w e ≤ ∑ e ∈ M, w e

private theorem swap_best [DecidableEq V] [DecidableEq E]
    {A B : Finset E} {S : Finset V} {pos : Finset E} {w : E → ℝ}
    (ha : best ends pos w A) (hb : best ends pos w B)
    (hca : closedOn ends A S) (hcb : closedOn ends B S) :
    best ends pos w ((A \ inside ends A S) ∪ inside ends B S) := by
  have sub (M N : Finset E) (hm : M ⊆ pos) (hn : N ⊆ pos) :
      (M \ inside ends M S) ∪ inside ends N S ⊆ pos :=
    union_subset (sdiff_subset.trans hm) ((filter_subset ..).trans hn)
  have hle := hb.2.2 _ (sub B A hb.1 ha.1) (swap_matching ends hb.2.1 ha.2.1 hcb)
  rw [swap_sum] at hle
  refine ⟨sub A B ha.1 hb.1, swap_matching ends ha.2.1 hb.2.1 hca, fun N hn hm => ?_⟩
  rw [swap_sum]
  linarith [ha.2.2 N hn hm]

private theorem card_uncovered [DecidableEq V]
    (h₂ : ∀ e, (ends e).card = 2) {M : Finset E} {S : Finset V}
    (hm : matching ends M) (hc : closedOn ends M S) :
    (S \ covered ends M).card + (inside ends M S).card * 2 = S.card := by
  have hh := covered_card ends h₂
    (M := inside ends M S) (hm.subset (show inside ends M S ⊆ M from filter_subset ..))
  rw [covered_inside ends hc, inter_comm] at hh
  rw [← hh, card_sdiff_add_card_inter]

private def related [DecidableEq V] (pos : Finset E) (w : E → ℝ) (u v : V) : Prop :=
  u = v ∨ ∀ M, best ends pos w M → u ∈ covered ends M ∨ v ∈ covered ends M

private theorem related_trans [Finite V] [DecidableEq V]
    (h₂ : ∀ e, (ends e).card = 2) {pos : Finset E} {w : E → ℝ}
    (hex : ∀ v, ∃ M, best ends pos w M ∧ v ∉ covered ends M)
    {u v z : V} (huv : related ends pos w u v) (hvz : related ends pos w v z) :
    related ends pos w u z := by
  classical
  obtain rfl | huv := huv
  · exact hvz
  obtain rfl | hvz := hvz
  · exact Or.inr huv
  by_cases huz : u = z
  · exact Or.inl huz
  right
  intro A hA
  by_contra! hn
  obtain ⟨B, hB, hv⟩ := hex v
  obtain ⟨S, hvs, hca, hcb, hsize⟩ := exists_closed_set ends h₂ A B v
  -- After the swap the matching misses v, so it covers both u and z inside S.
  -- Counting covered endpoints in the two original matchings leaves room for only two misses.
  have hs := swap_best ends hA hB hca hcb
  have hswap := swap_covered ends hca hcb
  have h₁ := huv _ hs
  have h₂' := hvz _ hs
  rw [hswap] at h₁ h₂'
  simp only [mem_union, mem_sdiff, mem_inter, hvs, hv, hn.1, hn.2, false_and, and_false,
    not_true_eq_false, false_or, or_false] at h₁ h₂'
  have hpair : {u, z} ⊆ S \ covered ends A := by
    simp [insert_subset_iff, h₁, h₂', hn]
  have hcard := card_le_card hpair
  simp [huz] at hcard
  have hother : (S \ covered ends B).Nonempty := ⟨v, mem_sdiff.mpr ⟨hvs, hv⟩⟩
  have := hother.card_pos
  have := card_uncovered ends h₂ hA.2.1 hca
  have := card_uncovered ends h₂ hB.2.1 hcb
  omega

private theorem related_endpoints [DecidableEq V]
    {pos : Finset E} {w : E → ℝ} (hpos : ∀ e ∈ pos, 0 < w e)
    {e : E} (he : e ∈ pos) {u v : V} (huv : ends e = {u, v}) :
    related ends pos w u v := by
  classical
  right
  intro M hM
  by_contra! hn
  have hd : ∀ f ∈ M, Disjoint (ends e) (ends f) := by
    intro f hf
    apply Finset.disjoint_left.mpr
    intro a ha hfa
    have : a ∈ covered ends M := mem_biUnion.mpr ⟨f, hf, hfa⟩
    grind
  have hne : e ∉ M := fun h => hn.1 (mem_biUnion.mpr ⟨e, h, by simp [huv]⟩)
  have hm : matching ends (insert e M) := by
    rw [matching, coe_insert, Set.pairwiseDisjoint_insert_of_notMem hne]
    exact ⟨hM.2.1, fun j hj => hd j hj⟩
  have := hM.2.2 _ (insert_subset he hM.1) hm
  rw [sum_insert hne] at this
  linarith [hpos e he]

-- If no vertex is always covered, each optimal matching misses at most one member of a class.
-- Choosing a matching that misses its representative shows that the class has odd size.
private theorem tight_row [Finite V] [DecidableEq V]
    (h₂ : ∀ e, (ends e).card = 2) {pos : Finset E} {w : E → ℝ}
    (hp : pos.Nonempty) (hpos : ∀ e ∈ pos, 0 < w e) :
    (∃ v, ∀ M, best ends pos w M → v ∈ covered ends M) ∨
    ∃ U : Finset V, Odd U.card ∧ 0 < U.card / 2 ∧
      ∀ M, best ends pos w M → (inside ends M U).card = U.card / 2 := by
  classical
  let _ := Fintype.ofFinite V
  by_contra! nh
  obtain ⟨hex, noU⟩ := nh
  obtain ⟨e, he⟩ := hp
  obtain ⟨u, v, huv, hends⟩ := card_eq_two.mp (h₂ e)
  let R := related ends pos w
  have symm {a b : V} (h : R a b) : R b a := h.elim (fun h => Or.inl h.symm)
    (fun h => Or.inr (fun M hm => (h M hm).symm))
  let U := univ.filter (R u)
  have hu : u ∈ U := mem_filter.mpr ⟨mem_univ _, Or.inl rfl⟩
  have hv : v ∈ U := mem_filter.mpr ⟨mem_univ _, related_endpoints ends hpos he hends⟩
  have hUc : 2 ≤ U.card := by
    simpa [huv] using card_le_card (show {u, v} ⊆ U by simp [insert_subset_iff, hu, hv])
  have hcl {M} (hm : best ends pos w M) : closedOn ends M U := by
    intro f hf a ha hau b hb
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    by_cases hab : a = b
    · exact hab ▸ (mem_filter.mp hau).2
    have hpair : ends f = {a, b} := (eq_of_subset_of_card_le (by
      simpa [insert_subset_iff] using And.intro ha hb : {a, b} ⊆ ends f)
        (by simp [h₂, hab])).symm
    exact related_trans ends h₂ hex (mem_filter.mp hau).2
      (related_endpoints ends hpos (hm.1 hf) hpair)
  have hmiss {M} (hm : best ends pos w M) : (U \ covered ends M).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha, hna⟩ := mem_sdiff.mp ha
    obtain ⟨hb, hnb⟩ := mem_sdiff.mp hb
    have hr := related_trans ends h₂ hex (symm (mem_filter.mp ha).2) (mem_filter.mp hb).2
    exact hr.resolve_right (fun h => (h M hm).elim hna hnb)
  obtain ⟨M, hm, hmu⟩ := hex u
  have hpos' := card_pos.mpr (show (U \ covered ends M).Nonempty from
    ⟨u, mem_sdiff.mpr ⟨hu, hmu⟩⟩)
  have hcnt := card_uncovered ends h₂ hm.2.1 (hcl hm)
  have := hmiss hm
  have hodd : Odd U.card := ⟨(inside ends M U).card, by omega⟩
  obtain ⟨N, hn, hn'⟩ := noU U hodd (by omega)
  have := card_uncovered ends h₂ hn.2.1 (hcl hn)
  have := hmiss hn
  omega

private def polar : Set (E → ℝ) :=
  {w | (∀ e, 0 ≤ w e) ∧ ∀ M, matching ends M → ∑ e ∈ M, w e ≤ 1}

private theorem polar_convex : Convex ℝ (polar ends) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), ?_⟩
  intro M hm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
  linarith [mul_le_mul_of_nonneg_left (hx.2 M hm) ha, mul_le_mul_of_nonneg_left (hy.2 M hm) hb]

private theorem polar_compact : IsCompact (polar ends) := by
  have hc : IsClosed (polar ends) := by
    dsimp only [polar]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter (fun e => isClosed_le continuous_const (continuous_apply e))).inter
      (isClosed_iInter (fun _ => isClosed_iInter (fun _ => isClosed_le (by fun_prop)
        continuous_const)))
  apply (isCompact_Icc (a := (0 : E → ℝ)) (b := 1)).of_isClosed_subset hc
  intro w hw
  refine ⟨hw.1, fun e => ?_⟩
  simpa using hw.2 {e} (by simp [matching])

open Filter Topology in
private theorem eq_extreme [Finite E] {w r : E → ℝ} (hw : w ∈ (polar ends).extremePoints ℝ)
    (hr : r ∈ polar ends) (hzero : ∀ e, w e = 0 → r e = 0)
    (htight : ∀ M, matching ends M → ∑ e ∈ M, w e = 1 → ∑ e ∈ M, r e = 1) : r = w := by
  -- Extend the line from r past w. Tight constraints remain equalities, and each of the
  -- finitely many strict inequalities persists for sufficiently small positive t.
  let y (t : ℝ) (e : E) := w e + t * (w e - r e)
  have hw' := extremePoints_subset hw
  have hp : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ e, 0 ≤ y t e := by
    apply eventually_all.mpr
    intro e
    by_cases h : w e = 0
    · exact Eventually.of_forall (fun t => by simp [y, h, hzero e h])
    have hpos : 0 < y 0 e := by simpa [y] using lt_of_le_of_ne (hw'.1 e) (Ne.symm h)
    have h : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < y t e :=
      (isOpen_lt (continuous_const (y := (0 : ℝ))) (show Continuous (fun t => y t e) by
        dsimp [y]; fun_prop)).mem_nhds hpos
    exact h.mono fun _ ht => ht.le
  have hs : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ M, matching ends M → ∑ e ∈ M, y t e ≤ 1 := by
    apply eventually_all.mpr
    intro M
    by_cases hm : matching ends M
    · by_cases h : ∑ e ∈ M, w e = 1
      · exact Eventually.of_forall (fun t _ => by
          simp [y, sum_add_distrib, ← mul_sum, sum_sub_distrib, h, htight M hm h])
      · have hh : ∑ e ∈ M, y 0 e < 1 := by simpa [y] using lt_of_le_of_ne (hw'.2 M hm) h
        have h : ∀ᶠ t in 𝓝 (0 : ℝ), ∑ e ∈ M, y t e < 1 :=
          (isOpen_lt (show Continuous (fun t => ∑ e ∈ M, y t e) by dsimp [y]; fun_prop)
            continuous_const).mem_nhds hh
        exact h.mono fun _ ht _ => ht.le
    · exact Eventually.of_forall (fun _ h => (hm h).elim)
  obtain ⟨t, ht, hpos, hsum⟩ :=
    ((show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin).and
      ((hp.and hs).filter_mono nhdsWithin_le_nhds)).exists
  apply hw.2 hr (show y t ∈ polar ends from ⟨hpos, hsum⟩)
  refine ⟨t / (1 + t), 1 / (1 + t), by positivity, by positivity, ?_, ?_⟩
  · field_simp
    ring
  · funext e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, y]
    field_simp
    ring

private theorem incident_card [DecidableEq V] {M : Finset E} (hm : matching ends M) (v : V) :
    (M.filter (fun e => v ∈ ends e)).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro e he f hf
  by_contra hne
  exact disjoint_left.mp (hm (mem_filter.mp he).1 (mem_filter.mp hf).1 hne)
    (mem_filter.mp he).2 (mem_filter.mp hf).2

private theorem internal_card [DecidableEq V] (h₂ : ∀ e, (ends e).card = 2) {M : Finset E}
    (hm : matching ends M) (U : Finset V) : (inside ends M U).card ≤ U.card / 2 := by
  have sub : covered ends (inside ends M U) ⊆ U := by
    intro v hv
    obtain ⟨e, he, hv⟩ := mem_biUnion.mp hv
    exact (mem_filter.mp he).2 hv
  have hcard := card_le_card sub
  rw [covered_card ends h₂ (M := inside ends M U) (hm.subset (filter_subset ..))] at hcard
  omega

private theorem extreme_bound [Finite V] [DecidableEq V] [Fintype E]
    (h₂ : ∀ e, (ends e).card = 2) (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ v, ∑ e ∈ univ.filter (fun e => v ∈ ends e), x e ≤ 1)
    (ho : ∀ U : Finset V, Odd U.card → ∑ e ∈ inside ends univ U, x e ≤ (U.card / 2 : ℕ))
    {w : E → ℝ} (hw : w ∈ (polar ends).extremePoints ℝ) : ∑ e, w e * x e ≤ 1 := by
  classical
  let pos := univ.filter (fun e => 0 < w e)
  have hw' := extremePoints_subset hw
  have hpos (e) (he : e ∈ pos) : 0 < w e := (mem_filter.mp he).2
  by_cases hp : pos.Nonempty
  swap
  · have hz e : w e = 0 := le_antisymm (le_of_not_gt (fun h =>
          hp ⟨e, mem_filter.mpr ⟨mem_univ e, h⟩⟩)) (hw'.1 e)
    simp [hz]
  have hrow : ∃ (R : Finset E) (k : ℕ), 0 < k ∧ R ⊆ pos ∧
      (∀ M, matching ends M → (M ∩ R).card ≤ k) ∧
      (∀ M, best ends pos w M → (M ∩ R).card = k) ∧ ∑ e ∈ R, x e ≤ k := by
    obtain h | ⟨U, hodd, hk, ht⟩ := tight_row ends h₂ hp hpos
    · obtain ⟨v, ht⟩ := h
      let R := pos.filter (fun e => v ∈ ends e)
      have hsub (M : Finset E) : M ∩ R ⊆ M.filter (fun e => v ∈ ends e) := fun e he =>
        mem_filter.mpr ⟨(mem_inter.mp he).1, (mem_filter.mp (mem_inter.mp he).2).2⟩
      have hc (M : Finset E) (hm : matching ends M) :=
        (card_le_card (hsub M)).trans (incident_card ends hm v)
      refine ⟨R, 1, by decide, filter_subset .., hc, ?_, ?_⟩
      · intro M hm
        obtain ⟨e, he, hv⟩ := mem_biUnion.mp (ht M hm)
        have : (M ∩ R).Nonempty := ⟨e, mem_inter.mpr ⟨he, mem_filter.mpr ⟨hm.1 he, hv⟩⟩⟩
        have := this.card_pos
        have := hc M hm.2.1
        omega
      · rw [Nat.cast_one]
        exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (subset_univ pos))
          (fun e _ _ => hx e)).trans (hd v)
    · let R := inside ends pos U
      have hsub (M : Finset E) : M ∩ R ⊆ inside ends M U := fun e he =>
        mem_filter.mpr ⟨(mem_inter.mp he).1, (mem_filter.mp (mem_inter.mp he).2).2⟩
      refine ⟨R, _, hk, filter_subset .., fun M hm =>
        (card_le_card (hsub M)).trans (internal_card ends h₂ hm U), ?_, ?_⟩
      · intro M hm
        have : M ∩ R = inside ends M U := Subset.antisymm (hsub M) (fun e he =>
          mem_inter.mpr ⟨(mem_filter.mp he).1, mem_filter.mpr
            ⟨hm.1 (mem_filter.mp he).1, (mem_filter.mp he).2⟩⟩)
        rw [this, ht M hm]
      · exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (subset_univ pos))
          (fun e _ _ => hx e)).trans (ho U hodd)
  obtain ⟨R, k, hk, hR, hcount, ht, hbound⟩ := hrow
  -- Normalize the tight constraint and restrict it to the support of the extreme weight.
  let r : E → ℝ := fun e => if e ∈ R then (k : ℝ)⁻¹ else 0
  have hrSum (M : Finset E) : ∑ e ∈ M, r e = ((M ∩ R).card : ℝ) / k := by
    simp [r, div_eq_mul_inv]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hr : r ∈ polar ends := by
    refine ⟨fun e => by dsimp [r]; split_ifs <;> positivity, fun M hm => ?_⟩
    rw [hrSum, div_le_one hk']
    exact_mod_cast hcount M hm
  have heq : r = w := by
    apply eq_extreme ends hw hr
    · intro e he
      simp [r, show e ∉ R from fun h => (hpos e (hR h)).ne' he]
    · intro M hm hM
      have hmass : ∑ e ∈ M ∩ pos, w e = 1 := by
        rw [← hM]
        apply sum_subset inter_subset_left
        intro e he he'
        have hn : ¬0 < w e := fun h => he' (mem_inter.mpr ⟨he, mem_filter.mpr ⟨mem_univ _, h⟩⟩)
        exact le_antisymm (le_of_not_gt hn) (hw'.1 e)
      have hb : best ends pos w (M ∩ pos) :=
        ⟨inter_subset_right, hm.subset inter_subset_left, fun N _ hn => hmass ▸ hw'.2 N hn⟩
      have hset : M ∩ pos ∩ R = M ∩ R := by rw [inter_assoc, inter_eq_right.mpr hR]
      have hc := ht _ hb
      rw [hset] at hc
      rw [hrSum, hc, div_self hk'.ne']
  rw [← heq]
  simp only [r, ite_mul, zero_mul, ← sum_filter, filter_mem_eq_inter, univ_inter, ← mul_sum]
  rw [← div_eq_inv_mul, div_le_one hk']
  exact hbound

private theorem polar_bound [Finite V] [DecidableEq V] [Fintype E]
    (h₂ : ∀ e, (ends e).card = 2) (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hd : ∀ v, ∑ e ∈ univ.filter (fun e => v ∈ ends e), x e ≤ 1)
    (ho : ∀ U : Finset V, Odd U.card → ∑ e ∈ inside ends univ U, x e ≤ (U.card / 2 : ℕ))
    {w : E → ℝ} (hw : w ∈ polar ends) : ∑ e, w e * x e ≤ 1 := by
  let H : Set (E → ℝ) := {a | ∑ e, a e * x e ≤ 1}
  suffices polar ends ⊆ H from this hw
  rw [← closure_convexHull_extremePoints (polar_compact ends) (polar_convex ends)]
  apply closure_minimal _ (isClosed_le (by fun_prop) continuous_const)
  apply convexHull_min (fun w hw => extreme_bound ends h₂ x hx hd ho hw)
  intro a ha b hb t s ht hs hts
  change ∑ e, (t * a e + s * b e) * x e ≤ 1
  simp only [add_mul, mul_assoc, sum_add_distrib, ← mul_sum]
  change ∑ e, a e * x e ≤ 1 at ha
  change ∑ e, b e * x e ≤ 1 at hb
  linarith [mul_le_mul_of_nonneg_left ha ht, mul_le_mul_of_nonneg_left hb hs]

private theorem mem_of_polar [Fintype E] [DecidableEq E] (x : E → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hdual : ∀ w ∈ polar ends, ∑ e, w e * x e ≤ 1)
    (K : Set (E → ℝ)) (hk : Convex ℝ K) (hc : IsClosed K)
    (hm : ∀ M, matching ends M → (fun e => if e ∈ M then (1 : ℝ) else 0) ∈ K) : x ∈ K := by
  classical
  by_contra h
  obtain ⟨f, c, hK, hcx⟩ := geometric_hahn_banach_closed_point hk hc h
  let a (e : E) := f (Pi.single e 1)
  have frep (z : E → ℝ) : f z = ∑ e, a e * z e := by
    have hz : z = ∑ e, z e • Pi.single e (1 : ℝ) := by
      funext i
      simp [Pi.smul_apply, Pi.single_apply, mul_ite]
    conv_lhs => rw [hz, map_sum]
    simp [a, mul_comm]
  have hcpos : 0 < c := by
    have hzero := hm ∅ (by simp [matching])
    simpa [frep] using hK _ hzero
  have hlt (M : Finset E) (hm' : matching ends M) : ∑ e ∈ M, a e < c := by
    have h := hK _ (hm M hm')
    simpa [frep, mul_ite] using h
  let w e := max (a e) 0 / c
  have hw : w ∈ polar ends := by
    refine ⟨fun e => div_nonneg (le_max_right ..) hcpos.le, fun M hM => ?_⟩
    change ∑ e ∈ M, max (a e) 0 / c ≤ 1
    simp only [div_eq_mul_inv, ← sum_mul]
    rw [← div_eq_mul_inv, div_le_one hcpos]
    have hs := hlt (M.filter (fun e => 0 < a e)) (hM.subset (filter_subset ..))
    rw [sum_filter] at hs
    convert hs.le using 1
    apply sum_congr rfl
    intro e _
    split_ifs with h
    · exact max_eq_left h.le
    · exact max_eq_right (le_of_not_gt h)
  have hle := hdual w hw
  have hsum : ∑ e, w e * x e = (∑ e, max (a e) 0 * x e) / c := by
    rw [div_eq_mul_inv, sum_mul]
    apply sum_congr rfl
    intro e _
    dsimp [w]
    ring
  rw [hsum, div_le_one hcpos] at hle
  rw [frep] at hcx
  exact hcx.not_ge ((sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (le_max_left ..) (hx e))
    |>.trans hle)

end WeightProof

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem eq_of_common_vertex {M : G.Subgraph} (hM : M.IsMatching) {v : V}
    {e f : G.edgeSet} (he : e.val ∈ M.edgeSet) (hf : f.val ∈ M.edgeSet)
    (hv : v ∈ e.val) (hw : v ∈ f.val) : e = f := by
  obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.mp hv
  obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp hw
  rw [ha] at he
  rw [hb] at hf
  have h : a = b := hM.eq_of_adj_left he hf
  exact Subtype.ext (ha.trans (h ▸ hb.symm))

private def feasible : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧
        (∀ v : V, ∑ e ∈ univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V)), x e ≤ 1) ∧
        ∀ U : Finset V, Odd U.card →
          ∑ e ∈ univ.filter (fun e : G.edgeSet => (e : Sym2 V) ∈ U.sym2), x e ≤
            ((U.card / 2 : ℕ) : ℝ)}

private theorem feasible_convex : Convex ℝ (feasible G) := by
  intro x hx y hy a b ha hb hab
  have sum_le (S : Finset G.edgeSet) (c : ℝ)
      (hx' : ∑ e ∈ S, x e ≤ c) (hy' : ∑ e ∈ S, y e ≤ c) :
      ∑ e ∈ S, (a • x + b • y) e ≤ c := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
    calc
      _ ≤ a * c + b * c := add_le_add (mul_le_mul_of_nonneg_left hx' ha)
        (mul_le_mul_of_nonneg_left hy' hb)
      _ = c := by rw [← add_mul, hab, one_mul]
  exact ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)),
    fun v => sum_le _ _ (hx.2.1 v) (hy.2.1 v),
    fun U hU => sum_le _ _ (hx.2.2 U hU) (hy.2.2 U hU)⟩

private theorem matching_subset : matchingPolytope G ⊆ feasible G := by
  classical
  apply convexHull_min _ (feasible_convex G)
  rintro _ ⟨M, hM, rfl⟩
  let edges := univ.filter (fun e : G.edgeSet => e.val ∈ M.edgeSet)
  let ends (e : G.edgeSet) := e.val.toFinset
  have hem (e : G.edgeSet) : e ∈ edges ↔ e.val ∈ M.edgeSet := by simp [edges]
  have hm : WeightProof.matching ends edges := by
    intro e he f hf hne
    apply disjoint_left.mpr
    intro v hv hw
    exact hne (eq_of_common_vertex G hM ((hem e).mp he) ((hem f).mp hf)
      (Sym2.mem_toFinset.mp hv) (Sym2.mem_toFinset.mp hw))
  have sum_on (P : G.edgeSet → Prop) [DecidablePred P] :
      ∑ e ∈ univ.filter P, edgeIncidence G M e = ((edges.filter P).card : ℝ) := by
    simp only [edgeIncidence, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext e
    simp [hem, and_comm]
  refine ⟨fun e => by simp [edgeIncidence, apply_ite], ?_, ?_⟩
  · intro v
    rw [sum_on]
    exact_mod_cast (by simpa only [ends, Sym2.mem_toFinset] using
      WeightProof.incident_card ends hm v :
      (edges.filter (fun e => v ∈ e.val)).card ≤ 1)
  · intro U _
    rw [sum_on]
    have he (e : G.edgeSet) : ends e ⊆ U ↔ e.val ∈ U.sym2 := by
      simp only [ends, Finset.subset_iff, Sym2.mem_toFinset, mem_sym2_iff]
    have h₂ (e : G.edgeSet) : (ends e).card = 2 :=
      Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet e.property)
    exact_mod_cast (by simpa only [WeightProof.inside, he] using
      WeightProof.internal_card ends h₂ hm U :
      (edges.filter (fun e => e.val ∈ U.sym2)).card ≤ U.card / 2)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem matching_closed [Finite V] : IsClosed (matchingPolytope G) := by
  have h : {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = edgeIncidence G M}.Finite := by
    apply (Set.finite_range (edgeIncidence G)).subset
    rintro _ ⟨M, _, rfl⟩
    exact ⟨M, rfl⟩
  exact (h.isCompact_convexHull ℝ).isClosed

omit [Fintype V] [DecidableRel G.Adj] in
private theorem indicator_mem {M : Finset G.edgeSet}
    (hm : WeightProof.matching (fun e : G.edgeSet => e.val.toFinset) M) :
    (fun e => if e ∈ M then (1 : ℝ) else 0) ∈ matchingPolytope G := by
  classical
  let R (u v : V) : Prop := ∃ h : G.Adj u v, (⟨s(u, v), h⟩ : G.edgeSet) ∈ M
  have hs : Std.Symm R := ⟨by
    rintro u v ⟨h, he⟩
    exact ⟨h.symm, (show (⟨s(v, u), h.symm⟩ : G.edgeSet) = ⟨s(u, v), h⟩ from
      Subtype.ext Sym2.eq_swap).symm ▸ he⟩⟩
  let N : G.Subgraph :=
    { verts := {u | ∃ v, R u v}
      Adj := R
      adj_sub := fun ⟨h, _⟩ => h
      edge_vert := fun {u v} h => ⟨v, h⟩
      symm := hs }
  apply subset_convexHull ℝ _
  refine ⟨N, ?_, ?_⟩
  · rintro u ⟨v, hv⟩
    refine ⟨v, hv, ?_⟩
    rintro z ⟨hz, hez⟩
    obtain ⟨hv, hev⟩ := hv
    have heq : (⟨s(u, z), hz⟩ : G.edgeSet) = ⟨s(u, v), hv⟩ := by
      by_contra h
      exact disjoint_left.mp (hm hez hev h) (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left ..))
        (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left ..))
    exact Sym2.congr_right.mp (congrArg Subtype.val heq)
  · funext ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      have hn : s(u, v) ∈ N.edgeSet ↔ (⟨s(u, v), he⟩ : G.edgeSet) ∈ M :=
        ⟨fun ⟨_, h⟩ => h, fun h => ⟨he, h⟩⟩
      simp only [edgeIncidence, hn]

/-- **Edmonds' matching polytope theorem.** The matching polytope of a finite graph is the set of
`x ∈ ℝ^E` with `x ≥ 0`, `x(δ(v)) ≤ 1` for every vertex `v`, and `x(E[U]) ≤ ⌊|U| / 2⌋` for every
vertex set `U` of odd size, where `E[U]` is the set of edges with both ends in `U` (Schrijver,
*A Course in Combinatorial Optimization*, §5.4, Corollary 5.6b, constraints (30)). -/
theorem matchingPolytope_eq :
    matchingPolytope G =
      {x | (∀ e, 0 ≤ x e) ∧
        (∀ v : V, ∑ e ∈ univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V)), x e ≤ 1) ∧
        ∀ U : Finset V, Odd U.card →
          ∑ e ∈ univ.filter (fun e : G.edgeSet => (e : Sym2 V) ∈ U.sym2), x e ≤
            ((U.card / 2 : ℕ) : ℝ)} := by
  classical
  apply Set.Subset.antisymm (matching_subset G)
  intro x hx
  let ends (e : G.edgeSet) := e.val.toFinset
  have h₂ (e : G.edgeSet) : (ends e).card = 2 :=
    Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet e.property)
  have hd (v : V) : ∑ e ∈ univ.filter (fun e => v ∈ ends e), x e ≤ 1 := by
    simpa only [ends, Sym2.mem_toFinset] using hx.2.1 v
  have ho (U : Finset V) (hU : Odd U.card) :
      ∑ e ∈ WeightProof.inside ends univ U, x e ≤ (U.card / 2 : ℕ) := by
    have he (e : G.edgeSet) : ends e ⊆ U ↔ e.val ∈ U.sym2 := by
      simp only [ends, Finset.subset_iff, Sym2.mem_toFinset, mem_sym2_iff]
    simpa only [WeightProof.inside, he] using hx.2.2 U hU
  exact WeightProof.mem_of_polar ends x hx.1
    (fun _ hw => WeightProof.polar_bound ends h₂ x hx.1 hd ho hw)
    (matchingPolytope G) (convex_convexHull ℝ _) (matching_closed G) (fun _ => indicator_mem G)

end MathlibExt.Combinatorics.MatchingPolytopeWanted
