/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Rectangles in the Boolean cube

A vertex is its set of coordinates equal to one. A chosen root `s` and two disjoint nonempty
masks `a`, `b` give four distinct vertices by flipping neither mask, either mask, or both.
The rectangle is their vertex set; it retains neither the root nor the order of the masks.
From any vertex the symmetric differences to the other three are `a`, `b`, and `a ∪ b`, so
the set determines the unordered pair of side masks. Marking one selects its two parallel
sides, not an endpoint or an orientation.

We count rooted presentations and their fibres over these finite sets. For a fixed marked mask
there is also a bijection obtained by projecting onto the mask and its complement. The census
counts all possible marked classes independently of the signs of any real weight differences.

## Reference

Kristina Crona, *Rank orders and signed interactions in evolutionary biology*, eLife 9:e51004
(2020), doi:10.7554/eLife.51004, Methods, “Counting rectangular perturbation”, Theorem 1,
Corollary and Lemmas 1–2. The source states the total for dimensions at least three; the
natural-number identity here has no division and also gives the two-dimensional case.
-/

@[expose] public section

namespace CubeRectangle

open Finset
open scoped symmDiff

section

variable {ι : Type*} [DecidableEq ι]

/-- From root `s`, flip neither mask, just `a`, just `b`, or both, and collect the resulting
vertices in a finset. Repeated vertices count once. If `a` and `b` are disjoint and nonempty,
these are the four distinct vertices of a rectangle with those side masks. -/
def corners (s a b : Finset ι) : Finset (Finset ι) :=
  {s, s ∆ a, s ∆ b, s ∆ a ∆ b}

private theorem swap (s a b : Finset ι) : corners s b a = corners s a b := by
  ext x
  simp only [corners, mem_insert, mem_singleton, symmDiff_right_comm s b a]
  tauto

private theorem flip (s a b : Finset ι) : corners (s ∆ a) a b = corners s a b := by
  ext x
  simp only [corners, mem_insert, mem_singleton, symmDiff_symmDiff_cancel_right]
  tauto

private theorem flip' (s a b : Finset ι) : corners (s ∆ b) a b = corners s a b := by
  rw [← swap, flip, swap]

private theorem reroot {t s a b : Finset ι} (ht : t ∈ corners s a b) :
    corners t a b = corners s a b := by
  simp only [corners, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rfl
  · apply flip
  · apply flip'
  · rw [flip', flip]

omit [DecidableEq ι] in
private theorem different {a b : Finset ι} (ha : a.Nonempty) (h : Disjoint a b) : a ≠ b := by
  rintro rfl
  exact ha.ne_empty (disjoint_self.mp h)

private theorem offsets (s a b : Finset ι) :
    (corners s a b).image (s ∆ ·) = {∅, a, b, a ∆ b} := by
  simp [corners, symmDiff_assoc]

/-- From any root `s`, flipping two disjoint nonempty masks gives four distinct vertices. -/
theorem card_corners (s : Finset ι) {a b : Finset ι} (ha : a.Nonempty) (hb : b.Nonempty)
    (h : Disjoint a b) : (corners s a b).card = 4 := by
  have hab := different ha h
  rw [← card_image_of_injective _ (symmDiff_right_injective s), offsets]
  have hab' : a ∆ b ≠ ∅ := by simpa using hab
  have h₁ : a ∆ b ≠ a := fun e => hb.ne_empty (symmDiff_eq_left.mp e)
  have h₂ : a ∆ b ≠ b := fun e => ha.ne_empty (symmDiff_eq_right.mp e)
  simp [ha.ne_empty.symm, hb.ne_empty.symm, hab'.symm, hab, h₁.symm, h₂.symm]

private theorem union_of_offsets (a b : Finset ι) :
    ({∅, a, b, a ∪ b} : Finset _).biUnion id = a ∪ b := by
  ext i
  simp

private theorem mask_pair {s a b c d : Finset ι} (ha : a.Nonempty) (hb : b.Nonempty)
    (hc : c.Nonempty) (hd : d.Nonempty) (h : Disjoint a b) (g : Disjoint c d)
    (e : corners s a b = corners s c d) : ({a, b} : Finset _) = {c, d} := by
  have z := congrArg (Finset.image (s ∆ ·)) e
  rw [offsets, offsets, symmDiff_eq_union h, symmDiff_eq_union g] at z
  have u := congrArg (Finset.biUnion · id) z
  rw [union_of_offsets, union_of_offsets] at u
  have remove (x y : Finset ι) (hx : x.Nonempty) (hy : y.Nonempty) (hdj : Disjoint x y) :
      (({∅, x, y, x ∪ y} : Finset _).erase ∅).erase (x ∪ y) = {x, y} := by
    have h₁ : x ∪ y ≠ x := by
      rw [← symmDiff_eq_union hdj]
      exact fun e => hy.ne_empty (symmDiff_eq_left.mp e)
    have h₂ : x ∪ y ≠ y := by
      rw [← symmDiff_eq_union hdj]
      exact fun e => hx.ne_empty (symmDiff_eq_right.mp e)
    ext i
    simp only [mem_erase, mem_insert, mem_singleton]
    grind [Finset.Nonempty.ne_empty]
  rw [← remove a b ha hb h, z, u, remove c d hc hd g]

/-- Two presentations with disjoint nonempty side masks give the same vertex set exactly when
one root belongs to the other's vertex set and their masks agree up to exchange. -/
theorem corners_eq_iff {s t a b c d : Finset ι} (ha : a.Nonempty) (hb : b.Nonempty)
    (hc : c.Nonempty) (hd : d.Nonempty) (h : Disjoint a b) (g : Disjoint c d) :
    corners t c d = corners s a b ↔ t ∈ corners s a b ∧ ((c = a ∧ d = b) ∨ (c = b ∧ d = a)) := by
  constructor
  · intro e
    have ht : t ∈ corners s a b := e ▸ mem_insert_self ..
    have p := mask_pair hc hd ha hb g h (e.trans (reroot ht).symm)
    have hh (x : Finset ι) : x = c ∨ x = d ↔ x = a ∨ x = b := by
      simpa using Finset.ext_iff.mp p x
    have hc' := (hh c).mp (Or.inl rfl)
    have hd' := (hh d).mp (Or.inr rfl)
    exact ⟨ht, by grind only [different hc g]⟩
  · rintro ⟨ht, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact reroot ht
    · rw [swap]; exact reroot ht

end

section

variable {ι : Type*} [DecidableEq ι]

/-- For each `t ∈ V`, collect the finset `{t, t ∆ a}`; equal finsets occur only once. If `V`
is a rectangle marked by the side mask `a`, this family consists of its two parallel `a`-edges. -/
def sides (V : Finset (Finset ι)) (a : Finset ι) : Finset (Finset (Finset ι)) :=
  V.image fun t => {t, t ∆ a}

/-- For any root `s` and masks `a`, `b`, translating by `a` pairs `s` with `s ∆ a` and
`s ∆ b` with `s ∆ a ∆ b`. The two displayed finsets can coincide, for instance when `b = ∅`.
For disjoint nonempty masks they are the two distinct parallel sides marked by `a`. -/
theorem sides_corners (s a b : Finset ι) : sides (corners s a b) a =
    {{s, s ∆ a}, {s ∆ b, s ∆ a ∆ b}} := by
  simp only [sides, corners, image_insert, image_singleton, symmDiff_symmDiff_cancel_right,
    symmDiff_right_comm s b a, symmDiff_right_comm (s ∆ a) b a]
  rw [pair_comm (s ∆ a) s, pair_comm (s ∆ a ∆ b) (s ∆ b)]
  simp

end

section

variable {ι : Type*} [DecidableEq ι]

/-- For real vertex weights `w`, multiply the weight difference for flipping `a` at `s` by
the weight difference for flipping `a` at `s ∆ b`, taking the initial weight minus the final
weight in both cases. When `a` and `b` are disjoint and nonempty, these are the differences
along the parallel sides marked by `a`. They have opposite signs exactly when the product is
negative. -/
noncomputable def sideProduct (w : Finset ι → ℝ) (s a b : Finset ι) : ℝ :=
  (w s - w (s ∆ a)) * (w (s ∆ b) - w (s ∆ a ∆ b))

private theorem product_flip (w : Finset ι → ℝ) (s a b : Finset ι) :
    sideProduct w (s ∆ a) a b = sideProduct w s a b := by
  simp only [sideProduct, symmDiff_symmDiff_cancel_right]; ring

private theorem product_flip' (w : Finset ι → ℝ) (s a b : Finset ι) :
    sideProduct w (s ∆ b) a b = sideProduct w s a b := by
  simp only [sideProduct, symmDiff_right_comm s b a, symmDiff_symmDiff_cancel_right]; ring

/-- For arbitrary real vertex weights, two presentations by disjoint nonempty masks give the
same product if their vertex sets agree and their first (marked) mask is the same. Thus the
test for opposite signs depends on the marked rectangle, not its root. Exchanging the marked
and unmarked masks changes the comparison being tested. -/
theorem sideProduct_eq_of_same_mark (w : Finset ι → ℝ) {s t a b d : Finset ι}
    (ha : a.Nonempty) (hb : b.Nonempty) (hd : d.Nonempty) (h : Disjoint a b)
    (g : Disjoint a d) (e : corners t a d = corners s a b) :
    sideProduct w t a d = sideProduct w s a b := by
  obtain ⟨ht, hm⟩ := (corners_eq_iff ha hb ha hd h g).mp e
  have ed : d = b := hm.elim And.right (fun z => (different ha h z.1).elim)
  subst d
  simp only [corners, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rfl
  · apply product_flip
  · apply product_flip'
  · rw [product_flip', product_flip]

end

section

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Ordered pairs of disjoint masks with first mask in `A` and nonempty second mask. -/
def blocks (A : Finset (Finset ι)) :=
  A.biUnion fun a => {a} ×ˢ (((univ \ a).powerset).erase ∅)

private theorem mem_blocks {A : Finset (Finset ι)} {a b : Finset ι} :
    (a, b) ∈ blocks A ↔ a ∈ A ∧ b.Nonempty ∧ Disjoint a b := by
  simp [blocks, nonempty_iff_ne_empty, ← compl_eq_univ_sdiff, subset_compl_iff_disjoint_left]

private abbrev Code (ι : Type*) := Finset ι × Finset ι × Finset ι
/-- Rooted presentations with first mask in `A` and disjoint nonempty second mask. To obtain
rectangles, `A` must exclude the empty mask. -/
def presentations (A : Finset (Finset ι)) : Finset (Finset ι × Finset ι × Finset ι) :=
  univ ×ˢ blocks A

private def vertices (x : Code ι) := corners x.1 x.2.1 x.2.2
private def mark (x : Code ι) := (vertices x, x.2.1)
private def selected (A : Finset (Finset ι)) := (presentations A).image mark

variable (ι) in
/-- All unlabelled vertex sets obtained from disjoint nonempty coordinate flips in the Boolean
cube on `ι`. A vertex is the set of its coordinates equal to one. -/
def rectangles : Finset (Finset (Finset ι)) :=
  (presentations (univ.erase ∅)).image fun x => corners x.1 x.2.1 x.2.2

variable (ι) in
/-- All pairs of a rectangle vertex set and the mask of one of its two parallel side classes.
Neither an endpoint nor a direction along a side is distinguished. -/
def markings : Finset (Finset (Finset ι) × Finset ι) :=
  (presentations (univ.erase ∅)).image fun x => (corners x.1 x.2.1 x.2.2, x.2.1)

private theorem mem_codes {s a b : Finset ι} {A : Finset (Finset ι)} :
    (s, a, b) ∈ presentations A ↔ a ∈ A ∧ b.Nonempty ∧ Disjoint a b := by
  simp [presentations, mem_blocks]

/-- Membership as a marked vertex set is equivalent to having a presentation with the specified
first flip mask and a disjoint nonempty second flip mask. Both masks must be nonempty. -/
theorem mem_markings {V : Finset (Finset ι)} {a : Finset ι} :
    (V, a) ∈ markings ι ↔ a.Nonempty ∧ ∃ s b, b.Nonempty ∧ Disjoint a b ∧ corners s a b = V := by
  change (V, a) ∈ selected (univ.erase ∅) ↔ _
  simp only [selected, mem_image, Prod.exists, mem_codes, mem_erase, mem_univ,
    and_true, mark, vertices, Prod.mk.injEq, nonempty_iff_ne_empty]
  constructor
  · rintro ⟨s, c, b, ⟨hc, hb, h⟩, e, rfl⟩; exact ⟨hc, s, b, hb, h, e⟩
  · rintro ⟨ha, s, b, hb, h, e⟩; exact ⟨s, a, b, ⟨ha, hb, h⟩, e, rfl⟩

/-- A vertex set belongs to the rectangle family exactly when it is the set of corners of two
disjoint nonempty coordinate flips based at one vertex. -/
theorem mem_rectangles {V : Finset (Finset ι)} : V ∈ rectangles ι ↔
    ∃ s a b, a.Nonempty ∧ b.Nonempty ∧ Disjoint a b ∧ corners s a b = V := by
  simp only [rectangles, mem_image, Prod.exists, mem_codes, mem_erase, mem_univ,
    and_true, nonempty_iff_ne_empty]; grind only

private theorem const_fibres {α β : Type*} [DecidableEq β] (S : Finset α) (f : α → β)
    (k : ℕ) (h : ∀ x ∈ S, (S.filter (fun y => f y = f x)).card = k) :
    S.card = (S.image f).card * k := by
  rw [card_eq_sum_card_image f S]
  apply sum_const_nat
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact h x hx

private theorem four_per_mark (A : Finset (Finset ι)) (hA : ∀ a ∈ A, a.Nonempty) :
    (presentations A).card = (selected A).card * 4 := by
  apply const_fibres
  rintro ⟨s, a, b⟩ hx
  obtain ⟨ha, hb, hd⟩ := mem_codes.mp hx
  have eqn : ((presentations A).filter (fun x => mark x = mark (s, a, b))) =
      corners s a b ×ˢ {(a, b)} := by
    ext ⟨t, c, d⟩
    simp only [mem_filter, mem_codes, mark, vertices, Prod.mk.injEq, mem_product, mem_singleton]
    constructor
    · rintro ⟨⟨hc, hd', h⟩, e, rfl⟩
      have p := (corners_eq_iff (hA _ ha) hb (hA _ hc) hd' hd h).mp e
      grind only [different (hA _ ha) hd]
    · rintro ⟨ht, rfl, rfl⟩; exact ⟨⟨ha, hb, hd⟩, reroot ht, rfl⟩
  rw [eqn, card_product, card_singleton, mul_one, card_corners s (hA _ ha) hb hd]

/-- Every rectangle has exactly two possible markings, one for each of its two disjoint
nonempty side masks, irrespective of any weights assigned to the vertices. -/
theorem card_markings : (markings ι).card = (rectangles ι).card * 2 := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := rectangles ι) (by
    rintro ⟨V, a⟩ hm
    obtain ⟨ha, s, b, hb, h, e⟩ := mem_markings.mp hm
    exact mem_rectangles.mpr ⟨s, a, b, ha, hb, h, e⟩)]
  apply sum_const_nat
  intro V hV
  obtain ⟨s, a, b, ha, hb, h, rfl⟩ := mem_rectangles.mp hV
  have fibre : ((markings ι).filter (fun x => x.1 = corners s a b)) =
      ({corners s a b} : Finset _) ×ˢ ({a, b} : Finset _) := by
    ext ⟨W, c⟩
    simp only [mem_filter, mem_product, mem_singleton, mem_insert]
    constructor
    · rintro ⟨hm, rfl⟩
      obtain ⟨hc, t, d, hd, g, e⟩ := mem_markings.mp hm
      have z := (corners_eq_iff ha hb hc hd h g).mp e
      exact ⟨rfl, z.2.elim (fun p => Or.inl p.1) (fun p => Or.inr p.1)⟩
    · rintro ⟨rfl, rfl | rfl⟩
      · exact ⟨mem_markings.mpr ⟨ha, s, b, hb, h, rfl⟩, rfl⟩
      · exact ⟨mem_markings.mpr ⟨hb, s, a, ha, h.symm, swap ..⟩, rfl⟩
  rw [fibre, card_product, card_singleton, one_mul, card_pair (different ha h)]

end

section

variable {ι : Type*} [DecidableEq ι]

/-- Given two families of restrictions on disjoint coordinate blocks, reconstruct all their
joint vertices by union. -/
def assemble (P Y : Finset (Finset ι)) : Finset (Finset ι) :=
  P.biUnion fun p => Y.image (p ∪ ·)

/-- A pair of unordered restriction families for the marked mask `a`: a word and its complement
inside `a`, and two distinct backgrounds supported outside `a`. The mask must be nonempty. -/
def IsChart (a : Finset ι) (P Y : Finset (Finset ι)) : Prop :=
  a.Nonempty ∧ (∃ p ⊆ a, P = {p, a \ p}) ∧
    ∃ v w : Finset ι, Disjoint a v ∧ Disjoint a w ∧ v ≠ w ∧ Y = {v, w}

private theorem box_form {a p v w : Finset ι} (hp : p ⊆ a) (hv : Disjoint a v)
    (hw : Disjoint a w) : corners (p ∪ v) a (v ∆ w) = assemble {p, a \ p} {v, w} := by
  have h₁ : (p ∪ v) ∆ a = (a \ p) ∪ v := by
    ext i
    have hi : i ∈ p → i ∈ a := fun hip => hp hip
    simp only [mem_symmDiff, mem_union, mem_sdiff]
    grind only [disjoint_left.mp hv]
  have h₂ : (p ∪ v) ∆ (v ∆ w) = p ∪ w := by
    ext i
    have hi : i ∈ p → i ∈ a := fun hip => hp hip
    simp only [mem_symmDiff, mem_union]
    grind only [disjoint_left.mp hv, disjoint_left.mp hw]
  have h₃ : ((a \ p) ∪ v) ∆ (v ∆ w) = (a \ p) ∪ w := by
    ext i
    simp only [mem_symmDiff, mem_union, mem_sdiff]
    grind only [disjoint_left.mp hv, disjoint_left.mp hw]
  ext x
  simp only [corners, h₁, h₂, h₃, assemble, biUnion_insert, singleton_biUnion,
    image_insert, image_singleton, mem_insert, mem_singleton, mem_union]
  tauto

/-- Projecting all four unions from a valid restriction chart back onto the mask and its
complement recovers both unordered families. -/
theorem project_assemble {a : Finset ι} {P Y : Finset (Finset ι)} (h : IsChart a P Y) :
    ((assemble P Y).image (· ∩ a), (assemble P Y).image (· \ a)) = (P, Y) := by
  obtain ⟨_, ⟨p, hp, rfl⟩, v, w, hv, hw, _, rfl⟩ := h
  have split (q z : Finset ι) (hq : q ⊆ a) (hz : Disjoint a z) :
      (q ∪ z) ∩ a = q ∧ (q ∪ z) \ a = z := by
    constructor <;> ext i <;> have hi : i ∈ q → i ∈ a := fun hiq => hq hiq
    all_goals simp only [mem_union, mem_inter, mem_sdiff]; grind only [disjoint_left.mp hz]
  have hq : a \ p ⊆ a := sdiff_subset
  simp [assemble, split p v hp hv, split p w hp hw, split _ v hq hv, split _ w hq hw]

variable [Fintype ι]

/-- The four unions from any valid restriction chart give a rectangle marked by its mask. -/
theorem assemble_mem_markings {a : Finset ι} {P Y : Finset (Finset ι)} (h : IsChart a P Y) :
    (assemble P Y, a) ∈ markings ι := by
  obtain ⟨ha, ⟨p, hp, rfl⟩, v, w, hv, hw, hn, rfl⟩ := h
  exact mem_markings.mpr ⟨ha, p ∪ v, v ∆ w, symmDiff_nonempty.mpr hn, hv.symmDiff_right hw,
    box_form hp hv hw⟩

private theorem exists_chart {a : Finset ι} {V : Finset (Finset ι)} (hm : (V, a) ∈ markings ι) :
    ∃ P Y, IsChart a P Y ∧ assemble P Y = V := by
  obtain ⟨ha, s, b, hb, h, rfl⟩ := mem_markings.mp hm
  let p := s ∩ a
  let v := s \ a
  have hp : p ⊆ a := inter_subset_right
  have hv : Disjoint a v := disjoint_sdiff_self_right
  have hw := hv.symmDiff_right h
  have hvw : v ≠ v ∆ b := fun e => hb.ne_empty (symmDiff_eq_left.mp e.symm)
  refine ⟨{p, a \ p}, {v, v ∆ b}, ⟨ha, ⟨p, hp, rfl⟩, v, v ∆ b, hv, hw, hvw, rfl⟩, ?_⟩
  rw [← box_form hp hv hw, symmDiff_symmDiff_cancel_left]
  have e : p ∪ v = s := by ext i; simp [p, v]
  rw [e]

/-- At a fixed mask, projection onto that mask and its complement bijects genuine marked vertex
sets with a complementary pair of restrictions and a distinct pair of backgrounds. The inverse
takes all four unions; neither unordered pair has a distinguished first element. -/
def chartEquiv (a : Finset ι) :
    {V : Finset (Finset ι) // (V, a) ∈ markings ι} ≃
      {q : Finset (Finset ι) × Finset (Finset ι) // IsChart a q.1 q.2} where
  toFun V := ⟨(V.1.image (· ∩ a), V.1.image (· \ a)), by
    obtain ⟨P, Y, h, e⟩ := exists_chart V.2
    rw [← e, project_assemble h]; exact h⟩
  invFun q := ⟨assemble q.1.1 q.1.2, assemble_mem_markings q.2⟩
  left_inv V := by
    apply Subtype.ext
    obtain ⟨P, Y, h, e⟩ := exists_chart V.2
    change assemble ((V.1.image (· ∩ a), V.1.image (· \ a)) : _ × _).1
        ((V.1.image (· ∩ a), V.1.image (· \ a)) : _ × _).2 = V.1
    rw [← e, project_assemble h]
  right_inv q := Subtype.ext (project_assemble q.2)

end

section

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

private theorem card_blocks (A : Finset (Finset ι)) :
    (blocks A).card = ∑ a ∈ A, (2 ^ (univ \ a).card - 1) := by
  unfold blocks
  rw [card_biUnion]
  · apply sum_congr rfl
    intro a _
    rw [card_product, card_singleton, one_mul, card_erase_of_mem (by simp), card_powerset]
  · intro a _ b _ h
    apply disjoint_left.mpr
    rintro ⟨x, y⟩ hx hy
    simp only [mem_product, mem_singleton] at hx hy
    exact h (hx.1.symm.trans hy.1)

/-- If `R` is the number of unlabelled rectangles in an `n`-dimensional Boolean cube,
then `8 * R + 2 * 4^n = 6^n + 2^n`. The identity also covers dimensions zero, one and two. -/
theorem card_rectangles : 8 * (rectangles ι).card + 2 * 4 ^ Fintype.card ι =
    6 ^ Fintype.card ι + 2 ^ Fintype.card ι := by
  let A := (univ : Finset (Finset ι)).erase ∅
  have hA : ∀ a ∈ A, a.Nonempty := fun _ ha => nonempty_iff_ne_empty.mpr (mem_erase.mp ha).1
  have hsum : ∑ a : Finset ι, 2 ^ (univ \ a).card = 3 ^ Fintype.card ι := by
    simpa using (prod_add (fun _ : ι => 1) (fun _ => 2 : ι → ℕ) univ).symm
  have e := sum_erase_add (univ : Finset (Finset ι)) (fun a => 2 ^ (univ \ a).card) (mem_univ ∅)
  have e' : (∑ a ∈ A, 2 ^ (univ \ a).card) + 2 ^ Fintype.card ι = 3 ^ Fintype.card ι := by
    simpa [A, hsum] using e
  have v : A.card + 1 = 2 ^ Fintype.card ι := by
    simpa [A] using (card_erase_add_one (mem_univ (∅ : Finset ι)))
  have u : (blocks A).card + A.card = ∑ a ∈ A, 2 ^ (univ \ a).card := by
    rw [card_blocks, card_eq_sum_ones A, ← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    have := Nat.two_pow_pos (univ \ a).card
    omega
  have q : (blocks A).card + 2 * 2 ^ Fintype.card ι = 3 ^ Fintype.card ι + 1 := by omega
  have hc : 2 ^ Fintype.card ι * (blocks A).card = (rectangles ι).card * 2 * 4 := by
    rw [← card_markings]
    change _ = (selected A).card * 4
    simpa only [presentations, card_product, card_univ, Fintype.card_finset] using
      four_per_mark A hA
  have r := congrArg (2 ^ Fintype.card ι * ·) q
  rw [Nat.mul_add, Nat.mul_add, hc, Nat.mul_one, Nat.mul_left_comm _ 2, ← Nat.mul_pow,
    ← Nat.mul_pow] at r
  simpa only [Nat.reduceMul, mul_assoc, mul_comm 8] using r

private theorem selected_eq {A : Finset (Finset ι)} (hA : ∀ a ∈ A, a.Nonempty) :
    selected A = (markings ι).filter (fun p => p.2 ∈ A) := by
  ext ⟨V, a⟩
  simp only [selected, mem_image, Prod.exists, mem_codes, mark, vertices, Prod.mk.injEq,
    mem_filter, mem_markings]
  constructor
  · rintro ⟨s, c, b, ⟨hc, hb, h⟩, e, rfl⟩; exact ⟨⟨hA _ hc, s, b, hb, h, e⟩, hc⟩
  · rintro ⟨⟨_, s, b, hb, h, e⟩, ha⟩; exact ⟨s, a, b, ⟨ha, hb, h⟩, e, rfl⟩

/-- In dimension `n`, for `1 ≤ k < n`, the number of marked vertex sets whose distinguished
side flips `k` coordinates is `2^(k - 1) * choose n k * choose (2^(n - k)) 2`. This count tests no
condition on vertex weights. -/
theorem card_markings_size (k : ℕ) (hk : 1 ≤ k) (hn : k < Fintype.card ι) :
    ((markings ι).filter (fun p => p.2.card = k)).card =
      2 ^ (k - 1) * (Fintype.card ι).choose k * (2 ^ (Fintype.card ι - k)).choose 2 := by
  let n := Fintype.card ι
  let A := (univ : Finset ι).powersetCard k
  have size : ∀ a ∈ A, (a : Finset ι).card = k := fun _ => mem_powersetCard_univ.mp
  have hA : ∀ a ∈ A, a.Nonempty := fun a ha => card_pos.mp ((size a ha).symm ▸ hk)
  have q : (blocks A).card = n.choose k * (2 ^ (n - k) - 1) := by
    rw [card_blocks, sum_const_nat (m := 2 ^ (n - k) - 1) (fun a ha => by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, size a ha])]
    simp [A, n]
  have hc := four_per_mark A hA
  rw [presentations, card_product, card_univ, Fintype.card_finset, q, selected_eq hA] at hc
  simp only [A, mem_powersetCard_univ] at hc
  have p : 2 ^ n = 2 ^ (k - 1) * 2 * 2 ^ (n - k) := by
    rw [← pow_succ, ← pow_add]; congr 1; dsimp [n]; omega
  have z : (2 ^ (n - k)).choose 2 * 2 = 2 ^ (n - k) * (2 ^ (n - k) - 1) := by
    simpa using Nat.choose_succ_right_eq (2 ^ (n - k)) 1
  change _ = 2 ^ (k - 1) * n.choose k * (2 ^ (n - k)).choose 2
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 4)
  rw [← hc]
  change 2 ^ n * _ = _
  rw [p]
  calc
    _ = 2 ^ (k - 1) * n.choose k * (2 ^ (n - k) * (2 ^ (n - k) - 1)) * 2 := by ring
    _ = _ := by rw [← z]; ring

/-- For a cube of dimension at least two, the possible comparisons along a singleton mask
number `n * choose (2^(n-1)) 2`: one chooses a coordinate and an unordered pair of backgrounds. -/
theorem card_markings_singleton (hn : 1 < Fintype.card ι) :
    ((markings ι).filter (fun p => p.2.card = 1)).card =
      Fintype.card ι * (2 ^ (Fintype.card ι - 1)).choose 2 := by
  simpa using card_markings_size (ι := ι) 1 le_rfl hn

end

end CubeRectangle
