/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.BagSelection
public import CSLibExt.Computability.Complexity.Parameterized.HardnessClauses
import Mathlib.Data.Finset.Fin
import Mathlib.Data.List.ProdSigma

/-!
# Gluing the local tables into a weighted assignment

Every slot has a singleton color. Compatibility forces every table mentioning
the slot to use the singleton's value. Two-slot colors then force the resulting
assignment to be strictly increasing. The bounded-width false-clause witnesses
live in colors of size at most twice the clause width.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows

open Cslib.Complexity.PolynomialEncoding.Comprehension

private theorem allowed_spec (slots shape : List ℕ) (p : Formula) (r : Local) :
    allowed slots shape p r ↔
      (∀ i ∈ shape, ∃ v, (i, v) ∈ r) ∧ (∀ e ∈ r, e.1 ∈ shape) ∧
      (∀ e ∈ r, ∀ z ∈ r, (e.1 = z.1 → e.2 = z.2) ∧ (e.1 < z.1 → e.2 < z.2)) ∧
      ∀ c ∈ p, ¬ ∀ l ∈ c, forcesFalse slots r l := by
  simp only [allowed, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    List.contains_iff_mem, decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    and_assoc]
  constructor
  · rintro ⟨cover, rest⟩
    exact ⟨fun i hi => by obtain ⟨⟨_, v⟩, h, rfl⟩ := cover i hi; exact ⟨v, h⟩, rest⟩
  · rintro ⟨cover, rest⟩
    exact ⟨fun i hi => by obtain ⟨v, h⟩ := cover i hi; exact ⟨(i, v), h, rfl⟩, rest⟩

private def shapeSet (k : ℕ) (s : List ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun i => i.val ∈ s

@[simp] private theorem mem_shapeSet {k : ℕ} (s : List ℕ) (i : Fin k) :
    i ∈ shapeSet k s ↔ i.val ∈ s := by simp [shapeSet]

private theorem card_shapeSet (k : ℕ) (s : List ℕ) : (shapeSet k s).card ≤ s.length := by
  have h : (shapeSet k s).image Fin.val ⊆ s.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr ((mem_shapeSet s i).mp hi)
  have sz := Finset.card_le_card h
  rw [Finset.card_image_of_injective _ Fin.val_injective] at sz
  exact sz.trans (List.toFinset_card_le s)

private theorem false_iff {k : ℕ} (a : Fin k → ℕ) (b : Finset (Fin k)) (r : Local)
    (bounds : ∀ e ∈ r, e.1 < k)
    (table : ∀ (i : Fin k) v, (i.val, v) ∈ r ↔ i ∈ b ∧ a i = v)
    (l : ℕ × Bool) :
    forcesFalse (List.range k) r l ↔ WeightedClauses.forcesFalse b (fun j => a j.val) l := by
  obtain ⟨z, pos⟩ := l
  cases pos with
  | false =>
    simp only [forcesFalse, WeightedClauses.forcesFalse, Bool.false_eq_true, ↓reduceIte,
      List.any_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨⟨j, v⟩, hj, rfl⟩
      let i : Fin k := ⟨j, bounds _ hj⟩
      obtain ⟨hi, hv⟩ := (table i _).mp hj
      exact ⟨⟨i, hi⟩, hv⟩
    · rintro ⟨j, hj⟩
      exact ⟨(j.val.val, z), (table _ _).mpr ⟨j.property, hj⟩, rfl⟩
  | true =>
    simp only [forcesFalse, WeightedClauses.forcesFalse, ↓reduceIte, List.all_eq_true,
      List.mem_range, List.any_eq_true, decide_eq_true_eq]
    constructor
    · intro h i
      obtain ⟨⟨j, v⟩, hj, hc⟩ := h i.val i.isLt
      let j' : Fin k := ⟨j, bounds _ hj⟩
      obtain ⟨hb, hv⟩ := (table j' v).mp hj
      exact ⟨⟨j', hb⟩, hv ▸ hc⟩
    · intro h i hi
      obtain ⟨j, hj⟩ := h ⟨i, hi⟩
      exact ⟨(j.val.val, a j.val), (table _ _).mpr ⟨j.property, rfl⟩, hj⟩

private theorem selection_to_assignment (d k n : ℕ) (family : List Formula)
    (width : ∀ p ∈ family, ∀ c ∈ p, c.toFinset.card ≤ d)
    (selection : Selection (max 2 (2 * d)) (List.range k) (List.range n) family) :
    HasAssignment k n family := by
  let B := max 2 (2 * d)
  let cs := tuples (List.range k) B
  obtain ⟨p, hp, f, ok, compat⟩ := selection
  have info (c : Fin cs.length) := (allowed_spec _ _ _ _).mp (ok c).2
  have bound (c : Fin cs.length) (e) (he : e ∈ f c) : e.1 < k ∧ e.2 < n := by
    have h := (mem_tuples.mp (ok c).1).2 _ he
    exact ⟨List.mem_range.mp (List.mem_product.mp h).1, List.mem_range.mp (List.mem_product.mp h).2⟩
  have find (s : List ℕ) (h : s.length ≤ B) (hs : ∀ i ∈ s, i < k) :
      ∃ c : Fin cs.length, cs[c.val] = s := by
    have hm : s ∈ cs := mem_tuples.mpr ⟨h, by simpa using hs⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    exact ⟨⟨i, hi⟩, he⟩
  have single (i : Fin k) : ∃ c : Fin cs.length, cs[c.val] = [i.val] :=
    find _ (by dsimp [B]; simp) (by simp)
  choose index singleton using single
  have chooseValue (i : Fin k) : ∃ v, (i.val, v) ∈ f (index i) :=
    (info (index i)).1 _ (by rw [singleton]; simp)
  choose a chosen using chooseValue
  have reads (c : Fin cs.length) (i : Fin k) (v : ℕ) (hv : (i.val, v) ∈ f c) : a i = v := by
    by_cases same : index i = c
    · have ha := chosen i
      rw [same] at ha
      exact ((info c).2.2.1 _ ha _ hv).1 rfl
    · exact (agrees_iff ..).mp (compat _ _ same) _ (chosen i) _ hv rfl
  have inc : StrictMono a := by
    intro i j hij
    obtain ⟨c, shape⟩ := find [i.val, j.val] (by dsimp [B]; simp)
      (by intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl <;> exact Fin.isLt _)
    obtain ⟨v, hv⟩ := (info c).1 i.val (by rw [shape]; simp)
    obtain ⟨w, hw⟩ := (info c).1 j.val (by rw [shape]; simp)
    rw [reads c i v hv, reads c j w hw]
    exact ((info c).2.2.1 _ hv _ hw).2 hij
  refine ⟨p, hp, a, fun i => (bound _ _ (chosen i)).2, inc,
    (WeightedClauses.all_bags_iff_models d a inc p (width p hp)).mp ?_⟩
  intro b
  let s := b.val.toList.map Fin.val
  obtain ⟨c, shape⟩ := find s
    (by simpa only [s, List.length_map, Finset.length_toList] using b.property)
    (by intro i hi; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi; exact j.isLt)
  have isSlot (i : Fin k) : i.val ∈ cs[c.val] ↔ i ∈ b.val := by
    simp only [shape, s, List.mem_map, Finset.mem_toList, Fin.val_inj, exists_eq_right]
  have pair (i : Fin k) (v : ℕ) : (i.val, v) ∈ f c ↔ i ∈ b.val ∧ a i = v := by
    constructor
    · exact fun h => ⟨(isSlot i).mp ((info c).2.1 _ h), reads c i v h⟩
    · rintro ⟨hi, rfl⟩
      obtain ⟨w, hw⟩ := (info c).1 _ ((isSlot i).mpr hi)
      rwa [reads c i w hw]
  intro cl hcl bad
  exact (info c).2.2.2 cl hcl fun l hl =>
    (false_iff a _ _ (fun e he => (bound c e he).1) pair l).mpr (bad l hl)

private theorem assignment_to_selection (d k n : ℕ) (family : List Formula)
    (width : ∀ p ∈ family, ∀ c ∈ p, c.toFinset.card ≤ d)
    (h : HasAssignment k n family) :
    Selection (max 2 (2 * d)) (List.range k) (List.range n) family := by
  obtain ⟨p, hp, a, valid, inc, models⟩ := h
  let B := max 2 (2 * d)
  let cs := tuples (List.range k) B
  let val (i : ℕ) := if hi : i < k then a ⟨i, hi⟩ else 0
  let f (c : Fin cs.length) := cs[c.val].map fun i => (i, val i)
  have hval (i : Fin k) : val i.val = a i := by simp [val, i.isLt]
  have input (c : Fin cs.length) := mem_tuples.mp (List.getElem_mem c.isLt : cs[c.val] ∈ cs)
  have mem (c : Fin cs.length) (i v : ℕ) :
      (i, v) ∈ f c ↔ i ∈ cs[c.val] ∧ val i = v := by simp [f]
  have validSlot (c : Fin cs.length) {i : ℕ} (hi : i ∈ cs[c.val]) : i < k :=
    List.mem_range.mp ((input c).2 _ hi)
  have pos (c : Fin cs.length) (e : ℕ × ℕ) (he : e ∈ f c) : e.1 < k :=
    validSlot c ((mem c e.1 e.2).mp he).1
  refine ⟨p, hp, f, fun c => ⟨?_, (allowed_spec ..).mpr ?_⟩, ?_⟩
  · refine mem_tuples.mpr ⟨by simpa only [f, List.length_map] using (input c).1, ?_⟩
    rintro ⟨i, v⟩ hi
    have hv := (mem c i v).mp hi
    let j : Fin k := ⟨i, validSlot c hv.1⟩
    have he : a j = v := (hval j).symm.trans hv.2
    exact List.mem_product.mpr ⟨List.mem_range.mpr j.isLt, List.mem_range.mpr (he ▸ valid j)⟩
  · refine ⟨fun i hi => ⟨_, (mem c i _).mpr ⟨hi, rfl⟩⟩,
      fun e he => ((mem c e.1 e.2).mp he).1, ?_, ?_⟩
    · rintro ⟨i, v⟩ hv ⟨j, w⟩ hw
      have h1 := ((mem c i v).mp hv).2
      have h2 := ((mem c j w).mp hw).2
      refine ⟨fun he => h1.symm.trans ((congrArg val he).trans h2), fun hl => ?_⟩
      let u : Fin k := ⟨i, pos c _ hv⟩
      let z : Fin k := ⟨j, pos c _ hw⟩
      rw [← h1, ← h2, hval u, hval z]
      exact inc (show u < z from hl)
    · let b : WeightedClauses.Bag k (2 * d) :=
        ⟨shapeSet k cs[c.val], (card_shapeSet ..).trans (input c).1⟩
      have pair (i : Fin k) (v : ℕ) : (i.val, v) ∈ f c ↔ i ∈ b.val ∧ a i = v := by
        rw [mem, hval]
        exact and_congr_left' (mem_shapeSet ..).symm
      intro cl hcl allFalse
      exact (WeightedClauses.all_bags_iff_models d a inc p (width p hp)).mpr models b cl hcl
        fun l hl => (false_iff a _ _ (pos c) pair l).mp (allFalse l hl)
  · intro c j _
    apply (agrees_iff ..).mpr
    rintro ⟨i, v⟩ hv ⟨q, w⟩ hw rfl
    exact ((mem c _ _).mp hv).2.symm.trans ((mem j _ _).mp hw).2

/-- The explicit table graph is correct for every signed bounded-width
instance, including empty families, color domains, and variable domains. -/
theorem query_correct (d k n : ℕ) (family : List Formula)
    (width : ∀ p ∈ family, ∀ c ∈ p, c.toFinset.card ≤ d) :
    let result := query d (List.range k) (List.range n) family
    CliqueParam result.1 result.2 ↔ HasAssignment k n family := by
  dsimp only
  rw [query_iff_selection]
  exact ⟨selection_to_assignment d k n family width, assignment_to_selection d k n family width⟩

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows
