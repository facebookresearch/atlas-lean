/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.LonelyMarriageableSingles
import Mathlib.Data.Fin.Embedding
import MathlibExt.Combinatorics.Finpartition.Comap

/-!
# Strict growth of the lonely and marriageable singles counts

Attach the new last point to the previous last point's block for lonely partitions, and
append a new singleton block for marriageable partitions. Restriction to the old points
recovers the original partition in both cases. Each construction misses a partition of
its own class.

Adding two points at the end gives four disjoint families. The two points can be singletons,
form their own block, or include one singleton and one point attached to its old cyclic neighbor.
If the attachment consumes a marriageable singleton, the new singleton can replace it.

## References

* Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and Catalan
  Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, pp. 1–13,
  Proposition 20 (pp. 6–7) and Proposition 22 (pp. 7–8)
  (<https://cs.uwaterloo.ca/journals/JIS/VOL28/Rouyer/rouyer5.pdf>).
* H. W. Becker, "Planar rhyme schemes", *Bull. Amer. Math. Soc.* 58 (1952), p. 39;
  G. Kreweras, "Sur les partitions non croisées d’un cycle", *Discrete Math.* 1 (1972),
  pp. 333–350; and Y. Poupard, "Étude et dénombrement parallèles des partitions non-croisées
  d’un cycle et des découpages d’un polygone convexe", *Discrete Math.* 2 (1972), pp. 279–288.
  These are credited in Section 1 of Rouyer and Ninet for early work on noncrossing partitions.
-/

namespace MetaMathlibExt

open Finset NoncrossingPartition

variable {n m : ℕ}

private theorem part_eq_iff_mem (P : SetPartition n) (x y : Fin n) :
    P.part x = P.part y ↔ x ∈ P.part y :=
  (P.mem_part_iff_part_eq_part (mem_univ x) (mem_univ y)).symm

private theorem partition_ext {P Q : SetPartition n}
    (h : ∀ x y, x ∈ P.part y ↔ x ∈ Q.part y) : P = Q := by
  have heq (x : Fin n) : P.part x = Q.part x := Finset.ext (fun y => h y x)
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨x, -, rfl⟩ := P.part_surjOn hB
    rw [heq x]
    exact part_mem_parts Q x
  · intro hB
    obtain ⟨x, -, rfl⟩ := Q.part_surjOn hB
    rw [← heq x]
    exact part_mem_parts P x

private theorem mem_part_comap (P : SetPartition n) (f : Fin m → Fin n) (x y : Fin m) :
    x ∈ (P.comap f).part y ↔ f x ∈ P.part (f y) := by
  let B := univ.filter fun z : Fin m => f z ∈ P.part (f y)
  have hy : y ∈ B := by simp [B]
  have hB : B ∈ (P.comap f).parts :=
    Finpartition.mem_comap_parts.mpr ⟨⟨y, hy⟩, P.part (f y), part_mem_parts P _, rfl⟩
  rw [(P.comap f).part_eq_of_mem hB hy]
  simp [B]

private theorem part_comap_eq (P : SetPartition n) (f : Fin m → Fin n) (x y : Fin m) :
    (P.comap f).part x = (P.comap f).part y ↔ P.part (f x) = P.part (f y) := by
  simp only [part_eq_iff_mem, mem_part_comap]

private theorem mergedSameBlock_comap (P : SetPartition n) (f : Fin m → Fin n)
    (i j x y : Fin m) :
    mergedSameBlock (P.comap f) i j x y ↔ mergedSameBlock P (f i) (f j) (f x) (f y) := by
  simp only [mergedSameBlock, part_comap_eq, mem_part_comap]

-- A crossing depends only on the equality relation on the block labels.
private def LabelCrossing {α : Type*} (f : Fin n → α) : Prop :=
  ∃ a b c d, a < b ∧ b < c ∧ c < d ∧ f a = f c ∧ f b = f d ∧ f a ≠ f b

private theorem crossing_map_of_monotone {α β : Type*} {f : Fin m → α} {g : Fin n → β}
    (e : Fin m → Fin n) (he : Monotone e) {S : Fin m → Prop}
    (heq : ∀ x y, S x → S y → (f x = f y ↔ g (e x) = g (e y)))
    (hgap : ∀ x y, x.val + 1 < y.val → f x = f y → S x ∧ S y)
    (h : LabelCrossing f) : LabelCrossing g := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩ := h
  simp only [Fin.lt_def] at hab hbc hcd
  obtain ⟨ha, hc⟩ := hgap _ _ (by omega) hac
  obtain ⟨hb, hd⟩ := hgap _ _ (by omega) hbd
  have hac' := (heq _ _ ha hc).mp hac
  have hbd' := (heq _ _ hb hd).mp hbd
  have hne' := fun h => hne ((heq _ _ ha hb).mpr h)
  exact ⟨e a, e b, e c, e d, lt_of_le_of_ne (he hab.le) (fun h => hne' (congrArg g h)),
    lt_of_le_of_ne (he hbc.le) (fun h => hne' (hac'.trans (congrArg g h.symm))),
    lt_of_le_of_ne (he hcd.le) (fun h => hne' (hac'.trans ((congrArg g h).trans hbd'.symm))),
    hac', hbd', hne'⟩

-- A monotone pullback cannot create a crossing.
private theorem isNoncrossing_comap (P : SetPartition n) (hP : IsNoncrossing P)
    (f : Fin m → Fin n) (hf : Monotone f) : IsNoncrossing (P.comap f) := by
  intro h
  exact hP (crossing_map_of_monotone (f := (P.comap f).part) (g := P.part) f hf
    (S := fun _ => True) (fun x y _ _ => part_comap_eq P f x y)
    (fun _ _ _ _ => ⟨trivial, trivial⟩) h)

private def contractLast (hn : 0 < n) (x : Fin (n + 1)) : Fin n :=
  ⟨min x.val (n - 1), lt_of_le_of_lt (min_le_right ..) (by omega)⟩

private theorem contractLast_castSucc (hn : 0 < n) (x : Fin n) :
    contractLast hn x.castSucc = x := by
  apply Fin.ext
  change min x.val (n - 1) = x.val
  exact min_eq_left (by have := x.isLt; omega)

private theorem contractLast_monotone (hn : 0 < n) : Monotone (contractLast hn) := by
  intro x y h
  change min x.val (n - 1) ≤ min y.val (n - 1)
  exact min_le_min_right _ (show x.val ≤ y.val from h)

private def duplicateLast (hn : 0 < n) (P : _root_.NoncrossingPartition n) :
    _root_.NoncrossingPartition (n + 1) :=
  ⟨P.val.comap (contractLast hn),
    isNoncrossing_comap P.val P.property _ (contractLast_monotone hn)⟩

private theorem isMarriageableSingles_of_duplicateLast (hn : 0 < n)
    (P : _root_.NoncrossingPartition n) (h : IsMarriageableSingles (duplicateLast hn P).val) :
    IsMarriageableSingles P.val := by
  change IsMarriageableSingles (P.val.comap (contractLast hn)) at h
  obtain ⟨i, j, hij, hi, hj, hnc⟩ := h
  have oldSingleton (x : Fin (n + 1)) (hx : (P.val.comap (contractLast hn)).part x = {x}) :
      P.val.part (contractLast hn x) = {contractLast hn x} := by
    ext y
    constructor
    · intro hy
      have hy' : y.castSucc ∈ (P.val.comap (contractLast hn)).part x :=
        (mem_part_comap ..).mpr (by simpa only [contractLast_castSucc] using hy)
      rw [hx] at hy'
      have he := congrArg (contractLast hn) (mem_singleton.mp hy')
      simpa only [contractLast_castSucc, mem_singleton] using he
    · rintro hy
      rw [mem_singleton.mp hy]
      exact mem_part_self P.val _
  refine ⟨contractLast hn i, contractLast hn j, ?_, oldSingleton i hi, oldSingleton j hj, ?_⟩
  · intro he
    have hm : i ∈ (P.val.comap (contractLast hn)).part j :=
      (mem_part_comap ..).mpr (he ▸ mem_part_self P.val _)
    exact hij (mem_singleton.mp (hj ▸ hm))
  · rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
    -- An old crossing after merging lifts along the increasing section of `contractLast`.
    apply hnc
    refine ⟨a.castSucc, b.castSucc, c.castSucc, d.castSucc, hab, hbc, hcd, ?_, ?_, ?_⟩
    · simpa only [mergedSameBlock_comap, contractLast_castSucc] using hac
    · simpa only [mergedSameBlock_comap, contractLast_castSucc] using hbd
    · simpa only [mergedSameBlock_comap, contractLast_castSucc] using hne

private noncomputable def labelPartition {α : Type*} (f : Fin n → α) : SetPartition n := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker f)

private theorem mem_part_label {α : Type*} (f : Fin n → α) (x y : Fin n) :
    x ∈ (labelPartition f).part y ↔ f x = f y := by
  classical
  rw [labelPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  exact eq_comm

private theorem part_eq_label {α : Type*} (f : Fin n → α) (x y : Fin n) :
    (labelPartition f).part x = (labelPartition f).part y ↔ f x = f y :=
  (part_eq_iff_mem ..).trans (mem_part_label ..)

private noncomputable def appendLast (P : SetPartition n) : SetPartition (n + 1) :=
  labelPartition (Fin.lastCases none (fun x => some (P.part x)))

private theorem part_appendLast_castSucc (P : SetPartition n) (y : Fin n) :
    (appendLast P).part y.castSucc = (P.part y).map Fin.castSuccEmb := by
  ext x
  refine Fin.lastCases ?_ (fun x => ?_) x
  · simp [appendLast, mem_part_label, Finset.mem_map, Fin.castSuccEmb_apply]
  · change _ ↔ Fin.castSuccEmb x ∈ (P.part y).map Fin.castSuccEmb
    rw [Finset.mem_map', appendLast, mem_part_label]
    simpa only [Fin.lastCases_castSucc, Option.some.injEq] using part_eq_iff_mem P x y

private theorem part_appendLast_last (P : SetPartition n) :
    (appendLast P).part (Fin.last n) = {Fin.last n} := by
  ext x
  refine Fin.lastCases ?_ (fun x => ?_) x <;> simp [appendLast, mem_part_label]

-- A crossing cannot use a new last point that is alone in its block. This also applies
-- after merging two old singleton blocks.
private theorem crossing_of_append {R : Fin (n + 1) → Fin (n + 1) → Prop}
    {S : Fin n → Fin n → Prop} (old : ∀ x y : Fin n, R x.castSucc y.castSucc ↔ S x y)
    (last : ∀ x, R x (Fin.last n) → x = Fin.last n)
    (h : ∃ a b c d, a < b ∧ b < c ∧ c < d ∧ R a c ∧ R b d ∧ ¬ R a b) :
    ∃ a b c d, a < b ∧ b < c ∧ c < d ∧ S a c ∧ S b d ∧ ¬ S a b := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩ := h
  have hd : d.val < n := by
    by_contra! h
    have he : d = Fin.last n := Fin.ext (by simp; omega)
    exact (hbc.trans hcd).ne ((last b (he ▸ hbd)).trans he.symm)
  let d' := d.castLT hd
  let c' := c.castLT (Nat.lt_trans hcd hd)
  let b' := b.castLT (Nat.lt_trans hbc c'.isLt)
  let a' := a.castLT (Nat.lt_trans hab b'.isLt)
  exact ⟨a', b', c', d', hab, hbc, hcd, (old _ _).mp hac, (old _ _).mp hbd,
    fun h => hne ((old _ _).mpr h)⟩

private noncomputable def appendLastNCP (P : _root_.NoncrossingPartition n) :
    _root_.NoncrossingPartition (n + 1) :=
  ⟨appendLast P.val, by
    intro h
    apply P.property
    refine crossing_of_append (fun x y => ?_) (fun x hx => ?_) h
    · simp only [part_appendLast_castSucc, Finset.map_inj]
    · rw [part_eq_iff_mem, part_appendLast_last, mem_singleton] at hx
      exact hx⟩

private theorem isMarriageableSingles_appendLast {P : SetPartition n}
    (hP : IsMarriageableSingles P) : IsMarriageableSingles (appendLast P) := by
  obtain ⟨i, j, hij, hi, hj, hnc⟩ := hP
  refine ⟨i.castSucc, j.castSucc, fun h => hij (Fin.castSuccEmb.injective h), ?_, ?_, ?_⟩
  · simp [part_appendLast_castSucc, hi]
  · simp [part_appendLast_castSucc, hj]
  · intro h
    apply hnc
    refine crossing_of_append (fun x y => ?_) (fun x hx => ?_) h
    · simp only [mergedSameBlock, part_appendLast_castSucc, Finset.map_inj]
      simp only [← Fin.castSuccEmb_apply, Finset.mem_map']
    · rcases hx with he | ⟨-, hlast⟩
      · rwa [part_eq_iff_mem, part_appendLast_last, mem_singleton] at he
      · rw [part_appendLast_castSucc, part_appendLast_castSucc, hi, hj] at hlast
        rcases hlast with hlast | hlast
        · exact (Fin.castSucc_ne_last i (mem_singleton.mp hlast).symm).elim
        · exact (Fin.castSucc_ne_last j (mem_singleton.mp hlast).symm).elim

private theorem restrict_duplicateLast (hn : 0 < n) (P : _root_.NoncrossingPartition n) :
    ((duplicateLast hn P).val.comap Fin.castSucc) = P.val := by
  change (P.val.comap (contractLast hn)).comap Fin.castSucc = P.val
  rw [Finpartition.comap_comap, show contractLast hn ∘ Fin.castSucc = id from
    funext (contractLast_castSucc hn), Finpartition.comap_refl]

private theorem restrict_appendLast (P : _root_.NoncrossingPartition n) :
    ((appendLastNCP P).val.comap Fin.castSucc) = P.val := by
  change (appendLast P.val).comap Fin.castSucc = P.val
  apply partition_ext
  intro x y
  rw [mem_part_comap, part_appendLast_castSucc]
  exact Finset.mem_map' Fin.castSuccEmb

-- The indiscrete old block has at least two points, so only the appended point is a singleton.
private theorem appendLast_indiscrete_lonely (hn : 2 ≤ n) :
    ¬ IsMarriageableSingles (appendLast (indiscrete n).val) := by
  have onlyLast (x : Fin (n + 1)) (hx : (appendLast (indiscrete n).val).part x = {x}) :
      x = Fin.last n := by
    revert hx
    refine Fin.lastCases (fun _ => rfl) (fun x hx => ?_) x
    have hcard := congrArg Finset.card hx
    change ((appendLast (indiscrete n).val).part x.castSucc).card =
      ({x.castSucc} : Finset (Fin (n + 1))).card at hcard
    rw [part_appendLast_castSucc, Finset.card_map] at hcard
    change (block (indiscrete n) x).card = _ at hcard
    simp at hcard
    omega
  rintro ⟨i, j, hij, hi, hj, -⟩
  exact hij ((onlyLast i hi).trans (onlyLast j hj).symm)

-- Labels 0 and 1 isolate the first two points; label 2 groups every remaining point.
private def firstTwoLabel (x : Fin (n + 1)) : ℕ := min x.val 2

private noncomputable def firstTwo (n : ℕ) : _root_.NoncrossingPartition (n + 1) :=
  ⟨labelPartition firstTwoLabel, by
    rintro ⟨a, b, c, d, hab, hbc, _, hac, _, hne⟩
    rw [part_eq_label] at hac
    simp only [Ne, part_eq_label] at hne
    have hf : Monotone (firstTwoLabel (n := n)) := fun _ _ h => min_le_min_right _ h
    exact hne (le_antisymm (hf hab.le) ((hf hbc.le).trans hac.ge))⟩

private theorem firstTwo_marriageable (hn : 3 ≤ n) : IsMarriageableSingles (firstTwo n).val := by
  let i : Fin (n + 1) := ⟨0, by omega⟩
  let j : Fin (n + 1) := ⟨1, by omega⟩
  have singleton (x : Fin (n + 1)) (hx : x.val < 2) : (firstTwo n).val.part x = {x} := by
    ext y
    change y ∈ (labelPartition firstTwoLabel).part x ↔ y ∈ {x}
    simp only [mem_part_label, firstTwoLabel, mem_singleton, Fin.ext_iff]
    omega
  have hi : (firstTwo n).val.part i = {i} := singleton i (by simp [i])
  have hj : (firstTwo n).val.part j = {j} := singleton j (by simp [j])
  refine ⟨i, j, by simp [Fin.ext_iff, i, j], hi, hj, ?_⟩
  rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
  simp only [mergedSameBlock, hi, hj, mem_singleton] at hac hbd hne
  simp only [firstTwo, part_eq_label, firstTwoLabel, Fin.ext_iff, i, j] at hac hbd hne
  simp only [Fin.lt_def] at hab hbc hcd
  omega

private theorem duplicateLast_ne_appendLast_indiscrete (hn : 0 < n)
    (P : _root_.NoncrossingPartition n) : duplicateLast hn P ≠ appendLastNCP (indiscrete n) := by
  intro h
  let k : Fin n := ⟨n - 1, by omega⟩
  have he : contractLast hn k.castSucc = contractLast hn (Fin.last n) := by
    rw [contractLast_castSucc]
    apply Fin.ext
    change n - 1 = min n (n - 1)
    exact (min_eq_right (Nat.sub_le n 1)).symm
  have hm : k.castSucc ∈ (duplicateLast hn P).val.part (Fin.last n) := by
    change k.castSucc ∈ (P.val.comap (contractLast hn)).part (Fin.last n)
    rw [mem_part_comap, he]
    exact mem_part_self P.val _
  rw [h] at hm
  change k.castSucc ∈ (appendLast (indiscrete n).val).part (Fin.last n) at hm
  rw [part_appendLast_last, mem_singleton] at hm
  exact Fin.castSucc_ne_last k hm

private theorem appendLast_ne_firstTwo (hn : 3 ≤ n) (P : _root_.NoncrossingPartition n) :
    appendLastNCP P ≠ firstTwo n := by
  intro h
  let k : Fin (n + 1) := ⟨2, by omega⟩
  have hm : k ∈ (firstTwo n).val.part (Fin.last n) := by
    change k ∈ (labelPartition firstTwoLabel).part (Fin.last n)
    rw [mem_part_label]
    change min 2 2 = min n 2
    rw [min_self, min_eq_right (show 2 ≤ n by omega)]
  rw [← h] at hm
  change k ∈ (appendLast P.val).part (Fin.last n) at hm
  rw [part_appendLast_last, mem_singleton, Fin.ext_iff] at hm
  change 2 = n at hm
  omega

private theorem extension_source_eq {P Q : _root_.NoncrossingPartition n}
    {R S : _root_.NoncrossingPartition m} {e : Fin n → Fin m}
    (hR : R.val.comap e = P.val) (hS : S.val.comap e = Q.val) (h : R = S) : P = Q :=
  NoncrossingPartition.ext (hR.symm.trans ((congrArg (fun T => T.val.comap e) h).trans hS))

private theorem card_filter_lt_of_extension
    (p : SetPartition n → Prop) (q : SetPartition (n + 1) → Prop)
    [DecidablePred p] [DecidablePred q]
    (f : _root_.NoncrossingPartition n → _root_.NoncrossingPartition (n + 1))
    (hrestrict : ∀ P, (f P).val.comap Fin.castSucc = P.val)
    (hm : ∀ P, p P.val → q (f P).val)
    (Q : _root_.NoncrossingPartition (n + 1)) (hQ : q Q.val) (hmiss : ∀ P, f P ≠ Q) :
    (univ.filter fun P : _root_.NoncrossingPartition n => p P.val).card <
      (univ.filter fun P : _root_.NoncrossingPartition (n + 1) => q P.val).card := by
  let e : _root_.NoncrossingPartition n ↪ _root_.NoncrossingPartition (n + 1) :=
    ⟨f, fun P P' h => extension_source_eq (hrestrict P) (hrestrict P') h⟩
  rw [← Finset.card_map e]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro R hR
    obtain ⟨P, hp, rfl⟩ := mem_map.mp hR
    exact mem_filter.mpr ⟨mem_univ _, hm P (mem_filter.mp hp).2⟩
  · intro he
    have hmem : Q ∈ _ := he ▸ mem_filter.mpr ⟨mem_univ Q, hQ⟩
    obtain ⟨P, -, hP⟩ := mem_map.mp hmem
    exact hmiss P hP

/-- **Strict growth of the lonely and marriageable singles counts.** $L_n < L_{n+1}$ for every
$n \ge 2$, and $M_n < M_{n+1}$ for every $n \ge 3$, where $M_n$ is the number of noncrossing
partitions of $\{0, \dots, n-1\}$ that are marriageable singles partitions and $L_n$ is the
number of those that are not.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 20
(`jis-2025-25.1.1-prop-20`). -/
public theorem lonely_marriageable_strictMono :
    (∀ n, 2 ≤ n → lonelySinglesCount n < lonelySinglesCount (n + 1)) ∧
    ∀ n, 3 ≤ n → marriageableSinglesCount n < marriageableSinglesCount (n + 1) := by
  constructor
  · intro n hn
    have hn' : 0 < n := by omega
    exact card_filter_lt_of_extension (fun P => ¬ IsMarriageableSingles P)
      (fun P => ¬ IsMarriageableSingles P) (duplicateLast hn') (restrict_duplicateLast hn')
      (fun P h hm => h (isMarriageableSingles_of_duplicateLast hn' P hm))
      (appendLastNCP (indiscrete n)) (appendLast_indiscrete_lonely hn)
      (duplicateLast_ne_appendLast_indiscrete hn')
  · intro n hn
    exact card_filter_lt_of_extension IsMarriageableSingles IsMarriageableSingles appendLastNCP
      restrict_appendLast (fun _ => isMarriageableSingles_appendLast) (firstTwo n)
      (firstTwo_marriageable hn) (appendLast_ne_firstTwo hn)

private def joinLabel {α : Type*} [DecidableEq α] (a b : α) (v : α) : Option α :=
  if v = a ∨ v = b then none else some v

private theorem joinLabel_eq_iff {α : Type*} [DecidableEq α] {a b x y : α} :
    joinLabel a b x = joinLabel a b y ↔
      x = y ∨ ((x = a ∨ x = b) ∧ (y = a ∨ y = b)) := by
  unfold joinLabel
  split <;> split <;> simp_all <;> grind

private def LabelMarriageable {α : Type*} [DecidableEq α] (f : Fin n → α) : Prop :=
  ∃ i j, i ≠ j ∧ (∀ x, f x = f i → x = i) ∧ (∀ x, f x = f j → x = j) ∧
    ¬ LabelCrossing (joinLabel (f i) (f j) ∘ f)

private theorem labelMarriageable_iff {α : Type*} [DecidableEq α] (f : Fin n → α) :
    LabelMarriageable f ↔ IsMarriageableSingles (labelPartition f) := by
  have hs (i : Fin n) : (∀ x, f x = f i → x = i) ↔ (labelPartition f).part i = {i} := by
    simp only [Finset.ext_iff, mem_part_label, mem_singleton]
    exact forall_congr' (fun x => ⟨fun h => ⟨h, by rintro rfl; rfl⟩, Iff.mp⟩)
  simp only [LabelMarriageable, IsMarriageableSingles, hs, LabelCrossing, Function.comp_apply,
    joinLabel_eq_iff, mergedHasCrossing, mergedSameBlock, part_eq_label, mem_part_label, Ne]

private abbrev keepOld (x : Fin n) : Fin (n + 2) := x.castSucc.castSucc
private abbrev penultimate (n : ℕ) : Fin (n + 2) := (Fin.last n).castSucc
private abbrev ultimate (n : ℕ) : Fin (n + 2) := Fin.last (n + 1)

private def endLabels {α : Type*} (f : Fin n → α) (a b : α) : Fin (n + 2) → α :=
  Fin.lastCases b (Fin.lastCases a f)

@[simp] private theorem endLabels_old {α : Type*} (f : Fin n → α) (a b : α) (x : Fin n) :
    endLabels f a b (keepOld x) = f x := by simp [endLabels]

@[simp] private theorem endLabels_penultimate {α : Type*} (f : Fin n → α) (a b : α) :
    endLabels f a b (penultimate n) = a := by simp [endLabels]

@[simp] private theorem endLabels_ultimate {α : Type*} (f : Fin n → α) (a b : α) :
    endLabels f a b (ultimate n) = b := by simp [endLabels]

private theorem endCases {C : Fin (n + 2) → Prop} (ho : ∀ x : Fin n, C (keepOld x))
    (ha : C (penultimate n)) (hb : C (ultimate n)) (x : Fin (n + 2)) : C x :=
  Fin.lastCases hb (Fin.lastCases ha ho) x

private theorem comp_endLabels {α β : Type*} (g : α → β) (f : Fin n → α) (a b : α) :
    g ∘ endLabels f a b = endLabels (g ∘ f) (g a) (g b) := by
  funext x
  induction x using endCases <;> simp

private theorem not_crossing_endLabels_fresh {α : Type*} {f : Fin n → α} {a b : α}
    (hf : ¬ LabelCrossing f) (ha : ∀ x, f x ≠ a) (hb : ∀ x, f x ≠ b) :
    ¬ LabelCrossing (endLabels f a b) := by
  have hgap (x y : Fin (n + 2)) (hxy : x.val + 1 < y.val)
      (h : endLabels f a b x = endLabels f a b y) : y.val < n := by
    induction y using endCases with
    | ho y => exact y.isLt
    | ha =>
      induction x using endCases with
      | ho x => exact (ha x (by simpa using h)).elim
      | ha => simp only [Fin.val_castSucc, Fin.val_last] at hxy; omega
      | hb => simp only [Fin.val_castSucc, Fin.val_last] at hxy; omega
    | hb =>
      induction x using endCases with
      | ho x => exact (hb x (by simpa using h)).elim
      | ha => simp only [Fin.val_castSucc, Fin.val_last] at hxy; omega
      | hb => simp only [Fin.val_last] at hxy; omega
  rintro ⟨x, y, z, w, hxy, hyz, hzw, hxz, hyw, hne⟩
  simp only [Fin.lt_def] at hxy hyz hzw
  have hw := hgap y w (by omega) hyw
  let w' := w.castLT hw
  let z' := z.castLT (Nat.lt_trans hzw hw)
  let y' := y.castLT (Nat.lt_trans hyz z'.isLt)
  let x' := x.castLT (Nat.lt_trans hxy y'.isLt)
  have hval (v : Fin (n + 2)) (hv : v.val < n) :
      endLabels f a b v = f (v.castLT hv) := by
    have h : keepOld (v.castLT hv) = v := Fin.ext rfl
    exact (congrArg (endLabels f a b) h.symm).trans (endLabels_old ..)
  exact hf ⟨x', y', z', w', hxy, hyz, hzw,
    (hval x _).symm.trans (hxz.trans (hval z _)),
    (hval y _).symm.trans (hyw.trans (hval w _)),
    fun h => hne ((hval x _).trans (h.trans (hval y _).symm))⟩

private theorem singleton_endLabels_old {α : Type*} {f : Fin n → α} {a b : α} {i : Fin n}
    (hi : ∀ x, f x = f i → x = i) (ha : a ≠ f i) (hb : b ≠ f i) :
    ∀ x, endLabels f a b x = endLabels f a b (keepOld i) → x = keepOld i := by
  intro x
  induction x using endCases <;> simp_all

private theorem singleton_endLabels_penultimate {α : Type*} {f : Fin n → α} {a b : α}
    (ha : ∀ x, f x ≠ a) (hab : b ≠ a) :
    ∀ x, endLabels f a b x = endLabels f a b (penultimate n) → x = penultimate n := by
  intro x
  induction x using endCases <;> simp_all

private theorem singleton_endLabels_ultimate {α : Type*} {f : Fin n → α} {a b : α}
    (hb : ∀ x, f x ≠ b) (hab : a ≠ b) :
    ∀ x, endLabels f a b x = endLabels f a b (ultimate n) → x = ultimate n := by
  intro x
  induction x using endCases <;> simp_all

private theorem joinLabel_ne_of_ne {α : Type*} [DecidableEq α] {i j x y : α}
    (hxy : x ≠ y) (hyI : y ≠ i) (hyJ : y ≠ j) : joinLabel i j x ≠ joinLabel i j y := by
  simp [joinLabel_eq_iff, hxy, hyI, hyJ]

private theorem labelMarriageable_endLabels_fresh {α : Type*} [DecidableEq α]
    {f : Fin n → α} (h : LabelMarriageable f) {a b : α}
    (ha : ∀ x, f x ≠ a) (hb : ∀ x, f x ≠ b) : LabelMarriageable (endLabels f a b) := by
  obtain ⟨i, j, hij, hi, hj, hc⟩ := h
  refine ⟨keepOld i, keepOld j,
    fun h => hij (Fin.castSuccEmb.injective (Fin.castSuccEmb.injective h)),
    singleton_endLabels_old hi (ha i).symm (hb i).symm,
    singleton_endLabels_old hj (ha j).symm (hb j).symm, ?_⟩
  simp only [endLabels_old, comp_endLabels]
  exact not_crossing_endLabels_fresh hc
    (fun x => joinLabel_ne_of_ne (ha x) (ha i).symm (ha j).symm)
    (fun x => joinLabel_ne_of_ne (hb x) (hb i).symm (hb j).symm)

private theorem labelMarriageable_endLabels_distinct_fresh {α : Type*} [DecidableEq α]
    {f : Fin n → α} (h : ¬ LabelCrossing f) {a b : α}
    (ha : ∀ x, f x ≠ a) (hb : ∀ x, f x ≠ b) (hab : a ≠ b) :
    LabelMarriageable (endLabels f a b) := by
  refine ⟨penultimate n, ultimate n, Fin.castSucc_ne_last _,
    singleton_endLabels_penultimate ha hab.symm, singleton_endLabels_ultimate hb hab, ?_⟩
  simp only [endLabels_penultimate, endLabels_ultimate, comp_endLabels]
  have hjoin : joinLabel a b ∘ f = some ∘ f := by
    funext x
    simp [joinLabel, ha x, hb x]
  rw [hjoin]
  have hn : ¬ LabelCrossing (some ∘ f) := by simpa [LabelCrossing] using h
  exact not_crossing_endLabels_fresh hn
    (fun x => by simp [joinLabel]) (fun x => by simp [joinLabel])

-- Duplicating the last label is a monotone pullback. A fresh label on the final point
-- cannot occur in an alternating pair, so the existing single-point crossing lemma applies.
private theorem not_crossing_endLabels_attach {α : Type*} {f : Fin n → α}
    (hn : 0 < n) {b : α} (hf : ¬ LabelCrossing f) (hb : ∀ x, f x ≠ b) :
    ¬ LabelCrossing (endLabels f (f ⟨n - 1, by omega⟩) b) := by
  let k : Fin n := ⟨n - 1, by omega⟩
  let F := endLabels f (f k) b
  have hproj (x : Fin (n + 1)) : F x.castSucc = f (contractLast hn x) := by
    refine Fin.lastCases ?_ (fun y => ?_) x
    · suffices he : contractLast hn (Fin.last n) = k by simp [F, he]
      apply Fin.ext
      exact min_eq_right (Nat.sub_le n 1)
    · simp [F, contractLast_castSucc]
  change ¬ LabelCrossing F
  intro h
  have hprefix : LabelCrossing (f ∘ contractLast hn) := by
    apply crossing_of_append (fun x y => by simp [hproj]) (fun x hx => ?_) h
    induction x using endCases with
    | ho x => exact (hb x (by simpa [F] using hx)).elim
    | ha => exact (hb k (by simpa [F] using hx)).elim
    | hb => rfl
  apply hf
  exact crossing_map_of_monotone (contractLast hn) (contractLast_monotone hn)
    (S := fun _ => True) (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => ⟨trivial, trivial⟩) hprefix

-- When the last old singleton is used in the marriage, the new last point replaces it.
-- The two copies of the old last point become an isolated adjacent two-block.
private theorem not_crossing_insert_pair_before_last {α : Type*}
    {f : Fin n → α} (k : Fin n) (hk : k.val + 1 = n) {u : α}
    (hf : ¬ LabelCrossing f) (hu : ∀ x, f x ≠ u) :
    ¬ LabelCrossing (endLabels (fun x => if x = k then u else f x) u (f k)) := by
  let F := endLabels (fun x => if x = k then u else f x) u (f k)
  have hn : 0 < n := by omega
  let e : Fin (n + 2) → Fin n := contractLast hn ∘ contractLast (Nat.zero_lt_succ n)
  have heOld (x : Fin n) : e (keepOld x) = x := by simp [e, contractLast_castSucc]
  have heLast : e (ultimate n) = k := by
    apply Fin.ext
    change min (min (n + 1) (n + 1 - 1)) (n - 1) = k.val
    omega
  have hval (x : Fin (n + 2)) (hx : F x ≠ u) : F x = f (e x) := by
    induction x using endCases with
    | ho x =>
      have hxk : x ≠ k := by
        rintro rfl
        exact hx (by simp [F])
      simp [F, heOld, hxk]
    | ha => exact (hx (by simp [F])).elim
    | hb => simp [F, heLast]
  have hband (x : Fin (n + 2)) (hx : F x = u) : k.val ≤ x.val ∧ x.val ≤ n := by
    induction x using endCases with
    | ho x =>
      have hxk : x = k := by
        by_contra! h
        exact hu x (by simpa [F, h] using hx)
      subst x
      exact ⟨le_rfl, k.isLt.le⟩
    | ha => exact ⟨k.isLt.le, le_rfl⟩
    | hb => exact (hu k (by simpa [F] using hx)).elim
  intro h
  apply hf
  refine crossing_map_of_monotone e ((contractLast_monotone hn).comp (contractLast_monotone _))
    (S := fun x => F x ≠ u) (fun x y hx hy => by
      change F x = F y ↔ _
      rw [hval x hx, hval y hy]) ?_ h
  intro x y hxy h
  have hx : F x ≠ u := by
    intro hh
    have ha := hband x hh
    have hb := hband y (h.symm.trans hh)
    omega
  exact ⟨hx, fun hy => hx (h.trans hy)⟩

private theorem labelMarriageable_endLabels_attach {α : Type*} [DecidableEq α] {f : Fin n → α}
    (hn : 0 < n) {b : α} (hm : LabelMarriageable f) (hb : ∀ x, f x ≠ b) :
    LabelMarriageable (endLabels f (f ⟨n - 1, by omega⟩) b) := by
  let k : Fin n := ⟨n - 1, by omega⟩
  have hm' : ∃ i j, i ≠ j ∧ (∀ x, f x = f i → x = i) ∧ (∀ x, f x = f j → x = j) ∧
      ¬ LabelCrossing (joinLabel (f i) (f j) ∘ f) ∧ i ≠ k := by
    obtain ⟨i, j, hij, hi, hj, hc⟩ := hm
    by_cases h : i = k
    · have he : joinLabel (f i) (f j) = joinLabel (f j) (f i) := by
        funext x
        simp [joinLabel, or_comm]
      refine ⟨j, i, hij.symm, hj, hi, he ▸ hc, ?_⟩
      exact h ▸ hij.symm
    · exact ⟨i, j, hij, hi, hj, hc, h⟩
  obtain ⟨i, j, hij, hi, hj, hc, hik⟩ := hm'
  have hki : f k ≠ f i := fun h => hik (hi k h).symm
  by_cases hjk : j = k
  · subst j
    have hne : keepOld i ≠ ultimate n := Fin.castSucc_ne_last _
    change LabelMarriageable (endLabels f (f k) b)
    refine ⟨keepOld i, ultimate n, hne, singleton_endLabels_old hi hki (hb i).symm,
      singleton_endLabels_ultimate hb (hb k), ?_⟩
    simp only [endLabels_old, endLabels_ultimate, comp_endLabels]
    let g := joinLabel (f i) (f k) ∘ f
    let u := joinLabel (f i) b (f k)
    have he : joinLabel (f i) b ∘ f = fun x => if x = k then u else g x := by
      funext x
      by_cases hx : x = k
      · subst x
        simp [u]
      · have hxk : f x ≠ f k := fun h => hx (hj x h)
        simp [g, joinLabel, hx, hxk, hb x]
    have hfar : joinLabel (f i) b b = g k := by simp [g, joinLabel]
    have hu (x : Fin n) : g x ≠ u := by
      simp [g, u, joinLabel, hki, hb k]
    rw [he, hfar]
    exact not_crossing_insert_pair_before_last k (by dsimp [k]; omega) hc hu
  · have hkj : f k ≠ f j := fun h => hjk (hj k h).symm
    refine ⟨keepOld i, keepOld j,
      fun h => hij (Fin.castSuccEmb.injective (Fin.castSuccEmb.injective h)),
      singleton_endLabels_old hi hki (hb i).symm,
      singleton_endLabels_old hj hkj (hb j).symm, ?_⟩
    simp only [endLabels_old, comp_endLabels]
    exact not_crossing_endLabels_attach hn hc
      (fun x => joinLabel_ne_of_ne (hb x) (hb i).symm (hb j).symm)

-- Reverse each of the two intervals cut at `k`. This reverses cyclic order: on a
-- sorted quadruple it is a reversal followed by a cyclic shift at the cut.
private def flipAt (k : ℕ) (x : Fin n) : Fin n :=
  ⟨if x.val < k then min k n - 1 - x.val else n + k - 1 - x.val, by
    split <;> omega⟩

private theorem flipAt_revLeft {k : ℕ} (hk : k ≤ n) (x : Fin n) (hx : x.val < k) :
    (flipAt k x).val < k := by
  simp [flipAt, hx]
  omega

private theorem flipAt_revRight {k : ℕ} (x : Fin n) (hx : k ≤ x.val) :
    k ≤ (flipAt k x).val := by
  simp [flipAt, hx.not_gt]
  omega

private theorem flipAt_involutive {k : ℕ} (hk : k ≤ n) :
    Function.Involutive (flipAt k : Fin n → Fin n) := by
  intro x
  apply Fin.ext
  by_cases hx : x.val < k
  · have hl := flipAt_revLeft hk x hx
    simp only [flipAt, ite_eq_left hx] at hl
    simp only [flipAt, ite_eq_left hx, ite_eq_left hl]
    omega
  · have hr := flipAt_revRight x (Nat.le_of_not_gt hx)
    simp only [flipAt, ite_eq_right hx] at hr
    simp only [flipAt, ite_eq_right hx, ite_eq_right (Nat.not_lt_of_ge hr)]
    omega

private theorem crossing_flipAt {α : Type*} (f : Fin n → α) {k : ℕ} (hk : k ≤ n)
    (h : LabelCrossing (f ∘ flipAt k)) : LabelCrossing f := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩ := h
  simp only [Function.comp_apply] at hac hbd hne
  simp only [Fin.lt_def] at hab hbc hcd
  have lo (x y : Fin n) (hxy : x < y) (hy : y.val < k) : flipAt k y < flipAt k x := by
    have hx : x.val < k := Nat.lt_trans hxy hy
    simp only [Fin.lt_def, flipAt, ite_eq_left hx, ite_eq_left hy] at hxy ⊢
    omega
  have hi (x y : Fin n) (hx : k ≤ x.val) (hxy : x < y) : flipAt k y < flipAt k x := by
    have hy : k ≤ y.val := Nat.le_trans hx (Nat.le_of_lt hxy)
    simp only [Fin.lt_def, flipAt, ite_eq_right hx.not_gt, ite_eq_right hy.not_gt] at hxy ⊢
    omega
  have sep (x y : Fin n) (hx : x.val < k) (hy : k ≤ y.val) : flipAt k x < flipAt k y :=
    (flipAt_revLeft hk x hx).trans_le (flipAt_revRight y hy)
  have hdc : f (flipAt k d) ≠ f (flipAt k c) :=
    fun h => hne (hac.trans (h.symm.trans hbd.symm))
  by_cases hd : d.val < k
  · exact ⟨flipAt k d, flipAt k c, flipAt k b, flipAt k a, lo c d hcd hd,
      lo b c hbc (Nat.lt_trans hcd hd), lo a b hab (by omega), hbd.symm, hac.symm, hdc⟩
  by_cases hc : c.val < k
  · exact ⟨flipAt k c, flipAt k b, flipAt k a, flipAt k d, lo b c hbc hc,
      lo a b hab (Nat.lt_trans hbc hc), sep _ _ (by omega) (Nat.le_of_not_gt hd),
      hac.symm, hbd, fun h => hne (hac.trans h)⟩
  by_cases hb : b.val < k
  · exact ⟨flipAt k b, flipAt k a, flipAt k d, flipAt k c, lo a b hab hb,
      sep _ _ (Nat.lt_trans hab hb) (Nat.le_of_not_gt hd), hi c d (Nat.le_of_not_gt hc) hcd,
      hbd, hac, hne.symm⟩
  by_cases ha : a.val < k
  · exact ⟨flipAt k a, flipAt k d, flipAt k c, flipAt k b,
      sep _ _ ha (Nat.le_of_not_gt hd), hi c d (Nat.le_of_not_gt hc) hcd,
      hi b c (Nat.le_of_not_gt hb) hbc, hac, hbd.symm, fun h => hne (h.trans hbd.symm)⟩
  · exact ⟨flipAt k d, flipAt k c, flipAt k b, flipAt k a, hi c d (Nat.le_of_not_gt hc) hcd,
      hi b c (Nat.le_of_not_gt hb) hbc, hi a b (Nat.le_of_not_gt ha) hab, hbd.symm, hac.symm, hdc⟩

private theorem labelMarriageable_flipAt {α : Type*} [DecidableEq α] {f : Fin n → α}
    {k : ℕ} (hk : k ≤ n) (h : LabelMarriageable f) : LabelMarriageable (f ∘ flipAt k) := by
  obtain ⟨i, j, hij, hi, hj, hnc⟩ := h
  have he (x : Fin n) : flipAt k (flipAt k x) = x := flipAt_involutive hk x
  have hinj : Function.Injective (flipAt k : Fin n → Fin n) := (flipAt_involutive hk).injective
  refine ⟨flipAt k i, flipAt k j, fun h => hij (hinj h), ?_, ?_, ?_⟩
  · intro x hx
    exact hinj ((hi (flipAt k x) (by simpa only [Function.comp_apply, he] using hx)).trans
      (he i).symm)
  · intro x hx
    exact hinj ((hj (flipAt k x) (by simpa only [Function.comp_apply, he] using hx)).trans
      (he j).symm)
  · simp only [Function.comp_apply, he]
    exact fun h => hnc (crossing_flipAt (joinLabel (f i) (f j) ∘ f) hk h)

private theorem endLabels_flipAt {α : Type*} (f : Fin n → α) (a b : α) :
    endLabels (f ∘ flipAt n) a b ∘ flipAt n = endLabels f b a := by
  have hOld (x : Fin n) : flipAt n (keepOld x) = keepOld (flipAt n x) := by
    apply Fin.ext
    simp only [flipAt, Fin.val_castSucc, ite_eq_left x.isLt, min_self,
      min_eq_left (Nat.le_add_right n 2)]
  have hNear : flipAt n (penultimate n) = ultimate n := by
    apply Fin.ext
    simp [flipAt]
  have hFar : flipAt n (ultimate n) = penultimate n := by
    apply Fin.ext
    simp only [flipAt, Fin.val_last, Fin.val_castSucc]
    rw [ite_eq_right (by omega)]
    omega
  have he (x : Fin n) : flipAt n (flipAt n x) = x := flipAt_involutive (le_refl n) x
  funext x
  induction x using endCases <;> simp [hOld, hNear, hFar, he]

private theorem endLabels_attach_first {α : Type*} [DecidableEq α] {f : Fin n → α}
    (hn : 0 < n) {b : α} (hb : ∀ x, f x ≠ b) :
    (¬ LabelCrossing f → ¬ LabelCrossing (endLabels f b (f ⟨0, hn⟩))) ∧
    (LabelMarriageable f → LabelMarriageable (endLabels f b (f ⟨0, hn⟩))) := by
  let g : Fin n → α := f ∘ flipAt n
  have hk : g ⟨n - 1, by omega⟩ = f ⟨0, hn⟩ := by
    apply congrArg f
    apply Fin.ext
    simp only [flipAt, ite_eq_left (show n - 1 < n by omega), min_self, Nat.sub_self]
  have hb' : ∀ x, g x ≠ b := fun x => hb (flipAt n x)
  rw [← endLabels_flipAt, ← hk]
  constructor
  · intro hf h
    have hg : ¬ LabelCrossing g := fun h => hf (crossing_flipAt f (le_refl _) h)
    exact not_crossing_endLabels_attach hn hg hb'
      (crossing_flipAt _ (Nat.le_add_right n 2) h)
  · intro hf
    exact labelMarriageable_flipAt (Nat.le_add_right n 2)
      (labelMarriageable_endLabels_attach hn (labelMarriageable_flipAt (le_refl n) hf) hb')

private abbrev BlockTag (n : ℕ) := Finset (Fin n) ⊕ Bool

private def blockTag (P : SetPartition n) (x : Fin n) : BlockTag n := Sum.inl (P.part x)

private theorem blockTag_partition (P : SetPartition n) : labelPartition (blockTag P) = P := by
  apply partition_ext
  intro x y
  simp only [mem_part_label, blockTag, Sum.inl.injEq, part_eq_iff_mem]

private theorem labelPartition_noncrossing_iff {α : Type*} (f : Fin n → α) :
    IsNoncrossing (labelPartition f) ↔ ¬ LabelCrossing f := by
  simp only [IsNoncrossing, HasCrossing, LabelCrossing, Ne, part_eq_label]

private theorem restrict_endLabels (P : SetPartition n) (a b : BlockTag n) :
    (labelPartition (endLabels (blockTag P) a b)).comap keepOld = P := by
  apply partition_ext
  intro x y
  simp only [mem_part_comap, mem_part_label, endLabels_old, blockTag, Sum.inl.injEq,
    part_eq_iff_mem]

private abbrev MarriageableNCP (n : ℕ) :=
  {P : _root_.NoncrossingPartition n // IsMarriageableSingles P.val}

private theorem card_marriageableNCP (n : ℕ) :
    Fintype.card (MarriageableNCP n) = marriageableSinglesCount n :=
  Fintype.card_subtype _

private noncomputable def buildEnd (P : SetPartition n) (a b : BlockTag n)
    (hnc : ¬ LabelCrossing (endLabels (blockTag P) a b))
    (hm : LabelMarriageable (endLabels (blockTag P) a b)) : MarriageableNCP (n + 2) :=
  ⟨⟨labelPartition _, (labelPartition_noncrossing_iff _).mpr hnc⟩,
    (labelMarriageable_iff _).mp hm⟩

private noncomputable def appendFreshSingletons (P : _root_.NoncrossingPartition n) :
    MarriageableNCP (n + 2) := by
  have hnc := (labelPartition_noncrossing_iff (blockTag P.val)).mp
    (by rw [blockTag_partition]; exact P.property)
  exact buildEnd P.val (Sum.inr false) (Sum.inr true)
    (not_crossing_endLabels_fresh hnc (fun _ => by simp [blockTag])
      (fun _ => by simp [blockTag]))
    (labelMarriageable_endLabels_distinct_fresh hnc (fun _ => by simp [blockTag])
      (fun _ => by simp [blockTag]) (by simp))

-- The two Booleans say whether the penultimate and final point are singletons.
private def nearTag (P : SetPartition n) (hn : 0 < n) (a b : Bool) : BlockTag n :=
  if !a && b then blockTag P ⟨n - 1, by omega⟩ else Sum.inr false

private def farTag (P : SetPartition n) (hn : 0 < n) (a b : Bool) : BlockTag n :=
  if b then Sum.inr true else if a then blockTag P ⟨0, hn⟩ else Sum.inr false

private theorem endLabels_has_shape (P : SetPartition n) (hn : 0 < n) (a b : Bool) :
    let f := endLabels (blockTag P) (nearTag P hn a b) (farTag P hn a b)
    ((labelPartition f).part (penultimate n) = {penultimate n} ↔ a = true) ∧
      ((labelPartition f).part (ultimate n) = {ultimate n} ↔ b = true) := by
  have near (u v : BlockTag n) (h : ∀ x, blockTag P x ≠ u) (hv : v ≠ u) :
      (labelPartition (endLabels (blockTag P) u v)).part (penultimate n) = {penultimate n} := by
    ext x
    simp only [mem_part_label, mem_singleton]
    exact ⟨singleton_endLabels_penultimate h hv x, fun hx => hx ▸ rfl⟩
  have far (u v : BlockTag n) (h : ∀ x, blockTag P x ≠ v) (hu : u ≠ v) :
      (labelPartition (endLabels (blockTag P) u v)).part (ultimate n) = {ultimate n} := by
    ext x
    simp only [mem_part_label, mem_singleton]
    exact ⟨singleton_endLabels_ultimate h hu x, fun hx => hx ▸ rfl⟩
  have notNear (u v : BlockTag n) (x : Fin (n + 2)) (hx : x ≠ penultimate n)
      (h : endLabels (blockTag P) u v x = u) :
      (labelPartition (endLabels (blockTag P) u v)).part (penultimate n) ≠ {penultimate n} := by
    intro hh
    have hx' : x ∈ (labelPartition (endLabels (blockTag P) u v)).part (penultimate n) := by
      simpa only [mem_part_label, endLabels_penultimate] using h
    exact hx (mem_singleton.mp (hh ▸ hx'))
  have notFar (u v : BlockTag n) (x : Fin (n + 2)) (hx : x ≠ ultimate n)
      (h : endLabels (blockTag P) u v x = v) :
      (labelPartition (endLabels (blockTag P) u v)).part (ultimate n) ≠ {ultimate n} := by
    intro hh
    have hx' : x ∈ (labelPartition (endLabels (blockTag P) u v)).part (ultimate n) := by
      simpa only [mem_part_label, endLabels_ultimate] using h
    exact hx (mem_singleton.mp (hh ▸ hx'))
  cases a <;> cases b <;>
    simp only [nearTag, farTag, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, ite_false, ite_true, iff_false, iff_true]
  · exact ⟨notNear _ _ (ultimate n) (Fin.castSucc_ne_last _).symm (by simp),
      notFar _ _ (penultimate n) (Fin.castSucc_ne_last _) (by simp)⟩
  · refine ⟨notNear _ _ (keepOld ⟨n - 1, by omega⟩) ?_ (by simp),
      far _ _ (fun _ => by simp [blockTag]) (by simp [blockTag])⟩
    exact fun h => Fin.castSucc_ne_last _ (Fin.castSuccEmb.injective h)
  · exact ⟨near _ _ (fun _ => by simp [blockTag]) (by simp [blockTag]),
      notFar _ _ (keepOld ⟨0, hn⟩) (Fin.castSucc_ne_last _) (by simp)⟩
  · exact ⟨near _ _ (fun _ => by simp [blockTag]) (by simp),
      far _ _ (fun _ => by simp [blockTag]) (by simp)⟩

private noncomputable def boundaryExtension (hn : 0 < n) (a b : Bool)
    (P : _root_.NoncrossingPartition n) (hp : (a = true ∧ b = true) ∨ IsMarriageableSingles P.val) :
    MarriageableNCP (n + 2) := by
  have hnc := (labelPartition_noncrossing_iff (blockTag P.val)).mp
    (by rw [blockTag_partition]; exact P.property)
  apply buildEnd P.val (nearTag P.val hn a b) (farTag P.val hn a b)
  · cases a <;> cases b <;> simp only [nearTag, farTag, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
    · exact not_crossing_endLabels_fresh hnc (fun _ => by simp [blockTag])
        (fun _ => by simp [blockTag])
    · exact not_crossing_endLabels_attach hn hnc (fun _ => by simp [blockTag])
    · exact (endLabels_attach_first hn (fun _ => by simp [blockTag])).1 hnc
    · exact not_crossing_endLabels_fresh hnc (fun _ => by simp [blockTag])
        (fun _ => by simp [blockTag])
  · cases a <;> cases b <;>
      simp only [nearTag, farTag, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
        Bool.false_eq_true, ite_false, ite_true, false_and, and_false, false_or, true_and,
        true_or] at hp ⊢
    · exact labelMarriageable_endLabels_fresh ((labelMarriageable_iff _).mpr
        (by rwa [blockTag_partition])) (fun _ => by simp [blockTag]) (fun _ => by simp [blockTag])
    · exact labelMarriageable_endLabels_attach hn ((labelMarriageable_iff _).mpr
        (by rwa [blockTag_partition])) (fun _ => by simp [blockTag])
    · exact (endLabels_attach_first hn (fun _ => by simp [blockTag])).2
        ((labelMarriageable_iff _).mpr (by rwa [blockTag_partition]))
    · exact labelMarriageable_endLabels_distinct_fresh hnc (fun _ => by simp [blockTag])
        (fun _ => by simp [blockTag]) (by simp)

private def extensionShape : Option Bool → Bool × Bool
  | none => (false, false)
  | some a => (a, !a)

private theorem extensionShape_injective : Function.Injective extensionShape := by
  intro x y h
  cases x with
  | none => cases y with
    | none => rfl
    | some y => cases y <;> cases h
  | some x => cases y with
    | none => cases x <;> cases h
    | some y => exact congrArg some (congrArg Prod.fst h)

private theorem extensionShape_ne_both (x : Option Bool) : extensionShape x ≠ (true, true) := by
  cases x with
  | none => decide
  | some x => cases x <;> decide

private theorem restrict_boundaryExtension (hn : 0 < n) (a b : Bool)
    (P : _root_.NoncrossingPartition n) (hP) :
    (boundaryExtension hn a b P hP).val.val.comap keepOld = P.val :=
  restrict_endLabels P.val _ _

private noncomputable def fourExtensions (hn : 0 < n) :
    _root_.NoncrossingPartition n ⊕ (Option Bool × MarriageableNCP n) → MarriageableNCP (n + 2)
  | Sum.inl P => boundaryExtension hn true true P (Or.inl ⟨rfl, rfl⟩)
  | Sum.inr (i, P) => boundaryExtension hn (extensionShape i).1 (extensionShape i).2 P.val
      (Or.inr P.property)

private theorem boundaryExtension_shape_eq (hn : 0 < n) (a b c d : Bool)
    (P Q : _root_.NoncrossingPartition n) (hP hQ)
    (h : boundaryExtension hn a b P hP = boundaryExtension hn c d Q hQ) : (a, b) = (c, d) := by
  have help₁ := (endLabels_has_shape P.val hn a b).1
  have help₂ := (endLabels_has_shape P.val hn a b).2
  have help₃ := (endLabels_has_shape Q.val hn c d).1
  have help₄ := (endLabels_has_shape Q.val hn c d).2
  have he : (labelPartition (endLabels (blockTag P.val) (nearTag P.val hn a b)
      (farTag P.val hn a b))) = labelPartition (endLabels (blockTag Q.val) (nearTag Q.val hn c d)
      (farTag Q.val hn c d)) := congrArg (fun R : MarriageableNCP (n + 2) => R.val.val) h
  rw [he] at help₁ help₂
  exact Prod.ext (by cases a <;> cases c <;> simp_all) (by cases b <;> cases d <;> simp_all)

private theorem fourExtensions_injective (hn : 0 < n) : Function.Injective (fourExtensions hn) := by
  intro x y h
  cases x with
  | inl P =>
    cases y with
    | inl Q =>
      congr 1
      exact extension_source_eq (restrict_boundaryExtension hn true true P (Or.inl ⟨rfl, rfl⟩))
        (restrict_boundaryExtension hn true true Q (Or.inl ⟨rfl, rfl⟩)) (congrArg Subtype.val h)
    | inr ij =>
      obtain ⟨i, Q⟩ := ij
      have hshape := boundaryExtension_shape_eq hn _ _ _ _ P Q.val
        (Or.inl ⟨rfl, rfl⟩) (Or.inr Q.property) h
      exact (extensionShape_ne_both i hshape.symm).elim
  | inr ij =>
    obtain ⟨i, P⟩ := ij
    cases y with
    | inl Q =>
      have hshape := boundaryExtension_shape_eq hn _ _ _ _ P.val Q
        (Or.inr P.property) (Or.inl ⟨rfl, rfl⟩) h
      exact (extensionShape_ne_both i hshape).elim
    | inr jk =>
      obtain ⟨j, Q⟩ := jk
      have hij : i = j := extensionShape_injective (boundaryExtension_shape_eq hn _ _ _ _
        P.val Q.val (Or.inr P.property) (Or.inr Q.property) h)
      have hpq : P.val = Q.val := extension_source_eq
        (restrict_boundaryExtension hn (extensionShape i).1 (extensionShape i).2 P.val
          (Or.inr P.property))
        (restrict_boundaryExtension hn (extensionShape j).1 (extensionShape j).2 Q.val
          (Or.inr Q.property)) (congrArg Subtype.val h)
      exact congrArg Sum.inr (Prod.ext hij (Subtype.ext hpq))

/-- **Recursive lower bound for marriageable singles partitions.** For every $n \ge 0$,
$C_n + 3M_n \le M_{n+2}$, where $C_n$ is the number of noncrossing partitions of
$\{0, \dots, n-1\}$ and $M_n$ is the number of those that are marriageable singles partitions.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 22
(`jis-2025-25.1.1-prop-22`). -/
public theorem card_add_three_mul_marriageable_le (n : ℕ) :
    Fintype.card (_root_.NoncrossingPartition n) + 3 * marriageableSinglesCount n ≤
      marriageableSinglesCount (n + 2) := by
  by_cases hn : n ≤ 1
  · rw [marriageableSinglesCount_of_le_one hn, mul_zero, add_zero, ← card_marriageableNCP]
    apply Fintype.card_le_of_injective appendFreshSingletons
    intro P Q h
    exact extension_source_eq (restrict_endLabels P.val _ _) (restrict_endLabels Q.val _ _)
      (congrArg Subtype.val h)
  · have h := Fintype.card_le_of_injective (fourExtensions (n := n) (by omega))
      (fourExtensions_injective (by omega))
    simpa [Fintype.card_sum, Fintype.card_prod, Fintype.card_option, card_marriageableNCP] using h

end MetaMathlibExt
