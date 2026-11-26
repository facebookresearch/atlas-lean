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

## References

* Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and Catalan
  Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, pp. 1–13, Proposition 20
  (pp. 6–7).
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

-- A monotone pullback may identify points, but not consecutive vertices of an alternating
-- crossing: their images lie in distinct blocks.
private theorem isNoncrossing_comap (P : SetPartition n) (hP : IsNoncrossing P)
    (f : Fin m → Fin n) (hf : Monotone f) : IsNoncrossing (P.comap f) := by
  rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
  simp only [part_comap_eq] at hac hbd
  simp only [Ne, part_comap_eq] at hne
  have h₁ : f a ≠ f b := fun h => hne (congrArg P.part h)
  have h₂ : f b ≠ f c := fun h => hne (hac.trans (congrArg P.part h.symm))
  have h₃ : f c ≠ f d := fun h => hne (hac.trans ((congrArg P.part h).trans hbd.symm))
  exact hP ⟨f a, f b, f c, f d, lt_of_le_of_ne (hf hab.le) h₁,
    lt_of_le_of_ne (hf hbc.le) h₂, lt_of_le_of_ne (hf hcd.le) h₃, hac, hbd, hne⟩

private def contractLast (hn : 0 < n) (x : Fin (n + 1)) : Fin n :=
  ⟨min x.val (n - 1), lt_of_le_of_lt (min_le_right ..) (by omega)⟩

private theorem contractLast_castSucc (hn : 0 < n) (x : Fin n) :
    contractLast hn x.castSucc = x := by
  apply Fin.ext
  change min x.val (n - 1) = x.val
  exact min_eq_left (by have := x.isLt; omega)

private def duplicateLast (hn : 0 < n) (P : _root_.NoncrossingPartition n) :
    _root_.NoncrossingPartition (n + 1) :=
  ⟨P.val.comap (contractLast hn), isNoncrossing_comap P.val P.property _ (by
    intro x y h
    change min x.val (n - 1) ≤ min y.val (n - 1)
    exact min_le_min_right _ (show x.val ≤ y.val from h))⟩

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
    ⟨f, fun P P' h => NoncrossingPartition.ext <|
      (hrestrict P).symm.trans ((congrArg (fun T => T.val.comap Fin.castSucc) h).trans
        (hrestrict P'))⟩
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

end MetaMathlibExt
