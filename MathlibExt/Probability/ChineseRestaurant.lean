/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import MathlibExt.Combinatorics.Finpartition.Comap

/-!
# The Chinese restaurant process

The Chinese restaurant process with parameter `θ > 0` builds a random set partition of the
customers `Fin n` one customer at a time (Aldous 1985, §11; Pitman 2006, ch. 3). Customer `0`
sits alone; when customers `0, …, m - 1` are seated, customer `m` joins an occupied table `B`
with probability `|B| / (m + θ)` and opens a new table with probability `θ / (m + θ)`.

We define the process as a `PMF` on `Finpartition (univ : Finset (Fin n))`, built by `PMF.bind`
from the one-customer step `crpStep`, and prove:

* the law of the partition is `P(π) = θ^{|π|} ∏_{B ∈ π} (|B| - 1)! / θ^{(n)}`, where `|π|` is
  the number of blocks and `θ^{(n)} = θ (θ + 1) ⋯ (θ + n - 1)` is the rising factorial
  (`ascPochhammer`) (Pitman 2006, §3.1);
* exchangeability: the law is invariant under relabeling the customers by any permutation of
  `Fin n` (Aldous 1985, §11);
* consistency: restricting the partition of `Fin (n + 1)` to the first `n` customers gives the
  law for `n` customers.

## References

* D. J. Aldous, *Exchangeability and related topics*, École d'Été de Probabilités de
  Saint-Flour XIII (1983), Lecture Notes in Math. 1117 (1985), §11.
* J. Pitman, *Combinatorial Stochastic Processes*, Lecture Notes in Math. 1875 (2006), ch. 3.
-/

@[expose] public section

noncomputable section

open Finset

namespace MathlibExt.Biology.PopulationGenetics.ChineseRestaurant

/-- Seat customer `n` at a new table: the partition of `Fin (n + 1)` whose blocks are the
blocks of `π` (relabeled into `Fin (n + 1)`) together with the singleton `{n}`. -/
def newTable {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    Finpartition (univ : Finset (Fin (n + 1))) :=
  Finpartition.ofExistsUnique
    (insert {Fin.last n} (π.parts.map (mapEmbedding Fin.castSuccEmb).toEmbedding))
    (fun _ _ ↦ subset_univ _)
    (fun a _ ↦ by
      induction a using Fin.lastCases with
      | last =>
        refine ⟨{Fin.last n}, ⟨mem_insert_self _ _, mem_singleton_self _⟩, ?_⟩
        rintro t ⟨ht, hat⟩
        simp only [mem_insert, mem_map, RelEmbedding.coe_toEmbedding, mapEmbedding_apply] at ht
        rcases ht with rfl | ⟨B, -, rfl⟩
        · rfl
        · simp [Fin.castSucc_ne_last] at hat
      | cast i =>
        obtain ⟨B, ⟨hB, hiB⟩, hu⟩ := π.existsUnique_mem (mem_univ i)
        refine ⟨B.map Fin.castSuccEmb, ⟨mem_insert_of_mem (mem_map_of_mem _ hB), ?_⟩, ?_⟩
        · simpa using hiB
        · rintro t ⟨ht, hat⟩
          simp only [mem_insert, mem_map, RelEmbedding.coe_toEmbedding,
            mapEmbedding_apply] at ht
          rcases ht with rfl | ⟨B', hB', rfl⟩
          · simp [Fin.castSucc_ne_last] at hat
          · rw [hu B' ⟨hB', by simpa using hat⟩])
    (by
      simp only [mem_insert, mem_map, RelEmbedding.coe_toEmbedding, mapEmbedding_apply,
        not_or]
      refine ⟨(singleton_ne_empty _).symm, ?_⟩
      rintro ⟨B, hB, h⟩
      exact π.ne_empty hB (map_eq_empty.1 h))

/-- Seat customer `n` at the occupied table `B` of `π`: the block `B` becomes `B ∪ {n}` and
the other blocks are unchanged. -/
def joinTable {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) (B : Finset (Fin n))
    (hB : B ∈ π.parts) : Finpartition (univ : Finset (Fin (n + 1))) :=
  Finpartition.ofExistsUnique
    (insert (insert (Fin.last n) (B.map Fin.castSuccEmb))
      ((π.parts.erase B).map (mapEmbedding Fin.castSuccEmb).toEmbedding))
    (fun _ _ ↦ subset_univ _)
    (fun a _ ↦ by
      induction a using Fin.lastCases with
      | last =>
        refine ⟨_, ⟨mem_insert_self _ _, mem_insert_self _ _⟩, ?_⟩
        rintro t ⟨ht, hat⟩
        simp only [mem_insert, mem_map, RelEmbedding.coe_toEmbedding, mapEmbedding_apply] at ht
        rcases ht with rfl | ⟨C, -, rfl⟩
        · rfl
        · simp [Fin.castSucc_ne_last] at hat
      | cast i =>
        obtain ⟨C, ⟨hC, hiC⟩, hu⟩ := π.existsUnique_mem (mem_univ i)
        by_cases hCB : C = B
        · subst hCB
          refine ⟨_, ⟨mem_insert_self _ _, by simpa using hiC⟩, ?_⟩
          rintro t ⟨ht, hat⟩
          simp only [mem_insert, mem_map, RelEmbedding.coe_toEmbedding,
            mapEmbedding_apply, mem_erase] at ht
          rcases ht with rfl | ⟨C', ⟨hC'C, hC'⟩, rfl⟩
          · rfl
          · exact absurd (hu C' ⟨hC', by simpa using hat⟩) hC'C
        · refine ⟨C.map Fin.castSuccEmb, ⟨mem_insert_of_mem (mem_map_of_mem _
            (mem_erase.2 ⟨hCB, hC⟩)), by simpa using hiC⟩, ?_⟩
          rintro t ⟨ht, hat⟩
          simp only [mem_insert, mem_map, RelEmbedding.coe_toEmbedding,
            mapEmbedding_apply, mem_erase] at ht
          rcases ht with rfl | ⟨C', ⟨-, hC'⟩, rfl⟩
          · have hiB : i ∈ B := by simpa [Fin.castSucc_ne_last] using hat
            exact absurd (hu B ⟨hB, hiB⟩).symm hCB
          · rw [hu C' ⟨hC', by simpa using hat⟩])
    (by
      simp only [mem_insert, mem_map, RelEmbedding.coe_toEmbedding, mapEmbedding_apply,
        not_or, mem_erase]
      refine ⟨(insert_ne_empty _ _).symm, ?_⟩
      rintro ⟨C, ⟨-, hC⟩, h⟩
      exact π.ne_empty hC (map_eq_empty.1 h))

/-- The blocks of `newTable π`. -/
@[simp]
theorem parts_newTable {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    (newTable π).parts =
      insert {Fin.last n} (π.parts.map (mapEmbedding Fin.castSuccEmb).toEmbedding) :=
  rfl

/-- The blocks of `joinTable π B hB`. -/
@[simp]
theorem parts_joinTable {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) (B : Finset (Fin n))
    (hB : B ∈ π.parts) :
    (joinTable π B hB).parts =
      insert (insert (Fin.last n) (B.map Fin.castSuccEmb))
        ((π.parts.erase B).map (mapEmbedding Fin.castSuccEmb).toEmbedding) :=
  rfl

private lemma map_filter_castSucc {n : ℕ} (D : Finset (Fin (n + 1))) :
    (univ.filter fun i : Fin n ↦ Fin.castSucc i ∈ D).map Fin.castSuccEmb =
      D.erase (Fin.last n) := by
  ext x
  induction x using Fin.lastCases with
  | last => simp [Fin.castSucc_ne_last]
  | cast i => simp [Fin.castSucc_ne_last]

private lemma last_notMem_map {n : ℕ} (B : Finset (Fin n)) :
    Fin.last n ∉ B.map Fin.castSuccEmb := by
  simp [Fin.castSucc_ne_last]

private lemma filter_castSucc_map {n : ℕ} (B : Finset (Fin n)) :
    (univ.filter fun i : Fin n ↦ Fin.castSucc i ∈ B.map Fin.castSuccEmb) = B := by
  ext i
  simp

private lemma filter_castSucc_insert_last {n : ℕ} (S : Finset (Fin (n + 1))) :
    (univ.filter fun i : Fin n ↦ Fin.castSucc i ∈ insert (Fin.last n) S) =
      univ.filter fun i : Fin n ↦ Fin.castSucc i ∈ S := by
  ext i
  simp [Fin.castSucc_ne_last]

/-- Seat customer `n` according to the choice `c`: `none` opens a new table, `some B` joins
the occupied table `B`. -/
def seat {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    Option π.parts → Finpartition (univ : Finset (Fin (n + 1)))
  | none => newTable π
  | some B => joinTable π B.1 B.2

/-- The probability of each seating choice for customer `n` given the partition `π` of the
first `n` customers: `θ / (n + θ)` for a new table, `|B| / (n + θ)` for the table `B`. -/
def seatWeight (θ : ℝ) {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    Option π.parts → ℝ
  | none => θ / (n + θ)
  | some B => #B.1 / (n + θ)

/-- The seating probabilities are nonnegative for `θ > 0`. -/
theorem seatWeight_nonneg {θ : ℝ} (hθ : 0 < θ) {n : ℕ}
    (π : Finpartition (univ : Finset (Fin n))) (c : Option π.parts) :
    0 ≤ seatWeight θ π c := by
  cases c <;> simp only [seatWeight] <;> positivity

/-- The seating probabilities sum to one for `θ > 0`. -/
theorem sum_seatWeight {θ : ℝ} (hθ : 0 < θ) {n : ℕ}
    (π : Finpartition (univ : Finset (Fin n))) :
    ∑ c, seatWeight θ π c = 1 := by
  have hn : (n : ℝ) + θ ≠ 0 := by positivity
  have hsum : ∑ B : π.parts, (#B.1 : ℝ) = n := by
    rw [sum_coe_sort π.parts (fun B ↦ (#B : ℝ))]
    exact_mod_cast (π.sum_card_parts.trans (by simp))
  rw [Fintype.sum_option]
  simp only [seatWeight]
  rw [← sum_div, hsum, ← add_div, add_comm, div_self hn]

/-- The seating choice of customer `n`, as a probability distribution. -/
def seatChoice (θ : ℝ) (hθ : 0 < θ) {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    PMF (Option π.parts) :=
  PMF.ofFintype (fun c ↦ ENNReal.ofReal (seatWeight θ π c)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ ↦ seatWeight_nonneg hθ π c),
      sum_seatWeight hθ, ENNReal.ofReal_one])

/-- One step of the Chinese restaurant process: the law of the partition of `Fin (n + 1)`
given the partition `π` of the first `n` customers. -/
def crpStep (θ : ℝ) (hθ : 0 < θ) {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    PMF (Finpartition (univ : Finset (Fin (n + 1)))) :=
  (seatChoice θ hθ π).map (seat π)

/-- The **Chinese restaurant process** with parameter `θ > 0`: the law of the random
partition of the customers `Fin n` into tables, built one customer at a time by `crpStep`
(Aldous 1985, §11; Pitman 2006, ch. 3). -/
def crp (θ : ℝ) (hθ : 0 < θ) : (n : ℕ) → PMF (Finpartition (univ : Finset (Fin n)))
  | 0 => PMF.pure ⊥
  | n + 1 => (crp θ hθ n).bind (crpStep θ hθ)

/-- The closed-form law of the Chinese restaurant process,
`θ^{|π|} ∏_{B ∈ π} (|B| - 1)! / θ^{(n)}` (Pitman 2006, §3.1). Every block is nonempty,
so `|B| - 1` is never a truncated natural subtraction. -/
def crpProb (θ : ℝ) {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) : ℝ :=
  θ ^ #π.parts * π.cardProd (fun k ↦ ((k - 1).factorial : ℝ)) / (ascPochhammer ℝ n).eval θ

/-- Removing the last customer undoes every seating: restricting `seat π c` to the first `n`
customers gives back `π`. -/
theorem comap_castSucc_seat {n : ℕ} (π : Finpartition (univ : Finset (Fin n)))
    (c : Option π.parts) : (seat π c).comap Fin.castSucc = π := by
  ext C
  rw [Finpartition.mem_comap_parts]
  rcases c with _ | ⟨B, hB⟩
  · rw [seat, parts_newTable]
    constructor
    · rintro ⟨hC, D, hD, rfl⟩
      rcases mem_insert.1 hD with rfl | hD
      · exfalso
        obtain ⟨i, hi⟩ := hC
        simp [Fin.castSucc_ne_last] at hi
      · obtain ⟨B, hB, rfl⟩ := mem_map.1 hD
        rwa [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, filter_castSucc_map]
    · intro hC
      refine ⟨π.nonempty_of_mem_parts hC, C.map Fin.castSuccEmb,
        mem_insert_of_mem (mem_map_of_mem _ hC), filter_castSucc_map C⟩
  · rw [seat, parts_joinTable]
    constructor
    · rintro ⟨-, D, hD, rfl⟩
      rcases mem_insert.1 hD with rfl | hD
      · rwa [filter_castSucc_insert_last, filter_castSucc_map]
      · obtain ⟨E, hE, rfl⟩ := mem_map.1 hD
        rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, filter_castSucc_map]
        exact mem_of_mem_erase hE
    · intro hC
      refine ⟨π.nonempty_of_mem_parts hC, ?_⟩
      by_cases hCB : C = B
      · subst hCB
        exact ⟨_, mem_insert_self _ _, by rw [filter_castSucc_insert_last, filter_castSucc_map]⟩
      · exact ⟨C.map Fin.castSuccEmb, mem_insert_of_mem (mem_map_of_mem _
          (mem_erase.2 ⟨hCB, hC⟩)), filter_castSucc_map C⟩

/-- Different seating choices give different partitions. -/
theorem seat_injective {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    Function.Injective (seat π) := by
  have hlast : ∀ (B : Finset (Fin n)) (hB : B ∈ π.parts) (D : Finset (Fin (n + 1))),
      D ∈ (joinTable π B hB).parts → Fin.last n ∈ D →
        D = insert (Fin.last n) (B.map Fin.castSuccEmb) := by
    intro B hB D hD hlD
    rcases mem_insert.1 hD with rfl | hD
    · rfl
    · obtain ⟨E, -, rfl⟩ := mem_map.1 hD
      exact absurd hlD (last_notMem_map E)
  have hnew : ∀ (B : Finset (Fin n)) (hB : B ∈ π.parts), newTable π ≠ joinTable π B hB := by
    intro B hB h
    have hmem : {Fin.last n} ∈ (joinTable π B hB).parts := by
      rw [← h, parts_newTable]
      exact mem_insert_self _ _
    have h1 := congrArg (fun D ↦ univ.filter fun i : Fin n ↦ Fin.castSucc i ∈ D)
      (hlast B hB _ hmem (mem_singleton_self _))
    simp only [filter_castSucc_insert_last, filter_castSucc_map] at h1
    apply π.ne_empty hB
    rw [← h1]
    ext i
    simp [Fin.castSucc_ne_last]
  rintro (_ | ⟨B, hB⟩) (_ | ⟨B', hB'⟩) h
  · rfl
  · exact absurd h (hnew B' hB')
  · exact absurd h.symm (hnew B hB)
  · have hmem : insert (Fin.last n) (B.map Fin.castSuccEmb) ∈ (joinTable π B' hB').parts := by
      change joinTable π B hB = joinTable π B' hB' at h
      rw [← h, parts_joinTable]
      exact mem_insert_self _ _
    have h1 := congrArg (fun D ↦ univ.filter fun i : Fin n ↦ Fin.castSucc i ∈ D)
      (hlast B' hB' _ hmem (mem_insert_self _ _))
    simp only [filter_castSucc_insert_last, filter_castSucc_map] at h1
    simp [h1]

/-- Every partition of `Fin (n + 1)` arises by seating customer `n` into its restriction to
the first `n` customers. -/
theorem exists_seat_eq {n : ℕ} (π' : Finpartition (univ : Finset (Fin (n + 1)))) :
    ∃ c, seat (π'.comap Fin.castSucc) c = π' := by
  set π0 := π'.comap Fin.castSucc
  let pre : Finset (Fin (n + 1)) → Finset (Fin n) := fun D ↦
    univ.filter fun i : Fin n ↦ Fin.castSucc i ∈ D
  have hC : π'.part (Fin.last n) ∈ π'.parts := π'.part_mem.2 (mem_univ _)
  have hlC : Fin.last n ∈ π'.part (Fin.last n) := π'.mem_part_self.2 (mem_univ _)
  have hblock : ∀ D ∈ π'.parts, Fin.last n ∈ D → D = π'.part (Fin.last n) :=
    fun D hD hlD ↦ π'.eq_of_mem_parts hD hC hlD hlC
  have hmapD : ∀ D, Fin.last n ∉ D → (pre D).map Fin.castSuccEmb = D := fun D hD ↦ by
    rw [map_filter_castSucc, erase_eq_of_notMem hD]
  have hmem0 : ∀ D ∈ π'.parts, (pre D).Nonempty → pre D ∈ π0.parts := fun D hD hne ↦
    Finpartition.mem_comap_parts.2 ⟨hne, D, hD, rfl⟩
  have hfne : ∀ D ∈ π'.parts, Fin.last n ∉ D → (pre D).Nonempty := fun D hD hlD ↦ by
    rw [← map_nonempty (f := Fin.castSuccEmb), hmapD D hlD]
    exact π'.nonempty_of_mem_parts hD
  have hπ0 : ∀ E ∈ π0.parts, ∃ D ∈ π'.parts, pre D = E := fun E hE ↦
    (Finpartition.mem_comap_parts.1 hE).2
  by_cases hsing : π'.part (Fin.last n) = {Fin.last n}
  · refine ⟨none, Finpartition.ext ?_⟩
    ext D
    simp only [seat, parts_newTable]
    constructor
    · intro hD
      rcases mem_insert.1 hD with rfl | hD
      · rw [← hsing]
        exact hC
      · obtain ⟨E, hE, rfl⟩ := mem_map.1 hD
        obtain ⟨D', hD', rfl⟩ := hπ0 E hE
        have hlD' : Fin.last n ∉ D' := by
          intro hl
          have hE' := (Finpartition.mem_comap_parts.1 hE).1
          rw [hblock D' hD' hl, hsing] at hE'
          obtain ⟨i, hi⟩ := hE'
          simp [pre, Fin.castSucc_ne_last] at hi
        rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, hmapD D' hlD']
        exact hD'
    · intro hD
      by_cases hlD : Fin.last n ∈ D
      · rw [hblock D hD hlD, hsing]
        exact mem_insert_self _ _
      · refine mem_insert_of_mem (mem_map.2 ⟨pre D, hmem0 D hD (hfne D hD hlD), ?_⟩)
        rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, hmapD D hlD]
  · set C := π'.part (Fin.last n)
    have hBmap : (pre C).map Fin.castSuccEmb = C.erase (Fin.last n) := map_filter_castSucc C
    have hBne : (pre C).Nonempty := by
      rw [← map_nonempty (f := Fin.castSuccEmb), hBmap]
      by_contra h
      rw [not_nonempty_iff_eq_empty, erase_eq_empty_iff] at h
      rcases h with h | h
      · exact π'.ne_empty hC h
      · exact hsing h
    have hB : pre C ∈ π0.parts := hmem0 C hC hBne
    have hins : insert (Fin.last n) ((pre C).map Fin.castSuccEmb) = C := by
      rw [hBmap, insert_erase hlC]
    refine ⟨some ⟨pre C, hB⟩, Finpartition.ext ?_⟩
    ext D
    simp only [seat, parts_joinTable]
    rw [hins]
    constructor
    · intro hD
      rcases mem_insert.1 hD with rfl | hD
      · exact hC
      · obtain ⟨E, hE, rfl⟩ := mem_map.1 hD
        obtain ⟨hEB, hE⟩ := mem_erase.1 hE
        obtain ⟨D', hD', rfl⟩ := hπ0 E hE
        have hlD' : Fin.last n ∉ D' := by
          intro hl
          exact hEB (by rw [hblock D' hD' hl])
        rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, hmapD D' hlD']
        exact hD'
    · intro hD
      by_cases hlD : Fin.last n ∈ D
      · rw [hblock D hD hlD]
        exact mem_insert_self _ _
      · refine mem_insert_of_mem (mem_map.2 ⟨pre D, mem_erase.2 ⟨?_, hmem0 D hD
          (hfne D hD hlD)⟩, ?_⟩)
        · intro hDC
          obtain ⟨x, hx⟩ := π'.nonempty_of_mem_parts hD
          have hxC : x ∈ C := by
            rw [← hmapD D hlD, hDC, hBmap] at hx
            exact mem_of_mem_erase hx
          exact hlD (by rw [π'.eq_of_mem_parts hD hC hx hxC]; exact hlC)
        · rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, hmapD D hlD]

private lemma crpProb_nonneg {θ : ℝ} (hθ : 0 < θ) {n : ℕ}
    (π : Finpartition (univ : Finset (Fin n))) : 0 ≤ crpProb θ π := by
  have := ascPochhammer_pos n θ hθ
  unfold crpProb Finpartition.cardProd
  exact div_nonneg (mul_nonneg (pow_nonneg hθ.le _) (prod_nonneg fun _ _ ↦ by positivity))
    this.le

private lemma singleton_last_notMem {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    {Fin.last n} ∉ π.parts.map (mapEmbedding Fin.castSuccEmb).toEmbedding := by
  intro h
  obtain ⟨B, -, hB⟩ := mem_map.1 h
  rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply] at hB
  exact last_notMem_map B (hB ▸ mem_singleton_self _)

private lemma insert_last_notMem {n : ℕ} (π : Finpartition (univ : Finset (Fin n)))
    (B : Finset (Fin n)) :
    insert (Fin.last n) (B.map Fin.castSuccEmb) ∉
      (π.parts.erase B).map (mapEmbedding Fin.castSuccEmb).toEmbedding := by
  intro h
  obtain ⟨C, -, hC⟩ := mem_map.1 h
  rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply] at hC
  exact last_notMem_map C (hC ▸ mem_insert_self _ _)

/-- One seating multiplies the closed-form law by the seating probability. -/
lemma crpProb_seat {θ : ℝ} (hθ : 0 < θ) {n : ℕ}
    (π : Finpartition (univ : Finset (Fin n))) (c : Option π.parts) :
    crpProb θ (seat π c) = crpProb θ π * seatWeight θ π c := by
  have hp := (ascPochhammer_pos n θ hθ).ne'
  have hn : (n : ℝ) + θ ≠ 0 := by positivity
  rcases c with _ | ⟨B, hB⟩
  · have hcard : #(seat π none).parts = #π.parts + 1 := by
      simp only [seat, parts_newTable]
      rw [card_insert_of_notMem (singleton_last_notMem π), card_map]
    have hprod : (seat π none).cardProd (fun k ↦ ((k - 1).factorial : ℝ)) =
        π.cardProd (fun k ↦ ((k - 1).factorial : ℝ)) := by
      simp only [Finpartition.cardProd, seat, parts_newTable]
      rw [prod_insert (singleton_last_notMem π), prod_map]
      simp
    rw [crpProb, crpProb, hcard, hprod, ascPochhammer_succ_eval, seatWeight]
    field_simp
    ring
  · have hne : π.parts.Nonempty := ⟨B, hB⟩
    have hcard : #(seat π (some ⟨B, hB⟩)).parts = #π.parts := by
      simp only [seat, parts_joinTable]
      rw [card_insert_of_notMem (insert_last_notMem π B), card_map, card_erase_of_mem hB]
      have := hne.card_pos
      omega
    have hB0 : #B ≠ 0 := (π.nonempty_of_mem_parts hB).card_pos.ne'
    have hprod : (seat π (some ⟨B, hB⟩)).cardProd (fun k ↦ ((k - 1).factorial : ℝ)) =
        #B * π.cardProd (fun k ↦ ((k - 1).factorial : ℝ)) := by
      simp only [Finpartition.cardProd, seat, parts_joinTable]
      rw [prod_insert (insert_last_notMem π B), prod_map, ← mul_prod_erase _ _ hB,
        card_insert_of_notMem (last_notMem_map B), card_map, Nat.add_sub_cancel]
      simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, card_map]
      rw [← Nat.mul_factorial_pred hB0, Nat.cast_mul]
      ring
    rw [crpProb, crpProb, hcard, hprod, ascPochhammer_succ_eval, seatWeight]
    field_simp
    ring

/-- The process puts mass `P(π) * seatWeight θ π c` on the seating `seat π c`. -/
private lemma crp_seat {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (π : Finpartition (univ : Finset (Fin n)))
    (c : Option π.parts) :
    crp θ hθ (n + 1) (seat π c) = crp θ hθ n π * ENNReal.ofReal (seatWeight θ π c) := by
  change ((crp θ hθ n).bind (crpStep θ hθ)) (seat π c) = _
  rw [PMF.bind_apply, tsum_fintype, sum_eq_single π]
  · congr 1
    rw [crpStep, PMF.map_apply, tsum_fintype, sum_eq_single c]
    · simp [seatChoice]
    · intro c' _ hc'
      split_ifs with h
      · exact absurd (seat_injective π h).symm hc'
      · rfl
    · simp
  · intro π' _ hπ'
    rw [crpStep, PMF.map_apply, tsum_fintype, sum_eq_zero, mul_zero]
    intro c' _
    split_ifs with h
    · refine absurd ?_ hπ'
      rw [← comap_castSucc_seat π c, h, comap_castSucc_seat]
    · rfl
  · simp

/-- **Law of the Chinese restaurant process** (Pitman 2006, §3.1):
`P(π) = θ^{|π|} ∏_{B ∈ π} (|B| - 1)! / θ^{(n)}`. -/
theorem crp_apply {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    crp θ hθ n π = ENNReal.ofReal (crpProb θ π) := by
  induction n with
  | zero =>
    have hparts : π.parts = ∅ := Finpartition.parts_eq_empty_iff.2 (by simp)
    have hπ : π = ⊥ := Finpartition.ext (by rw [hparts, Finpartition.parts_bot]; simp)
    subst hπ
    simp [crp, crpProb, Finpartition.cardProd, hparts]
  | succ n ih =>
    obtain ⟨c, hc⟩ := exists_seat_eq π
    rw [← hc, crp_seat, ih, ← ENNReal.ofReal_mul (crpProb_nonneg hθ _), crpProb_seat hθ]

/-- The law of the Chinese restaurant process as a real number. -/
theorem crp_toReal {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    (crp θ hθ n π).toReal = crpProb θ π := by
  rw [crp_apply, ENNReal.toReal_ofReal (crpProb_nonneg hθ π)]

/-- **Exchangeability**, pointwise: relabeling the customers by a permutation `σ` does not
change the probability of a partition. -/
theorem crp_comap_perm {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (π : Finpartition (univ : Finset (Fin n))) :
    crp θ hθ n (π.comap σ) = crp θ hθ n π := by
  rw [crp_apply, crp_apply, crpProb, crpProb, Finpartition.card_parts_comap_equiv,
    Finpartition.cardProd_comap_equiv]

/-- **Exchangeability of the Chinese restaurant process** (Aldous 1985, §11): the law of the
partition relabeled by any permutation of the customers is the law of the partition. -/
theorem crp_map_comap_perm {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (crp θ hθ n).map (Finpartition.comap σ) = crp θ hθ n := by
  ext π
  rw [PMF.map_apply, tsum_fintype]
  have hiff : ∀ π' : Finpartition (univ : Finset (Fin n)),
      π = π'.comap σ ↔ π' = π.comap σ.symm := by
    intro π'
    constructor
    · rintro rfl
      exact (Finpartition.comap_symm_comap σ π').symm
    · rintro rfl
      simpa using (Finpartition.comap_symm_comap σ.symm π).symm
  simp_rw [hiff]
  rw [sum_ite_eq' univ (π.comap σ.symm)]
  simp only [mem_univ, ↓reduceIte]
  simpa using crp_comap_perm hθ σ.symm π

/-- **Consistency of the Chinese restaurant process**: restricting the random partition of
`Fin (n + 1)` to the first `n` customers gives the process with `n` customers. -/
theorem crp_map_restrict {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    (crp θ hθ (n + 1)).map (Finpartition.comap Fin.castSucc) = crp θ hθ n := by
  change ((crp θ hθ n).bind (crpStep θ hθ)).map _ = _
  rw [PMF.map_bind]
  have h : ∀ π : Finpartition (univ : Finset (Fin n)),
      (crpStep θ hθ π).map (Finpartition.comap Fin.castSucc) = PMF.pure π := by
    intro π
    rw [crpStep, PMF.map_comp]
    have hf : (Finpartition.comap Fin.castSucc ∘ seat π) = Function.const _ π :=
      funext (comap_castSucc_seat π)
    rw [hf, PMF.map_const]
  simp_rw [h]
  exact PMF.bind_pure _

/-- **Consistency for every sample size**: restricting the random partition of `Fin n` to the
first `m ≤ n` customers gives the process with `m` customers. -/
theorem crp_map_restrict_castLE {θ : ℝ} (hθ : 0 < θ) {m n : ℕ} (h : m ≤ n) :
    (crp θ hθ n).map (Finpartition.comap (Fin.castLE h)) = crp θ hθ m := by
  induction n, h using Nat.le_induction with
  | base =>
    have hid : (Fin.castLE (le_refl m) : Fin m → Fin m) = id := funext fun i ↦ Fin.ext rfl
    have hcomap : Finpartition.comap (id : Fin m → Fin m) = id :=
      funext Finpartition.comap_refl
    rw [hid, hcomap, PMF.map_id]
  | succ n hmn ih =>
    have hc : (Fin.castLE (hmn.trans n.le_succ) : Fin m → Fin (n + 1)) =
        Fin.castSucc ∘ Fin.castLE hmn := funext fun i ↦ Fin.ext rfl
    have hf : Finpartition.comap (Fin.castSucc ∘ Fin.castLE hmn) =
        Finpartition.comap (Fin.castLE hmn) ∘ Finpartition.comap Fin.castSucc :=
      funext fun P ↦ (Finpartition.comap_comap _ _ P).symm
    rw [hc, hf, ← PMF.map_comp, crp_map_restrict, ih]

/-- The integer partition associated to a set partition of `Fin n`: its block sizes form a
partition of the integer `n`. -/
def blockSizes {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) : n.Partition where
  parts := π.parts.val.map card
  parts_pos := by
    simp only [Multiset.mem_map, mem_val]
    rintro _ ⟨B, hB, rfl⟩
    exact (π.nonempty_of_mem_parts hB).card_pos
  parts_sum := by
    rw [← sum_eq_multiset_sum, π.sum_card_parts, card_univ, Fintype.card_fin]

/-- Opening a table adds a block of size one. -/
lemma blockSizes_newTable {n : ℕ} (π : Finpartition (univ : Finset (Fin n))) :
    (blockSizes (newTable π)).parts = 1 ::ₘ (blockSizes π).parts := by
  simp only [blockSizes, parts_newTable]
  rw [insert_val_of_notMem (singleton_last_notMem π), Multiset.map_cons, map_val,
    Multiset.map_map]
  simp [Function.comp_def]

/-- Joining a table increases the size of that block by one. -/
lemma blockSizes_joinTable {n : ℕ} (π : Finpartition (univ : Finset (Fin n)))
    (B : Finset (Fin n)) (hB : B ∈ π.parts) :
    (blockSizes (joinTable π B hB)).parts =
      (#B + 1) ::ₘ (blockSizes π).parts.erase #B := by
  simp only [blockSizes, parts_joinTable]
  rw [insert_val_of_notMem (insert_last_notMem π B), Multiset.map_cons, map_val,
    Multiset.map_map, card_insert_of_notMem (last_notMem_map B), card_map, erase_val]
  congr 1
  have hB' : B ∈ π.parts.val := hB
  conv_rhs => rw [← Multiset.cons_erase hB', Multiset.map_cons, Multiset.erase_cons_head]
  simp [Function.comp_def]

end MathlibExt.Biology.PopulationGenetics.ChineseRestaurant
