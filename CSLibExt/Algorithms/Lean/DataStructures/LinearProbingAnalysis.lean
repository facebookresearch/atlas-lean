/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import MathlibExt.Combinatorics.Enumerative.PollakPartialParkingFunctions

/-!
# Analysis of hashing with linear probing

Knuth's model of linear probing (D. E. Knuth, *Notes on "open" addressing*, 22 July 1963,
typeset by H. Prodinger in 1997; the model of its Section 1): a cyclic table of `N` cells, all
initially empty; the `k`-th item has a hash address `a_k`, and is entered into the first empty
cell among `a_k, a_k + 1, …` (indices modulo `N`). All `N ^ k` hash sequences `a_1, …, a_k` are
equally likely. The cost of an insertion is the number of times the comparison step is executed,
that is one more than the number of occupied cells passed over.

## Main definitions

* `displacement S h`, `probes S h`, `insertCell S h`: one cyclic linear-probing insertion with
  hash address `h` into a table whose occupied cells form `S`.
* `occupancy l`: the occupied cells after inserting the hash sequence `l` in order.
* `insertionCost N n`: the expected number of probes to insert an item into a table of `N` cells
  that already holds `n` items, all hash addresses uniform and independent. This is Knuth's
  `M(N, n + 1)`; the same scan is the scan of an unsuccessful search, which stops at the first
  empty cell.
* `successfulSearchCost N n`: the average of `insertionCost N i` over `i < n`, Knuth's `T(N, n)`
  (Section 7 of the note: a search for an item retraces its insertion).
* `knuthE r N k`: Knuth's sum `E_r(N, k) = ∑_{j < k} C(r + j, r) (k - 1)^{(j)} / N ^ j`, with
  `(k - 1)^{(j)}` the falling factorial (Section 5 of the note).

## Main results

* `card_linSuccess`: Lemma 1 of the note. For `0 < k ≤ n`, the number of hash sequences of `k`
  items in a table of `n` cells for which linear probing never runs past the last cell (no
  overflow step) is `(n + 1 - k)(n + 1) ^ (k - 1)`. It is derived from Pollak's count of partial
  parking functions through `linSuccess_iff_isPartialParkingFunction`.
* `insertionCost_zero`, `successfulSearchCost_one`: the empty-table boundary values.

Knuth's exact formulas `M(N, k) = (1 + E_1(N, k)) / 2` and `T(N, k) = (1 + E_0(N, k)) / 2`
(Theorem 2 and Section 7 of the note) and their load-factor asymptotics are recorded in
`WantedExt.ComputerScience.LinearProbingAnalysisWanted`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LinearProbing

variable {N : ℕ}

/-- **Linear-probing scan with a probe budget.** Starting at cell `h` of a cyclic table whose
occupied cells form `S`, the number of consecutive occupied cells `h, h + 1, …` (indices modulo
the table size) met before the first empty cell, scanning at most `fuel` cells. -/
def displacementAux (S : Finset (Fin N)) : Fin N → ℕ → ℕ
  | _, 0 => 0
  | h, fuel + 1 => if h ∈ S then displacementAux S (finRotate N h) (fuel) + 1 else 0

/-- **Displacement of a linear-probing insertion.** In a cyclic table of `N` cells whose
occupied cells form `S`, the number of occupied cells passed over by an item with hash address
`h` before it reaches an empty cell (at most `N`). -/
def displacement (S : Finset (Fin N)) (h : Fin N) : ℕ :=
  displacementAux S h N

/-- **Probes of a linear-probing insertion.** The number of times the comparison step is
executed when an item with hash address `h` is entered into a cyclic table whose occupied cells
form `S`: one more than its displacement. This assumes that the table is not full
(`S ≠ Finset.univ`). On a full table the scan stops after `N` cells and the value `N + 1` is
not the cost of an insertion: a full one-cell table reports two probes. -/
def probes (S : Finset (Fin N)) (h : Fin N) : ℕ :=
  displacement S h + 1

/-- **Cell taken by a linear-probing insertion.** The cell `h + displacement S h` (modulo the
table size) into which an item with hash address `h` falls. This assumes that the table is not
full (`S ≠ Finset.univ`), so that an empty cell exists. On a full table the scan wraps around to
`h` itself, so the returned cell is occupied and is not an insertion target. -/
def insertCell (S : Finset (Fin N)) (h : Fin N) : Fin N :=
  (finRotate N ^ displacement S h) h

/-- **Occupied cells after a hash sequence.** The occupied cells of a cyclic table of `N` cells,
initially empty, after the items with hash addresses `l` are entered in order by linear
probing. -/
def occupancy (l : List (Fin N)) : Finset (Fin N) :=
  l.foldl (fun S h => insert (insertCell S h) S) ∅

/-- **Expected cost of a linear-probing insertion.** The expected number of probes made when an
item is entered by linear probing into a cyclic table of `N` cells that already holds `n` items,
when the `n + 1` hash addresses are independent and uniform on the `N` cells: the average of
`probes` over all `N ^ (n + 1)` hash sequences. This is `M(N, n + 1)` in Knuth's 1963 note on
open addressing; it is also the expected cost of an unsuccessful search in that table. It is that
expected cost when the table has a free cell, `n < N`. For `n ≥ N ≥ 1` the search for a free cell
is capped and the value is the capped algebraic extension (for example `insertionCost 1 1 = 2`),
not the cost of inserting into a full table; for `N = 0` there is no table and no hash sequence,
and the value is `0` (`0 / 0`). The formula is kept for all `N` and `n` for the exact counts and
limits, whose statements carry their own capacity hypotheses. -/
def insertionCost (N n : ℕ) : ℚ :=
  (∑ a : Fin n → Fin N, ∑ h : Fin N, (probes (occupancy (List.ofFn a)) h : ℚ)) /
    (N : ℚ) ^ (n + 1)

/-- **Expected cost of a successful linear-probing search.** For a table of `N` cells built
from `n` uniformly random hash addresses, the average over the `n` stored items of the expected
number of probes needed to find an item, which equals the number needed to insert it:
`T(N, n) = (1 / n) ∑_{i < n} insertionCost N i` (Section 7 of Knuth's 1963 note). It is that
average for `1 ≤ n ≤ N` stored items; for `n > N` it averages capped extensions of
`insertionCost` (see there), and for `n = 0` there is no item to find and the value is `0`
(`0 / 0`), not an average number of probes. -/
def successfulSearchCost (N n : ℕ) : ℚ :=
  (∑ i ∈ Finset.range n, insertionCost N i) / n

/-- **Knuth's auxiliary sums for linear probing.**
`E_r(N, k) = ∑_{j = 0}^{k - 1} C(r + j, r) (k - 1)(k - 2)⋯(k - j) / N ^ j`,
the sums in which Knuth's 1963 note expresses the exact mean costs of linear probing. -/
def knuthE (r N k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range k, ((r + j).choose r * (k - 1).descFactorial j : ℚ) / (N : ℚ) ^ j

/-- **An insertion into an empty table has displacement zero.** The scan stops at once. -/
theorem displacement_empty (h : Fin N) : displacement (∅ : Finset (Fin N)) h = 0 := by
  rcases N with _ | N
  · exact h.elim0
  · simp [displacement, displacementAux]

/-- **An insertion into an empty table makes one probe.** -/
theorem probes_empty (h : Fin N) : probes (∅ : Finset (Fin N)) h = 1 := by
  simp [probes, displacement_empty]

/-- **Inserting into an empty table costs one probe.** For every table size `N > 0`,
`insertionCost N 0 = 1`, Knuth's `M(N, 1) = 1`. -/
theorem insertionCost_zero (hN : 0 < N) : insertionCost N 0 = 1 := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [insertionCost, occupancy, probes_empty, hN']

/-- **A table holding one item is searched in one probe.** For every table size `N > 0`,
`successfulSearchCost N 1 = 1`, Knuth's `T(N, 1) = 1`. -/
theorem successfulSearchCost_one (hN : 0 < N) : successfulSearchCost N 1 = 1 := by
  simp [successfulSearchCost, insertionCost_zero hN]

/-! ### Rotational symmetry and the number of sequences leaving a cell empty -/

section Rotation

/-- A permutation of the cells that commutes with the cyclic successor map. -/
private def CommutesRotate (σ : Equiv.Perm (Fin N)) : Prop :=
  ∀ x, σ (finRotate N x) = finRotate N (σ x)

private theorem pow_apply_of_commutesRotate {σ : Equiv.Perm (Fin N)} (hσ : CommutesRotate σ)
    (d : ℕ) (x : Fin N) : (finRotate N ^ d) (σ x) = σ ((finRotate N ^ d) x) := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, hσ]

private theorem commutesRotate_pow (j : ℕ) : CommutesRotate (finRotate N ^ j) := by
  intro x
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_succ, ← pow_succ']

private theorem displacementAux_image {σ : Equiv.Perm (Fin N)} (hσ : CommutesRotate σ)
    (S : Finset (Fin N)) : ∀ (h : Fin N) (fuel : ℕ),
    displacementAux (S.image σ) (σ h) fuel = displacementAux S h fuel
  | _, 0 => rfl
  | h, fuel + 1 => by
      simp only [displacementAux, σ.injective.mem_finset_image]
      rw [← hσ, displacementAux_image hσ S (finRotate N h) fuel]

private theorem insertCell_image {σ : Equiv.Perm (Fin N)} (hσ : CommutesRotate σ)
    (S : Finset (Fin N)) (h : Fin N) : insertCell (S.image σ) (σ h) = σ (insertCell S h) := by
  simp only [insertCell, displacement, displacementAux_image hσ,
    pow_apply_of_commutesRotate hσ]

private theorem foldl_map_image {σ : Equiv.Perm (Fin N)} (hσ : CommutesRotate σ)
    (l : List (Fin N)) : ∀ S : Finset (Fin N),
    (l.map σ).foldl (fun S h => insert (insertCell S h) S) (S.image σ) =
      (l.foldl (fun S h => insert (insertCell S h) S) S).image σ := by
  induction l with
  | nil => intro S; rfl
  | cons h l ih =>
      intro S
      simp only [List.map_cons, List.foldl_cons, insertCell_image hσ, ← Finset.image_insert]
      exact ih _

/-- **Linear probing commutes with rotations of the table.** Rotating every hash address by `j`
cells rotates the set of occupied cells by `j` cells. -/
theorem occupancy_map_rotate (j : ℕ) (l : List (Fin N)) :
    occupancy (l.map (finRotate N ^ j)) = (occupancy l).image (finRotate N ^ j) := by
  have h := foldl_map_image (commutesRotate_pow (N := N) j) l ∅
  simpa [occupancy] using h

open Fin.NatCast in
private theorem finRotate_pow_apply (n : ℕ) (k : ℕ) (h : Fin (n + 1)) :
    (finRotate (n + 1) ^ k) h = h + (k : Fin (n + 1)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, finRotate_apply, Nat.cast_succ, add_assoc]

open Fin.NatCast in
/-- Every cell is reached from every other by fewer than `N` cyclic steps. -/
private theorem exists_pow_eq (h c : Fin N) : ∃ k < N, (finRotate N ^ k) h = c := by
  rcases N with _ | n
  · exact h.elim0
  · refine ⟨(c - h).val, (c - h).isLt, ?_⟩
    rw [finRotate_pow_apply, Fin.cast_val_eq_self, add_sub_cancel]

private theorem not_mem_displacementAux (S : Finset (Fin N)) : ∀ (fuel : ℕ) (h : Fin N),
    (∃ i < fuel, (finRotate N ^ i) h ∉ S) →
      (finRotate N ^ displacementAux S h fuel) h ∉ S
  | 0, _, ⟨_, hi, _⟩ => absurd hi (Nat.not_lt_zero _)
  | fuel + 1, h, ⟨i, hi, hiS⟩ => by
      by_cases hh : h ∈ S
      · simp only [displacementAux, hh, ite_true]
        rw [pow_succ, Equiv.Perm.mul_apply]
        apply not_mem_displacementAux S fuel
        rcases i with _ | i
        · exact absurd hh (by simpa using hiS)
        · refine ⟨i, by omega, ?_⟩
          rwa [pow_succ, Equiv.Perm.mul_apply] at hiS
      · simp [displacementAux, hh]

/-- **An insertion into a table that is not full lands on an empty cell.** -/
theorem insertCell_not_mem {S : Finset (Fin N)} (hS : S.card < N) (h : Fin N) :
    insertCell S h ∉ S := by
  obtain ⟨c, hc⟩ : ∃ c, c ∉ S := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have : S = Finset.univ := Finset.eq_univ_of_forall hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hS
    exact lt_irrefl _ hS
  obtain ⟨k, hk, hkc⟩ := exists_pow_eq h c
  exact not_mem_displacementAux S N h ⟨k, hk, hkc ▸ hc⟩

private theorem card_foldl (l : List (Fin N)) : ∀ S : Finset (Fin N), S.card + l.length ≤ N →
    (l.foldl (fun S h => insert (insertCell S h) S) S).card = S.card + l.length := by
  induction l with
  | nil => intro S _; simp
  | cons h l ih =>
      intro S hS
      simp only [List.foldl_cons, List.length_cons] at hS ⊢
      have hlt : S.card < N := by omega
      rw [ih _ (by rw [Finset.card_insert_of_notMem (insertCell_not_mem hlt h)]; omega),
        Finset.card_insert_of_notMem (insertCell_not_mem hlt h)]
      omega

/-- **Linear probing places every item while the table has room.** If at most `N` items are
entered, they occupy exactly as many cells as there are items. -/
theorem card_occupancy {l : List (Fin N)} (hl : l.length ≤ N) :
    (occupancy l).card = l.length := by
  simpa [occupancy] using card_foldl l ∅ (by simpa using hl)

/-- **Rotational symmetry of linear probing** (the circle argument of Knuth's 1963 note, Lemma 1;
D. E. Knuth, *Linear probing and graphs*, Algorithmica 22 (1998), Section 1). For `n ≤ N` and
every cell `c` of a cyclic table of `N` cells, `N` times the number of hash sequences of `n`
items that leave `c` empty is `(N - n) N ^ n`: each cell is left empty by the same number of
sequences, and every sequence leaves exactly `N - n` cells empty. -/
theorem mul_card_not_mem_occupancy {n : ℕ} (hn : n ≤ N) (c : Fin N) :
    N * (Finset.univ.filter fun a : Fin n → Fin N => c ∉ occupancy (List.ofFn a)).card =
      (N - n) * N ^ n := by
  set E : Fin N → ℕ := fun c =>
    (Finset.univ.filter fun a : Fin n → Fin N => c ∉ occupancy (List.ofFn a)).card with hE
  -- Every cell is left empty by the same number of sequences.
  have hconst : ∀ c', E c' = E c := by
    intro c'
    obtain ⟨k, -, hk⟩ := exists_pow_eq c c'
    set σ := finRotate N ^ k
    refine Finset.card_bij' (fun a _ => fun x => σ.symm (a x)) (fun a _ => fun x => σ (a x))
      ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      intro hmem
      apply ha
      have hmap : List.ofFn a = (List.ofFn fun x => σ.symm (a x)).map σ := by
        rw [List.map_ofFn]; congr 1; funext x; simp
      rw [hmap, occupancy_map_rotate, ← hk]
      exact Finset.mem_image_of_mem _ hmem
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      intro hmem
      apply ha
      have hmap : List.ofFn (fun x => σ (a x)) = (List.ofFn a).map σ := by
        rw [List.map_ofFn]; rfl
      rw [hmap, occupancy_map_rotate, ← hk] at hmem
      exact σ.injective.mem_finset_image.mp hmem
    · intro a _; funext x; simp
    · intro a _; funext x; simp
  -- Summing over the cells counts, for every sequence, its `N - n` empty cells.
  have hsum : ∑ c', E c' = (N - n) * N ^ n := by
    simp only [hE, Finset.card_filter]
    rw [Finset.sum_comm]
    have hrow : ∀ a : Fin n → Fin N,
        (∑ c' : Fin N, if c' ∉ occupancy (List.ofFn a) then 1 else 0) = N - n := by
      intro a
      rw [← Finset.card_filter, Finset.filter_not, Finset.filter_mem_eq_inter,
        Finset.univ_inter, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, card_occupancy (by simpa using hn), List.length_ofFn]
    rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, smul_eq_mul, mul_comm]
  rw [← hsum, Finset.sum_congr rfl fun c' _ => hconst c', Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Number of hash sequences that leave a given cell empty** (Knuth, *Linear probing and
graphs*, 1998, Section 1: of the `m ^ n` hash sequences, exactly a fraction `(m - n) / m` leave
cell `0` unoccupied). For `1 ≤ n ≤ N` and every cell `c` of a cyclic table of `N` cells, exactly
`(N - n) N ^ (n - 1)` of the `N ^ n` hash sequences of `n` items leave `c` empty after linear
probing. -/
theorem card_not_mem_occupancy {n : ℕ} (hn₁ : 1 ≤ n) (hn : n ≤ N) (c : Fin N) :
    (Finset.univ.filter fun a : Fin n → Fin N => c ∉ occupancy (List.ofFn a)).card =
      (N - n) * N ^ (n - 1) := by
  have hN : 0 < N := lt_of_lt_of_le hn₁ hn
  have h := mul_card_not_mem_occupancy hn c
  have hpow : N ^ n = N * N ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow, mul_left_comm] at h
  exact Nat.eq_of_mul_eq_mul_left hN h

end Rotation

open MetaMathlibExt.PollakPartialParking in
/-- **Number of hash sequences without overflow** (Knuth, *Notes on "open" addressing*, 1963,
Lemma 1). For `0 < k ≤ n`, the number of hash sequences `f : Fin k → Fin n` for which linear
probing without wrap-around places all `k` items in a table of `n` cells is
`(n + 1 - k)(n + 1) ^ (k - 1)`. Knuth's lemma also covers `k = 0` and `k = n + 1`; for `k = n`
the count `(n + 1) ^ (n - 1)` is the number of parking functions. -/
theorem card_linSuccess (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    Nat.card {f : Fin k → Fin n // LinSuccess k n f} = (n + 1 - k) * (n + 1) ^ (k - 1) := by
  rw [← pollak_partial_parking_functions_card k n hk hkn]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun f =>
    linSuccess_iff_isPartialParkingFunction k n f hkn)

end Cslib.Algorithms.Lean.LinearProbing
