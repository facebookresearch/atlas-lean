/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.RNA.Nussinov
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Tropical.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Exp
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max

/-!
# RNA secondary structure: semiring folding, the McCaskill partition function

The Nussinov recursion (`Cslib.Bioinformatics.RNA.Nussinov`) works over any commutative
semiring once a structure is scored by the product of the weights of its base pairs. Fix a
sequence `s`, a complementarity relation `pair`, a minimum hairpin size `m` and a weight
`w i j` in a commutative semiring `R` for each candidate pair `(i, j)` of positions. The
**inside value** `inside pair m s w i len` is the sum, over all secondary structures `P`
supported in the interval `[i, i + len)`, of `∏ (i, j) ∈ P, w i j`. It satisfies the
recursion on the first base of the interval: that base is either unpaired, or paired with a
later base `i + 1 + k` (`k ≥ m`), which splits the rest into an enclosed and an outer
interval. The choice of semiring gives the classical algorithms:

* the min-plus (tropical) semiring with weight `-1` per pair gives minus the maximum number
  of base pairs, i.e. the Nussinov value (Nussinov et al. 1978);
* the counting semiring `ℕ` with unit weights and every pair allowed counts secondary
  structures on `n` points with minimum hairpin `m`: Waterman's numbers `S_m(n)`, which are
  the Motzkin numbers for `m = 0` and the Stein–Waterman numbers for `m = 1`;
* the sum-product semiring `ℝ` with Boltzmann weights `exp (-e i j / RT)` gives the
  **McCaskill partition function** `Z = ∑_S exp (-E(S) / RT)` for an additive base-pair
  energy `E(S) = ∑ (i, j) ∈ S, e i j` (McCaskill 1990).

McCaskill's **outside recursion** gives the total weight of the structures that contain a
fixed pair `(i, j)`: such a structure either has no pair enclosing `(i, j)`, or has a unique
innermost enclosing pair `(a, b)`. Dividing by `Z` gives the base-pair probability
`P(i, j)`, and since each base lies in at most one pair, `∑_j (P(i, j) + P(j, i)) ≤ 1`.

## Main definitions

* `CanPair pair s i j`: positions `i` and `j` of `s` carry complementary bases.
* `inside`, `outside`: the inside and outside recursions over a commutative semiring.
* `structuresIn`, `structures`: the finite sets of secondary structures (in an interval / on
  the whole sequence); `weight w P = ∏ (i, j) ∈ P, w i j`.
* `watermanNumber m n`: Waterman's recursion for the number of secondary structures.
* `energy`, `partitionFunction`, `pairProb`: the additive energy model, its Boltzmann
  partition function and the base-pair probabilities.

## Scope

The energy model here is additive over base pairs (any position-dependent weight `w i j`, so
any base-pair-dependent energy). McCaskill's paper uses the loop (nearest-neighbor) energy model;
its pair-side loop decomposition (each pair is the branch of exactly one loop) and
Zuker's minimum free energy algorithm for that model are proved
in `CSLibExt.Bioinformatics.RNA.Zuker`. Positions are not decomposed into loops there:
`existsUnique_loop_of_pos` gives only an innermost strict-container assignment. The Stein–Waterman closed form for `m = 1`
is not formalized; only the recursion.

## Main results

* `inside_eq_sum`: the inside recursion sums the weights of all structures in the interval.
* `outside_mul_eq_sum`: the outside recursion times the inside value of `(i, j)` sums the
  weights of all structures containing the pair `(i, j)`.
* `inside_minTropical`: over the min-plus semiring with weight `-1` per pair the inside value
  is minus the Nussinov maximum number of pairs.
* `card_structures_eq_watermanNumber`, `watermanNumber_zero_eq_motzkinNumber`: counting.
* `inside_boltzmann_eq_partitionFunction`, `pairProb_eq_outside`, `one_le_sum_weight`,
  `sum_pairProb_le_one`: McCaskill's algorithm and base-pair probabilities.

## Cost model

`inside` and `outside` are specifications by recursion on interval lengths and take
exponential time if evaluated directly; memoizing them on the `O(n²)` intervals gives
an `O(n³)` inside table and an `O(n⁴)` outside table for this form of the recursion (an
`O(n³)` outside pass needs a further refactoring of the outside sum). The tables are not
formalized here.

## References

* J. S. McCaskill, *The equilibrium partition function and base pair binding probabilities
  for RNA secondary structure*, Biopolymers 29 (1990), 1105–1119.
* R. Nussinov, G. Pieczenik, J. R. Griggs and D. J. Kleitman, *Algorithms for loop
  matchings*, SIAM J. Appl. Math. 35 (1978), 68–82.
* M. S. Waterman, *Secondary structure of single-stranded nucleic acids*, Adv. Math. Suppl.
  Stud. 1 (1978), 167–212.
* P. R. Stein and M. S. Waterman, *On some new sequences generalizing the Catalan and Motzkin
  numbers*, Discrete Math. 26 (1979), 261–272.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.RNA.PartitionFunction

open Cslib.Bioinformatics.RNA.Nussinov

variable {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)

/-- Positions `i` and `j` of `s` both lie in `s` and carry complementary bases. -/
def CanPair (i j : ℕ) : Prop :=
  ∃ a b, s[i]? = some a ∧ s[j]? = some b ∧ pair a b

/-- `CanPair` is decidable for a decidable complementarity relation. -/
instance [DecidableRel pair] (i j : ℕ) : Decidable (CanPair pair s i j) :=
  decidable_of_iff (∃ a ∈ s[i]?, ∃ b ∈ s[j]?, pair a b) (by simp [CanPair, Option.mem_def])

/-- **Inside recursion** over a commutative semiring `R`: `inside pair m s w i len` is the
weighted sum over the secondary structures supported in the interval `[i, i + len)` (proved in
`inside_eq_sum`). Base `i` is either unpaired, or paired with `i + 1 + k` for some `k ≥ m`
with `CanPair pair s i (i + 1 + k)`, which contributes `w i (i + 1 + k)` times the inside
values of the enclosed interval `[i + 1, i + 1 + k)` and of the outer interval
`[i + k + 2, i + len + 1)`. -/
def inside [DecidableRel pair] {R : Type*} [CommSemiring R] (w : ℕ → ℕ → R) :
    ℕ → ℕ → R
  | _, 0 => 1
  | i, len + 1 =>
      inside w (i + 1) len +
        ∑ k : Fin len, if m ≤ k.val ∧ CanPair pair s i (i + 1 + k.val) then
          w i (i + 1 + k.val) * inside w (i + 1) k.val *
            inside w (i + k.val + 2) (len - 1 - k.val)
        else 0
  termination_by _ len => len
  decreasing_by all_goals omega

/-- **Outside recursion** (McCaskill 1990) over a commutative semiring `R`, for a sequence of
length `n = s.length`: `outside pair m s w i j` is the weighted sum of the parts outside the
pair `(i, j)` of all structures containing it (proved in `outside_mul_eq_sum`). Either no pair
encloses `(i, j)`, leaving independent structures on `[0, i)` and `[j + 1, n)`, or there is a
unique innermost enclosing pair `(a, b)` (`a < i`, `j < b < n`), contributing the outside value
of `(a, b)`, its weight, and the inside values of `[a + 1, i)` and `[j + 1, b)`. -/
def outside [DecidableRel pair] {R : Type*} [CommSemiring R] (w : ℕ → ℕ → R) (i j : ℕ) : R :=
  inside pair m s w 0 i * inside pair m s w (j + 1) (s.length - (j + 1)) +
    ∑ a : Fin i, ∑ c : Fin (s.length - (j + 1)),
      if a.val + m < j + 1 + c.val ∧ CanPair pair s a.val (j + 1 + c.val) then
        outside w a.val (j + 1 + c.val) * w a.val (j + 1 + c.val) *
          inside pair m s w (a.val + 1) (i - (a.val + 1)) * inside pair m s w (j + 1) c.val
      else 0
  termination_by s.length - (j - i)
  decreasing_by omega

open Classical in
/-- The secondary structures on `s` (`IsStructure pair m s`) all of whose pairs lie in the
interval `[i, i + len)`. -/
noncomputable def structuresIn (i len : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((Finset.Ico i (i + len) ×ˢ Finset.Ico i (i + len)).powerset).filter
    fun P => IsStructure pair m s P

/-- All secondary structures on `s` with minimum hairpin `m` (see `mem_structures`). -/
noncomputable def structures : Finset (Finset (ℕ × ℕ)) :=
  structuresIn pair m s 0 s.length

/-- The weight of a structure: the product of the weights of its base pairs. -/
def weight {R : Type*} [CommMonoid R] (w : ℕ → ℕ → R) (P : Finset (ℕ × ℕ)) : R :=
  ∏ p ∈ P, w p.1 p.2

/-- `structures` is exactly the set of secondary structures on `s`. -/
theorem mem_structures (P : Finset (ℕ × ℕ)) :
    P ∈ structures pair m s ↔ IsStructure pair m s P := by
  classical
  simp only [structures, structuresIn, Finset.mem_filter, Finset.mem_powerset, Nat.zero_add,
    and_iff_right_iff_imp]
  intro hP p hp
  obtain ⟨a, b, ha, hb, _⟩ := hP.compl p hp
  have h₁ := (List.getElem?_eq_some_iff.mp ha).choose
  have h₂ := (List.getElem?_eq_some_iff.mp hb).choose
  simp only [Finset.mem_product, Finset.mem_Ico]
  omega

private theorem structure_subset {B : Type*} (pair : B → B → Prop) (m : ℕ)
    (s : List B) {P Q : Finset (ℕ × ℕ)} (h : IsStructure pair m s P) (hQP : Q ⊆ P) :
    IsStructure pair m s Q where
  loop p hp := h.loop p (hQP hp)
  compl p hp := h.compl p (hQP hp)
  disjoint p hp q hq hn := h.disjoint p (hQP hp) q (hQP hq) hn
  noncrossing p hp q hq := h.noncrossing p (hQP hp) q (hQP hq)

private theorem mem_interval {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    (i len : ℕ) (P : Finset (ℕ × ℕ)) :
    P ∈ structuresIn pair m s i len ↔
      IsStructure pair m s P ∧ ∀ p ∈ P, i ≤ p.1 ∧ p.2 < i + len := by
  classical
  simp only [structuresIn, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hb, hs⟩
    refine ⟨hs, ?_⟩
    intro p hp
    have h := hb hp
    simp only [Finset.mem_product, Finset.mem_Ico] at h
    exact ⟨h.1.1, h.2.2⟩
  · rintro ⟨hs, hb⟩
    refine ⟨?_, hs⟩
    intro p hp
    have h := hb p hp
    have hl := hs.loop p hp
    simp only [Finset.mem_product, Finset.mem_Ico]
    omega

private theorem structure_union {B : Type*} (pair : B → B → Prop) (m : ℕ)
    (s : List B) {P Q : Finset (ℕ × ℕ)} (hp : IsStructure pair m s P)
    (hq : IsStructure pair m s Q) (hsep : ∀ p ∈ P, ∀ q ∈ Q, p.2 < q.1) :
    IsStructure pair m s (P ∪ Q) := by
  classical
  constructor
  · intro p h
    rcases Finset.mem_union.mp h with h | h
    · exact hp.loop p h
    · exact hq.loop p h
  · intro p h
    rcases Finset.mem_union.mp h with h | h
    · exact hp.compl p h
    · exact hq.compl p h
  · intro p h q h' hn
    rcases Finset.mem_union.mp h with h | h <;>
      rcases Finset.mem_union.mp h' with h' | h'
    · exact hp.disjoint p h q h' hn
    · have hlp := hp.loop p h
      have hlq := hq.loop q h'
      have hs := hsep p h q h'
      omega
    · have hlp := hq.loop p h
      have hlq := hp.loop q h'
      have hs := hsep q h' p h
      omega
    · exact hq.disjoint p h q h' hn
  · intro p h q h'
    rcases Finset.mem_union.mp h with h | h <;>
      rcases Finset.mem_union.mp h' with h' | h'
    · exact hp.noncrossing p h q h'
    · have hs := hsep p h q h'
      omega
    · have hs := hsep q h' p h
      have hlp := hq.loop p h
      have hlq := hp.loop q h'
      omega
    · exact hq.noncrossing p h q h'

private theorem structure_insert {B : Type*} (pair : B → B → Prop) (m : ℕ)
    (s : List B) {P : Finset (ℕ × ℕ)} (i j : ℕ) (hp : IsStructure pair m s P)
    (hl : i + m < j) (hc : CanPair pair s i j)
    (hsep : ∀ p ∈ P, (i < p.1 ∧ p.2 < j) ∨ j < p.1) :
    IsStructure pair m s (insert (i, j) P) := by
  classical
  constructor
  · intro p h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact hl
    · exact hp.loop p h
  · intro p h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact hc
    · exact hp.compl p h
  · intro p h q h' hn
    rcases Finset.mem_insert.mp h with rfl | h <;>
      rcases Finset.mem_insert.mp h' with rfl | h'
    · exact (hn rfl).elim
    · have hs := hsep q h'
      have hq := hp.loop q h'
      dsimp at *
      omega
    · have hs := hsep p h
      have hlp := hp.loop p h
      dsimp at *
      omega
    · exact hp.disjoint p h q h' hn
  · intro p h q h'
    rcases Finset.mem_insert.mp h with rfl | h <;>
      rcases Finset.mem_insert.mp h' with rfl | h'
    · simp
    · have hs := hsep q h'
      dsimp at *
      omega
    · have hs := hsep p h
      have hlp := hp.loop p h
      dsimp at *
      omega
    · exact hp.noncrossing p h q h'

private theorem join_mem {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    (i n k : ℕ) (hk : k < n) (hm : m ≤ k) (hc : CanPair pair s i (i + 1 + k))
    {I O : Finset (ℕ × ℕ)} (hi : I ∈ structuresIn pair m s (i + 1) k)
    (ho : O ∈ structuresIn pair m s (i + k + 2) (n - 1 - k)) :
    insert (i, i + 1 + k) (I ∪ O) ∈ structuresIn pair m s i (n + 1) := by
  classical
  obtain ⟨his, hib⟩ := (mem_interval pair m s _ _ _).mp hi
  obtain ⟨hos, hob⟩ := (mem_interval pair m s _ _ _).mp ho
  apply (mem_interval pair m s _ _ _).mpr
  refine ⟨structure_insert pair m s i (i + 1 + k)
    (structure_union pair m s his hos ?_) (by omega) hc ?_, ?_⟩
  · intro p hp q hq
    have h1 := hib p hp
    have h2 := hob q hq
    omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have hb := hib p hp
      exact Or.inl ⟨by omega, hb.2⟩
    · have hb := hob p hp
      exact Or.inr (by omega)
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · dsimp
      omega
    · rcases Finset.mem_union.mp hp with hp | hp
      · have hb := hib p hp
        omega
      · have hb := hob p hp
        omega

private theorem split_region {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    (i len j : ℕ) {P : Finset (ℕ × ℕ)} (hP : P ∈ structuresIn pair m s i len)
    (hc : (i, j) ∈ P) {p : ℕ × ℕ} (hp : p ∈ P) (hne : p ≠ (i, j)) :
    (i < p.1 ∧ p.2 < j) ∨ j < p.1 := by
  obtain ⟨hs, hb⟩ := (mem_interval pair m s _ _ _).mp hP
  have h := hb p hp
  have hl := hs.loop p hp
  have hd := hs.disjoint p hp (i, j) hc hne
  have hn := hs.noncrossing (i, j) hc p hp
  dsimp at *
  omega

private theorem split_mem {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    (i n k : ℕ) (hk : k < n) {P : Finset (ℕ × ℕ)}
    (hP : P ∈ structuresIn pair m s i (n + 1)) (hc : (i, i + 1 + k) ∈ P) :
    P.filter (fun p => p.2 < i + 1 + k) ∈ structuresIn pair m s (i + 1) k ∧
    P.filter (fun p => i + 1 + k < p.1) ∈
      structuresIn pair m s (i + k + 2) (n - 1 - k) := by
  classical
  obtain ⟨hs, hb⟩ := (mem_interval pair m s _ _ _).mp hP
  constructor
  · apply (mem_interval pair m s _ _ _).mpr
    refine ⟨structure_subset pair m s hs (Finset.filter_subset _ _), ?_⟩
    intro p hp
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
    have hne : p ≠ (i, i + 1 + k) := by rintro rfl; omega
    have hr := split_region pair m s i (n + 1) _ hP hc hp hne
    have hl := hs.loop p hp
    omega
  · apply (mem_interval pair m s _ _ _).mpr
    refine ⟨structure_subset pair m s hs (Finset.filter_subset _ _), ?_⟩
    intro p hp
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
    have h := hb p hp
    omega

private theorem split_join {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    (i n k : ℕ) {P : Finset (ℕ × ℕ)} (hP : P ∈ structuresIn pair m s i (n + 1))
    (hc : (i, i + 1 + k) ∈ P) :
    insert (i, i + 1 + k)
      (P.filter (fun p => p.2 < i + 1 + k) ∪
        P.filter (fun p => i + 1 + k < p.1)) = P := by
  classical
  ext p
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (rfl | ⟨hp, _⟩ | ⟨hp, _⟩)
    · exact hc
    · exact hp
    · exact hp
  · intro hp
    by_cases he : p = (i, i + 1 + k)
    · exact Or.inl he
    · have hr := split_region pair m s i (n + 1) _ hP hc hp he
      rcases hr with h | h
      · exact Or.inr (Or.inl ⟨hp, h.2⟩)
      · exact Or.inr (Or.inr ⟨hp, h⟩)

private theorem join_left {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    (i n k : ℕ) {I O : Finset (ℕ × ℕ)}
    (hi : I ∈ structuresIn pair m s (i + 1) k)
    (ho : O ∈ structuresIn pair m s (i + k + 2) (n - 1 - k)) :
    (insert (i, i + 1 + k) (I ∪ O)).filter (fun p => p.2 < i + 1 + k) = I := by
  classical
  obtain ⟨his, hib⟩ := (mem_interval pair m s _ _ _).mp hi
  obtain ⟨hos, hob⟩ := (mem_interval pair m s _ _ _).mp ho
  ext p
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨rfl | hp | hp, hlt⟩
    · omega
    · exact hp
    · have hb := hob p hp
      have hl := hos.loop p hp
      omega
  · intro hp
    exact ⟨Or.inr (Or.inl hp), (hib p hp).2⟩

private theorem join_right {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    (i n k : ℕ) {I O : Finset (ℕ × ℕ)}
    (hi : I ∈ structuresIn pair m s (i + 1) k)
    (ho : O ∈ structuresIn pair m s (i + k + 2) (n - 1 - k)) :
    (insert (i, i + 1 + k) (I ∪ O)).filter (fun p => i + 1 + k < p.1) = O := by
  classical
  obtain ⟨his, hib⟩ := (mem_interval pair m s _ _ _).mp hi
  obtain ⟨hos, hob⟩ := (mem_interval pair m s _ _ _).mp ho
  ext p
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨rfl | hp | hp, hlt⟩
    · omega
    · have hb := hib p hp
      have hl := his.loop p hp
      omega
    · exact hp
  · intro hp
    refine ⟨Or.inr (Or.inr hp), ?_⟩
    have hb := hob p hp
    omega

private theorem weight_join {B R : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    [CommSemiring R] (w : ℕ → ℕ → R) (i n k : ℕ) {I O : Finset (ℕ × ℕ)}
    (hi : I ∈ structuresIn pair m s (i + 1) k)
    (ho : O ∈ structuresIn pair m s (i + k + 2) (n - 1 - k)) :
    weight w (insert (i, i + 1 + k) (I ∪ O)) =
      w i (i + 1 + k) * weight w I * weight w O := by
  classical
  obtain ⟨his, hib⟩ := (mem_interval pair m s _ _ _).mp hi
  obtain ⟨hos, hob⟩ := (mem_interval pair m s _ _ _).mp ho
  have hn : (i, i + 1 + k) ∉ I ∪ O := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have hb := hib _ h
      dsimp at hb
      omega
    · have hb := hob _ h
      dsimp at hb
      omega
  have hd : Disjoint I O := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hb := hib p hp
    have hb' := hob p hq
    have hl := his.loop p hp
    omega
  simp only [weight, Finset.prod_insert hn, Finset.prod_union hd, mul_assoc]

private theorem branch_sum {B R : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    [DecidableRel pair] [CommSemiring R] (w : ℕ → ℕ → R) (i n k : ℕ) (hk : k < n) :
    ∑ P ∈ (structuresIn pair m s i (n + 1)).filter
        (fun P => (i, i + 1 + k) ∈ P), weight w P =
      if m ≤ k ∧ CanPair pair s i (i + 1 + k) then
        w i (i + 1 + k) *
          (∑ I ∈ structuresIn pair m s (i + 1) k, weight w I) *
          (∑ O ∈ structuresIn pair m s (i + k + 2) (n - 1 - k), weight w O)
      else 0 := by
  classical
  by_cases hc : m ≤ k ∧ CanPair pair s i (i + 1 + k)
  · rw [ite_eq_left hc]
    symm
    calc
      _ = ∑ t ∈ structuresIn pair m s (i + 1) k ×ˢ
          structuresIn pair m s (i + k + 2) (n - 1 - k),
          w i (i + 1 + k) * weight w t.1 * weight w t.2 := by
        rw [Finset.sum_product]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_bij (fun t _ => insert (i, i + 1 + k) (t.1 ∪ t.2))
        · intro t ht
          obtain ⟨hi, ho⟩ := Finset.mem_product.mp ht
          exact Finset.mem_filter.mpr
            ⟨join_mem pair m s i n k hk hc.1 hc.2 hi ho, Finset.mem_insert_self _ _⟩
        · intro t ht u hu he
          obtain ⟨hi, ho⟩ := Finset.mem_product.mp ht
          obtain ⟨hi', ho'⟩ := Finset.mem_product.mp hu
          apply Prod.ext
          · have h := congrArg (Finset.filter (fun p => p.2 < i + 1 + k)) he
            simpa only [join_left pair m s i n k hi ho,
              join_left pair m s i n k hi' ho'] using h
          · have h := congrArg (Finset.filter (fun p => i + 1 + k < p.1)) he
            simpa only [join_right pair m s i n k hi ho,
              join_right pair m s i n k hi' ho'] using h
        · intro P hP
          obtain ⟨hP, hclose⟩ := Finset.mem_filter.mp hP
          obtain ⟨hi, ho⟩ := split_mem pair m s i n k hk hP hclose
          exact ⟨(_, _), Finset.mem_product.mpr ⟨hi, ho⟩,
            split_join pair m s i n k hP hclose⟩
        · intro t ht
          obtain ⟨hi, ho⟩ := Finset.mem_product.mp ht
          exact (weight_join pair m s w i n k hi ho).symm
  · rw [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro P hP
    obtain ⟨hP, hclose⟩ := Finset.mem_filter.mp hP
    have hs := ((mem_interval pair m s _ _ _).mp hP).1
    have hl := hs.loop _ hclose
    have hp := hs.compl _ hclose
    apply (hc ?_).elim
    exact ⟨by dsimp at hl; omega, hp⟩

private theorem unpaired_eq {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    (i n : ℕ) :
    (structuresIn pair m s i (n + 1)).filter (fun P => ∀ p ∈ P, p.1 ≠ i) =
      structuresIn pair m s (i + 1) n := by
  classical
  ext P
  simp only [Finset.mem_filter, mem_interval]
  constructor
  · rintro ⟨⟨hs, hb⟩, hn⟩
    refine ⟨hs, ?_⟩
    intro p hp
    have h := hb p hp
    have hne := hn p hp
    omega
  · rintro ⟨hs, hb⟩
    refine ⟨⟨hs, ?_⟩, ?_⟩
    · intro p hp
      have h := hb p hp
      omega
    · intro p hp
      have h := hb p hp
      omega

private theorem branches_disjoint {B : Type*} (pair : B → B → Prop) (m : ℕ)
    (s : List B) (i n : ℕ) {k l : ℕ} (hne : k ≠ l) :
    Disjoint ((structuresIn pair m s i (n + 1)).filter
      (fun P => (i, i + 1 + k) ∈ P))
      ((structuresIn pair m s i (n + 1)).filter (fun P => (i, i + 1 + l) ∈ P)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro P hk hl
  obtain ⟨hP, hk⟩ := Finset.mem_filter.mp hk
  obtain ⟨_, hl⟩ := Finset.mem_filter.mp hl
  have hs := ((mem_interval pair m s _ _ _).mp hP).1
  have he : (i, i + 1 + k) ≠ (i, i + 1 + l) := by
    intro h
    have h' := congrArg Prod.snd h
    dsimp at h'
    omega
  exact (hs.disjoint _ hk _ hl he).1 rfl

private theorem paired_eq {B : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    (i n : ℕ) :
    (structuresIn pair m s i (n + 1)).filter (fun P => ¬ ∀ p ∈ P, p.1 ≠ i) =
      (Finset.range n).biUnion (fun k =>
        (structuresIn pair m s i (n + 1)).filter (fun P => (i, i + 1 + k) ∈ P)) := by
  classical
  ext P
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨hP, hn⟩
    simp only [not_forall, ne_eq, not_not] at hn
    obtain ⟨p, hp, hi⟩ := hn
    obtain ⟨hs, hb⟩ := (mem_interval pair m s _ _ _).mp hP
    have hl := hs.loop p hp
    have h := hb p hp
    refine ⟨p.2 - i - 1, by omega, hP, ?_⟩
    have he : (i, i + 1 + (p.2 - i - 1)) = p := by
      apply Prod.ext <;> dsimp <;> omega
    rwa [he]
  · rintro ⟨k, hk, hP, hc⟩
    refine ⟨hP, ?_⟩
    intro hn
    exact hn _ hc rfl

private theorem sum_step {B R : Type*} (pair : B → B → Prop) (m : ℕ) (s : List B)
    [DecidableRel pair] [CommSemiring R] (w : ℕ → ℕ → R) (i n : ℕ) :
    ∑ P ∈ structuresIn pair m s i (n + 1), weight w P =
      (∑ P ∈ structuresIn pair m s (i + 1) n, weight w P) +
        ∑ k : Fin n, if m ≤ k.val ∧ CanPair pair s i (i + 1 + k.val) then
          w i (i + 1 + k.val) *
            (∑ I ∈ structuresIn pair m s (i + 1) k.val, weight w I) *
            (∑ O ∈ structuresIn pair m s (i + k.val + 2) (n - 1 - k.val), weight w O)
        else 0 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun P => ∀ p ∈ P, p.1 ≠ i),
    unpaired_eq pair m s i n, paired_eq pair m s i n]
  congr 1
  rw [Finset.sum_biUnion]
  · apply Finset.sum_bij (fun k hk => (⟨k, Finset.mem_range.mp hk⟩ : Fin n))
    · intro k hk
      exact Finset.mem_univ _
    · intro k hk l hl he
      exact congrArg Fin.val he
    · intro k hk
      exact ⟨k.val, Finset.mem_range.mpr k.isLt, rfl⟩
    · intro k hk
      exact branch_sum pair m s w i n k (Finset.mem_range.mp hk)
  · intro k hk l hl hne
    exact branches_disjoint pair m s i n hne

private theorem structures_zero {B : Type*} (pair : B → B → Prop) (m : ℕ)
    (s : List B) (i : ℕ) : structuresIn pair m s i 0 = {∅} := by
  classical
  ext P
  rw [mem_interval]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨hs, hb⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have h := hb p hp
    have hl := hs.loop p hp
    omega
  · rintro rfl
    constructor
    · constructor <;> simp
    · simp

/-- **Inside algorithm**: the inside recursion sums the weights of all secondary structures
supported in the interval `[i, i + len)`, over any commutative semiring. -/
theorem inside_eq_sum [DecidableRel pair] {R : Type*} [CommSemiring R] (w : ℕ → ℕ → R)
    (i len : ℕ) :
    inside pair m s w i len = ∑ P ∈ structuresIn pair m s i len, weight w P := by
  classical
  induction len using Nat.strong_induction_on generalizing i with
  | h len ih =>
    cases len with
    | zero => simp [inside, structures_zero, weight]
    | succ n =>
      rw [inside, sum_step pair m s w i n, ih n (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hc : m ≤ k.val ∧ CanPair pair s i (i + 1 + k.val)
      · rw [ite_eq_left hc, ite_eq_left hc, ih k.val (by omega),
          ih (n - 1 - k.val) (by omega)]
      · simp only [ite_eq_right hc]

/-- The inside value of the whole sequence sums the weights of all its secondary structures. -/
theorem inside_eq_sum_structures [DecidableRel pair] {R : Type*} [CommSemiring R]
    (w : ℕ → ℕ → R) :
    inside pair m s w 0 s.length = ∑ P ∈ structures pair m s, weight w P :=
  inside_eq_sum pair m s w 0 s.length

private theorem out_structure_subset {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {P Q : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P)
    (hQ : Q ⊆ P) : IsStructure pair m s Q :=
  ⟨fun p hp => hP.loop p (hQ hp), fun p hp => hP.compl p (hQ hp),
    fun p hp q hq => hP.disjoint p (hQ hp) q (hQ hq),
    fun p hp q hq => hP.noncrossing p (hQ hp) q (hQ hq)⟩

private theorem pair_bounds {B : Type*} {pair : B → B → Prop} {s : List B}
    {i j : ℕ} (hc : CanPair pair s i j) : i < s.length ∧ j < s.length := by
  obtain ⟨a, b, ha, hb, _⟩ := hc
  exact ⟨(List.getElem?_eq_some_iff.mp ha).choose,
    (List.getElem?_eq_some_iff.mp hb).choose⟩

private theorem out_mem_interval {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i len : ℕ} {P : Finset (ℕ × ℕ)} :
    P ∈ structuresIn pair m s i len ↔ IsStructure pair m s P ∧
      ∀ p ∈ P, i ≤ p.1 ∧ p.1 < i + len ∧ i ≤ p.2 ∧ p.2 < i + len := by
  classical
  simp only [structuresIn, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_iff, Finset.mem_product, Finset.mem_Ico]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨hs, fun p hp => ⟨(h hp).1.1, (h hp).1.2, (h hp).2.1, (h hp).2.2⟩⟩
  · rintro ⟨hs, h⟩
    exact ⟨fun p hp => ⟨⟨(h p hp).1, (h p hp).2.1⟩,
      ⟨(h p hp).2.2.1, (h p hp).2.2.2⟩⟩, hs⟩

private def apart (p q : ℕ × ℕ) : Prop :=
  p.2 < q.1 ∨ q.2 < p.1 ∨ (p.1 < q.1 ∧ q.2 < p.2) ∨
    (q.1 < p.1 ∧ p.2 < q.2)

private theorem structure_apart {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {P : Finset (ℕ × ℕ)} (hs : IsStructure pair m s P)
    {p q : ℕ × ℕ} (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) : apart p q := by
  have hlp := hs.loop p hp
  have hlq := hs.loop q hq
  have hd := hs.disjoint p hp q hq hne
  have hn := hs.noncrossing p hp q hq
  have hn' := hs.noncrossing q hq p hp
  unfold apart
  omega

private theorem out_structure_union {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {P Q : Finset (ℕ × ℕ)} (hP : IsStructure pair m s P)
    (hQ : IsStructure pair m s Q) (hcross : ∀ p ∈ P, ∀ q ∈ Q, apart p q) :
    IsStructure pair m s (P ∪ Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP.loop p hp
    · exact hQ.loop p hp
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP.compl p hp
    · exact hQ.compl p hp
  · intro p hp q hq hne
    rcases Finset.mem_union.mp hp with hp | hp <;>
      rcases Finset.mem_union.mp hq with hq | hq
    · exact hP.disjoint p hp q hq hne
    · have h := hcross p hp q hq
      have hlp := hP.loop p hp
      have hlq := hQ.loop q hq
      unfold apart at h
      omega
    · have h := hcross q hq p hp
      have hlp := hQ.loop p hp
      have hlq := hP.loop q hq
      unfold apart at h
      omega
    · exact hQ.disjoint p hp q hq hne
  · intro p hp q hq
    rcases Finset.mem_union.mp hp with hp | hp <;>
      rcases Finset.mem_union.mp hq with hq | hq
    · exact hP.noncrossing p hp q hq
    · have h := hcross p hp q hq
      unfold apart at h
      omega
    · have h := hcross q hq p hp
      unfold apart at h
      omega
    · exact hQ.noncrossing p hp q hq

private theorem out_structure_insert {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {P : Finset (ℕ × ℕ)} (hs : IsStructure pair m s P)
    {i j : ℕ} (hij : i + m < j) (hc : CanPair pair s i j)
    (hcross : ∀ p ∈ P, apart (i, j) p) : IsStructure pair m s (insert (i, j) P) := by
  have hsingle : IsStructure pair m s {(i, j)} := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Finset.mem_singleton] using fun p (hp : p = (i, j)) => hp ▸ hij
    · simpa only [Finset.mem_singleton] using fun p (hp : p = (i, j)) => hp ▸ hc
    · intro p hp q hq hne
      simp only [Finset.mem_singleton] at hp hq
      exact (hne (hp.trans hq.symm)).elim
    · intro p hp q hq
      simp only [Finset.mem_singleton] at hp hq
      subst p
      subst q
      omega
  simpa using out_structure_union hsingle hs (by
    intro p hp q hq
    simp only [Finset.mem_singleton] at hp
    subst p
    exact hcross q hq)

private def ext (i j : ℕ) (p : ℕ × ℕ) : Prop :=
  p.2 < i ∨ j < p.1 ∨ (p.1 < i ∧ j < p.2)

open Classical in
private noncomputable def exteriors {B : Type*} (pair : B → B → Prop) (m : ℕ)
    (s : List B) (i j : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (structures pair m s).filter fun Q => ∀ p ∈ Q, ext i j p

private theorem mem_exteriors {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} {Q : Finset (ℕ × ℕ)} :
    Q ∈ exteriors pair m s i j ↔ IsStructure pair m s Q ∧ ∀ p ∈ Q, ext i j p := by
  classical
  simp only [exteriors, Finset.mem_filter, mem_structures]

private theorem weight_union {R : Type*} [CommMonoid R] (w : ℕ → ℕ → R)
    {P Q : Finset (ℕ × ℕ)} (hd : Disjoint P Q) :
    weight w (P ∪ Q) = weight w P * weight w Q := by
  exact Finset.prod_union hd

private theorem weight_insert {R : Type*} [CommMonoid R] (w : ℕ → ℕ → R)
    {P : Finset (ℕ × ℕ)} {i j : ℕ} (hn : (i, j) ∉ P) :
    weight w (insert (i, j) P) = w i j * weight w P := by
  exact Finset.prod_insert hn

private def enclosed (i j : ℕ) (p : ℕ × ℕ) : Prop := i < p.1 ∧ p.2 < j

private theorem mem_segment {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {a b : ℕ} {P : Finset (ℕ × ℕ)} (hab : a ≤ b) :
    P ∈ structuresIn pair m s a (b - a) ↔
      IsStructure pair m s P ∧ ∀ p ∈ P, a ≤ p.1 ∧ p.2 < b := by
  rw [out_mem_interval]
  constructor
  · rintro ⟨hs, h⟩
    exact ⟨hs, fun p hp => by have := h p hp; omega⟩
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun p hp => ?_⟩
    have := h p hp
    have := hs.loop p hp
    omega

private theorem attach_mem {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} (hij : i + m < j) (hc : CanPair pair s i j)
    {Q I : Finset (ℕ × ℕ)} (hQ : Q ∈ exteriors pair m s i j)
    (hI : I ∈ structuresIn pair m s (i + 1) (j - (i + 1))) :
    insert (i, j) (Q ∪ I) ∈ (structures pair m s).filter fun P => (i, j) ∈ P := by
  classical
  obtain ⟨hsQ, heQ⟩ := mem_exteriors.mp hQ
  obtain ⟨hsI, heI⟩ := (mem_segment (by omega)).mp hI
  refine Finset.mem_filter.mpr ⟨(mem_structures _ _ _ _).mpr ?_, Finset.mem_insert_self _ _⟩
  apply out_structure_insert (out_structure_union hsQ hsI ?_) hij hc
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have := heQ p hp
      unfold ext at this
      unfold apart
      omega
    · have := heI p hp
      exact Or.inr (Or.inr (Or.inl ⟨by omega, this.2⟩))
  · intro p hp q hq
    have := heQ p hp
    have := heI q hq
    have := hsQ.loop p hp
    have := hsI.loop q hq
    unfold ext at *
    unfold apart
    omega

open Classical in
private theorem attach_inverse {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} (hij : i + m < j)
    {Q I : Finset (ℕ × ℕ)} (hQ : Q ∈ exteriors pair m s i j)
    (hI : I ∈ structuresIn pair m s (i + 1) (j - (i + 1))) :
    ((insert (i, j) (Q ∪ I)).filter (ext i j),
      (insert (i, j) (Q ∪ I)).filter (enclosed i j)) = (Q, I) := by
  classical
  obtain ⟨hsQ, heQ⟩ := mem_exteriors.mp hQ
  obtain ⟨hsI, heI⟩ := (mem_segment (by omega)).mp hI
  apply Prod.ext <;> apply Finset.ext <;> intro p <;>
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
  · constructor
    · rintro ⟨hp | hp, he⟩
      · subst p; unfold ext at he; omega
      · rcases hp with hp | hp
        · exact hp
        · have := heI p hp
          have := hsI.loop p hp
          unfold ext at he
          omega
    · intro hp
      exact ⟨Or.inr (Or.inl hp), heQ p hp⟩
  · constructor
    · rintro ⟨hp | hp, he⟩
      · subst p; unfold enclosed at he; omega
      · rcases hp with hp | hp
        · have hreg := heQ p hp
          have hloop := hsQ.loop p hp
          unfold ext at hreg
          unfold enclosed at he
          omega
        · exact hp
    · intro hp
      have := heI p hp
      exact ⟨Or.inr (Or.inr hp), by unfold enclosed; omega⟩

open Classical in
private theorem detach_mem {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} (hij : i + m < j) {P : Finset (ℕ × ℕ)}
    (hs : IsStructure pair m s P) (_hp : (i, j) ∈ P) :
    P.filter (ext i j) ∈ exteriors pair m s i j ∧
      P.filter (enclosed i j) ∈ structuresIn pair m s (i + 1) (j - (i + 1)) := by
  classical
  constructor
  · exact mem_exteriors.mpr ⟨out_structure_subset hs (Finset.filter_subset _ _),
      fun p hp => (Finset.mem_filter.mp hp).2⟩
  · apply (mem_segment (by omega)).mpr
    refine ⟨out_structure_subset hs (Finset.filter_subset _ _), ?_⟩
    intro p hp
    have := (Finset.mem_filter.mp hp).2
    unfold enclosed at this
    omega

open Classical in
private theorem detach_inverse {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} {P : Finset (ℕ × ℕ)}
    (hs : IsStructure pair m s P) (hp : (i, j) ∈ P) :
    insert (i, j) (P.filter (ext i j) ∪ P.filter (enclosed i j)) = P := by
  classical
  apply Finset.ext
  intro p
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (rfl | h | h)
    · exact hp
    · exact h.1
    · exact h.1
  · intro h
    by_cases he : p = (i, j)
    · exact Or.inl he
    · have := structure_apart hs h hp he
      unfold apart ext enclosed at *
      tauto

private theorem attach_weight {B R : Type*} [CommSemiring R] {pair : B → B → Prop}
    {m : ℕ} {s : List B} (w : ℕ → ℕ → R) {i j : ℕ} (hij : i + m < j)
    {Q I : Finset (ℕ × ℕ)} (hQ : Q ∈ exteriors pair m s i j)
    (hI : I ∈ structuresIn pair m s (i + 1) (j - (i + 1))) :
    weight w (insert (i, j) (Q ∪ I)) = w i j * (weight w Q * weight w I) := by
  obtain ⟨hsQ, heQ⟩ := mem_exteriors.mp hQ
  obtain ⟨hsI, heI⟩ := (mem_segment (by omega)).mp hI
  have hd : Disjoint Q I := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have := heQ p hp
    have := heI p hq
    have := hsI.loop p hq
    unfold ext at *
    omega
  have hn : (i, j) ∉ Q ∪ I := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have := heQ (i, j) h
      unfold ext at this
      omega
    · have := heI (i, j) h
      omega
  rw [weight_insert w hn, weight_union w hd]

private theorem containing_sum {B R : Type*} [CommSemiring R] {pair : B → B → Prop}
    [DecidableRel pair] {m : ℕ} {s : List B} (w : ℕ → ℕ → R) {i j : ℕ}
    (hij : i + m < j) (hc : CanPair pair s i j) :
    (∑ P ∈ structures pair m s with (i, j) ∈ P, weight w P) =
      w i j * (∑ Q ∈ exteriors pair m s i j, weight w Q) *
        inside pair m s w (i + 1) (j - (i + 1)) := by
  classical
  rw [inside_eq_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product _ _
    (fun t : Finset (ℕ × ℕ) × Finset (ℕ × ℕ) =>
      w i j * weight w t.1 * weight w t.2)]
  symm
  apply Finset.sum_nbij'
    (fun t => insert (i, j) (t.1 ∪ t.2))
    (fun P => (P.filter (ext i j), P.filter (enclosed i j)))
  · intro t ht
    obtain ⟨hQ, hI⟩ := Finset.mem_product.mp ht
    exact attach_mem hij hc hQ hI
  · intro P hP
    obtain ⟨hs, hp⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_product.mpr (detach_mem hij (mem_structures _ _ _ _ |>.mp hs) hp)
  · intro t ht
    obtain ⟨hQ, hI⟩ := Finset.mem_product.mp ht
    exact attach_inverse hij hQ hI
  · intro P hP
    obtain ⟨hs, hp⟩ := Finset.mem_filter.mp hP
    exact detach_inverse (mem_structures _ _ _ _ |>.mp hs) hp
  · intro t ht
    obtain ⟨hQ, hI⟩ := Finset.mem_product.mp ht
    rw [attach_weight w hij hQ hI]
    ac_rfl

private def encloses (i j : ℕ) (p : ℕ × ℕ) : Prop := p.1 < i ∧ j < p.2

open Classical in
private noncomputable def ground {B : Type*} (pair : B → B → Prop) (m : ℕ)
    (s : List B) (i j : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (exteriors pair m s i j).filter fun Q => ∀ p ∈ Q, ¬encloses i j p

private theorem mem_ground {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} {Q : Finset (ℕ × ℕ)} (hij : i < j) :
    Q ∈ ground pair m s i j ↔
      IsStructure pair m s Q ∧ ∀ p ∈ Q, p.2 < i ∨ j < p.1 := by
  classical
  simp only [ground, Finset.mem_filter, mem_exteriors]
  constructor
  · rintro ⟨⟨hs, he⟩, hn⟩
    refine ⟨hs, fun p hp => ?_⟩
    have h1 := he p hp
    have h2 := hn p hp
    unfold ext encloses at *
    tauto
  · rintro ⟨hs, he⟩
    refine ⟨⟨hs, fun p hp => ?_⟩, fun p hp => ?_⟩
    · have := he p hp
      unfold ext
      tauto
    · have h1 := he p hp
      have h2 := hs.loop p hp
      unfold encloses
      omega

private theorem ground_join {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} (hij : i < j) (hjn : j < s.length)
    {L U : Finset (ℕ × ℕ)} (hL : L ∈ structuresIn pair m s 0 i)
    (hU : U ∈ structuresIn pair m s (j + 1) (s.length - (j + 1))) :
    L ∪ U ∈ ground pair m s i j := by
  obtain ⟨hsL, heL⟩ := (mem_segment (Nat.zero_le i)).mp (by simpa using hL)
  obtain ⟨hsU, heU⟩ := (mem_segment (by omega)).mp hU
  apply (mem_ground hij).mpr
  refine ⟨out_structure_union hsL hsU ?_, ?_⟩
  · intro p hp q hq
    have h1 := heL p hp
    have h2 := heU q hq
    exact Or.inl (by omega)
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Or.inl (heL p hp).2
    · exact Or.inr (by have := heU p hp; omega)

open Classical in
private theorem ground_split {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} (hij : i < j) (hjn : j < s.length) {Q : Finset (ℕ × ℕ)}
    (hQ : Q ∈ ground pair m s i j) :
    Q.filter (fun p => p.2 < i) ∈ structuresIn pair m s 0 i ∧
      Q.filter (fun p => j < p.1) ∈
        structuresIn pair m s (j + 1) (s.length - (j + 1)) := by
  obtain ⟨hs, _⟩ := (mem_ground hij).mp hQ
  constructor
  · simpa only [Nat.sub_zero] using (mem_segment (Nat.zero_le i)).mpr
      ⟨out_structure_subset hs (Finset.filter_subset _ _),
        fun p hp => ⟨Nat.zero_le _, (Finset.mem_filter.mp hp).2⟩⟩
  · apply (mem_segment (by omega)).mpr
    refine ⟨out_structure_subset hs (Finset.filter_subset _ _), ?_⟩
    intro p hp
    have h1 := (Finset.mem_filter.mp hp).2
    have h2 := pair_bounds (hs.compl p (Finset.mem_filter.mp hp).1)
    omega

open Classical in
private theorem ground_join_inverse {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} (hij : i < j) (hjn : j < s.length)
    {L U : Finset (ℕ × ℕ)} (hL : L ∈ structuresIn pair m s 0 i)
    (hU : U ∈ structuresIn pair m s (j + 1) (s.length - (j + 1))) :
    ((L ∪ U).filter (fun p => p.2 < i), (L ∪ U).filter (fun p => j < p.1)) =
      (L, U) := by
  obtain ⟨hsL, heL⟩ := (mem_segment (Nat.zero_le i)).mp (by simpa using hL)
  obtain ⟨hsU, heU⟩ := (mem_segment (by omega)).mp hU
  apply Prod.ext <;> apply Finset.ext <;> intro p <;>
    simp only [Finset.mem_filter, Finset.mem_union]
  · constructor
    · rintro ⟨hp | hp, h⟩
      · exact hp
      · have h1 := heU p hp
        have h2 := hsU.loop p hp
        omega
    · intro hp
      exact ⟨Or.inl hp, (heL p hp).2⟩
  · constructor
    · rintro ⟨hp | hp, h⟩
      · have h1 := heL p hp
        have h2 := hsL.loop p hp
        omega
      · exact hp
    · intro hp
      exact ⟨Or.inr hp, by have := heU p hp; omega⟩

open Classical in
private theorem ground_sum {B R : Type*} [CommSemiring R] {pair : B → B → Prop}
    [DecidableRel pair] {m : ℕ} {s : List B} (w : ℕ → ℕ → R) {i j : ℕ}
    (hij : i < j) (hjn : j < s.length) :
    (∑ Q ∈ ground pair m s i j, weight w Q) =
      inside pair m s w 0 i * inside pair m s w (j + 1) (s.length - (j + 1)) := by
  classical
  rw [inside_eq_sum, inside_eq_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_product _ _
    (fun t : Finset (ℕ × ℕ) × Finset (ℕ × ℕ) => weight w t.1 * weight w t.2)]
  symm
  apply Finset.sum_nbij' (fun t => t.1 ∪ t.2)
    (fun Q => (Q.filter (fun p => p.2 < i), Q.filter (fun p => j < p.1)))
  · intro t ht
    obtain ⟨hL, hU⟩ := Finset.mem_product.mp ht
    exact ground_join hij hjn hL hU
  · intro Q hQ
    exact Finset.mem_product.mpr (ground_split hij hjn hQ)
  · intro t ht
    obtain ⟨hL, hU⟩ := Finset.mem_product.mp ht
    exact ground_join_inverse hij hjn hL hU
  · intro Q hQ
    obtain ⟨_, he⟩ := (mem_ground hij).mp hQ
    apply Finset.ext
    intro p
    simp only [Finset.mem_union, Finset.mem_filter]
    exact ⟨fun h => h.elim And.left And.left,
      fun hp => (he p hp).elim (fun h => Or.inl ⟨hp, h⟩) (fun h => Or.inr ⟨hp, h⟩)⟩
  · intro t ht
    obtain ⟨hL, hU⟩ := Finset.mem_product.mp ht
    obtain ⟨hsL, heL⟩ := (mem_segment (Nat.zero_le i)).mp (by simpa using hL)
    obtain ⟨hsU, heU⟩ := (mem_segment (by omega)).mp hU
    symm
    apply weight_union
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h1 := heL p hp
    have h2 := heU p hq
    have h3 := hsL.loop p hp
    omega

private def layer (i j : ℕ) (ab : ℕ × ℕ) (Q : Finset (ℕ × ℕ)) : Prop :=
  ab ∈ Q ∧ encloses i j ab ∧ ∀ p ∈ Q, encloses i j p → p.1 ≤ ab.1

open Classical in
private noncomputable def layers {B : Type*} (pair : B → B → Prop) (m : ℕ)
    (s : List B) (i j : ℕ) (ab : ℕ × ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (exteriors pair m s i j).filter (layer i j ab)

private theorem mem_layers {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} {ab : ℕ × ℕ} {Q : Finset (ℕ × ℕ)} :
    Q ∈ layers pair m s i j ab ↔ Q ∈ exteriors pair m s i j ∧ layer i j ab Q := by
  classical
  exact Finset.mem_filter

private theorem layer_unique {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {i j : ℕ} {P : Finset (ℕ × ℕ)} (hs : IsStructure pair m s P)
    {ab cd : ℕ × ℕ} (hab : layer i j ab P) (hcd : layer i j cd P) : ab = cd := by
  by_contra hne
  have h1 := hs.disjoint ab hab.1 cd hcd.1 hne
  have h2 := hab.2.2 cd hcd.1 hcd.2.1
  have h3 := hcd.2.2 ab hab.1 hab.2.1
  omega

private theorem layer_exists {i j : ℕ} {Q : Finset (ℕ × ℕ)}
    (hn : ∃ p ∈ Q, encloses i j p) : ∃ ab, layer i j ab Q := by
  classical
  have hnon : (Q.filter (encloses i j)).Nonempty := by
    obtain ⟨p, hp, he⟩ := hn
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, he⟩⟩
  obtain ⟨ab, hab, hmax⟩ := Finset.exists_max_image
    (Q.filter (encloses i j)) Prod.fst hnon
  obtain ⟨hmem, hen⟩ := Finset.mem_filter.mp hab
  exact ⟨ab, hmem, hen, fun p hp he => hmax p (Finset.mem_filter.mpr ⟨hp, he⟩)⟩

private theorem nested_inner {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {a b i j : ℕ} (hai : a < i) (hij : i < j) (hjb : j < b)
    {X Y : Finset (ℕ × ℕ)}
    (hX : X ∈ structuresIn pair m s (a + 1) (i - (a + 1)))
    (hY : Y ∈ structuresIn pair m s (j + 1) (b - (j + 1))) :
    X ∪ Y ∈ structuresIn pair m s (a + 1) (b - (a + 1)) := by
  obtain ⟨hsX, heX⟩ := (mem_segment (by omega)).mp hX
  obtain ⟨hsY, heY⟩ := (mem_segment (by omega)).mp hY
  apply (mem_segment (by omega)).mpr
  refine ⟨out_structure_union hsX hsY ?_, ?_⟩
  · intro p hp q hq
    have h1 := heX p hp
    have h2 := heY q hq
    exact Or.inl (by omega)
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have := heX p hp
      omega
    · have := heY p hp
      omega

private theorem nested_join {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {a b i j : ℕ} (hai : a < i) (hij : i < j) (hjb : j < b)
    (hab : a + m < b) (hc : CanPair pair s a b) {Q X Y : Finset (ℕ × ℕ)}
    (hQ : Q ∈ exteriors pair m s a b)
    (hX : X ∈ structuresIn pair m s (a + 1) (i - (a + 1)))
    (hY : Y ∈ structuresIn pair m s (j + 1) (b - (j + 1))) :
    insert (a, b) (Q ∪ (X ∪ Y)) ∈ layers pair m s i j (a, b) := by
  classical
  have hI := nested_inner hai hij hjb hX hY
  have hS := (mem_structures _ _ _ _).mp
    (Finset.mem_filter.mp (attach_mem hab hc hQ hI)).1
  obtain ⟨_, heQ⟩ := mem_exteriors.mp hQ
  obtain ⟨hsX, heX⟩ := (mem_segment (by omega)).mp hX
  obtain ⟨hsY, heY⟩ := (mem_segment (by omega)).mp hY
  apply mem_layers.mpr
  refine ⟨mem_exteriors.mpr ⟨hS, ?_⟩,
    Finset.mem_insert_self _ _, ⟨hai, hjb⟩, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Or.inr (Or.inr ⟨hai, hjb⟩)
    · rcases Finset.mem_union.mp hp with hp | hp
      · have h1 := heQ p hp
        unfold ext at *
        omega
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact Or.inl (heX p hp).2
        · exact Or.inr (Or.inl (by have := heY p hp; omega))
  · intro p hp hen
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact le_rfl
    · rcases Finset.mem_union.mp hp with hp | hp
      · have h1 := heQ p hp
        unfold ext at h1
        unfold encloses at hen
        omega
      · rcases Finset.mem_union.mp hp with hp | hp
        · have h1 := heX p hp
          unfold encloses at hen
          omega
        · have h1 := heY p hp
          unfold encloses at hen
          omega

open Classical in
private noncomputable def nested_split (a b i j : ℕ) (P : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) × (Finset (ℕ × ℕ) × Finset (ℕ × ℕ)) :=
  (P.filter (ext a b),
    ((P.filter (enclosed a b)).filter (fun p => p.2 < i),
      (P.filter (enclosed a b)).filter (fun p => j < p.1)))

private theorem nested_split_mem {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {a b i j : ℕ} (hai : a < i) (_hij : i < j) (hjb : j < b)
    {P : Finset (ℕ × ℕ)} (hP : P ∈ layers pair m s i j (a, b)) :
    (nested_split a b i j P).1 ∈ exteriors pair m s a b ∧
      (nested_split a b i j P).2.1 ∈ structuresIn pair m s (a + 1) (i - (a + 1)) ∧
      (nested_split a b i j P).2.2 ∈ structuresIn pair m s (j + 1) (b - (j + 1)) := by
  classical
  obtain ⟨hE, hmem, _⟩ := mem_layers.mp hP
  obtain ⟨hs, _⟩ := mem_exteriors.mp hE
  have hab := hs.loop (a, b) hmem
  have hd := detach_mem hab hs hmem
  refine ⟨hd.1, ?_, ?_⟩
  · apply (mem_segment (by omega)).mpr
    refine ⟨out_structure_subset hs ?_, ?_⟩
    · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    · intro p hp
      simp only [nested_split, Finset.mem_filter] at hp
      unfold enclosed at hp
      omega
  · apply (mem_segment (by omega)).mpr
    refine ⟨out_structure_subset hs ?_, ?_⟩
    · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    · intro p hp
      simp only [nested_split, Finset.mem_filter] at hp
      unfold enclosed at hp
      omega

open Classical in
private theorem nested_split_inverse {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {a b i j : ℕ} (_hai : a < i) (_hij : i < j) (_hjb : j < b)
    {P : Finset (ℕ × ℕ)} (hP : P ∈ layers pair m s i j (a, b)) :
    insert (a, b) ((nested_split a b i j P).1 ∪
      ((nested_split a b i j P).2.1 ∪ (nested_split a b i j P).2.2)) = P := by
  obtain ⟨hE, hmem, _, hmax⟩ := mem_layers.mp hP
  obtain ⟨hs, he⟩ := mem_exteriors.mp hE
  have hparts : (P.filter (enclosed a b)).filter (fun p => p.2 < i) ∪
      (P.filter (enclosed a b)).filter (fun p => j < p.1) = P.filter (enclosed a b) := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨hp, hinside⟩
      have h1 := he p hp
      have h2 := hmax p hp
      unfold ext at h1
      unfold encloses at h2
      unfold enclosed at hinside
      have hside : p.2 < i ∨ j < p.1 := by omega
      exact hside.elim (fun h => Or.inl ⟨⟨hp, hinside⟩, h⟩)
        (fun h => Or.inr ⟨⟨hp, hinside⟩, h⟩)
  simpa only [nested_split, hparts] using detach_inverse hs hmem

open Classical in
private theorem nested_join_inverse {B : Type*} {pair : B → B → Prop} {m : ℕ}
    {s : List B} {a b i j : ℕ} (hai : a < i) (hij : i < j) (hjb : j < b)
    (hab : a + m < b) {Q X Y : Finset (ℕ × ℕ)}
    (hQ : Q ∈ exteriors pair m s a b)
    (hX : X ∈ structuresIn pair m s (a + 1) (i - (a + 1)))
    (hY : Y ∈ structuresIn pair m s (j + 1) (b - (j + 1))) :
    nested_split a b i j (insert (a, b) (Q ∪ (X ∪ Y))) = (Q, (X, Y)) := by
  have ha := attach_inverse hab hQ (nested_inner hai hij hjb hX hY)
  have hext := congrArg Prod.fst ha
  have hinside := congrArg Prod.snd ha
  change (insert (a, b) (Q ∪ (X ∪ Y))).filter (ext a b) = Q at hext
  change (insert (a, b) (Q ∪ (X ∪ Y))).filter (enclosed a b) = X ∪ Y at hinside
  unfold nested_split
  rw [hext, hinside]
  obtain ⟨hsX, heX⟩ := (mem_segment (by omega)).mp hX
  obtain ⟨hsY, heY⟩ := (mem_segment (by omega)).mp hY
  congr 1
  apply Prod.ext <;> apply Finset.ext <;> intro p <;>
    simp only [Finset.mem_filter, Finset.mem_union]
  · constructor
    · rintro ⟨hp | hp, h⟩
      · exact hp
      · have h1 := heY p hp
        have h2 := hsY.loop p hp
        omega
    · intro hp
      exact ⟨Or.inl hp, (heX p hp).2⟩
  · constructor
    · rintro ⟨hp | hp, h⟩
      · have h1 := heX p hp
        have h2 := hsX.loop p hp
        omega
      · exact hp
    · intro hp
      exact ⟨Or.inr hp, by have := heY p hp; omega⟩

private theorem nested_weight {B R : Type*} [CommSemiring R] {pair : B → B → Prop}
    {m : ℕ} {s : List B} (w : ℕ → ℕ → R) {a b i j : ℕ}
    (hai : a < i) (hij : i < j) (hjb : j < b) (hab : a + m < b)
    {Q X Y : Finset (ℕ × ℕ)} (hQ : Q ∈ exteriors pair m s a b)
    (hX : X ∈ structuresIn pair m s (a + 1) (i - (a + 1)))
    (hY : Y ∈ structuresIn pair m s (j + 1) (b - (j + 1))) :
    weight w (insert (a, b) (Q ∪ (X ∪ Y))) =
      weight w Q * w a b * weight w X * weight w Y := by
  rw [attach_weight w hab hQ (nested_inner hai hij hjb hX hY)]
  have hd : Disjoint X Y := by
    obtain ⟨hsX, heX⟩ := (mem_segment (by omega)).mp hX
    obtain ⟨hsY, heY⟩ := (mem_segment (by omega)).mp hY
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h1 := heX p hp
    have h2 := heY p hq
    have h3 := hsX.loop p hp
    omega
  rw [weight_union w hd]
  ac_rfl

open Classical in
private theorem layer_sum {B R : Type*} [CommSemiring R] {pair : B → B → Prop}
    [DecidableRel pair] {m : ℕ} {s : List B} (w : ℕ → ℕ → R) {a b i j : ℕ}
    (hai : a < i) (hij : i < j) (hjb : j < b) (hab : a + m < b)
    (hc : CanPair pair s a b) :
    (∑ P ∈ layers pair m s i j (a, b), weight w P) =
      (∑ Q ∈ exteriors pair m s a b, weight w Q) * w a b *
        inside pair m s w (a + 1) (i - (a + 1)) * inside pair m s w (j + 1) (b - (j + 1)) := by
  let domain := exteriors pair m s a b ×ˢ
    (structuresIn pair m s (a + 1) (i - (a + 1)) ×ˢ
      structuresIn pair m s (j + 1) (b - (j + 1)))
  have hbij : (∑ t ∈ domain, weight w (insert (a, b) (t.1 ∪ (t.2.1 ∪ t.2.2)))) =
      ∑ P ∈ layers pair m s i j (a, b), weight w P := by
    apply Finset.sum_nbij' (fun t => insert (a, b) (t.1 ∪ (t.2.1 ∪ t.2.2)))
      (nested_split a b i j)
    · intro t ht
      obtain ⟨hQ, hX, hY⟩ := (Finset.mem_product.mp ht).imp_right Finset.mem_product.mp
      exact nested_join hai hij hjb hab hc hQ hX hY
    · intro P hP
      obtain ⟨hQ, hX, hY⟩ := nested_split_mem hai hij hjb hP
      exact Finset.mem_product.mpr ⟨hQ, Finset.mem_product.mpr ⟨hX, hY⟩⟩
    · intro t ht
      obtain ⟨hQ, hX, hY⟩ := (Finset.mem_product.mp ht).imp_right Finset.mem_product.mp
      exact nested_join_inverse hai hij hjb hab hQ hX hY
    · intro P hP
      exact nested_split_inverse hai hij hjb hP
    · intro t ht
      rfl
  rw [← hbij]
  change (∑ t ∈ exteriors pair m s a b ×ˢ
    (structuresIn pair m s (a + 1) (i - (a + 1)) ×ˢ
      structuresIn pair m s (j + 1) (b - (j + 1))), _) = _
  rw [Finset.sum_product]
  have heq : (∑ Q ∈ exteriors pair m s a b,
      ∑ t ∈ structuresIn pair m s (a + 1) (i - (a + 1)) ×ˢ
        structuresIn pair m s (j + 1) (b - (j + 1)),
          weight w (insert (a, b) (Q ∪ (t.1 ∪ t.2)))) =
      ∑ Q ∈ exteriors pair m s a b,
        ∑ X ∈ structuresIn pair m s (a + 1) (i - (a + 1)),
          ∑ Y ∈ structuresIn pair m s (j + 1) (b - (j + 1)),
            weight w Q * w a b * weight w X * weight w Y := by
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro X hX
    apply Finset.sum_congr rfl
    intro Y hY
    exact nested_weight w hai hij hjb hab hQ hX hY
  rw [heq, inside_eq_sum, inside_eq_sum]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

open Classical in
private theorem exterior_partition {B R : Type*} [CommSemiring R]
    {pair : B → B → Prop} {m : ℕ} {s : List B} (w : ℕ → ℕ → R) {i j : ℕ} :
    (∑ Q ∈ exteriors pair m s i j, weight w Q) =
      (∑ Q ∈ ground pair m s i j, weight w Q) +
        ∑ ab ∈ Finset.Ico 0 i ×ˢ Finset.Ico (j + 1) s.length,
          ∑ Q ∈ layers pair m s i j ab, weight w Q := by
  let idx := Finset.Ico 0 i ×ˢ Finset.Ico (j + 1) s.length
  let bad := (exteriors pair m s i j).filter fun Q => ¬∀ p ∈ Q, ¬encloses i j p
  have hbij : (∑ t ∈ idx.sigma (layers pair m s i j), weight w t.2) =
      ∑ Q ∈ bad, weight w Q := by
    apply Finset.sum_bij (fun t _ => t.2)
    · intro t ht
      obtain ⟨_, hL⟩ := Finset.mem_sigma.mp ht
      obtain ⟨hE, hmem, hen, _⟩ := mem_layers.mp hL
      exact Finset.mem_filter.mpr ⟨hE, fun hn => hn t.1 hmem hen⟩
    · intro t ht u hu heq
      obtain ⟨_, htL⟩ := Finset.mem_sigma.mp ht
      obtain ⟨_, huL⟩ := Finset.mem_sigma.mp hu
      obtain ⟨htE, htLayer⟩ := mem_layers.mp htL
      obtain ⟨huE, huLayer⟩ := mem_layers.mp huL
      have hab : t.1 = u.1 := layer_unique (mem_exteriors.mp htE).1 htLayer (heq ▸ huLayer)
      cases t with
      | mk ab P =>
        cases u with
        | mk cd Q =>
          simp only at hab heq
          subst cd
          subst Q
          rfl
    · intro Q hQ
      obtain ⟨hE, hn⟩ := Finset.mem_filter.mp hQ
      push Not at hn
      obtain ⟨ab, hLayer⟩ := layer_exists hn
      obtain ⟨hs, _⟩ := mem_exteriors.mp hE
      have hb := pair_bounds (hs.compl ab hLayer.1)
      have hen := hLayer.2.1
      unfold encloses at hen
      have hidx : ab ∈ idx := by
        simp only [idx, Finset.mem_product, Finset.mem_Ico]
        exact ⟨⟨Nat.zero_le _, hen.1⟩, ⟨by omega, hb.2⟩⟩
      exact ⟨⟨ab, Q⟩, Finset.mem_sigma.mpr ⟨hidx, mem_layers.mpr ⟨hE, hLayer⟩⟩, rfl⟩
    · intro t ht
      rfl
  rw [Finset.sum_sigma', hbij]
  exact (Finset.sum_filter_add_sum_filter_not
    (exteriors pair m s i j) (fun Q => ∀ p ∈ Q, ¬encloses i j p) (weight w)).symm

open Classical in
private theorem layer_sum_conditional {B R : Type*} [CommSemiring R]
    {pair : B → B → Prop} [DecidableRel pair] {m : ℕ} {s : List B}
    (w : ℕ → ℕ → R) {a b i j : ℕ} (hai : a < i) (hij : i < j) (hjb : j < b) :
    (∑ P ∈ layers pair m s i j (a, b), weight w P) =
      if a + m < b ∧ CanPair pair s a b then
        (∑ Q ∈ exteriors pair m s a b, weight w Q) * w a b *
          inside pair m s w (a + 1) (i - (a + 1)) *
            inside pair m s w (j + 1) (b - (j + 1))
      else 0 := by
  split_ifs with h
  · exact layer_sum w hai hij hjb h.1 h.2
  · apply Finset.sum_eq_zero
    intro P hP
    obtain ⟨hE, hmem, _⟩ := mem_layers.mp hP
    have hs := (mem_exteriors.mp hE).1
    exact (h ⟨hs.loop (a, b) hmem, hs.compl (a, b) hmem⟩).elim

private theorem outside_eq_exteriors {B R : Type*} [CommSemiring R]
    {pair : B → B → Prop} [DecidableRel pair] {m : ℕ} {s : List B}
    (w : ℕ → ℕ → R) (i j : ℕ) (hij : i + m < j) (hc : CanPair pair s i j) :
    outside pair m s w i j = ∑ Q ∈ exteriors pair m s i j, weight w Q := by
  classical
  generalize hmeasure : s.length - (j - i) = d
  induction d using Nat.strong_induction_on generalizing i j with
  | h d ih =>
    have hjn := (pair_bounds hc).2
    rw [outside, exterior_partition, ground_sum w (by omega) hjn]
    congr 1
    rw [Finset.sum_product]
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.sub_zero, Nat.zero_add]
    simp_rw [Finset.sum_Ico_eq_sum_range]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro c _
    rw [layer_sum_conditional w a.isLt (by omega) (by omega)]
    split_ifs with h
    · have hlt : s.length - (j + 1 + c.val - a.val) < d := by
        have := a.isLt
        have := c.isLt
        omega
      rw [ih _ hlt a.val (j + 1 + c.val) h.1 h.2 rfl]
      congr 2
      omega
    · rfl

/-- **Outside algorithm** (McCaskill 1990): for a candidate pair `(i, j)` (`i + m < j` and
`CanPair pair s i j`), the outside value times the pair's weight times the inside value of the
enclosed interval `[i + 1, j)` sums the weights of all secondary structures containing
`(i, j)`. -/
theorem outside_mul_eq_sum [DecidableRel pair] {R : Type*} [CommSemiring R]
    (w : ℕ → ℕ → R) (i j : ℕ) (hij : i + m < j) (hc : CanPair pair s i j) :
    outside pair m s w i j * w i j * inside pair m s w (i + 1) (j - (i + 1)) =
      ∑ P ∈ structures pair m s with (i, j) ∈ P, weight w P := by
  rw [outside_eq_exteriors w i j hij hc, containing_sum w hij hc]
  ac_rfl

/-! ### Min-plus: the Nussinov maximum -/

/-- **Tropical semiring**: with every base pair weighted `-1` in the min-plus semiring
`MinTropical (WithTop ℤ)` (addition `min`, multiplication `+`), a structure with `k` pairs has
weight `-k`, so the inside value of the whole sequence is minus the Nussinov maximum number of
base pairs. -/
theorem inside_minTropical [DecidableRel pair] :
    inside pair m s (fun _ _ => MinTropical.trop ((-1 : ℤ) : WithTop ℤ)) 0 s.length =
      MinTropical.trop ((-(nussinov pair m s : ℤ) : ℤ) : WithTop ℤ) := by
  rw [inside_eq_sum_structures]
  apply MinTropical.untrop_injective
  rw [MinTropical.Finset.untrop_sum', MinTropical.untrop_trop]
  have hw (P : Finset (ℕ × ℕ)) :
      MinTropical.untrop (weight (fun _ _ => MinTropical.trop ((-1 : ℤ) : WithTop ℤ)) P) =
        ((-(P.card : ℤ) : ℤ) : WithTop ℤ) := by
    rw [weight, MinTropical.untrop_prod]
    simp only [MinTropical.untrop_trop, Finset.sum_const]
    norm_cast
    simp
  simp only [Function.comp_def, hw]
  apply le_antisymm
  · obtain ⟨P, hP, hc⟩ := exists_isStructure_card_eq pair m s
    calc (structures pair m s).inf (fun P => ((-(P.card : ℤ) : ℤ) : WithTop ℤ))
        ≤ ((-(P.card : ℤ) : ℤ) : WithTop ℤ) :=
          Finset.inf_le ((mem_structures pair m s P).mpr hP)
      _ = _ := by rw [hc]
  · apply Finset.le_inf
    intro P hP
    have := card_le_nussinov pair m s P ((mem_structures pair m s P).mp hP)
    exact WithTop.coe_le_coe.mpr (by omega)

/-! ### Counting: Waterman, Motzkin, Stein–Waterman -/

/-- **Waterman's recursion** for the number `S_m(n)` of secondary structures on `n` points
with minimum hairpin `m` when every pair is allowed: `S(0) = 1` and
`S(n + 1) = S(n) + ∑_{m ≤ k < n} S(k) S(n - 1 - k)` (Waterman 1978; Stein–Waterman 1979).
For `m = 0` these are the Motzkin numbers (`watermanNumber_zero_eq_motzkinNumber`); for `m = 1`
the Stein–Waterman numbers `1, 1, 1, 2, 4, 8, 17, 37, …` (OEIS A004148), whose closed form is not
formalized here. -/
def watermanNumber (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      watermanNumber m n +
        ∑ k : Fin n, if m ≤ k.val then
          watermanNumber m k.val * watermanNumber m (n - 1 - k.val) else 0
  termination_by n => n
  decreasing_by all_goals omega

/-- **Counting semiring**: the number of secondary structures on `n` points with minimum
hairpin `m`, when every pair of positions may pair, is Waterman's number `S_m(n)`. -/
theorem card_structures_eq_watermanNumber (m n : ℕ) :
    (structures (fun _ _ : Unit => True) m (List.replicate n ())).card =
      watermanNumber m n := by
  have hcard : (structures (fun _ _ : Unit => True) m (List.replicate n ())).card =
      inside (fun _ _ : Unit => True) m (List.replicate n ()) (fun _ _ => (1 : ℕ)) 0
        (List.replicate n ()).length := by
    rw [inside_eq_sum_structures, Finset.card_eq_sum_ones]
    simp [weight]
  have key : ∀ len i, i + len ≤ n →
      inside (fun _ _ : Unit => True) m (List.replicate n ()) (fun _ _ => (1 : ℕ)) i len =
        watermanNumber m len := by
    intro len
    induction len using Nat.strong_induction_on with
    | h len ih =>
      intro i hi
      cases len with
      | zero => simp [inside, watermanNumber]
      | succ len =>
        rw [inside, watermanNumber, ih len (by omega) (i + 1) (by omega)]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk := k.isLt
        have hc : CanPair (fun _ _ : Unit => True) (List.replicate n ()) i (i + 1 + k.val) := by
          refine ⟨(), (), ?_, ?_, trivial⟩ <;> rw [List.getElem?_replicate, ite_eq_left (by omega)]
        simp only [hc, and_true, one_mul]
        split_ifs
        · rw [ih k.val (by omega) (i + 1) (by omega),
            ih (len - 1 - k.val) (by omega) (i + k.val + 2) (by omega)]
        · rfl
  rw [hcard, key _ 0 (by simp)]
  simp

section Motzkin

open Finset MetaMathlibExt

private theorem choose_sum (n q : ℕ) :
    (∑ a ∈ range (n + 1), a.choose q) = (n + 1).choose (q + 1) := by
  induction n with
  | zero =>
    cases q with
    | zero => simp
    | succ q => simp [Nat.choose_eq_zero_of_lt (by omega : 1 < q + 1 + 1)]
  | succ n ih =>
    rw [sum_range_succ, ih]
    cases q with
    | zero => simp
    | succ q =>
      rw [Nat.choose_succ_succ (n + 1) (q + 1)]
      exact Nat.add_comm _ _

private theorem choose_convolution (n p q : ℕ) :
    (∑ ab ∈ antidiagonal n, ab.1.choose p * ab.2.choose q) =
      (n + 1).choose (p + q + 1) := by
  induction n generalizing p q with
  | zero =>
    cases p <;> cases q <;> simp [Nat.choose_succ_succ, Nat.choose_zero_succ, ← Nat.add_assoc]
  | succ n ih =>
    cases p with
    | zero =>
      simp only [Nat.choose_zero_right, one_mul, zero_add]
      rw [← Nat.sum_antidiagonal_swap]
      simp only [Prod.snd_swap]
      rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ => a.choose q)]
      exact choose_sum (n + 1) q
    | succ p =>
      rw [Nat.sum_antidiagonal_succ]
      simp only [Nat.choose_zero_succ, zero_mul, zero_add]
      conv_lhs => simp only [Nat.choose_succ_succ, add_mul]
      rw [sum_add_distrib, ih, ih]
      simpa only [Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using
        (Nat.choose_succ_succ (n + 1) (p + q + 1)).symm

private theorem motzkinNumber_eq_sum (n r : ℕ) (h : n < r) :
    motzkinNumber n = ∑ k ∈ range r, n.choose (2 * k) * catalan k := by
  unfold motzkinNumber
  apply sum_subset (range_mono (by omega))
  intro k hk hkn
  rw [Nat.choose_eq_zero_of_lt, zero_mul]
  simp only [mem_range] at hk hkn
  omega

private theorem sum_diagonals (r : ℕ) (f : ℕ → ℕ → ℕ)
    (h : ∀ i j, r ≤ i + j → f i j = 0) :
    (∑ i ∈ range r, ∑ j ∈ range r, f i j) =
      ∑ k ∈ range r, ∑ ij ∈ antidiagonal k, f ij.1 ij.2 := by
  rw [← sum_product' (range r) (range r) f]
  have hf : ∀ k ∈ range r,
      ((range r ×ˢ range r).filter (fun ij => ij.1 + ij.2 = k)) = antidiagonal k := by
    intro k hk
    ext ij
    simp only [mem_filter, mem_product, mem_range, mem_antidiagonal] at *
    omega
  calc
    _ = ∑ ij ∈ (range r ×ˢ range r).filter (fun ij => ij.1 + ij.2 ∈ range r),
        f ij.1 ij.2 := by
      symm
      apply sum_subset (filter_subset _ _)
      intro ij hij hn
      apply h
      simp only [mem_filter, hij, true_and, mem_range] at hn
      omega
    _ = ∑ k ∈ range r,
        ∑ ij ∈ (range r ×ˢ range r).filter (fun ij => ij.1 + ij.2 = k),
          f ij.1 ij.2 := (sum_fiberwise_eq_sum_filter _ _ _ _).symm
    _ = _ := sum_congr rfl fun k hk => by rw [hf k hk]

private theorem motzkinNumber_convolution (n : ℕ) :
    (∑ ab ∈ antidiagonal n, motzkinNumber ab.1 * motzkinNumber ab.2) =
      ∑ k ∈ range (n + 1), (n + 1).choose (2 * k + 1) * catalan (k + 1) := by
  calc
    _ = ∑ ab ∈ antidiagonal n, ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
        (ab.1.choose (2 * i) * ab.2.choose (2 * j)) * (catalan i * catalan j) := by
      apply sum_congr rfl
      intro ab hab
      have hab' := mem_antidiagonal.mp hab
      rw [motzkinNumber_eq_sum ab.1 (n + 1) (by omega),
        motzkinNumber_eq_sum ab.2 (n + 1) (by omega), sum_mul_sum]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ac_rfl
    _ = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), ∑ ab ∈ antidiagonal n,
        (ab.1.choose (2 * i) * ab.2.choose (2 * j)) * (catalan i * catalan j) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      rw [sum_comm]
    _ = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
        (n + 1).choose (2 * i + 2 * j + 1) * (catalan i * catalan j) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [← sum_mul, choose_convolution]
    _ = ∑ k ∈ range (n + 1), ∑ ij ∈ antidiagonal k,
        (n + 1).choose (2 * ij.1 + 2 * ij.2 + 1) *
          (catalan ij.1 * catalan ij.2) := by
      apply sum_diagonals
      intro i j hij
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      rw [catalan_succ', mul_sum]
      apply sum_congr rfl
      intro ij hij
      have hij' := mem_antidiagonal.mp hij
      rw [show 2 * ij.1 + 2 * ij.2 + 1 = 2 * k + 1 by omega]

private theorem motzkinNumber_pascal (n : ℕ) :
    motzkinNumber (n + 1) = motzkinNumber n +
      ∑ k ∈ range (n + 1), n.choose (2 * k + 1) * catalan (k + 1) := by
  have hp (k : ℕ) : (n + 1).choose (2 * (k + 1)) =
      n.choose (2 * (k + 1)) + n.choose (2 * k + 1) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.choose_succ_succ']
    exact add_comm _ _
  rw [motzkinNumber_eq_sum (n + 1) (n + 2) (by omega),
    motzkinNumber_eq_sum n (n + 2) (by omega)]
  rw [sum_range_succ' (fun k => (n + 1).choose (2 * k) * catalan k) (n + 1),
    sum_range_succ' (fun k => n.choose (2 * k) * catalan k) (n + 1)]
  simp only [mul_zero, Nat.choose_zero_right, catalan_zero, mul_one]
  simp_rw [hp, add_mul]
  rw [sum_add_distrib]
  omega

private theorem motzkinNumber_succ (n : ℕ) :
    motzkinNumber (n + 1) = motzkinNumber n +
      ∑ k : Fin n, motzkinNumber k.val * motzkinNumber (n - 1 - k.val) := by
  cases n with
  | zero =>
    simp [motzkinNumber, sum_range_succ]
  | succ n =>
    rw [motzkinNumber_pascal, sum_range_succ]
    rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 < 2 * (n + 1) + 1), zero_mul,
      add_zero, ← motzkinNumber_convolution]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => motzkinNumber a * motzkinNumber b),
      sum_range]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]

end Motzkin

/-- For `m = 0` (no hairpin constraint) Waterman's numbers are the Motzkin numbers
`M(n) = ∑_k C(n, 2k) C(k)`: the number of non-crossing partial matchings on `n` points. -/
theorem watermanNumber_zero_eq_motzkinNumber (n : ℕ) :
    watermanNumber 0 n = MetaMathlibExt.motzkinNumber n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [watermanNumber, MetaMathlibExt.motzkinNumber]
    | succ n =>
      rw [watermanNumber, motzkinNumber_succ]
      simp only [Nat.zero_le, ite_true]
      rw [ih n (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := k.isLt
      rw [ih k.val (by omega), ih (n - 1 - k.val) (by omega)]

/-! ### Sum-product: the McCaskill partition function -/

/-- An **additive base-pair energy model**: the free energy of a structure is the sum of the
energies `e i j` of its base pairs (in the same units as `RT`). -/
def energy (e : ℕ → ℕ → ℝ) (P : Finset (ℕ × ℕ)) : ℝ :=
  ∑ p ∈ P, e p.1 p.2

/-- The **partition function** `Z = ∑_S exp (-E(S) / RT)` over all secondary structures `S`
on `s` with minimum hairpin `m`, for the additive energy `e` at thermal energy `RT`
(physically `0 < RT`; the identities below hold for every real `RT`). -/
noncomputable def partitionFunction (e : ℕ → ℕ → ℝ) (RT : ℝ) : ℝ :=
  ∑ P ∈ structures pair m s, Real.exp (-energy e P / RT)

/-- **McCaskill's algorithm** (inside part): over the sum-product semiring `ℝ` with Boltzmann
weights `exp (-e i j / RT)`, the inside value of the whole sequence is the partition function.
This is an algebraic identity valid for every real `RT`. -/
theorem inside_boltzmann_eq_partitionFunction [DecidableRel pair] (e : ℕ → ℕ → ℝ) (RT : ℝ) :
    inside pair m s (fun i j => Real.exp (-e i j / RT)) 0 s.length =
      partitionFunction pair m s e RT := by
  rw [inside_eq_sum_structures, partitionFunction]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [weight, ← Real.exp_sum, energy, ← Finset.sum_neg_distrib, Finset.sum_div]

/-- The **base-pair probability** `P(i, j)`: the total weight of the structures containing the
pair `(i, j)`, divided by the total weight `Z` of all structures. For nonnegative weights `Z ≥ 1`
(the empty structure has weight `1`), so the denominator is positive; for Boltzmann weights this
is the probability of `(i, j)` under the Boltzmann distribution on structures. -/
noncomputable def pairProb (w : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  (∑ P ∈ structures pair m s with (i, j) ∈ P, weight w P) /
    ∑ P ∈ structures pair m s, weight w P

/-- **McCaskill's base-pair probabilities**: for a candidate pair `(i, j)`,
`P(i, j) = outside(i, j) · w(i, j) · inside(i + 1, j) / inside(0, n)`. -/
theorem pairProb_eq_outside [DecidableRel pair] (w : ℕ → ℕ → ℝ) (i j : ℕ) (hij : i + m < j)
    (hc : CanPair pair s i j) :
    pairProb pair m s w i j =
      outside pair m s w i j * w i j * inside pair m s w (i + 1) (j - (i + 1)) /
        inside pair m s w 0 s.length := by
  rw [pairProb, outside_mul_eq_sum pair m s w i j hij hc, inside_eq_sum_structures]

/-- For nonnegative weights the total weight of all structures is at least `1`, the weight of
the empty structure; so the denominator of `pairProb` is positive. -/
theorem one_le_sum_weight (w : ℕ → ℕ → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    1 ≤ ∑ P ∈ structures pair m s, weight w P := by
  have he : (∅ : Finset (ℕ × ℕ)) ∈ structures pair m s :=
    (mem_structures pair m s ∅).mpr ⟨by simp, by simp, by simp, by simp⟩
  calc (1 : ℝ) = weight w ∅ := by simp [weight]
    _ ≤ ∑ P ∈ structures pair m s, weight w P :=
      Finset.single_le_sum (f := weight w)
        (fun P _ => Finset.prod_nonneg fun p _ => hw p.1 p.2) he

/-- Base-pair probabilities are nonnegative for nonnegative weights. -/
theorem pairProb_nonneg (w : ℕ → ℕ → ℝ) (hw : ∀ i j, 0 ≤ w i j) (i j : ℕ) :
    0 ≤ pairProb pair m s w i j := by
  exact div_nonneg (Finset.sum_nonneg fun P _ => Finset.prod_nonneg fun p _ => hw _ _)
    (Finset.sum_nonneg fun P _ => Finset.prod_nonneg fun p _ => hw _ _)

/-- **Each base pairs at most once**: for nonnegative weights, the probabilities that base `i`
pairs with some later base `j` or some earlier base `j` sum to at most `1`
(`∑_j (P(i, j) + P(j, i)) ≤ 1`). -/
theorem sum_pairProb_le_one (w : ℕ → ℕ → ℝ) (hw : ∀ i j, 0 ≤ w i j) (i : ℕ) :
    ∑ j ∈ Finset.range s.length, (pairProb pair m s w i j + pairProb pair m s w j i) ≤ 1 := by
  classical
  set S := structures pair m s
  have hwt (P : Finset (ℕ × ℕ)) : 0 ≤ weight w P := Finset.prod_nonneg fun p _ => hw _ _
  have hZ : 1 ≤ ∑ P ∈ S, weight w P := one_le_sum_weight pair m s w hw
  have hcount (P : Finset (ℕ × ℕ)) (hP : P ∈ S) :
      ∑ j ∈ Finset.range s.length,
        ((if (i, j) ∈ P then weight w P else 0) + if (j, i) ∈ P then weight w P else 0) ≤
        weight w P := by
    have hS := (mem_structures pair m s P).mp hP
    have hsum : ∑ j ∈ Finset.range s.length,
        ((if (i, j) ∈ P then weight w P else 0) + if (j, i) ∈ P then weight w P else 0) =
        ∑ j ∈ Finset.range s.length with ((i, j) ∈ P ∨ (j, i) ∈ P), weight w P := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h1 : (i, j) ∈ P <;> by_cases h2 : (j, i) ∈ P
      · have := hS.loop _ h1
        have := hS.loop _ h2
        simp only at *
        omega
      all_goals simp [h1, h2]
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_of_le_one_left (hwt P) ?_
    have hle : (Finset.filter (fun j => (i, j) ∈ P ∨ (j, i) ∈ P)
        (Finset.range s.length)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      by_contra hab
      rcases ha.2 with ha | ha <;> rcases hb.2 with hb | hb
      · exact (hS.disjoint _ ha _ hb (by simpa using hab)).1 rfl
      · exact (hS.disjoint _ ha _ hb (by
          intro h; simp only [Prod.mk.injEq] at h; omega)).2.1 rfl
      · exact (hS.disjoint _ ha _ hb (by
          intro h; simp only [Prod.mk.injEq] at h; omega)).2.2.1 rfl
      · exact (hS.disjoint _ ha _ hb (by simpa using hab)).2.2.2 rfl
    exact_mod_cast hle
  simp only [pairProb, ← add_div, ← Finset.sum_div]
  rw [div_le_one (by linarith)]
  simp only [Finset.sum_filter]
  simp only [← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum hcount

end Cslib.Bioinformatics.RNA.PartitionFunction
