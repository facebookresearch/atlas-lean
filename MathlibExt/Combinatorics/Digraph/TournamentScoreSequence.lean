/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Tournament score sequences

A tournament on `Fin n` is encoded by `T i j = true` for "`i` beats `j`",
with `score T i` the outdegree of `i`. We prove the results on score
sequences quoted by Harris and McShane:

* `egf_factorial_choose` (Theorem 1): the exponential generating function
  of `n! * C(n - a + b, b)` (`n ≥ a`) is `x^a * (1 - x)^{-(b+1)}`, stated
  in the multiplied-out form `(1 - x)^{b+1} * A(x) = x^a`.
* `landau_score_sequence` (Theorem 4, Landau): a nondecreasing sequence
  is a score sequence exactly when each initial segment of length `k` sums
  to at least `C(k, 2)`, with equality for the whole sequence.
* `isReducible_iff` (Theorem 5, Moon): a tournament with nondecreasing
  scores is reducible exactly when some proper initial segment of length
  `k ≥ 1` sums to exactly `C(k, 2)`.
* `card_circularTriads` (Theorem 6, Moon): a tournament has
  `C(n, 3) - ∑ i, C(s_i, 2)` circular triads.

Landau's theorem is deduced from the unsorted form
`exists_isTournament_score_eq_iff`: `s` is a score sequence exactly when
every set `S` of players has `∑ i ∈ S, s i ≥ C(#S, 2)` and the total is
`C(n, 2)`. Necessity holds because the players of `S` play `C(#S, 2)`
games among themselves (`sum_card_filter_eq_choose`). Sufficiency follows
from Hall's marriage theorem
(`Finset.all_card_le_biUnion_card_iff_exists_injective`): give player `i`
`s i` slots and assign each game to a slot of one of its two players. The
sorted form then follows from `sum_castLE_le_sum_of_monotone`: for
nondecreasing `s`, the first `#S` values sum to at most `∑ i ∈ S, s i`.

For Theorem 6, a `3`-set is not a circular triad exactly when one of its
players beats the other two, and then that player is unique
(`card_filter_card_filter_eq_two`). Each player `i` beats both others in
`C(score T i, 2)` of the `3`-sets (`card_filter_powersetCard_eq_choose`).

## References

* Ian R. Harris and Ryan P. A. McShane, "Counting Tournaments with a
  Specified Number of Circular Triads", *Journal of Integer Sequences* 27
  (2024), Article 24.8.7
  (<https://cs.uwaterloo.ca/journals/JIS/VOL27/McShane/mcshane1.html>).
* H. G. Landau, "On dominance relations and the structure of animal
  societies. III. The condition for a score structure", *Bulletin of
  Mathematical Biophysics* 15 (1953), 143–148.
* J. W. Moon, *Topics on Tournaments*, Holt, Rinehart and Winston, 1968.
-/

@[expose] public section

open Finset

namespace MetaMathlibExt

/-- A strictly monotone map `Fin k → Fin n` sends `j` to an element
whose value is at least `j`. -/
theorem val_le_val_of_strictMono {k n : ℕ} {f : Fin k → Fin n}
    (hf : StrictMono f) (j : Fin k) : (j : ℕ) ≤ f j := by
  obtain ⟨j, hj⟩ := j
  induction j with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 : f ⟨m, by omega⟩ < f ⟨m + 1, hj⟩ :=
      hf (Fin.mk_lt_mk.2 (Nat.lt_succ_self m))
    rw [Fin.lt_def] at h2
    simp only at h1 ⊢
    omega

/-- For a monotone `s : Fin n → M`, the sum of the first `#S` values is
at most the sum of `s` over `S`. -/
theorem sum_castLE_le_sum_of_monotone {n : ℕ} {M : Type*}
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    {s : Fin n → M} (hs : Monotone s) (S : Finset (Fin n))
    (hk : #S ≤ n) :
    ∑ i : Fin #S, s (Fin.castLE hk i) ≤ ∑ i ∈ S, s i := by
  conv_rhs =>
    rw [← image_orderEmbOfFin_univ S rfl,
      sum_image fun x _ y _ h => (S.orderEmbOfFin rfl).injective h]
  exact sum_le_sum fun j _ => hs (Fin.le_iff_val_le_val.2
    (val_le_val_of_strictMono (S.orderEmbOfFin rfl).strictMono j))

end MetaMathlibExt

namespace MathlibExt.GraphTheory.TournamentScoreSequenceWanted

/-- A tournament on `Fin n`: `T i j = true` means `i`
beats `j`; every pair has exactly one winner and there
are no self-wins. -/
def IsTournament {n : ℕ} (T : Fin n → Fin n → Bool) :
    Prop :=
  (∀ i, T i i = false) ∧ ∀ i j, i ≠ j → T i j ≠ T j i

/-- The score (outdegree) of a player in a tournament. -/
def score {n : ℕ} (T : Fin n → Fin n → Bool) (i : Fin n) :
    ℕ :=
  (Finset.univ.filter (fun j => T i j)).card

/-- A tournament is reducible if some nonempty proper
set of players loses all games against the complement. -/
def IsReducible {n : ℕ} (T : Fin n → Fin n → Bool) :
    Prop :=
  ∃ S : Finset (Fin n), S.Nonempty ∧ S ≠ Finset.univ ∧
    ∀ i ∈ S, ∀ j, j ∉ S → T i j = false

/-- A circular triad: a 3-subset in which every vertex
has outdegree exactly `1` (a directed 3-cycle). -/
def IsCircularTriad {n : ℕ} (T : Fin n → Fin n → Bool)
    (S : Finset (Fin n)) : Prop :=
  S.card = 3 ∧
    ∀ i ∈ S, (S.filter (fun j => T i j)).card = 1

instance {n : ℕ} (T : Fin n → Fin n → Bool)
    (S : Finset (Fin n)) :
    Decidable (IsCircularTriad T S) :=
  inferInstanceAs (Decidable (S.card = 3 ∧
    ∀ i ∈ S, (S.filter (fun j => T i j)).card = 1))

open MetaMathlibExt

/-! ### Theorem 1 -/

/-- **Theorem 1**: the sequence `g(n) = n! * C(n-a+b, b)`
(`n ≥ a`) has exponential generating function
`x^a * (1 - x)^{-(b+1)}` (stated in the multiplied-out
form `(1 - x)^{b+1} * A(x) = x^a` over `ℚ`).

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Theorem 1.

Proves `Wanted` entry `egf_factorial_choose`. -/
theorem egf_factorial_choose (a b : ℕ) :
    (1 - PowerSeries.X) ^ (b + 1) *
        PowerSeries.mk (fun n =>
          if a ≤ n then (Nat.choose (n - a + b) b : ℚ)
          else 0)
      = PowerSeries.X ^ a := by
  have h : PowerSeries.mk (fun n =>
      if a ≤ n then (Nat.choose (n - a + b) b : ℚ) else 0) =
      PowerSeries.X ^ a *
        PowerSeries.mk fun n => (Nat.choose (b + n) b : ℚ) := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_mk, Nat.add_comm b]
  rw [h, mul_left_comm,
    mul_comm ((1 - PowerSeries.X : PowerSeries ℚ) ^ (b + 1)),
    PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one, mul_one]

/-! ### Games inside a set of players -/

variable {n : ℕ} {T : Fin n → Fin n → Bool}

/-- In a tournament, the players of `S` win `C(#S, 2)` games against
each other in total, since every pair of distinct players of `S` plays
exactly one game. -/
theorem sum_card_filter_eq_choose (hT : IsTournament T)
    (S : Finset (Fin n)) :
    ∑ i ∈ S, #{j ∈ S | T i j} = (#S).choose 2 := by
  have key : ∀ i j : Fin n, ((if T i j then 1 else 0) +
      (if T j i then 1 else 0)) + (if i = j then 1 else 0) = 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [hT.1, Bool.false_eq_true, ↓reduceIte]
    · have h := hT.2 i j hij
      cases h1 : T i j <;> cases h2 : T j i <;>
        simp only [h1, h2, hij, ne_eq, not_true_eq_false,
          Bool.false_eq_true, ↓reduceIte] at h ⊢
  have hdiag : ∑ i ∈ S, ∑ j ∈ S, (if i = j then 1 else 0) = #S := by
    rw [sum_congr rfl fun i hi => sum_ite_eq S i fun _ => 1,
      sum_congr rfl fun i hi => ite_eq_left hi, card_eq_sum_ones]
  have hX : ∑ i ∈ S, #{j ∈ S | T i j} =
      ∑ i ∈ S, ∑ j ∈ S, if T i j then 1 else 0 := by
    simp only [card_filter]
  have htot : ((∑ i ∈ S, ∑ j ∈ S, if T i j then 1 else 0) +
      ∑ i ∈ S, ∑ j ∈ S, if T i j then 1 else 0) +
      ∑ i ∈ S, ∑ j ∈ S, (if i = j then 1 else 0) = #S * #S := by
    nth_rw 2 [sum_comm]
    simp only [← sum_add_distrib, key, sum_const, smul_eq_mul, mul_one]
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  generalize #S * #S = m at htot ⊢
  omega

/-- The total score of a set `S` of players in a tournament is `C(#S, 2)`
plus the number of games they win against players outside `S`. -/
theorem sum_score_eq_choose_add (hT : IsTournament T)
    (S : Finset (Fin n)) :
    ∑ i ∈ S, score T i =
      (#S).choose 2 + ∑ i ∈ S, #{j ∈ Sᶜ | T i j} := by
  rw [← sum_card_filter_eq_choose hT S, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [score, ← card_union_of_disjoint
    (disjoint_filter_filter disjoint_compl_right), ← filter_union,
    union_compl]

/-- **Landau's condition is necessary**: the players of any set `S` have
total score at least `C(#S, 2)`. -/
theorem choose_two_le_sum_score (hT : IsTournament T)
    (S : Finset (Fin n)) :
    (#S).choose 2 ≤ ∑ i ∈ S, score T i := by
  rw [sum_score_eq_choose_add hT S]
  exact Nat.le_add_right _ _

/-- The scores of a tournament on `Fin n` sum to `C(n, 2)`. -/
theorem sum_score_eq_choose (hT : IsTournament T) :
    ∑ i, score T i = n.choose 2 := by
  have h := sum_card_filter_eq_choose hT univ
  rw [card_fin] at h
  exact h

/-! ### Landau's theorem -/

/-- **Landau's condition is sufficient**: if every set `S` of players has
`∑ i ∈ S, s i ≥ C(#S, 2)` and the total is `C(n, 2)`, then `s` is the
score sequence of a tournament. The tournament comes from Hall's marriage
theorem: each game is assigned to one of `s i` slots of one of its two
players `i`, and that player wins the game. -/
theorem exists_isTournament_of_forall_choose_two_le (s : Fin n → ℕ)
    (hS : ∀ S : Finset (Fin n), (#S).choose 2 ≤ ∑ i ∈ S, s i)
    (htot : ∑ i, s i = n.choose 2) :
    ∃ T : Fin n → Fin n → Bool, IsTournament T ∧ ∀ i, score T i = s i := by
  classical
  -- A game is an unordered pair of distinct players; a slot of player `i`
  -- is an element of `Fin (s i)`.
  let t : {e : Sym2 (Fin n) // ¬ e.IsDiag} → Finset (Σ i, Fin (s i)) :=
    fun e => ({i | i ∈ e.1} : Finset (Fin n)).sigma fun _ => univ
  have hall : ∀ G : Finset {e : Sym2 (Fin n) // ¬ e.IsDiag},
      #G ≤ #(G.biUnion t) := by
    intro G
    let P : Finset (Fin n) := G.biUnion fun e => {i | i ∈ e.1}
    have hP : G.biUnion t = P.sigma fun _ => univ := by
      ext x
      simp [t, P]
    have hG : #G ≤ #(P.offDiag.image Sym2.mk.uncurry) := by
      refine card_le_card_of_injOn Subtype.val ?_ Subtype.val_injective.injOn
      rintro ⟨e, he⟩ heG
      induction e using Sym2.ind with
      | h a b =>
        refine mem_image.2 ⟨(a, b), mem_offDiag.2 ⟨?_, ?_, ?_⟩, rfl⟩
        · exact mem_biUnion.2 ⟨_, heG, by simp⟩
        · exact mem_biUnion.2 ⟨_, heG, by simp⟩
        · simpa using he
    rw [hP, card_sigma]
    simp only [card_univ, Fintype.card_fin]
    exact hG.trans ((Sym2.card_image_offDiag P).trans_le (hS P))
  obtain ⟨f, hf, hft⟩ :=
    (all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hmem : ∀ e, (f e).1 ∈ e.1 := fun e => by simpa [t] using hft e
  have hdiag : ∀ {i j : Fin n}, i ≠ j → ¬ (s(i, j)).IsDiag :=
    fun h => Sym2.mk_isDiag_iff.not.2 h
  -- `i` beats `j` when the game `{i, j}` is assigned to a slot of `i`.
  let T : Fin n → Fin n → Bool := fun i j =>
    if h : i = j then false else decide ((f ⟨s(i, j), hdiag h⟩).1 = i)
  have hT : IsTournament T := by
    refine ⟨fun i => dite_eq_left rfl, fun i j hij => ?_⟩
    have hswap : f ⟨s(j, i), hdiag (Ne.symm hij)⟩ = f ⟨s(i, j), hdiag hij⟩ :=
      congrArg f (Subtype.ext Sym2.eq_swap)
    simp only [T, dite_eq_right hij, dite_eq_right (Ne.symm hij), hswap]
    rcases Sym2.mem_iff.1 (hmem ⟨s(i, j), hdiag hij⟩) with h | h
    · simp [h, hij]
    · simp [h, Ne.symm hij]
  have hle : ∀ i, score T i ≤ s i := by
    intro i
    have hne : ∀ j ∈ ({j | T i j} : Finset (Fin n)), i ≠ j := by
      rintro j hj rfl
      simp [hT.1] at hj
    calc score T i = #({j | T i j} : Finset (Fin n)).attach :=
          (card_attach).symm
      _ ≤ #(({i} : Finset (Fin n)).sigma fun _ => univ) := by
        refine card_le_card_of_injOn
          (fun j => f ⟨s(i, j.1), hdiag (hne j.1 j.2)⟩) ?_ ?_
        · rintro ⟨j, hj⟩ -
          have hTj := (mem_filter.1 hj).2
          simp only [T, dite_eq_right (hne j hj), decide_eq_true_eq] at hTj
          simp [hTj]
        · rintro ⟨j, hj⟩ - ⟨j', hj'⟩ - h
          have := congrArg Subtype.val (hf h)
          exact Subtype.ext (Sym2.congr_right.1 this)
      _ = s i := by simp [card_sigma]
  refine ⟨T, hT, fun i => ?_⟩
  exact (sum_eq_sum_iff_of_le fun i _ => hle i).1
    ((sum_score_eq_choose hT).trans htot.symm) i (mem_univ i)

/-- **Landau's theorem**, unsorted form: `s` is the score sequence of a
tournament on `Fin n` exactly when every set `S` of players has
`∑ i ∈ S, s i ≥ C(#S, 2)` and the total is `C(n, 2)`. -/
theorem exists_isTournament_score_eq_iff (s : Fin n → ℕ) :
    (∃ T : Fin n → Fin n → Bool, IsTournament T ∧ ∀ i, score T i = s i) ↔
      (∀ S : Finset (Fin n), (#S).choose 2 ≤ ∑ i ∈ S, s i) ∧
        ∑ i, s i = n.choose 2 := by
  refine ⟨?_, fun h => exists_isTournament_of_forall_choose_two_le s h.1 h.2⟩
  rintro ⟨T, hT, hs⟩
  simp only [← hs]
  exact ⟨choose_two_le_sum_score hT, sum_score_eq_choose hT⟩

/-- The sum of `s` over the image of `Fin.castLE hk` is the sum of the
first `k` values of `s`. -/
private theorem sum_map_castLEEmb {M : Type*} [AddCommMonoid M]
    (s : Fin n → M) {k : ℕ} (hk : k ≤ n) :
    ∑ i ∈ univ.map (Fin.castLEEmb hk), s i =
      ∑ i : Fin k, s (Fin.castLE hk i) := by
  rw [sum_map]
  rfl

/-- **Theorem 4** (Landau, via Moon): a nondecreasing
sequence `s_1 ≤ ⋯ ≤ s_n` is the score sequence of a
tournament if and only if `∑_{i=1}^k s_i ≥ C(k, 2)` for
`1 ≤ k ≤ n`, with equality when `k = n`.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Theorem 4.

Proves `Wanted` entry `landau_score_sequence`. -/
theorem landau_score_sequence (n : ℕ)
    (s : Fin n → ℕ)
    (hs : ∀ i j : Fin n, i ≤ j → s i ≤ s j) :
    (∃ T : Fin n → Fin n → Bool, IsTournament T ∧
      ∀ i, score T i = s i) ↔
    (∀ k : ℕ, ∀ hk : k ≤ n, 1 ≤ k →
      Nat.choose k 2 ≤
        ∑ i : Fin k, s (Fin.castLE hk i)) ∧
    (∑ i, s i) = Nat.choose n 2 := by
  rw [exists_isTournament_score_eq_iff]
  refine and_congr_left fun _ => ⟨fun h k hk _ => ?_, fun h S => ?_⟩
  · have := h (univ.map (Fin.castLEEmb hk))
    rwa [card_map, card_fin, sum_map_castLEEmb] at this
  · have hk : #S ≤ n := card_le_univ S |>.trans_eq (Fintype.card_fin n)
    rcases Nat.eq_zero_or_pos #S with h0 | hpos
    · simp [h0]
    · exact (h _ hk hpos).trans
        (sum_castLE_le_sum_of_monotone (fun i j hij => hs i j hij) S hk)

/-! ### Moon's reducibility criterion -/

/-- **Theorem 5** (Moon): a tournament with score
sequence `s_1 ≤ ⋯ ≤ s_n` is reducible if and only if
`∑_{i=1}^k s_i = C(k, 2)` for some positive integer
`k < n`.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Theorem 5.

Proves `Wanted` entry `isReducible_iff`. -/
theorem isReducible_iff (n : ℕ)
    (T : Fin n → Fin n → Bool) (s : Fin n → ℕ)
    (hT : IsTournament T)
    (hs : ∀ i j : Fin n, i ≤ j → s i ≤ s j)
    (hscore : ∀ i, score T i = s i) :
    IsReducible T ↔
      ∃ k : ℕ, ∃ hk : k ≤ n, 1 ≤ k ∧ k < n ∧
        (∑ i : Fin k, s (Fin.castLE hk i)) =
          Nat.choose k 2 := by
  constructor
  · rintro ⟨S, hne, hS, hlose⟩
    have hk : #S ≤ n := card_le_univ S |>.trans_eq (Fintype.card_fin n)
    have hkn : #S < n :=
      ((card_lt_iff_ne_univ S).2 hS).trans_eq (Fintype.card_fin n)
    refine ⟨#S, hk, hne.card_pos, hkn, le_antisymm ?_ ?_⟩
    · calc ∑ i : Fin #S, s (Fin.castLE hk i) ≤ ∑ i ∈ S, s i :=
            sum_castLE_le_sum_of_monotone (fun i j hij => hs i j hij) S hk
        _ = ∑ i ∈ S, score T i := sum_congr rfl fun i _ => (hscore i).symm
        _ = (#S).choose 2 := by
          rw [sum_score_eq_choose_add hT S, sum_eq_zero, add_zero]
          intro i hi
          rw [card_eq_zero, filter_eq_empty_iff]
          intro j hj
          simp [hlose i hi j (mem_compl.1 hj)]
    · have := choose_two_le_sum_score hT (univ.map (Fin.castLEEmb hk))
      rwa [card_map, card_fin, sum_map_castLEEmb,
        sum_congr rfl fun i _ => hscore _] at this
  · rintro ⟨k, hk, hk1, hkn, hsum⟩
    set S := univ.map (Fin.castLEEmb hk) with hSdef
    have hcard : #S = k := by rw [card_map, card_fin]
    refine ⟨S, ⟨_, mem_map_of_mem (Fin.castLEEmb hk) (mem_univ ⟨0, hk1⟩)⟩,
      fun h => ?_,
      fun i hi j hj => ?_⟩
    · have := congrArg card h
      rw [hcard, card_univ, Fintype.card_fin] at this
      omega
    · have h := sum_score_eq_choose_add hT S
      rw [sum_congr rfl fun i _ => hscore i, sum_map_castLEEmb, hsum,
        hcard, left_eq_add, sum_eq_zero_iff] at h
      have hj' : j ∉ {j ∈ Sᶜ | T i j} := by
        rw [card_eq_zero.1 (h i hi)]
        exact notMem_empty j
      simpa [hj] using hj'

/-! ### Moon's circular-triad count -/

/-- In a `3`-set `S` of players, the number of players beating both
others is `0` if `S` is a circular triad and `1` otherwise. -/
theorem card_filter_card_filter_eq_two (hT : IsTournament T)
    {S : Finset (Fin n)} (hS : #S = 3) :
    #{i ∈ S | #{j ∈ S | T i j} = 2} =
      if IsCircularTriad T S then 0 else 1 := by
  have hsum : ∑ i ∈ S, #{j ∈ S | T i j} = 3 := by
    rw [sum_card_filter_eq_choose hT, hS]
    rfl
  have hle : ∀ i ∈ S, #{j ∈ S | T i j} ≤ 2 := by
    intro i hi
    refine (card_le_card (t := S.erase i) fun j hj =>
      mem_erase.2 ⟨?_, (mem_filter.1 hj).1⟩).trans ?_
    · rintro rfl
      simp [hT.1] at hj
    · rw [card_erase_of_mem hi, hS]
  have hD : #{i ∈ S | #{j ∈ S | T i j} = 2} ≤ 1 := by
    by_contra h
    have : 2 * #{i ∈ S | #{j ∈ S | T i j} = 2} ≤ 3 := by
      rw [← hsum, mul_comm, ← smul_eq_mul, ← sum_const]
      calc ∑ _ ∈ {i ∈ S | #{j ∈ S | T i j} = 2}, 2
          = ∑ i ∈ {i ∈ S | #{j ∈ S | T i j} = 2}, #{j ∈ S | T i j} :=
            sum_congr rfl fun i hi => (mem_filter.1 hi).2.symm
        _ ≤ ∑ i ∈ S, #{j ∈ S | T i j} :=
            sum_le_sum_of_subset (filter_subset _ _)
    omega
  by_cases hc : IsCircularTriad T S
  · rw [ite_eq_left hc, card_eq_zero, filter_eq_empty_iff]
    intro i hi h
    have := hc.2 i hi
    omega
  · rw [ite_eq_right hc]
    refine le_antisymm hD (Nat.one_le_iff_ne_zero.2 fun h0 => hc ⟨hS, ?_⟩)
    have hle1 : ∀ i ∈ S, #{j ∈ S | T i j} ≤ 1 := by
      intro i hi
      have h2 := hle i hi
      have hne : #{j ∈ S | T i j} ≠ 2 := fun h =>
        (filter_eq_empty_iff.1 (card_eq_zero.1 h0)) hi h
      omega
    refine (sum_eq_sum_iff_of_le hle1).1 ?_
    rw [hsum, sum_const, hS, smul_eq_mul, mul_one]

/-- The `3`-sets of players in which `i` beats both others correspond
to the pairs of players beaten by `i`, so there are `C(score T i, 2)` of
them. -/
theorem card_filter_powersetCard_eq_choose (hT : IsTournament T)
    (i : Fin n) :
    #{S ∈ univ.powersetCard 3 | i ∈ S ∧ #{j ∈ S | T i j} = 2} =
      (score T i).choose 2 := by
  rw [score, ← card_powersetCard]
  refine card_nbij' (fun S => S.erase i) (fun P => insert i P) ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_coe, mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨-, hS3⟩, hiS, hS2⟩ := hS
    have hsub : {j ∈ S | T i j} ⊆ S.erase i := fun j hj =>
      mem_erase.2 ⟨by rintro rfl; simp [hT.1] at hj, (mem_filter.1 hj).1⟩
    have heq : {j ∈ S | T i j} = S.erase i :=
      eq_of_subset_of_card_le hsub (by rw [card_erase_of_mem hiS]; omega)
    rw [mem_coe, mem_powersetCard]
    beta_reduce
    rw [← heq]
    exact ⟨fun j hj => mem_filter.2 ⟨mem_univ j, (mem_filter.1 hj).2⟩, hS2⟩
  · intro P hP
    rw [mem_coe, mem_powersetCard] at hP
    obtain ⟨hPsub, hP2⟩ := hP
    have hiP : i ∉ P := fun h => by simpa [hT.1] using hPsub h
    have hfil : {j ∈ insert i P | T i j} = P := by
      rw [filter_insert, ite_eq_right (by simp [hT.1]), filter_true_of_mem]
      intro j hj
      simpa using hPsub hj
    rw [mem_coe, mem_filter, mem_powersetCard, hfil, card_insert_of_notMem hiP,
      hP2]
    exact ⟨⟨subset_univ _, rfl⟩, mem_insert_self i P, rfl⟩
  · intro S hS
    rw [mem_coe, mem_filter] at hS
    exact insert_erase hS.2.1
  · intro P hP
    rw [mem_coe, mem_powersetCard] at hP
    exact erase_insert fun h => by simpa [hT.1] using hP.1 h

/-- **Theorem 6** (Moon): the number of circular triads
in a tournament with scores `s_1, …, s_n` is
`C(n, 3) - ∑_i C(s_i, 2)`.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Theorem 6.

Proves `Wanted` entry `card_circularTriads`. -/
theorem card_circularTriads (n : ℕ)
    (T : Fin n → Fin n → Bool) (hT : IsTournament T) :
    ((Finset.univ.powersetCard 3).filter
        (IsCircularTriad T)).card =
      Nat.choose n 3 - ∑ i, Nat.choose (score T i) 2 := by
  set A : Finset (Finset (Fin n)) := univ.powersetCard 3
  have hA : #A = n.choose 3 := by rw [card_powersetCard, card_fin]
  have hnon : #{S ∈ A | ¬ IsCircularTriad T S} =
      ∑ i, (score T i).choose 2 := by
    calc #{S ∈ A | ¬ IsCircularTriad T S}
        = ∑ S ∈ A, #{i ∈ S | #{j ∈ S | T i j} = 2} := by
          rw [card_filter]
          refine sum_congr rfl fun S hS => ?_
          rw [card_filter_card_filter_eq_two hT (mem_powersetCard.1 hS).2]
          by_cases hc : IsCircularTriad T S <;> simp [hc]
      _ = ∑ S ∈ A, ∑ i,
            if i ∈ S ∧ #{j ∈ S | T i j} = 2 then 1 else 0 := by
          refine sum_congr rfl fun S _ => ?_
          rw [← card_filter]
          congr 1
          ext i
          simp only [mem_filter, mem_univ, true_and]
      _ = ∑ i, (score T i).choose 2 := by
          rw [sum_comm]
          refine sum_congr rfl fun i _ => ?_
          rw [← card_filter_powersetCard_eq_choose hT i, card_filter]
  have := card_filter_add_card_filter_not (s := A) (IsCircularTriad T)
  omega

end MathlibExt.GraphTheory.TournamentScoreSequenceWanted
