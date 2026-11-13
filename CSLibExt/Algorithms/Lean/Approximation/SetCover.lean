/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Greedy set cover and the harmonic bound

`GREEDY-SET-COVER` from CLRS, third edition, Section 35.3: while some element of `X` is
uncovered, take a set of the family covering the most uncovered elements. CLRS Theorem 35.4: the
greedy cover has at most `H(max {|S| : S ∈ F})` times as many sets as an optimal cover, where
`H(d) = 1 + 1/2 + ⋯ + 1/d` is Mathlib's `harmonic`. Corollary 35.5 gives the factor
`ln |X| + 1`; it follows from the stronger intermediate factor `H(|X|)` and Mathlib's
`harmonic_le_one_add_log`.

`greedySetCover F U` takes the family as a list `F` and the uncovered set `U`; ties go to the
first maximizing set in list order (`List.argmax`). It stops when no set meets `U`, so it always
terminates; when `U` is covered by `F` the result covers `U` (`greedySetCover_covers`).

The bound is proved by induction on `U` with the potential `∑_{S ∈ C*} H(|S ∩ U|)` for any cover
`C*` drawn from `F` (`greedySetCover_length_le_sum_harmonic`): taking a set that covers `k` new
elements lowers each `H(|S ∩ U|)` by at least `|S ∩ U ∩ S₁| / k`, because greedy guarantees
`|S ∩ U| ≤ k`, and these drops sum to at least `1` because `C*` covers the `k` new elements. This
is CLRS's charging argument (each newly covered element is charged `1/k`), summed per step.

## Cost model

Every search for a best set, including the final one that finds nothing, costs
`|F| + ∑_{S ∈ F} |S|`: one unit per set of the family visited plus one per element scanned to
compute `|S ∩ U|` with constant-time membership in `U`. Removing the chosen set from `U` and
building the result are free. Each successful search covers a new element, so there are at most
`|U| + 1` searches and the cost is at most `(|U| + 1) * (|F| + ∑_{S ∈ F} |S|)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [DecidableEq α]

/-- **Greedy choice of a set.** Given a list $F$ of finite sets and a finite set $U$, the best set
of $F$ for $U$ is the first set $S$ in the list $F$ that maximizes $|S \cap U|$, or $\emptyset$
when $F$ is empty. -/
def bestSet (F : List (Finset α)) (U : Finset α) : Finset α :=
  (F.argmax fun S => (S ∩ U).card).getD ∅

/-- **Greedy set cover.** Let $F = [S_1, \dots, S_n]$ be a list of finite sets and $U$ a finite
set. The greedy set cover of $U$ from $F$ is computed as follows. Let $T$ be the first $S_i$ in
the list that maximizes $|S_i \cap U|$, or $T = \emptyset$ when $n = 0$. If
$T \cap U = \emptyset$, the result is the empty list; otherwise it is $T$ followed by the greedy
set cover of $U \setminus T$ from $F$. Each step, including the last one, costs
$n + |S_1| + \dots + |S_n|$. -/
def greedySetCover (F : List (Finset α)) (U : Finset α) : TimeM ℕ (List (Finset α)) := do
  ✓[F.length + (F.map Finset.card).sum]
  let S := bestSet F U
  if _hS : (S ∩ U).card = 0 then pure []
  else do
    let C ← greedySetCover F (U \ S)
    pure (S :: C)
termination_by U.card
decreasing_by
  have h := Finset.card_sdiff_add_card_inter U (bestSet F U)
  have hS' : ¬ (bestSet F U ∩ U).card = 0 := _hS
  rw [Finset.inter_comm] at h
  omega

theorem bestSet_mem {F : List (Finset α)} {U : Finset α} (h : (bestSet F U ∩ U).card ≠ 0) :
    bestSet F U ∈ F := by
  unfold bestSet at *
  cases hm : F.argmax (fun S => (S ∩ U).card) with
  | none => simp [hm] at h
  | some S => simpa using List.argmax_mem hm

theorem card_inter_le_bestSet {F : List (Finset α)} {U T : Finset α} (hT : T ∈ F) :
    (T ∩ U).card ≤ (bestSet F U ∩ U).card := by
  unfold bestSet
  cases hm : F.argmax (fun S => (S ∩ U).card) with
  | none => exact absurd (List.argmax_eq_none.1 hm) (List.ne_nil_of_mem hT)
  | some S => simpa using List.le_of_mem_argmax hT hm

theorem card_sdiff_lt {U S : Finset α} (hS : (S ∩ U).card ≠ 0) : (U \ S).card < U.card := by
  have h := Finset.card_sdiff_add_card_inter U S
  rw [Finset.inter_comm] at h
  omega

/-! ## The result is a cover from the family -/

/-- **The greedy set cover draws its sets from the family.** For every list $F$ of finite sets and
every finite set $U$, every set in the list returned by the greedy set cover algorithm on $F$ and
$U$ is a member of $F$. -/
theorem greedySetCover_mem (F : List (Finset α)) (U : Finset α) :
    ∀ S ∈ (greedySetCover F U).ret, S ∈ F := by
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    rw [greedySetCover]
    by_cases hS : (bestSet F U ∩ U).card = 0
    · simp [hS]
    · simp only [hS, dite_false, ret_bind, ret_pure, List.mem_cons]
      rintro T (rfl | hT)
      · exact bestSet_mem hS
      · exact ih _ (h ▸ card_sdiff_lt hS) _ rfl T hT

/-- **The greedy set cover is a cover.** Let $F$ be a list of finite sets and $U$ a finite set
such that every element of $U$ lies in some set of $F$. Then every element of $U$ lies in some
set of the list returned by the greedy set cover algorithm on $F$ and $U$. -/
theorem greedySetCover_covers (F : List (Finset α)) (U : Finset α)
    (hU : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) : ∀ x ∈ U, ∃ S ∈ (greedySetCover F U).ret, x ∈ S := by
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    intro x hx
    rw [greedySetCover]
    obtain ⟨T, hT, hxT⟩ := hU x hx
    have hTpos : 0 < (T ∩ U).card := Finset.card_pos.2 ⟨x, Finset.mem_inter.2 ⟨hxT, hx⟩⟩
    have hS : (bestSet F U ∩ U).card ≠ 0 := by
      have := card_inter_le_bestSet (U := U) hT
      omega
    simp only [hS, dite_false, ret_bind, ret_pure, List.mem_cons, exists_eq_or_imp]
    by_cases hxS : x ∈ bestSet F U
    · exact Or.inl hxS
    · refine Or.inr (ih _ (h ▸ card_sdiff_lt hS) (U \ bestSet F U) (fun y hy => ?_) rfl x
        (Finset.mem_sdiff.2 ⟨hx, hxS⟩))
      exact hU y (Finset.mem_sdiff.1 hy).1

/-! ## Cost -/

/-- **The greedy set cover has at most as many sets as elements.** For every list $F$ of finite
sets and every finite set $U$, the list returned by the greedy set cover algorithm on $F$ and $U$
has length at most $|U|$. -/
theorem greedySetCover_length_le (F : List (Finset α)) (U : Finset α) :
    (greedySetCover F U).ret.length ≤ U.card := by
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    rw [greedySetCover]
    by_cases hS : (bestSet F U ∩ U).card = 0
    · simp [hS]
    · simp only [hS, dite_false, ret_bind, ret_pure, List.length_cons]
      have hlt := card_sdiff_lt hS
      have := ih _ (h ▸ hlt) _ rfl
      omega

/-- **Running time of greedy set cover.** Let $F$ be a list of finite sets and $U$ a finite set.
The running time of greedy set cover of $U$ from $F$ is at most
$(|U| + 1)(|F| + \sum_{S \in F} |S|)$, where $|F|$ is the length of the list and the sum runs
over the entries of $F$, counted with repetition.

There are at most $|U| + 1$ searches for a best set, each costing $|F| + \sum_{S \in F} |S|$. -/
theorem greedySetCover_time_le (F : List (Finset α)) (U : Finset α) :
    (greedySetCover F U).time ≤ (U.card + 1) * (F.length + (F.map Finset.card).sum) := by
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    rw [greedySetCover]
    by_cases hS : (bestSet F U ∩ U).card = 0
    · simp only [hS, dite_true, time_bind, time_tick, time_pure, Nat.add_zero]
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    · simp only [hS, dite_false, time_bind, time_tick, time_pure, Nat.add_zero]
      have hlt := card_sdiff_lt hS
      have := ih _ (h ▸ hlt) _ rfl
      have hmono : ((U \ bestSet F U).card + 1) * (F.length + (F.map Finset.card).sum) ≤
          n * (F.length + (F.map Finset.card).sum) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-! ## The harmonic bound -/

/-- **Lower bound for a difference of harmonic numbers.** Write
$H(n) = 1 + \frac12 + \dots + \frac1n$ for the $n$-th harmonic number, so $H(0) = 0$. For natural
numbers $d \le a \le k$, we have $\frac{d}{k} \le H(a) - H(a - d)$, where $\frac{d}{k}$ is read
as $0$ when $k = 0$.

Each of the $d$ reciprocals $\frac{1}{a - d + 1}, \dots, \frac{1}{a}$ is at least $\frac1k$. -/
theorem div_le_harmonic_sub {a d k : ℕ} (hd : d ≤ a) (hak : a ≤ k) :
    (d : ℚ) / k ≤ harmonic a - harmonic (a - d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have ih := ih (by omega)
      have hsucc : harmonic (a - d) = harmonic (a - (d + 1)) + ((a - d : ℕ) : ℚ)⁻¹ := by
        rw [show a - d = (a - (d + 1)) + 1 by omega, harmonic_succ]
      have hk : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
      have hpos : (0 : ℚ) < ((a - d : ℕ) : ℚ) := by exact_mod_cast (show 0 < a - d by omega)
      have hle : (1 : ℚ) / k ≤ ((a - d : ℕ) : ℚ)⁻¹ := by
        rw [one_div]
        exact inv_anti₀ hpos (by exact_mod_cast (show a - d ≤ k by omega))
      have : ((d + 1 : ℕ) : ℚ) / k = (d : ℚ) / k + 1 / k := by push_cast; ring
      rw [this]
      linarith

theorem harmonic_le_harmonic {a b : ℕ} (h : a ≤ b) : harmonic a ≤ harmonic b :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => by positivity)

/-- **Covering bound by intersections.** Let $L$ be a list of finite sets and $T$ a finite set
such that every element of $T$ lies in some member of $L$. Then
$|T| \le \sum_{S \in L} |S \cap T|$, where the sum runs over the list $L$ with repetitions. -/
theorem card_le_sum_card_inter (L : List (Finset α)) (T : Finset α)
    (hT : ∀ x ∈ T, ∃ S ∈ L, x ∈ S) : T.card ≤ (L.map fun S => (S ∩ T).card).sum := by
  induction L generalizing T with
  | nil =>
      rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · simp
      · obtain ⟨S, hS, -⟩ := hT x hx
        simp at hS
  | cons S L ih =>
      simp only [List.map_cons, List.sum_cons]
      have hsplit := Finset.card_sdiff_add_card_inter T S
      have hrest := ih (T \ S) (fun x hx => by
        obtain ⟨S', hS', hxS'⟩ := hT x (Finset.mem_sdiff.1 hx).1
        rcases List.mem_cons.1 hS' with rfl | hS'
        · exact absurd hxS' (Finset.mem_sdiff.1 hx).2
        · exact ⟨S', hS', hxS'⟩)
      have hmono : (L.map fun S' => (S' ∩ (T \ S)).card).sum ≤
          (L.map fun S' => (S' ∩ T).card).sum :=
        List.sum_le_sum fun S' _ =>
          Finset.card_le_card (Finset.inter_subset_inter_left Finset.sdiff_subset)
      rw [Finset.inter_comm T S] at hsplit
      omega

/-- **Potential bound for greedy set cover.** Let $F$ be a list of finite sets, $U$ a finite set,
and $H(n) = 1 + \frac12 + \dots + \frac1n$ the $n$-th harmonic number. For every list $C^*$ of
members of $F$ that together cover $U$, the list of sets returned by the greedy set cover
algorithm on $F$ and $U$ has length at most $\sum_{S \in C^*} H(|S \cap U|)$, where the sum
runs over the list $C^*$ with repetitions. -/
theorem greedySetCover_length_le_sum_harmonic (F : List (Finset α)) (U : Finset α)
    (Cstar : List (Finset α)) (hsub : ∀ S ∈ Cstar, S ∈ F)
    (hcov : ∀ x ∈ U, ∃ S ∈ Cstar, x ∈ S) :
    ((greedySetCover F U).ret.length : ℚ) ≤
      (Cstar.map fun S => harmonic (S ∩ U).card).sum := by
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    rw [greedySetCover]
    by_cases hS : (bestSet F U ∩ U).card = 0
    · simp only [hS, dite_true, ret_bind, ret_pure, List.length_nil, Nat.cast_zero]
      exact List.sum_nonneg fun q hq => by
        obtain ⟨S, -, rfl⟩ := List.mem_map.1 hq
        exact Finset.sum_nonneg fun _ _ => by positivity
    · simp only [hS, dite_false, ret_bind, ret_pure, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      set S₁ := bestSet F U
      set k := (S₁ ∩ U).card
      have hIH := ih _ (h ▸ card_sdiff_lt hS) (U \ S₁)
        (fun x hx => hcov x (Finset.mem_sdiff.1 hx).1) rfl
      -- every set of `C*` meets `U` in at most `k` elements
      have hmax : ∀ S ∈ Cstar, (S ∩ U).card ≤ k := fun S hS' =>
        card_inter_le_bestSet (hsub S hS')
      -- splitting `S ∩ U` along `S₁`
      have hsplit : ∀ S : Finset α,
          (S ∩ (U \ S₁)).card + (S ∩ (S₁ ∩ U)).card = (S ∩ U).card := by
        intro S
        have := Finset.card_sdiff_add_card_inter (S ∩ U) S₁
        rw [Finset.inter_sdiff_assoc] at this
        convert this using 3
        ext y
        simp only [Finset.mem_inter]
        tauto
      have hdrop : ∀ S ∈ Cstar, harmonic (S ∩ (U \ S₁)).card +
          ((S ∩ (S₁ ∩ U)).card : ℚ) * (1 / k) ≤ harmonic (S ∩ U).card := by
        intro S hS'
        have h1 := div_le_harmonic_sub (a := (S ∩ U).card) (d := (S ∩ (S₁ ∩ U)).card)
          (k := k) (by have := hsplit S; omega) (hmax S hS')
        have h2 : (S ∩ U).card - (S ∩ (S₁ ∩ U)).card = (S ∩ (U \ S₁)).card := by
          have := hsplit S; omega
        rw [h2] at h1
        rw [mul_one_div]
        linarith
      have hcount : (k : ℚ) ≤ (Cstar.map fun S => ((S ∩ (S₁ ∩ U)).card : ℚ)).sum := by
        have := card_le_sum_card_inter Cstar (S₁ ∩ U)
          (fun x hx => hcov x (Finset.mem_inter.1 hx).2)
        have := (Nat.cast_le (α := ℚ)).2 this
        simpa [Nat.cast_list_sum, List.map_map, Function.comp_def] using this
      have hkpos : (0 : ℚ) < k := by exact_mod_cast Nat.pos_of_ne_zero hS
      have hone : (1 : ℚ) ≤
          (Cstar.map fun S => ((S ∩ (S₁ ∩ U)).card : ℚ) * (1 / k)).sum := by
        rw [List.sum_map_mul_right]
        calc (1 : ℚ) = k * (1 / k) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right hcount (one_div_nonneg.2 hkpos.le)
      have hsum := List.sum_le_sum hdrop
      rw [List.sum_map_add] at hsum
      linarith

/-- **Harmonic bound in the largest set size for greedy set cover.** Let $F$ be a list of finite
sets each with at most $d$ elements, $U$ a finite set, and $H(n) = 1 + \frac12 + \dots + \frac1n$
the $n$-th harmonic number. For every list $C^*$ of members of $F$ that together cover $U$, the
list of sets returned by the greedy set cover algorithm on $F$ and $U$ has length at most
$|C^*| \cdot H(d)$, where $|C^*|$ is the length of $C^*$.

Source: CLRS, third edition, Theorem 35.4. -/
theorem greedySetCover_approx (F : List (Finset α)) (U : Finset α) {d : ℕ}
    (hd : ∀ S ∈ F, S.card ≤ d) (Cstar : List (Finset α)) (hsub : ∀ S ∈ Cstar, S ∈ F)
    (hcov : ∀ x ∈ U, ∃ S ∈ Cstar, x ∈ S) :
    ((greedySetCover F U).ret.length : ℚ) ≤ Cstar.length * harmonic d := by
  refine (greedySetCover_length_le_sum_harmonic F U Cstar hsub hcov).trans ?_
  have : ∀ S ∈ Cstar, harmonic (S ∩ U).card ≤ harmonic d := fun S hS =>
    harmonic_le_harmonic ((Finset.card_le_card Finset.inter_subset_left).trans (hd S (hsub S hS)))
  have := List.sum_le_sum this
  simpa [List.sum_replicate, nsmul_eq_mul] using this

/-- **Harmonic bound in the universe size for greedy set cover.** Let $F$ be a list of finite
sets, $U$ a finite set, and $H(n) = 1 + \frac12 + \dots + \frac1n$ the $n$-th harmonic number. For
every list $C^*$ of members of $F$ that together cover $U$, the list of sets returned by the
greedy set cover algorithm on $F$ and $U$ has length at most $|C^*| \cdot H(|U|)$, where $|C^*|$
is the length of $C^*$.

Source: CLRS, third edition, Corollary 35.5, in the stronger harmonic form. -/
theorem greedySetCover_approx_card (F : List (Finset α)) (U : Finset α)
    (Cstar : List (Finset α)) (hsub : ∀ S ∈ Cstar, S ∈ F)
    (hcov : ∀ x ∈ U, ∃ S ∈ Cstar, x ∈ S) :
    ((greedySetCover F U).ret.length : ℚ) ≤ Cstar.length * harmonic U.card := by
  refine (greedySetCover_length_le_sum_harmonic F U Cstar hsub hcov).trans ?_
  have : ∀ S ∈ Cstar, harmonic (S ∩ U).card ≤ harmonic U.card := fun S _ =>
    harmonic_le_harmonic (Finset.card_le_card Finset.inter_subset_right)
  have := List.sum_le_sum this
  simpa [List.sum_replicate, nsmul_eq_mul] using this

/-- **Greedy set cover is a logarithmic approximation.** Let $F$ be a list of finite sets and $U$
a finite set. For every list $C^*$ of members of $F$ that together cover $U$, the list of sets
returned by the greedy set cover algorithm on $F$ and $U$ has length at most
$|C^*| \cdot (\ln |U| + 1)$, where $|C^*|$ is the length of $C^*$ and $\ln 0 = 0$.

Source: CLRS, third edition, Corollary 35.5, via Mathlib's `harmonic_le_one_add_log`. -/
theorem greedySetCover_approx_log (F : List (Finset α)) (U : Finset α)
    (Cstar : List (Finset α)) (hsub : ∀ S ∈ Cstar, S ∈ F)
    (hcov : ∀ x ∈ U, ∃ S ∈ Cstar, x ∈ S) :
    ((greedySetCover F U).ret.length : ℝ) ≤ Cstar.length * (Real.log U.card + 1) := by
  have h := greedySetCover_approx_card F U Cstar hsub hcov
  have h' : ((greedySetCover F U).ret.length : ℝ) ≤ Cstar.length * (harmonic U.card : ℝ) := by
    exact_mod_cast h
  refine h'.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have := harmonic_le_one_add_log U.card
  linarith

end Cslib.Algorithms.Lean.TimeM
