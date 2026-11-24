/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.Combinatorics.Additive.BhSet
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The fourth positive element in the greedy `B_h`-set

The greedy `B_h`-set starts with `a₀(h) = 0`, and `a_{k+1}(h)` is the least integer above
`a_k(h)` such that `{a₀(h), …, a_{k+1}(h)}` is still a `B_h`-set. Its next terms are `1`, `h + 1`
and `h² + h + 1`. This file expresses the greedy choice stage by stage (`IsNextGreedyBh`,
`IsFourthGreedyBh`) with `AdditiveCombinatorics.IsBhSet`, defines the quasipolynomial
`fourthValue h`, equal to `(h³ + 3h² + 3h + 1)/2` for odd `h` and `(h³ + 2h² + 3h + 2)/2` for even
`h`, and proves the upper bound `a₄(h) ≤ fourthValue h` for every `h ≥ 1`
(`isFourthGreedyBh_le_fourthValue`).

## Proof of the upper bound

Write `v = fourthValue h` and `A = {0, 1, h + 1, h² + h + 1}`. The fourth greedy term is the least
`b` above `A` for which `A ∪ {b}` is a `B_h`-set, so it suffices to show that `A ∪ {v}` is a
`B_h`-set. Two lists of `h` elements of `A ∪ {v}` are permutations of each other when each of the
five elements occurs equally often in both, so we compare these counts, given that the lists have
the same sum.

* We have `v = (h + 1)H`, where `2H = (h + 1)²` for odd `h` and `2H = h² + h + 2` for even `h`.
* Since `2v > h(h² + h + 1)`, the two counts of `v` differ by at most one. If they differ by one,
  the other list has more copies of `h² + h + 1`, say `t ≥ 1` more. Reducing modulo `h + 1`, where
  `h² + h + 1 ≡ 1`, and comparing sizes leaves an equation `H + x = y + th` with `x + t ≤ h - 1`
  and `y + t ≤ h`. It has no solution: for `2t ≤ h + 1` its right side is too small, and
  otherwise `x` is too large. This is the argument of Nathanson and O'Bryant, run without their
  reduction to summands that do not occur on both sides.
* When the counts of `v` agree, the remaining counts are the digits of the same number in the mixed
  base `1, h + 1, h² + h + 1`, so they agree too.

## References

* Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth Positive Element in the Greedy `B_h`-Set",
  *Journal of Integer Sequences* 27 (2024), Article 24.7.3
  (<https://cs.uwaterloo.ca/journals/JIS/VOL27/OBryant2/obryant4.html>); arXiv:2311.14021, where
  the upper bound is Lemma 2.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.GreedyBhFourthWanted

/-- **Next term of a greedy $B_h$-set.** Let $h$ and $a$ be natural numbers and $A$ a set of natural
numbers. Then $a$ is the next greedy $B_h$ choice after $A$ if $a$ is greater than every element
of $A$, the set $A \cup \{a\}$ is a $B_h$-set, and for every natural number $b < a$ that is
greater than every element of $A$, the set $A \cup \{b\}$ is not a $B_h$-set. -/
def IsNextGreedyBh (h : ℕ) (A : Set ℕ) (a : ℕ) : Prop :=
  (∀ x ∈ A, x < a) ∧ AdditiveCombinatorics.IsBhSet (insert a A) h ∧
    ∀ b : ℕ, (∀ x ∈ A, x < b) → b < a →
      ¬AdditiveCombinatorics.IsBhSet (insert b A) h

/-- **Fourth positive term of the greedy $B_h$-set.** For natural numbers $h$ and $a$, we say that
$a$ is the fourth positive element $a_4(h)$ of the greedy $B_h$-set if $1$ is the next greedy
$B_h$ choice after $\{0\}$, $h + 1$ is the next greedy $B_h$ choice after $\{0, 1\}$,
$h^2 + h + 1$ is the next greedy $B_h$ choice after $\{0, 1, h + 1\}$, and $a$ is the next
greedy $B_h$ choice after $\{0, 1, h + 1, h^2 + h + 1\}$. -/
def IsFourthGreedyBh (h a : ℕ) : Prop :=
  IsNextGreedyBh h {0} 1 ∧
    IsNextGreedyBh h {0, 1} (h + 1) ∧
    IsNextGreedyBh h {0, 1, h + 1} (h ^ 2 + h + 1) ∧
    IsNextGreedyBh h {0, 1, h + 1, h ^ 2 + h + 1} a

/-- **Quasipolynomial for the fourth greedy $B_h$ term.** For a natural number $h$, the value
$v(h)$ is $(h^3 + 3h^2 + 3h + 1)/2$ if $h$ is odd and $(h^3 + 2h^2 + 3h + 2)/2$ if $h$ is even.

Both numerators are even, so the divisions are exact. -/
def fourthValue (h : ℕ) : ℕ :=
  if Odd h then (h ^ 3 + 3 * h ^ 2 + 3 * h + 1) / 2
  else (h ^ 3 + 2 * h ^ 2 + 3 * h + 2) / 2

/-- The value `fourthValue h` is `(h + 1) * H`, where `2 * H = (h + 1) ^ 2` for odd `h` and
`2 * H = h ^ 2 + h + 2` for even `h`. -/
private theorem exists_fourthValue_eq_mul (h : ℕ) :
    ∃ H, fourthValue h = (h + 1) * H ∧
      ((∃ m, h = 2 * m + 1 ∧ 2 * H = h ^ 2 + 2 * h + 1) ∨
        (∃ m, h = 2 * m ∧ 2 * H = h ^ 2 + h + 2)) := by
  rcases Nat.even_or_odd h with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · refine ⟨2 * m ^ 2 + m + 1, ?_, Or.inr ⟨m, by ring, by ring⟩⟩
    have hodd : ¬Odd (m + m) := Nat.not_odd_iff_even.2 ⟨m, rfl⟩
    rw [fourthValue, ite_eq_right hodd, show (m + m) ^ 3 + 2 * (m + m) ^ 2 + 3 * (m + m) + 2 =
      2 * ((m + m + 1) * (2 * m ^ 2 + m + 1)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  · refine ⟨2 * (m + 1) ^ 2, ?_, Or.inl ⟨m, rfl, by ring⟩⟩
    rw [fourthValue, ite_eq_left ⟨m, rfl⟩, show (2 * m + 1) ^ 3 + 3 * (2 * m + 1) ^ 2 +
      3 * (2 * m + 1) + 1 = 2 * ((2 * m + 1 + 1) * (2 * (m + 1) ^ 2)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos

/-- For `h ≥ 1`, the value `fourthValue h` exceeds `h ^ 2 + h + 1`. -/
private theorem sq_add_add_one_lt_fourthValue {h : ℕ} (hh : 0 < h) :
    h ^ 2 + h + 1 < fourthValue h := by
  obtain ⟨H, hV, hH⟩ := exists_fourthValue_eq_mul h
  have hH2 : h ^ 2 + h + 2 ≤ 2 * H := by
    rcases hH with ⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩ <;> nlinarith
  rw [hV]
  nlinarith

/-- Uniqueness of the last digit and of the quotient: if `a + b * n = a' + b' * n` with
`a, a' < n`, then `a = a'` and `b = b'`. -/
private theorem eq_and_eq_of_add_mul_eq {n a b a' b' : ℕ} (ha : a < n) (ha' : a' < n)
    (h : a + b * n = a' + b' * n) : a = a' ∧ b = b' := by
  have hn : 0 < n := by omega
  have h1 : a = a' := by
    have := congrArg (· % n) h
    simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] using this
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hn (by omega)⟩

/-- The final step of the upper bound: if `2 * H = (h + 1) ^ 2` with `h` odd, or
`2 * H = h ^ 2 + h + 2` with `h` even, then the equation `x + H = y + T * h` has no solution with
`x + T + 1 ≤ h` and `y + T ≤ h`. -/
private theorem false_of_add_eq_add_mul {h H x y T : ℕ}
    (hH : (∃ m, h = 2 * m + 1 ∧ 2 * H = h ^ 2 + 2 * h + 1) ∨
      (∃ m, h = 2 * m ∧ 2 * H = h ^ 2 + h + 2))
    (e : x + H = y + T * h) (hx : x + T + 1 ≤ h) (hy : y + T ≤ h) : False := by
  rcases hH with ⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩
  · rcases Nat.lt_or_ge T (m + 2) with ht | ht
    · have : m * T ≤ m * (m + 1) := Nat.mul_le_mul_left m (by omega)
      linarith
    · have : (m + 2) * (2 * m + 1) ≤ T * (2 * m + 1) := Nat.mul_le_mul_right _ ht
      linarith
  · rcases Nat.lt_or_ge T (m + 1) with ht | ht
    · obtain ⟨r, rfl⟩ : ∃ r, m = T + r := ⟨m - T, by omega⟩
      have : r ≤ r * r := Nat.le_mul_self r
      have : 0 ≤ T * r := Nat.zero_le _
      linarith
    · have : (m + 1) * (2 * m) ≤ T * (2 * m) := Nat.mul_le_mul_right _ ht
      linarith

/-- Two sums of at most `h` elements of `{1, h + 1, h ^ 2 + h + 1, fourthValue h}` (with
multiplicities) that agree cannot use `fourthValue h` more often on the left than on the right. -/
private theorem false_of_count_lt {h : ℕ} (hh : 0 < h) {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℕ}
    (ha : a₄ + a₁ + a₂ + a₃ ≤ h) (hb : b₄ + b₁ + b₂ + b₃ ≤ h) (hlt : b₄ < a₄)
    (hs : a₄ * fourthValue h + a₁ + a₂ * (h + 1) + a₃ * (h ^ 2 + h + 1) =
      b₄ * fourthValue h + b₁ + b₂ * (h + 1) + b₃ * (h ^ 2 + h + 1)) : False := by
  obtain ⟨H, hV, hH⟩ := exists_fourthValue_eq_mul h
  have hH2 : h ^ 2 + h + 2 ≤ 2 * H := by
    rcases hH with ⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩ <;> nlinarith
  have hHh : h + 1 ≤ H := by nlinarith
  generalize fourthValue h = V at hs hV
  -- The left side uses `V` exactly once more, since `2 * V > h * (h ^ 2 + h + 1)`.
  have hk : a₄ = b₄ + 1 := by
    by_contra hne
    have e1 : (b₄ + 2) * V ≤ a₄ * V := Nat.mul_le_mul_right V (by omega)
    have e2 : b₁ ≤ b₁ * (h ^ 2 + h + 1) := Nat.le_mul_of_pos_right _ (by positivity)
    have e3 : b₂ * (h + 1) ≤ b₂ * (h ^ 2 + h + 1) := Nat.mul_le_mul_left _ (by nlinarith)
    have e4 : (b₁ + b₂ + b₃) * (h ^ 2 + h + 1) ≤ h * (h ^ 2 + h + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have e5 : (h + 1) * (h ^ 2 + h + 2) ≤ (h + 1) * (2 * H) := Nat.mul_le_mul_left _ hH2
    nlinarith
  subst hk
  have hs2 : V + a₁ + a₂ * (h + 1) + a₃ * (h ^ 2 + h + 1) =
      b₁ + b₂ * (h + 1) + b₃ * (h ^ 2 + h + 1) := by linarith
  -- The right side uses `h ^ 2 + h + 1` more often, since `V > h * (h + 1)`.
  have h3 : a₃ < b₃ := by
    by_contra h3
    have e1 : b₃ * (h ^ 2 + h + 1) ≤ a₃ * (h ^ 2 + h + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have e2 : (b₁ + b₂) * (h + 1) ≤ h * (h + 1) := Nat.mul_le_mul_right _ (by omega)
    have e3 : (h + 1) * (h + 1) ≤ (h + 1) * H := Nat.mul_le_mul_left _ hHh
    nlinarith
  obtain ⟨t, rfl⟩ : ∃ t, b₃ = a₃ + (t + 1) := ⟨b₃ - a₃ - 1, by omega⟩
  -- Compare last digits and quotients in base `h + 1`, using `h ^ 2 + h + 1 = h * (h + 1) + 1`.
  have key : a₁ + (a₂ + H) * (h + 1) = (b₁ + (t + 1)) + (b₂ + (t + 1) * h) * (h + 1) := by
    subst hV
    nlinarith
  obtain ⟨e1, e2⟩ :=
    eq_and_eq_of_add_mul_eq (by omega : a₁ < h + 1) (by omega : b₁ + (t + 1) < h + 1) key
  exact false_of_add_eq_add_mul hH e2 (by omega) (by omega)

/-- If two lists of `h` elements of `{fourthValue h, 0, 1, h + 1, h ^ 2 + h + 1}` have the same
sum, then each of the five elements occurs equally often in both; here the `a`s and `b`s are the
numbers of occurrences, in this order. -/
private theorem counts_eq_of_sum_eq {h : ℕ} (hh : 0 < h) {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : ℕ}
    (ha : a₄ + a₀ + a₁ + a₂ + a₃ = h) (hb : b₄ + b₀ + b₁ + b₂ + b₃ = h)
    (hs : a₄ * fourthValue h + a₁ + a₂ * (h + 1) + a₃ * (h ^ 2 + h + 1) =
      b₄ * fourthValue h + b₁ + b₂ * (h + 1) + b₃ * (h ^ 2 + h + 1)) :
    a₄ = b₄ ∧ a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  have h4 : a₄ = b₄ := by
    rcases lt_trichotomy a₄ b₄ with hlt | heq | hlt
    · exact (false_of_count_lt hh (by omega) (by omega) hlt hs.symm).elim
    · exact heq
    · exact (false_of_count_lt hh (by omega) (by omega) hlt hs).elim
  subst h4
  have hs' : (a₁ + a₂ * (h + 1)) + a₃ * (h ^ 2 + h + 1) =
      (b₁ + b₂ * (h + 1)) + b₃ * (h ^ 2 + h + 1) := by omega
  have hlow : ∀ x y : ℕ, x + y ≤ h → x + y * (h + 1) < h ^ 2 + h + 1 := by
    intro x y hxy
    have : y * h ≤ h * h := Nat.mul_le_mul_right h (by omega)
    nlinarith
  obtain ⟨e12, e3⟩ :=
    eq_and_eq_of_add_mul_eq (hlow a₁ a₂ (by omega)) (hlow b₁ b₂ (by omega)) hs'
  obtain ⟨e1, e2⟩ := eq_and_eq_of_add_mul_eq (by omega : a₁ < h + 1) (by omega : b₁ < h + 1) e12
  exact ⟨rfl, by omega, e1, e2, e3⟩

/-- For a nonempty list of natural numbers, `AdditiveCombinatorics.sumNE` is `List.sum`. -/
private theorem sumNE_eq_sum (l : List ℕ) (e : l ≠ []) :
    AdditiveCombinatorics.sumNE l e = l.sum := by
  cases l with
  | nil => exact absurd rfl e
  | cons a t =>
    simp only [AdditiveCombinatorics.sumNE, List.sum_cons]
    rw [List.foldl_eq_apply_foldr]
    rfl

/-- The length and the sum of a list of elements of `{fourthValue h, 0, 1, h + 1, h ^ 2 + h + 1}`,
in terms of the numbers of occurrences of these five elements. -/
private theorem length_eq_and_sum_eq {h : ℕ} (hh : 0 < h) (l : List ℕ)
    (hl : ∀ x ∈ l, x ∈ (insert (fourthValue h) {0, 1, h + 1, h ^ 2 + h + 1} : Set ℕ)) :
    l.length = l.count (fourthValue h) + l.count 0 + l.count 1 + l.count (h + 1) +
        l.count (h ^ 2 + h + 1) ∧
      l.sum = l.count (fourthValue h) * fourthValue h + l.count 1 +
        l.count (h + 1) * (h + 1) + l.count (h ^ 2 + h + 1) * (h ^ 2 + h + 1) := by
  have hv := sq_add_add_one_lt_fourthValue hh
  have hh2 : 0 < h ^ 2 := by positivity
  have hlT : ∀ x ∈ l, x ∈ ({fourthValue h, 0, 1, h + 1, h ^ 2 + h + 1} : Finset ℕ) :=
    fun x hx => by simpa using hl x hx
  have n1 : fourthValue h ∉ ({0, 1, h + 1, h ^ 2 + h + 1} : Finset ℕ) := by simp; omega
  have n2 : (0 : ℕ) ∉ ({1, h + 1, h ^ 2 + h + 1} : Finset ℕ) := by simp
  have n3 : (1 : ℕ) ∉ ({h + 1, h ^ 2 + h + 1} : Finset ℕ) := by simp; omega
  have n4 : h + 1 ∉ ({h ^ 2 + h + 1} : Finset ℕ) := by simp; omega
  have hlen := Multiset.sum_count_eq_card (m := (l : Multiset ℕ))
    (fun x hx => hlT x (by simpa using hx))
  have hsum := Finset.sum_list_count_of_subset l _ (fun x hx => hlT x (List.mem_toFinset.1 hx))
  rw [Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3, Finset.sum_insert n4,
    Finset.sum_singleton] at hlen hsum
  simp only [Multiset.coe_count, Multiset.coe_card, nsmul_eq_mul, Nat.cast_id] at hlen hsum
  constructor
  · omega
  · rw [hsum]
    ring

/-- For `h ≥ 1`, the set `{0, 1, h + 1, h ^ 2 + h + 1, fourthValue h}` is a `B_h`-set. -/
private theorem isBhSet_insert_fourthValue {h : ℕ} (hh : 0 < h) :
    AdditiveCombinatorics.IsBhSet
      (insert (fourthValue h) ({0, 1, h + 1, h ^ 2 + h + 1} : Set ℕ)) h := by
  refine ⟨⟨0, by simp⟩, hh, ?_⟩
  intro l₁ l₂ hm₁ hm₂ hl₁ hl₂ e₁ e₂ hsum
  rw [sumNE_eq_sum, sumNE_eq_sum] at hsum
  obtain ⟨len₁, sum₁⟩ := length_eq_and_sum_eq hh l₁ hm₁
  obtain ⟨len₂, sum₂⟩ := length_eq_and_sum_eq hh l₂ hm₂
  obtain ⟨c₄, c₀, c₁, c₂, c₃⟩ :=
    counts_eq_of_sum_eq hh (len₁ ▸ hl₁) (len₂ ▸ hl₂) (sum₁ ▸ sum₂ ▸ hsum)
  rw [List.perm_iff_count]
  intro x
  by_cases hx : x ∈ (insert (fourthValue h) ({0, 1, h + 1, h ^ 2 + h + 1} : Set ℕ))
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [List.count_eq_zero_of_not_mem (fun hx' => hx (hm₁ x hx')),
      List.count_eq_zero_of_not_mem (fun hx' => hx (hm₂ x hx'))]

/-- **Upper bound for the fourth greedy $B_h$ term.** Let $h$ and $a$ be natural numbers with
$h \ge 1$. If $a$ is the fourth positive element $a_4(h)$ of the greedy $B_h$-set, then
$a \le v(h)$, where $v(h) = (h^3 + 3h^2 + 3h + 1)/2$ if $h$ is odd and
$v(h) = (h^3 + 2h^2 + 3h + 2)/2$ if $h$ is even.

Source: Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth Positive
Element in the Greedy `B_h`-Set", Lemma 3. -/
theorem isFourthGreedyBh_le_fourthValue
    (h a : ℕ) (hh : 0 < h) (ha : IsFourthGreedyBh h a) :
    a ≤ fourthValue h := by
  by_contra hlt
  have hv := sq_add_add_one_lt_fourthValue hh
  refine ha.2.2.2.2.2 (fourthValue h) ?_ (by omega) (isBhSet_insert_fourthValue hh)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> omega

end MathlibExt.Combinatorics.GreedyBhFourthWanted
