/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Maximum Nim and the Josephus problem

This file develops Maximum Nim from the paper of Takahashi, Manabe and Miyadera on Maximum Nim and
the Josephus problem. In Maximum Nim with rule function $f : \mathbb{N} \to \mathbb{N}$, a move from
a pile of $x$ stones removes $u$ stones for some $u$ with $1 \le u \le f(x)$; the paper studies the
rule function $f(x) = \lfloor x/k \rfloor$.

## Main definitions

* `MetaMathlibExt.maximumNimMex`: the minimum excludant (mex) of a finite set of natural numbers.
* `MetaMathlibExt.maximumNimGrundy`: the Grundy number $G_f(x)$ of a pile of $x$ stones in
  Maximum Nim with rule function $f$.

## Main statements

* `MetaMathlibExt.maximumNimMex_eq_iff` and `MetaMathlibExt.maximumNimGrundy_eq`: the
  characterization of the mex and the recursive formula for $G_f$.
* `MetaMathlibExt.maximumNimGrundy_div_two_five`, `MetaMathlibExt.maximumNimGrundy_div_two_four`
  and `MetaMathlibExt.maximumNimGrundy_div_two_three`: for the rule function
  $f(x) = \lfloor x/2 \rfloor$, piles of $5$, $4$ and $3$ stones have Grundy numbers $1$, $2$
  and $0$.
* `MetaMathlibExt.maximumNim_sub_div_sub_one_eq`: for $k \ge 2$ and $x$ not a multiple of $k$,
  $x - \lfloor x/k \rfloor - 1 = \lfloor (k-1)x/k \rfloor$. For the rule function
  $f(x) = \lfloor x/k \rfloor$, which is flat at every such $x$, this identifies the position
  $x - f(x) - 1$ with $\lfloor (k-1)x/k \rfloor$.
* `MetaMathlibExt.maximumNimGrundy_div_eq_of_dvd`: for $k \ge 2$ and the rule function
  $f(y) = \lfloor y/k \rfloor$, every positive multiple $x$ of $k$ has Grundy number $x/k$.

## Proof outline

For the floor identity, write $(k-1)x = kx - x$. As $x \ge 1$, the core lemma `Nat.mul_sub_div`
gives $\lfloor (kx - x)/k \rfloor = x - (\lfloor (x-1)/k \rfloor + 1)$, and
$\lfloor (x-1)/k \rfloor = \lfloor x/k \rfloor$ because $k$ does not divide $x$
(`Nat.succ_div_of_not_dvd`).

For the Grundy numbers at multiples of $k$, two facts hold for every rule function $f$: the mex of
a finite set is at most its size, so $G_f(y) \le \min(f(y), y)$; and $G_f(y - v) \ne G_f(y)$
whenever $1 \le v \le \min(f(y), y)$, because the mex is not in the set. Write $x = km$ with
$m \ge 1$, so that the moves from $x$ remove $u$ stones for $1 \le u \le m$. Each option has
$G(km - u) \le \lfloor (km - u)/k \rfloor \le m - 1$. For $1 \le u < u' \le m$ the position
$km - u'$ can be reached from $km - u$, because
$u' - u \le m - u \le \lfloor (km - u)/k \rfloor$, so the $m$ values $G(km - u)$ are pairwise
distinct. They are therefore exactly $0, 1, \dots, m - 1$, and their mex is $m$. The paper
derives the result from the rule $G(x) = f(x)$ at the points where $f(x) > f(x - 1)$; the argument
above proves the case needed here directly.

## Implementation notes

The definitions `maximumNimMex` and `maximumNimGrundy`, their completed results and the theorems
`maximumNim_sub_div_sub_one_eq` and `maximumNimGrundy_div_eq_of_dvd` keep the full names,
statements, definition bodies and docstrings they had in
`WantedExt.Combinatorics.MaximumNimJosephusWanted`, which imports this module. Natural-number
division is the floor, and `¬k ∣ x` says that $x$ is not a multiple of $k$. In the floor identity,
$x \ge 1$, $\lfloor x/k \rfloor + 1 \le x$ and $k - 1 \ge 1$, so every truncated subtraction in the
statement is an ordinary difference. `maximumNimGrundy` allows the moves
$1 \le u \le \min(f(x), x)$, which for the rule function $f(x) = \lfloor x/k \rfloor$ with
$k \ge 1$ are the moves $1 \le u \le f(x)$ of the paper. `maximumNimGrundy_div_eq_of_dvd` keeps
the hypotheses $k \ge 2$ and $1 \le x$ of its wanted statement. Its proof uses the first only
through $k \ge 1$, and the conclusion also holds for $x = 0$, whose Grundy number is $0$.

## References

* Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and Josephus Problem*,
  arXiv:2403.19308v1 (2024) (<https://arxiv.org/abs/2403.19308>). Definition 2.1 in Section 2
  defines the mex and the Grundy numbers. In Section 3, Lemma 3.1(i) states that $G(x) = x/k$ when
  $x$ is a multiple of $k$; the paper derives it from Lemma 2.3(ii), $G(x) = f(x)$ when
  $f(x) > f(x - 1)$, which it states without proof. Equation (1) in the proof of Lemma 3.1 is the
  floor identity, displayed without proof and without the hypothesis that $k$ does not divide $x$,
  which it needs: at a positive multiple $x$ of $k$ the right side exceeds the left side by one.
  The docstrings cite the published version, *Maximum Nim and the Josephus Problem*, INTEGERS 24
  (2024), Article G5.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Minimum excludant of a finite set.** For a finite set $s$ of natural numbers,
$\operatorname{mex}(s)$ is the least natural number that does not belong to $s$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public def maximumNimMex (s : Finset ℕ) : ℕ :=
  Nat.find (show ∃ m, m ∉ s by
    let M := (insert 0 s).max' (by simp)
    refine ⟨M + 1, ?_⟩
    intro h
    have hle : M + 1 ≤ M := Finset.le_max' (insert 0 s) (M + 1) (by simp [h])
    omega)

/-- **Characterization of the minimum excludant.** Let $s$ be a finite set of natural numbers and
$m$ a natural number. Then $\operatorname{mex}(s)$, the least natural number not in $s$, equals $m$
if and only if $m \notin s$ and every natural number $n < m$ lies in $s$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public theorem maximumNimMex_eq_iff (s : Finset ℕ) (m : ℕ) :
    maximumNimMex s = m ↔ m ∉ s ∧ ∀ n < m, n ∈ s := by
  unfold maximumNimMex
  rw [Nat.find_eq_iff]
  simp

/-- **Grundy numbers of Maximum Nim.** For a rule function $f : \mathbb{N} \to \mathbb{N}$, the
Grundy number $G_f(x)$ of a pile of $x$ stones in Maximum Nim is defined by recursion on $x$ as the
mex (least natural number not in the set) of $\{G_f(x - u) : 1 \le u \le \min(f(x), x)\}$, the
Grundy numbers of the positions reachable from $x$ by removing $u$ stones.

Taking $\min(f(x), x)$ makes the definition total; under the source's hypotheses on $f$, which
include $f(0) = 0$, it does not change the legal moves.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public def maximumNimGrundy (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  maximumNimMex <|
    (Finset.Icc 1 (min (f x) x)).attach.image fun u =>
      maximumNimGrundy f (x - u.1)
termination_by x
decreasing_by
  have hu := u.property
  simp only [Finset.mem_Icc] at hu
  omega

/-- **Recursive formula for Maximum Nim Grundy numbers.** For every rule function
$f : \mathbb{N} \to \mathbb{N}$ and every pile size $x \in \mathbb{N}$, the Grundy number $G_f(x)$
of a pile of $x$ stones in Maximum Nim with rule function $f$ equals the mex (least natural number
not in the set) of $\{G_f(x - u) : 1 \le u \le \min(f(x), x)\}$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 2. -/
public theorem maximumNimGrundy_eq (f : ℕ → ℕ) (x : ℕ) :
    maximumNimGrundy f x =
      maximumNimMex ((Finset.Icc 1 (min (f x) x)).attach.image fun u =>
        maximumNimGrundy f (x - u.1)) := by
  rw [maximumNimGrundy]

/-- The `k=2` Grundy calculation starts with `G(0)=0`; this private computation
supports the requested examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_zero : maximumNimGrundy (· / 2) 0 = 0 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num

/-- For the `k=2` rule, `G(1)=0`; this private computation supports the requested
examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_one : maximumNimGrundy (· / 2) 1 = 0 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num

/-- For the `k=2` rule, `G(2)=1`; this private computation supports the requested
examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_two : maximumNimGrundy (· / 2) 2 = 1 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num [maximumNimGrundy_div_two_one]

/-- For the `k=2` rule, `G(3)=0`; this private computation supports the requested
examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_three_aux :
    maximumNimGrundy (· / 2) 3 = 0 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num [maximumNimGrundy_div_two_two]

/-- For the `k=2` rule, `G(4)=2`; this private computation supports the requested
examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_four_aux :
    maximumNimGrundy (· / 2) 4 = 2 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num
  constructor
  · intro x hx₁ hx₂
    interval_cases x <;>
      norm_num [maximumNimGrundy_div_two_three_aux, maximumNimGrundy_div_two_two]
  · intro n hn
    interval_cases n
    · exact ⟨1, by norm_num, maximumNimGrundy_div_two_three_aux⟩
    · exact ⟨2, by norm_num, maximumNimGrundy_div_two_two⟩

/-- For the `k=2` rule, `G(5)=1`; this private computation supports the requested
examples and introduces no deviation.
Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
private theorem maximumNimGrundy_div_two_five_aux :
    maximumNimGrundy (· / 2) 5 = 1 := by
  rw [maximumNimGrundy, maximumNimMex_eq_iff]
  norm_num
  constructor
  · intro x hx₁ hx₂
    interval_cases x <;>
      norm_num [maximumNimGrundy_div_two_four_aux, maximumNimGrundy_div_two_three_aux]
  · exact ⟨2, by norm_num, maximumNimGrundy_div_two_three_aux⟩

/-- **Grundy number of a pile of five in halving Maximum Nim.** In Maximum Nim with rule
function $f(x) = \lfloor x/2 \rfloor$, a pile of $5$ stones has Grundy number $1$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
public theorem maximumNimGrundy_div_two_five : maximumNimGrundy (· / 2) 5 = 1 := by
  exact maximumNimGrundy_div_two_five_aux

/-- **Grundy number of a pile of four in halving Maximum Nim.** In Maximum Nim with rule
function $f(x) = \lfloor x/2 \rfloor$, a pile of $4$ stones has Grundy number $2$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
public theorem maximumNimGrundy_div_two_four : maximumNimGrundy (· / 2) 4 = 2 := by
  exact maximumNimGrundy_div_two_four_aux

/-- **Grundy number of a pile of three in halving Maximum Nim.** In Maximum Nim with rule
function $f(x) = \lfloor x/2 \rfloor$, a pile of $3$ stones has Grundy number $0$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Section 3 (characteristic values). -/
public theorem maximumNimGrundy_div_two_three : maximumNimGrundy (· / 2) 3 = 0 := by
  exact maximumNimGrundy_div_two_three_aux

/-- **Floor identity for non-multiples in Maximum Nim.** Let $k \ge 2$ and $x$ be natural numbers
such that $x$ is not a multiple of $k$. Then
$x - \lfloor x/k \rfloor - 1 = \lfloor (k-1)x/k \rfloor$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 2 (`integers-2024-G5-lem-2`). -/
theorem maximumNim_sub_div_sub_one_eq (k x : ℕ) (hk : 2 ≤ k)
    (hxk : ¬k ∣ x) :
    x - x / k - 1 = (k - 1) * x / k := by
  have hx : x ≠ 0 := by
    rintro rfl
    exact hxk (Nat.dvd_zero k)
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hx
  have ha : a < k * (a + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_mul_of_pos_left (a + 1) (by omega))
  rw [Nat.succ_div_of_not_dvd hxk, Nat.sub_one_mul, Nat.mul_sub_div a k (a + 1) ha, Nat.sub_sub]

/-- The mex of a finite set is at most the size of the set, so a Grundy number is at most the
number $\min(f(y), y)$ of moves from its position. -/
private theorem maximumNimGrundy_le_min_rule (f : ℕ → ℕ) (y : ℕ) :
    maximumNimGrundy f y ≤ min (f y) y := by
  have h := (maximumNimMex_eq_iff _ (maximumNimGrundy f y)).mp (maximumNimGrundy_eq f y).symm
  calc maximumNimGrundy f y = (Finset.range (maximumNimGrundy f y)).card :=
        (Finset.card_range _).symm
    _ ≤ ((Finset.Icc 1 (min (f y) y)).attach.image fun u => maximumNimGrundy f (y - u.1)).card :=
        Finset.card_le_card fun n hn => h.2 n (Finset.mem_range.mp hn)
    _ ≤ (Finset.Icc 1 (min (f y) y)).attach.card := Finset.card_image_le
    _ = min (f y) y := by simp

/-- A position reachable in one move has a Grundy number different from the current one, because
the mex of a set is not in the set. -/
private theorem maximumNimGrundy_sub_ne_of_move (f : ℕ → ℕ) (y v : ℕ) (hv : 1 ≤ v)
    (hvy : v ≤ min (f y) y) : maximumNimGrundy f (y - v) ≠ maximumNimGrundy f y := by
  intro heq
  have h := ((maximumNimMex_eq_iff _ (maximumNimGrundy f y)).mp (maximumNimGrundy_eq f y).symm).1
  exact h (Finset.mem_image.mpr ⟨⟨v, Finset.mem_Icc.mpr ⟨hv, hvy⟩⟩, Finset.mem_attach _ _, heq⟩)

/-- **Maximum Nim Grundy numbers at multiples of the divisor.** Let $k \ge 2$ and let $G$ be
the Grundy number of Maximum Nim with rule function $f(y) = \lfloor y/k \rfloor$. Every positive
multiple $x$ of $k$ satisfies $G(x) = x/k$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 3(i) (`integers-2024-G5-lem-3`). -/
theorem maximumNimGrundy_div_eq_of_dvd (k x : ℕ) (hk : 2 ≤ k)
    (hx : 1 ≤ x) (hkx : k ∣ x) :
    maximumNimGrundy (· / k) x = x / k := by
  obtain ⟨m, rfl⟩ := hkx
  have hk0 : 0 < k := by omega
  have hm : 1 ≤ m := Nat.pos_of_ne_zero fun h => by simp [h] at hx
  have hmk : k * m / k = m := Nat.mul_div_cancel_left m hk0
  have hmin : min (k * m / k) (k * m) = m := by
    rw [hmk]
    exact min_eq_left (Nat.le_mul_of_pos_left m hk0)
  -- Every option `k * m - u` has Grundy number at most `(k * m - u) / k < m`.
  have hlt : ∀ u, 1 ≤ u → u ≤ m → maximumNimGrundy (· / k) (k * m - u) < m := by
    intro u hu hum
    calc maximumNimGrundy (· / k) (k * m - u) ≤ min ((k * m - u) / k) (k * m - u) :=
          maximumNimGrundy_le_min_rule _ _
      _ ≤ (k * m - u) / k := min_le_left _ _
      _ < m := by
        rw [Nat.div_lt_iff_lt_mul hk0, Nat.mul_comm m k]
        have : k ≤ k * m := Nat.le_mul_of_pos_right k hm
        omega
  -- The options have pairwise distinct Grundy numbers: `k * m - u'` is reachable from
  -- `k * m - u` when `u < u'`.
  have hne : ∀ u u', 1 ≤ u → u < u' → u' ≤ m →
      maximumNimGrundy (· / k) (k * m - u') ≠ maximumNimGrundy (· / k) (k * m - u) := by
    intro u u' hu huu' hu'm
    have hmove : u' - u ≤ min ((k * m - u) / k) (k * m - u) := by
      have h₁ : k * (u + (u' - u)) ≤ k * m := Nat.mul_le_mul_left k (by omega)
      have h₂ : u ≤ k * u := Nat.le_mul_of_pos_left u hk0
      rw [Nat.mul_add] at h₁
      refine le_min ?_ (by omega)
      rw [Nat.le_div_iff_mul_le hk0, Nat.mul_comm (u' - u) k]
      omega
    have h := maximumNimGrundy_sub_ne_of_move (· / k) (k * m - u) (u' - u) (by omega) hmove
    rwa [show k * m - u - (u' - u) = k * m - u' by omega] at h
  rw [hmk, maximumNimGrundy_eq, maximumNimMex_eq_iff]
  have hbound : ∀ u ∈ Finset.Icc 1 (min (k * m / k) (k * m)), 1 ≤ u ∧ u ≤ m := by
    intro u hu
    rwa [Finset.mem_Icc, hmin] at hu
  -- The `m` option values lie in `range m` and are distinct, so they fill `range m`.
  have hsub : ((Finset.Icc 1 (min (k * m / k) (k * m))).attach.image
      fun u => maximumNimGrundy (· / k) (k * m - u.1)) ⊆ Finset.range m := by
    intro n hn
    obtain ⟨⟨u, hu⟩, -, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (hlt u (hbound u hu).1 (hbound u hu).2)
  have hinj : Function.Injective fun u : Finset.Icc 1 (min (k * m / k) (k * m)) =>
      maximumNimGrundy (· / k) (k * m - u.1) := by
    rintro ⟨u, hu⟩ ⟨u', hu'⟩ heq
    simp only at heq
    rcases lt_trichotomy u u' with h | h | h
    · exact absurd heq.symm (hne u u' (hbound u hu).1 h (hbound u' hu').2)
    · exact Subtype.ext h
    · exact absurd heq (hne u' u (hbound u' hu').1 h (hbound u hu).2)
  have hcard : ((Finset.Icc 1 (min (k * m / k) (k * m))).attach.image
      fun u => maximumNimGrundy (· / k) (k * m - u.1)).card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, Nat.card_Icc, hmin,
      Nat.add_sub_cancel]
  rw [Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])]
  exact ⟨Finset.notMem_range_self, fun n hn => Finset.mem_range.mpr hn⟩

end

end MetaMathlibExt
