/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.Bitonic

/-!
# Batcher's odd-even merge sort

Batcher's odd-even merge sort (Batcher, *Sorting networks and their applications*, AFIPS 1968;
Knuth, *The Art of Computer Programming*, Volume 3, Section 5.3.4) sorts `2 ^ k` wires with
`(k² - k + 4) 2 ^ k / 4 - 1` comparators. The merger on `2 ^ (k + 1)` wires whose halves are
sorted merges the even wires and the odd wires recursively, then compares wires `2 i + 1` and
`2 i + 2` (`oddEvenMerge`, `finalLayer`); the sorter sorts both halves and merges
(`oddEvenSortN`). The recursion on even and odd wires is expressed by renaming wires
(`relabel`, `runN_relabel`), on the `ℕ`-indexed runner of `Bitonic.lean`.

Main results:

* `oddEvenMerge_merges`: if the two halves hold `a` and `c` zeros followed by ones, the merger
  leaves `a + c` zeros followed by ones. (The even wires receive `⌈a/2⌉ + ⌈c/2⌉` zeros and the
  odd wires `⌊a/2⌋ + ⌊c/2⌋`; these differ by at most `2`, and the last layer fixes the one pair
  that can be out of order.)
* `oddEvenSortN_sorts`: the sorter sorts every `0`-`1` input.
* `oddEvenSorter_sorts`: **the network sorts every input over every linear order**, by the 0-1
  principle.
* `length_oddEvenMerge` (`k 2 ^ k + 1` comparators on `2 ^ (k + 1)` wires) and
  `length_oddEvenSorter` (`4 (length + 1) + k 2 ^ k = (k² + 4) 2 ^ k`).

## Cost model

No `TimeM` cost model: this module measures a network by its comparator count; its depth (at most
`k (k + 1) / 2`) is bounded in `OddEvenDepth.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SortingNetworks.OddEven

open Bitonic

/-! ## Relabeling wires -/

/-- **Relabeling the wires of a comparator list.** Given a map $e : \mathbb{N} \to \mathbb{N}$
and a list of comparators, each a pair $(i, j)$ of wires in $\mathbb{N}$, the relabeled list
replaces every comparator $(i, j)$ by $(e(i), e(j))$ and keeps the order of the list. -/
def relabel (e : ℕ → ℕ) (ps : List (ℕ × ℕ)) : List (ℕ × ℕ) := ps.map fun q => (e q.1, e q.2)

/-- **Running a relabeled network.** Let $\alpha$ be a linearly ordered type and let
$e : \mathbb{N} \to \mathbb{N}$ be injective. For every list of comparators, every
$f : \mathbb{N} \to \alpha$ and every wire $j$, running the list relabeled by $e$ on $f$ gives at
wire $e(j)$ the same value as running the original list on the input $i \mapsto f(e(i))$ gives at
wire $j$. -/
theorem runN_relabel {α : Type*} [LinearOrder α] {e : ℕ → ℕ} (he : Function.Injective e) :
    ∀ (ps : List (ℕ × ℕ)) (f : ℕ → α) (j : ℕ),
      runN (relabel e ps) f (e j) = runN ps (fun i => f (e i)) j
  | [], _, _ => rfl
  | c :: ps, f, j => by
      simp only [relabel, List.map_cons, runN_cons]
      have := runN_relabel he ps (Bitonic.cmp (e c.1) (e c.2) f) j
      unfold relabel at this
      rw [this]
      congr 1
      funext i
      simp only [Bitonic.cmp, he.eq_iff]

/-- **Relabeled networks fix the wires outside the image.** Let $\alpha$ be a linearly ordered
type, $e : \mathbb{N} \to \mathbb{N}$ any map and $f : \mathbb{N} \to \alpha$ an assignment of
values to the wires. For every list of comparators and every wire $x$ that is not of the form
$e(y)$, running the list relabeled by $e$ on $f$ gives the value $f(x)$ at wire $x$. -/
theorem runN_relabel_of_not_mem {α : Type*} [LinearOrder α] {e : ℕ → ℕ} :
    ∀ (ps : List (ℕ × ℕ)) (f : ℕ → α) (x : ℕ), (∀ y, x ≠ e y) → runN (relabel e ps) f x = f x
  | [], _, _, _ => rfl
  | c :: ps, f, x, hx => by
      simp only [relabel, List.map_cons, runN_cons]
      have := runN_relabel_of_not_mem ps (Bitonic.cmp (e c.1) (e c.2) f) x hx
      unfold relabel at this
      rw [this]
      simp only [Bitonic.cmp, hx c.1, hx c.2, ↓reduceIte]

theorem length_relabel (e : ℕ → ℕ) (ps : List (ℕ × ℕ)) : (relabel e ps).length = ps.length :=
  List.length_map _

/-! ## The networks -/

/-- **Last layer of the odd-even merger.** For $k \in \mathbb{N}$, this is the list of comparators
$(2i + 1, 2i + 2)$ for $i = 0, 1, \dots, 2^{k+1} - 2$, in increasing order of $i$. It compares the
neighbouring wires $2i + 1$ and $2i + 2$ and is the last layer of the odd-even merger on
$2^{k+2}$ wires. -/
def finalLayer (k : ℕ) : List (ℕ × ℕ) :=
  (List.range (2 ^ (k + 1) - 1)).map fun i => (2 * i + 1, 2 * i + 2)

/-- **Batcher's odd-even merger.** For $k \in \mathbb{N}$, the odd-even merger on wires
$0, \dots, 2^{k+1} - 1$ is the comparator list defined by recursion on $k$. For $k = 0$ it is the
single comparator $(0, 1)$. For $k + 1$ it is the merger for $k$ with each wire $i$ renamed to
$2i$ (merging the even wires), followed by the merger for $k$ with each wire $i$ renamed to
$2i + 1$ (merging the odd wires), followed by the comparators $(2i + 1, 2i + 2)$ for
$i = 0, 1, \dots, 2^{k+1} - 2$ in increasing order of $i$. -/
def oddEvenMerge : ℕ → List (ℕ × ℕ)
  | 0 => [(0, 1)]
  | k + 1 => relabel (fun i => 2 * i) (oddEvenMerge k) ++
      relabel (fun i => 2 * i + 1) (oddEvenMerge k) ++ finalLayer k

/-- **Batcher's odd-even merge sort.** For $k \in \mathbb{N}$, odd-even merge sort on wires
$0, \dots, 2^k - 1$ is the comparator list defined by recursion on $k$. For $k = 0$ it is empty.
For $k + 1$ it is the sorter for $k$ (sorting wires $0, \dots, 2^k - 1$), followed by the sorter
for $k$ with each wire $i$ renamed to $2^k + i$ (sorting wires $2^k, \dots, 2^{k+1} - 1$),
followed by Batcher's odd-even merger on $2^{k+1}$ wires. -/
def oddEvenSortN : ℕ → List (ℕ × ℕ)
  | 0 => []
  | k + 1 => oddEvenSortN k ++ relabel (fun i => 2 ^ k + i) (oddEvenSortN k) ++ oddEvenMerge k

private theorem runN_finalLayer_aux {α : Type*} [LinearOrder α] (f : ℕ → α) :
    ∀ m x, runN ((List.range m).map fun i => (2 * i + 1, 2 * i + 2)) f x =
      if x % 2 = 1 ∧ x / 2 < m then min (f x) (f (x + 1))
      else if x % 2 = 0 ∧ 0 < x ∧ (x - 2) / 2 < m then max (f (x - 1)) (f x) else f x
  | 0, x => by
      simp only [List.range_zero, List.map_nil, runN_nil]
      split_ifs <;> first | omega | rfl
  | m + 1, x => by
      rw [List.range_succ, List.map_append, runN_append, List.map_singleton, runN_cons, runN_nil]
      have ih := runN_finalLayer_aux f m
      simp only [Bitonic.cmp, ih]
      split_ifs <;> first | omega | (subst_vars; simp_all)

/-- **Output of the last layer of the odd-even merger.** Let $\alpha$ be a linearly ordered type,
$k \in \mathbb{N}$ and $f : \mathbb{N} \to \alpha$ an assignment of values to the wires. Running
the final layer for $k$ on $f$ gives at a wire $x$ the value $\min(f(x), f(x + 1))$ if $x$ is
odd and $\lfloor x / 2 \rfloor < 2^{k+1} - 1$; otherwise the value $\max(f(x - 1), f(x))$ if
$x$ is even, $x > 0$ and $(x - 2) / 2 < 2^{k+1} - 1$; and the value $f(x)$ in all other cases.
In other words, for each $i < 2^{k+1} - 1$ wire $2i + 1$ receives the minimum and wire $2i + 2$
the maximum of the values of $f$ on these two wires, and every other wire keeps its value. -/
theorem runN_finalLayer {α : Type*} [LinearOrder α] (k : ℕ) (f : ℕ → α) (x : ℕ) :
    runN (finalLayer k) f x =
      if x % 2 = 1 ∧ x / 2 < 2 ^ (k + 1) - 1 then min (f x) (f (x + 1))
      else if x % 2 = 0 ∧ 0 < x ∧ (x - 2) / 2 < 2 ^ (k + 1) - 1 then max (f (x - 1)) (f x)
      else f x :=
  runN_finalLayer_aux f _ x

private theorem injective_double : Function.Injective fun i : ℕ => 2 * i :=
  fun a b h => by simp only at h; omega

private theorem injective_double_add_one : Function.Injective fun i : ℕ => 2 * i + 1 :=
  fun a b h => by simp only at h; omega

/-- **The odd-even merger merges.** Let $k \in \mathbb{N}$ and let $f$ assign a Boolean value to
each wire $0, 1, 2, \dots$, with false read as $0$ and true as $1$. Let $a, c \le 2^k$ be such
that wires $0, \dots, 2^k - 1$ hold $a$ zeros followed by ones (wire $i < 2^k$ holds $0$ exactly
when $i < a$) and wires $2^k, \dots, 2^{k+1} - 1$ hold $c$ zeros followed by ones (wire
$2^k + i$, for $i < 2^k$, holds $0$ exactly when $i < c$). Then after Batcher's odd-even merger
on $2^{k+1}$ wires runs on $f$, every wire $j < 2^{k+1}$ holds $0$ exactly when $j < a + c$. -/
theorem oddEvenMerge_merges : ∀ (k : ℕ) (f : ℕ → Bool) (a c : ℕ), a ≤ 2 ^ k → c ≤ 2 ^ k →
    (∀ i < 2 ^ k, f i = decide (a ≤ i)) → (∀ i < 2 ^ k, f (2 ^ k + i) = decide (c ≤ i)) →
    ∀ j < 2 ^ (k + 1), runN (oddEvenMerge k) f j = decide (a + c ≤ j)
  | 0, f, a, c, ha, hc, hf1, hf2, j, hj => by
      have h0 := hf1 0 (by simp)
      have h1 := hf2 0 (by simp)
      simp only [pow_zero, Nat.add_zero] at h0 h1 ha hc
      simp only [oddEvenMerge, runN_cons, runN_nil, Bitonic.cmp]
      have hj' : j = 0 ∨ j = 1 := by simp at hj; omega
      rcases hj' with rfl | rfl
      · simp only [↓reduceIte, h0, h1, Bool.min_eq_and, ← Bool.decide_and, decide_eq_decide]
        omega
      · simp only [one_ne_zero, ↓reduceIte, h0, h1, Bool.max_eq_or, ← Bool.decide_or,
          decide_eq_decide]
        omega
  | k + 1, f, a, c, ha, hc, hf1, hf2, j, hj => by
      set n := 2 ^ (k + 1) with hn
      have h2 : 2 ^ (k + 1 + 1) = 2 * n := by rw [hn, Nat.pow_succ, Nat.mul_comm]
      have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      have hpos := Nat.two_pow_pos k
      rw [oddEvenMerge, runN_append, runN_append]
      set h1 := runN (relabel (fun i => 2 * i) (oddEvenMerge k)) f with hh1
      set h2' := runN (relabel (fun i => 2 * i + 1) (oddEvenMerge k)) h1 with hh2
      -- even wires: the merge of the even halves, `⌈a/2⌉ + ⌈c/2⌉` zeros
      have hev : ∀ i < n, h2' (2 * i) = decide ((a + 1) / 2 + (c + 1) / 2 ≤ i) := by
        intro i hi
        rw [hh2, runN_relabel_of_not_mem _ _ _ (fun y => by omega), hh1,
          runN_relabel injective_double]
        refine oddEvenMerge_merges k _ ((a + 1) / 2) ((c + 1) / 2) (by omega) (by omega)
          (fun i' hi' => ?_) (fun i' hi' => ?_) i (by omega)
        · rw [hf1 (2 * i') (by omega)]
          simp only [decide_eq_decide]
          omega
        · rw [show 2 * (2 ^ k + i') = 2 ^ (k + 1) + 2 * i' by omega, hf2 (2 * i') (by omega)]
          simp only [decide_eq_decide]
          omega
      -- odd wires: the merge of the odd halves, `⌊a/2⌋ + ⌊c/2⌋` zeros
      have hod : ∀ i < n, h2' (2 * i + 1) = decide (a / 2 + c / 2 ≤ i) := by
        intro i hi
        rw [hh2, runN_relabel injective_double_add_one]
        have hodd : ∀ i', h1 (2 * i' + 1) = f (2 * i' + 1) := fun i' => by
          rw [hh1, runN_relabel_of_not_mem _ _ _ (fun y => by omega)]
        simp only [hodd]
        refine oddEvenMerge_merges k _ (a / 2) (c / 2) (by omega) (by omega)
          (fun i' hi' => ?_) (fun i' hi' => ?_) i (by omega)
        · rw [hf1 (2 * i' + 1) (by omega)]
          simp only [decide_eq_decide]
          omega
        · rw [show 2 * (2 ^ k + i') + 1 = 2 ^ (k + 1) + (2 * i' + 1) by omega,
            hf2 (2 * i' + 1) (by omega)]
          simp only [decide_eq_decide]
          omega
      -- the last layer fixes the one possible misplaced pair
      rw [runN_finalLayer, ← hn]
      rw [h2] at hj
      obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
      · by_cases hi0 : i = 0
        · have c1 : ¬((2 * i) % 2 = 1 ∧ 2 * i / 2 < n - 1) := by omega
          have c2 : ¬((2 * i) % 2 = 0 ∧ 0 < 2 * i ∧ (2 * i - 2) / 2 < n - 1) := by omega
          simp only [c1, ↓reduceIte]
          simp only [c2, ↓reduceIte]
          rw [hev i (by omega)]
          simp only [decide_eq_decide]
          omega
        · have c1 : ¬((2 * i) % 2 = 1 ∧ 2 * i / 2 < n - 1) := by omega
          have c2 : (2 * i) % 2 = 0 ∧ 0 < 2 * i ∧ (2 * i - 2) / 2 < n - 1 := by omega
          simp only [c1, ↓reduceIte]
          simp only [c2, and_self, ↓reduceIte, Bool.max_eq_or]
          rw [show 2 * i - 1 = 2 * (i - 1) + 1 by omega, hod (i - 1) (by omega), hev i (by omega)]
          simp only [← Bool.decide_or, decide_eq_decide]
          omega
      · by_cases hlast : i = n - 1
        · subst hlast
          have c1 : ¬((2 * (n - 1) + 1) % 2 = 1 ∧ (2 * (n - 1) + 1) / 2 < n - 1) := by omega
          have c2 : ¬((2 * (n - 1) + 1) % 2 = 0 ∧ 0 < 2 * (n - 1) + 1 ∧
              (2 * (n - 1) + 1 - 2) / 2 < n - 1) := by omega
          simp only [c1, ↓reduceIte]
          simp only [c2, ↓reduceIte]
          rw [hod (n - 1) (by omega)]
          simp only [decide_eq_decide]
          omega
        · have c1 : (2 * i + 1) % 2 = 1 ∧ (2 * i + 1) / 2 < n - 1 := by omega
          simp only [c1, and_self, ↓reduceIte, Bool.min_eq_and]
          rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega, hod i (by omega), hev (i + 1) (by omega)]
          simp only [← Bool.decide_and, decide_eq_decide]
          omega

/-- **Odd-even merge sort sorts every $0$-$1$ input.** Let $k \in \mathbb{N}$ and let $f$ assign a
Boolean value to each wire $0, 1, 2, \dots$, with false read as $0$ and true as $1$. After
Batcher's odd-even merge sort on $2^k$ wires runs on $f$, there is $z \le 2^k$ such that every
wire $j < 2^k$ holds $0$ exactly when $j < z$: wires $0, \dots, 2^k - 1$ hold $z$ zeros followed
by ones. -/
theorem oddEvenSortN_sorts : ∀ (k : ℕ) (f : ℕ → Bool),
    ∃ z ≤ 2 ^ k, ∀ j < 2 ^ k, runN (oddEvenSortN k) f j = decide (z ≤ j)
  | 0, f => by
      refine ⟨if f 0 then 0 else 1, by split_ifs <;> simp, fun j hj => ?_⟩
      have : j = 0 := by simpa using hj
      subst this
      simp only [oddEvenSortN, runN_nil]
      cases f 0 <;> simp
  | k + 1, f => by
      have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [oddEvenSortN, runN_append, runN_append]
      set g1 := runN (oddEvenSortN k) f with hg1
      set g2 := runN (relabel (fun i => 2 ^ k + i) (oddEvenSortN k)) g1 with hg2
      obtain ⟨a, ha, hfa⟩ := oddEvenSortN_sorts k f
      obtain ⟨c, hc, hfc⟩ := oddEvenSortN_sorts k fun i => g1 (2 ^ k + i)
      have hinj : Function.Injective fun i : ℕ => 2 ^ k + i := fun x y h => by simpa using h
      refine ⟨a + c, by omega, fun j hj => oddEvenMerge_merges k g2 a c ha hc
        (fun i hi => ?_) (fun i hi => ?_) j (by omega)⟩
      · rw [hg2, runN_relabel_of_not_mem _ _ _ (fun y => by omega), hg1]
        exact hfa i hi
      · rw [hg2, runN_relabel hinj]
        exact hfc i hi

/-! ## Wires, size, and the network on `2 ^ k` wires -/

/-- **Relabeling keeps comparators within an interval.** Let $ps$ be a list of comparators,
each a pair of natural numbers, that lies within $[l, h)$, and let $e : \mathbb{N} \to \mathbb{N}$
satisfy $l' \le e(x) < h'$ for every $x$ with $l \le x < h$. Then the list obtained from $ps$ by
relabeling its wires by $e$ lies within $[l', h')$. -/
theorem relabel_within {ps : List (ℕ × ℕ)} {lo hi : ℕ} (h : Within ps lo hi) (e : ℕ → ℕ)
    {lo' hi' : ℕ} (he : ∀ x, lo ≤ x → x < hi → lo' ≤ e x ∧ e x < hi') :
    Within (relabel e ps) lo' hi' := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
  have := h r hr
  have h1 := he r.1 this.1 this.2.1
  have h2 := he r.2 this.2.2.1 this.2.2.2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

theorem finalLayer_within (k : ℕ) : Within (finalLayer k) 0 (2 ^ (k + 2)) := by
  intro q hq
  simp only [finalLayer, List.mem_map, List.mem_range] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  simp only
  omega

theorem oddEvenMerge_within : ∀ k, Within (oddEvenMerge k) 0 (2 ^ (k + 1))
  | 0 => by
      intro q hq
      simp only [oddEvenMerge, List.mem_singleton] at hq
      subst hq
      simp
  | k + 1 => by
      have h2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [oddEvenMerge]
      refine (Within.append (Within.append ?_ ?_) (finalLayer_within k))
      · exact relabel_within (oddEvenMerge_within k) _ fun x _ hx => ⟨Nat.zero_le _, by omega⟩
      · exact relabel_within (oddEvenMerge_within k) _ fun x _ hx => ⟨Nat.zero_le _, by omega⟩

theorem oddEvenSortN_within : ∀ k, Within (oddEvenSortN k) 0 (2 ^ k)
  | 0 => fun _ hq => absurd hq List.not_mem_nil
  | k + 1 => by
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [oddEvenSortN]
      refine Within.append (Within.append ?_ ?_) ?_
      · exact (oddEvenSortN_within k).mono (Nat.le_refl _) (by omega)
      · exact relabel_within (oddEvenSortN_within k) _ fun x _ hx => ⟨Nat.zero_le _, by omega⟩
      · exact oddEvenMerge_within k

theorem length_finalLayer (k : ℕ) : (finalLayer k).length = 2 ^ (k + 1) - 1 := by
  simp [finalLayer]

/-- **Size of the odd-even merger.** For every $k \in \mathbb{N}$, Batcher's odd-even merger on
$2^{k+1}$ wires consists of exactly $k \cdot 2^k + 1$ comparators. -/
theorem length_oddEvenMerge : ∀ k, (oddEvenMerge k).length = k * 2 ^ k + 1
  | 0 => rfl
  | k + 1 => by
      have := Nat.two_pow_pos k
      simp only [oddEvenMerge, List.length_append, length_relabel, length_oddEvenMerge k,
        length_finalLayer, Nat.pow_succ]
      rw [Nat.add_mul, Nat.one_mul]
      have : k * 2 ^ k * 2 = k * (2 ^ k * 2) := Nat.mul_assoc _ _ _
      omega

/-- **Size of Batcher's odd-even merge sort.** For every $k \in \mathbb{N}$, the number $L$ of
comparators of Batcher's odd-even merge sort on $2^k$ wires satisfies
$4(L + 1) + k \cdot 2^k = (k^2 + 4) \cdot 2^k$, that is, $L = (k^2 - k + 4) \cdot 2^k / 4 - 1$.

The identity is stated without subtraction or division, and is exact for every $k$. -/
theorem length_oddEvenSortN : ∀ k,
    4 * ((oddEvenSortN k).length + 1) + k * 2 ^ k = (k * k + 4) * 2 ^ k
  | 0 => rfl
  | k + 1 => by
      have ih := length_oddEvenSortN k
      simp only [oddEvenSortN, List.length_append, length_relabel, length_oddEvenMerge k,
        Nat.pow_succ]
      nlinarith [ih]

/-- **Batcher's odd-even merge sorting network.** For $k \in \mathbb{N}$, this is the comparator
network on the $2^k$ wires $0, \dots, 2^k - 1$ given by the comparators of Batcher's odd-even
merge sort on $2^k$ wires, in the same order, with any comparator that touches a wire $\ge 2^k$
dropped. -/
def oddEvenSorter (k : ℕ) : Network (2 ^ k) := ofPairs (2 ^ k) (oddEvenSortN k)

/-- **Batcher's odd-even merge sort sorts every input over every linear order.** For every
$k \in \mathbb{N}$ and every linearly ordered type $\alpha$, Batcher's odd-even merge sorting
network on $2^k$ wires sorts every input over $\alpha$: for every assignment $v$ of elements of
$\alpha$ to the wires $0, \dots, 2^k - 1$, the output of the network on $v$ is monotone in the
wire order.

The proof goes through the 0-1 principle. -/
theorem oddEvenSorter_sorts (k : ℕ) (α : Type*) [LinearOrder α] :
    Sorts (oddEvenSorter k) α := by
  refine sorts_of_sorts_bool (fun v i j hij => ?_) α
  obtain ⟨z, -, hz⟩ := oddEvenSortN_sorts k (extendFalse v)
  have hi := hz i.val (by omega)
  have hj := hz j.val j.isLt
  rw [← ext_run_ofPairs _ (oddEvenSortN_within k)] at hi hj
  simp only [extendFalse, i.isLt, j.isLt, ↓reduceDIte, Fin.eta] at hi hj
  change run (oddEvenSorter k) v i ≤ run (oddEvenSorter k) v j
  rw [oddEvenSorter, hi, hj]
  simp only [Bool.le_iff_imp, decide_eq_true_eq]
  intro h
  have : (i : ℕ) ≤ j := hij
  omega

theorem length_oddEvenSorter (k : ℕ) :
    4 * ((oddEvenSorter k).length + 1) + k * 2 ^ k = (k * k + 4) * 2 ^ k := by
  rw [oddEvenSorter, length_ofPairs _ (oddEvenSortN_within k), length_oddEvenSortN]

end Cslib.Algorithms.Lean.SortingNetworks.OddEven
