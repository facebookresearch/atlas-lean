/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.ZeroOne
public import Mathlib.Tactic.Linarith

/-!
# Batcher's bitonic sorting network

Batcher's bitonic sorter (Batcher, *Sorting networks and their applications*, AFIPS 1968; Knuth,
*The Art of Computer Programming*, Volume 3, Section 5.3.4; the half-cleaner and the bitonic
merger as in CLRS, second edition, Section 27.3) sorts `2 ^ k` wires with `k (k + 1) 2 ^ k / 4`
comparators. It is built from

* the *half-cleaner* on `[b, b + 2 m)`, which compares wire `b + i` with `b + m + i`
  (`halfCleaner`, `runN_halfCleaner`);
* the *bitonic merger* (CLRS's `BITONIC-SORTER`), a half-cleaner followed by mergers on both
  halves (`bitonicMerge`); and
* Batcher's sorter, which sorts the first half up and the second half down, making the whole
  bitonic, then applies the bitonic merger (`bitonicSortN`, with the reversed comparators
  `ps.map swap`). This differs from CLRS's `SORTER` (Section 27.5), which sorts both halves up
  and combines them with `MERGER`, whose first stage compares wire `i` with wire `n - 1 - i`;
  both constructions have the same comparator count.

The networks are built on `ℕ`-indexed wires (`cmp`, `runN`) so the recursion can place blocks at
any offset, and transported to `Fin (2 ^ k)` (`ofPairs`, `bitonicSorter`).

Main results:

* `halfClean_bitonic` (CLRS Lemma 27.3): on a bitonic `0`-`1` input (`IsBitonic`: `0ᵃ1ᵇ0ᶜ` or
  `1ᵃ0ᵇ1ᶜ`) the half-cleaner leaves one half constant (`0`s on top or `1`s at the bottom) and the
  other bitonic.
* `bitonicMerge_sorts`: the bitonic merger sorts every bitonic `0`-`1` input.
* `bitonicSortN_sorts`: the bitonic sorter sorts every `0`-`1` input.
* `bitonicSorter_sorts`: **Batcher's network sorts every input over every linear order**, by the
  0-1 principle (`sorts_of_sorts_bool`).
* `length_bitonicSorter`: it has `k (k + 1) 2 ^ k / 4` comparators
  (`4 * length = k (k + 1) 2 ^ k`); `length_bitonicMerge`: the merger has `k 2 ^ (k - 1)`.

Depth (parallel rounds) is treated in `Depth.lean`: the bitonic sorter has depth at most
`k (k + 1) / 2` (`bitonicSorter_depthLE`), and every sorting network on `n` wires has depth at
least `log₂ n` (`Network.le_two_pow_of_sorts`).

## Cost model

No `TimeM` cost model: this module measures a network by its comparator count
(`length_bitonicSorter`); its depth is measured in `Depth.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SortingNetworks.Bitonic

/-! ## Comparators on `ℕ`-indexed wires -/

section Runner

variable {α : Type*} [LinearOrder α]

/-- **Comparator on natural-number-indexed wires.** Let $\alpha$ be a linear order. For wires
$i, j \in \mathbb{N}$ and an assignment $f$ of values in $\alpha$ to the wires $x \in \mathbb{N}$,
the comparator $(i, j)$ applied to $f$ puts $\min(f(i), f(j))$ on wire $i$, puts
$\max(f(i), f(j))$ on wire $j$ when $j \ne i$, and leaves every other wire unchanged. -/
def cmp (i j : ℕ) (f : ℕ → α) : ℕ → α :=
  fun x => if x = i then min (f i) (f j) else if x = j then max (f i) (f j) else f x

/-- **Running a comparator network on natural-number-indexed wires.** Let $\alpha$ be a
linear order. Given a list $ps$ of comparators, each a pair $(i, j)$ of natural numbers, and
an input $f : \mathbb{N} \to \alpha$ giving the value on each wire, running $ps$ on $f$
applies the comparators of $ps$ to the wire values one after another, from first to last. The
comparator $(i, j)$ puts the minimum of the values on wires $i$ and $j$ on wire $i$ and their
maximum on wire $j$, and leaves the other wires unchanged. -/
def runN (ps : List (ℕ × ℕ)) (f : ℕ → α) : ℕ → α :=
  ps.foldl (fun g c => cmp c.1 c.2 g) f

@[simp] theorem runN_nil (f : ℕ → α) : runN [] f = f := rfl

theorem runN_cons (c : ℕ × ℕ) (ps : List (ℕ × ℕ)) (f : ℕ → α) :
    runN (c :: ps) f = runN ps (cmp c.1 c.2 f) := rfl

theorem runN_append (ps qs : List (ℕ × ℕ)) (f : ℕ → α) :
    runN (ps ++ qs) f = runN qs (runN ps f) := by
  simp [runN, List.foldl_append]

/-- **Comparators within an interval.** A list $ps$ of comparators, each a pair $(i, j)$ of
natural numbers, lies within $[l, h)$ if every comparator $(i, j)$ in $ps$ satisfies
$l \le i < h$ and $l \le j < h$. -/
def Within (ps : List (ℕ × ℕ)) (lo hi : ℕ) : Prop :=
  ∀ p ∈ ps, lo ≤ p.1 ∧ p.1 < hi ∧ lo ≤ p.2 ∧ p.2 < hi

/-- **Locality of comparator networks.** Let $\alpha$ be a linear order and let $ps$ be a list
of comparators $(i, j)$ on $\mathbb{N}$-indexed wires that all lie within $[l, h)$, that is,
$l \le i < h$ and $l \le j < h$ for every $(i, j)$ in $ps$. Then for every input
$f : \mathbb{N} \to \alpha$ and every wire $x$ with $x < l$ or $h \le x$, the value of wire $x$
after running $ps$ on $f$ is $f(x)$. -/
theorem runN_of_not_mem : ∀ {ps : List (ℕ × ℕ)} {lo hi : ℕ}, Within ps lo hi →
    ∀ (f : ℕ → α) (x : ℕ), (x < lo ∨ hi ≤ x) → runN ps f x = f x
  | [], _, _, _, _, _, _ => rfl
  | c :: ps, lo, hi, h, f, x, hx => by
      rw [runN_cons, runN_of_not_mem (fun p hp => h p (List.mem_cons_of_mem _ hp)) _ x hx]
      have hc := h c List.mem_cons_self
      simp only [cmp]
      split_ifs <;> first | omega | rfl

/-- **Constant blocks stay constant.** Let $\alpha$ be a linear order, let $l, h \in \mathbb{N}$,
and let $c$ be a list of comparators on $\mathbb{N}$-indexed wires each of which joins two wires
$x$ with $l \le x < h$. If an input $f : \mathbb{N} \to \alpha$ takes the same value $a$ on
every wire $x$ with $l \le x < h$, then running $c$ on $f$ gives an output that also takes the
value $a$ on every such wire. -/
theorem runN_const : ∀ {ps : List (ℕ × ℕ)} {lo hi : ℕ}, Within ps lo hi →
    ∀ (f : ℕ → α) (a : α), (∀ x, lo ≤ x → x < hi → f x = a) →
    ∀ x, lo ≤ x → x < hi → runN ps f x = a
  | [], _, _, _, _, _, hf => hf
  | c :: ps, lo, hi, h, f, a, hf => by
      rw [runN_cons]
      refine runN_const (fun p hp => h p (List.mem_cons_of_mem _ hp)) _ a fun x h1 h2 => ?_
      have hc := h c List.mem_cons_self
      simp only [cmp]
      rw [hf c.1 hc.1 hc.2.1, hf c.2 hc.2.2.1 hc.2.2.2, min_self, max_self]
      split_ifs
      · rfl
      · rfl
      · exact hf x h1 h2

theorem Within.append {ps qs : List (ℕ × ℕ)} {lo hi : ℕ} (hp : Within ps lo hi)
    (hq : Within qs lo hi) : Within (ps ++ qs) lo hi := by
  intro p hmem
  rcases List.mem_append.1 hmem with h | h
  · exact hp p h
  · exact hq p h

theorem Within.mono {ps : List (ℕ × ℕ)} {lo hi lo' hi' : ℕ} (h : Within ps lo hi)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : Within ps lo' hi' := fun p hp => by
  have := h p hp; omega

end Runner

/-! ## The half-cleaner -/

section HalfCleaner

variable {α : Type*} [LinearOrder α]

/-- **Half-cleaner.** For natural numbers $m$ and $b$, the half-cleaner on the block of wires
$[b, b + 2m)$ is the list of comparators $(b + i, b + m + i)$ for $i = 0, 1, \dots, m - 1$, in
this order: it compares wire $b + i$ with wire $b + m + i$. -/
def halfCleaner (m b : ℕ) : List (ℕ × ℕ) := (List.range m).map fun i => (b + i, b + m + i)

theorem halfCleaner_within (m b : ℕ) : Within (halfCleaner m b) b (b + 2 * m) := by
  intro p hp
  simp only [halfCleaner, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  simp only
  omega

private theorem runN_halfCleaner_aux (m b : ℕ) (f : ℕ → α) :
    ∀ j, j ≤ m → ∀ x, runN ((List.range j).map fun i => (b + i, b + m + i)) f x =
      if b ≤ x ∧ x < b + j then min (f x) (f (x + m))
      else if b + m ≤ x ∧ x < b + m + j then max (f (x - m)) (f x) else f x
  | 0, _, x => by
      simp only [List.range_zero, List.map_nil, runN_nil]
      split_ifs <;> first | omega | rfl
  | j + 1, hj, x => by
      rw [List.range_succ, List.map_append, runN_append, List.map_singleton, runN_cons, runN_nil]
      have ih := runN_halfCleaner_aux m b f j (by omega)
      simp only [cmp, ih]
      have e1 : b + m + j - m = b + j := by omega
      split_ifs <;> first | omega | (subst_vars; simp_all; done) |
        (subst_vars; rw [show b + j + m = b + m + j by omega])

/-- **Output of the half-cleaner.** Let $\alpha$ be a linear order, let $m, b \in \mathbb{N}$, and
let $f : \mathbb{N} \to \alpha$ be an input on $\mathbb{N}$-indexed wires. Running the
half-cleaner on $[b, b + 2m)$ on $f$ puts $\min(f(b + i), f(b + m + i))$ on wire $b + i$ and
$\max(f(b + i), f(b + m + i))$ on wire $b + m + i$ for every $i < m$, and leaves the value $f(x)$
on every wire $x$ outside $[b, b + 2m)$ unchanged. -/
theorem runN_halfCleaner (m b : ℕ) (f : ℕ → α) (x : ℕ) :
    runN (halfCleaner m b) f x =
      if b ≤ x ∧ x < b + m then min (f x) (f (x + m))
      else if b + m ≤ x ∧ x < b + m + m then max (f (x - m)) (f x) else f x :=
  runN_halfCleaner_aux m b f m (Nat.le_refl m) x

end HalfCleaner

/-! ## Bitonic `0`-`1` sequences -/

/-- **Interval indicators.** A sequence $s : \mathbb{N} \to \{0, 1\}$ is an interval indicator
of length $L$ if there are natural numbers $a \le e \le L$ such that for every $i < L$,
$s(i) = 1$ exactly when $a \le i < e$. -/
def IsInterval (s : ℕ → Bool) (L : ℕ) : Prop :=
  ∃ a e, a ≤ e ∧ e ≤ L ∧ ∀ i < L, s i = decide (a ≤ i ∧ i < e)

/-- **Bitonic 0-1 sequences.** A sequence $s : \mathbb{N} \to \{0, 1\}$ is bitonic of length $L$
if either $s$ or its complement $1 - s$ is an interval indicator of length $L$; that is, on the
positions $0, \dots, L - 1$ it has the form $0^a 1^b 0^c$ or $1^a 0^b 1^c$. Values of $s$ at
positions $i \ge L$ are unconstrained. -/
def IsBitonic (s : ℕ → Bool) (L : ℕ) : Prop :=
  IsInterval s L ∨ IsInterval (fun i => !s i) L

theorem IsInterval.congr {s t : ℕ → Bool} {L : ℕ} (h : IsInterval s L)
    (hst : ∀ i < L, s i = t i) : IsInterval t L := by
  obtain ⟨a, e, hae, heL, hs⟩ := h
  exact ⟨a, e, hae, heL, fun i hi => (hst i hi).symm.trans (hs i hi)⟩

theorem IsBitonic.congr {s t : ℕ → Bool} {L : ℕ} (h : IsBitonic s L)
    (hst : ∀ i < L, s i = t i) : IsBitonic t L := by
  rcases h with h | h
  · exact Or.inl (h.congr hst)
  · exact Or.inr (h.congr fun i hi => by simp only [hst i hi])

theorem IsBitonic.not {s : ℕ → Bool} {L : ℕ} (h : IsBitonic s L) :
    IsBitonic (fun i => !s i) L := by
  rcases h with h | h
  · exact Or.inr (h.congr fun i _ => by simp)
  · exact Or.inl h

/-- **The half-cleaner lemma** for an interval indicator (CLRS Lemma 27.3): either the minima
are all `0` and the maxima form a bitonic sequence, or the maxima are all `1` and the minima
form a bitonic sequence. -/
private theorem halfClean_interval {s : ℕ → Bool} {m : ℕ} (h : IsInterval s (2 * m)) :
    ((∀ i < m, (s i && s (i + m)) = false) ∧ IsBitonic (fun i => s i || s (i + m)) m) ∨
    ((∀ i < m, (s i || s (i + m)) = true) ∧ IsBitonic (fun i => s i && s (i + m)) m) := by
  obtain ⟨a, e, hae, heL, hs⟩ := h
  have hv : ∀ i < m, s i = decide (a ≤ i ∧ i < e) ∧ s (i + m) = decide (a ≤ i + m ∧ i + m < e) :=
    fun i hi => ⟨hs i (by omega), hs (i + m) (by omega)⟩
  by_cases hb : e ≤ a + m
  · left
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [(hv i hi).1, (hv i hi).2]
      rw [Bool.and_eq_false_iff]
      by_cases h1 : a ≤ i ∧ i < e
      · right; simp only [decide_eq_false_iff_not]; omega
      · left; simp only [decide_eq_false_iff_not]; exact h1
    · by_cases h1 : e ≤ m
      · refine Or.inl ⟨a, e, hae, h1, fun i hi => ?_⟩
        beta_reduce
        rw [(hv i hi).1, (hv i hi).2, Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega
      · by_cases h2 : m ≤ a
        · refine Or.inl ⟨a - m, e - m, by omega, by omega, fun i hi => ?_⟩
          beta_reduce
          rw [(hv i hi).1, (hv i hi).2, Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          omega
        · refine Or.inr ⟨e - m, a, by omega, by omega, fun i hi => ?_⟩
          beta_reduce
          rw [(hv i hi).1, (hv i hi).2, Bool.eq_iff_iff]
          simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
            decide_eq_true_eq]
          omega
  · right
    refine ⟨fun i hi => ?_, Or.inl ⟨a, e - m, by omega, by omega, fun i hi => ?_⟩⟩
    · rw [(hv i hi).1, (hv i hi).2, Bool.or_eq_true]
      by_cases h1 : a ≤ i
      · left; simp only [decide_eq_true_eq]; omega
      · right; simp only [decide_eq_true_eq]; omega
    · beta_reduce
      rw [(hv i hi).1, (hv i hi).2, Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega

/-- **The half-cleaner lemma.** Let $m \in \mathbb{N}$ and let $s_0, s_1, \dots, s_{2m-1}$ be a
bitonic sequence of Booleans, ordered by $\mathrm{false} < \mathrm{true}$. For $i < m$ put
$\ell_i = \min(s_i, s_{i+m})$ and $u_i = \max(s_i, s_{i+m})$. Then either $\ell_i = \mathrm{false}$
for every $i < m$ and $u_0, \dots, u_{m-1}$ is bitonic, or $u_i = \mathrm{true}$ for every
$i < m$ and $\ell_0, \dots, \ell_{m-1}$ is bitonic.

The $\ell_i$ and $u_i$ are the outputs of the half-cleaner on $2m$ wires. This is CLRS Lemma 27.3
for bitonic $0$-$1$ sequences. -/
theorem halfClean_bitonic {s : ℕ → Bool} {m : ℕ} (h : IsBitonic s (2 * m)) :
    ((∀ i < m, (s i && s (i + m)) = false) ∧ IsBitonic (fun i => s i || s (i + m)) m) ∨
    ((∀ i < m, (s i || s (i + m)) = true) ∧ IsBitonic (fun i => s i && s (i + m)) m) := by
  rcases h with h | h
  · exact halfClean_interval h
  · -- complementing swaps the minima and the maxima
    rcases halfClean_interval h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inr ⟨fun i hi => ?_, ?_⟩
      · have := h1 i hi
        cases hs : s i <;> cases hs' : s (i + m) <;> simp_all
      · exact h2.not.congr fun i _ => by cases s i <;> cases s (i + m) <;> rfl
    · refine Or.inl ⟨fun i hi => ?_, ?_⟩
      · have := h1 i hi
        cases hs : s i <;> cases hs' : s (i + m) <;> simp_all
      · exact h2.not.congr fun i _ => by cases s i <;> cases s (i + m) <;> rfl

/-! ## The bitonic merger -/

/-- **Sorted on a block.** A Boolean sequence $g : \mathbb{N} \to \mathrm{Bool}$ is sorted on
the block $[b, b + L)$ if $g(b + i) \le g(b + j)$ for all $i \le j < L$, where Booleans are
ordered by $\mathrm{false} < \mathrm{true}$. -/
def SortedOn (g : ℕ → Bool) (b L : ℕ) : Prop := ∀ i j, i ≤ j → j < L → g (b + i) ≤ g (b + j)

/-- **Bitonic merger.** The bitonic merger on the block of wires $[b, b + 2^k)$ is the list of
comparators defined by recursion on $k$. For $k = 0$ it is empty. On the block $[b, b + 2^{k+1})$
it is the half-cleaner on $[b, b + 2^{k+1})$, followed by the bitonic merger on $[b, b + 2^k)$,
followed by the bitonic merger on $[b + 2^k, b + 2^{k+1})$.

This is CLRS's `BITONIC-SORTER`. -/
def bitonicMerge : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | k + 1, b => halfCleaner (2 ^ k) b ++ bitonicMerge k b ++ bitonicMerge k (b + 2 ^ k)

theorem bitonicMerge_within : ∀ k b, Within (bitonicMerge k b) b (b + 2 ^ k)
  | 0, _ => fun _ hp => absurd hp List.not_mem_nil
  | k + 1, b => by
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [bitonicMerge, h2]
      refine ((halfCleaner_within _ b).append ?_).append ?_
      · exact (bitonicMerge_within k b).mono (Nat.le_refl _) (by omega)
      · exact (bitonicMerge_within k (b + 2 ^ k)).mono (by omega) (by omega)

/-- **The bitonic merger sorts every bitonic `0`-`1` input.** Let $k, b \in \mathbb{N}$ and let $f$
assign a Boolean value to each wire $x \in \mathbb{N}$, with Booleans ordered by
$\mathrm{false} < \mathrm{true}$. If the sequence $f(b), f(b + 1), \dots, f(b + 2^k - 1)$ is
bitonic, then running the bitonic merger on the block $[b, b + 2^k)$ on $f$ gives an assignment
$g$ that is sorted on that block: $g(b + i) \le g(b + j)$ whenever $i \le j < 2^k$.

This is the correctness of CLRS's `BITONIC-SORTER`, proved by recursion on the half-cleaner
lemma. -/
theorem bitonicMerge_sorts : ∀ (k b : ℕ) (f : ℕ → Bool), IsBitonic (fun i => f (b + i)) (2 ^ k) →
    SortedOn (runN (bitonicMerge k b) f) b (2 ^ k)
  | 0, b, f, _ => fun i j hij hj => by
      have : i = j := by simp at hj; omega
      subst this; exact le_refl _
  | k + 1, b, f, hf => by
      set m := 2 ^ k with hm
      have h2 : 2 ^ (k + 1) = 2 * m := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [h2] at hf ⊢
      rw [bitonicMerge, ← hm, runN_append, runN_append]
      set g := runN (halfCleaner m b) f with hg
      have hgt : ∀ i < m, g (b + i) = (f (b + i) && f (b + i + m)) := fun i hi => by
        have c1 : b ≤ b + i ∧ b + i < b + m := by omega
        rw [hg, runN_halfCleaner]; simp only [c1, and_self, ↓reduceIte]; rfl
      have hgb : ∀ i < m, g (b + m + i) = (f (b + i) || f (b + i + m)) := fun i hi => by
        have c1 : ¬(b ≤ b + m + i ∧ b + m + i < b + m) := by omega
        have c2 : b + m ≤ b + m + i ∧ b + m + i < b + m + m := by omega
        rw [hg, runN_halfCleaner]
        simp only [c1, c2, and_self, ↓reduceIte]
        rw [show b + m + i - m = b + i by omega, show b + i + m = b + m + i by omega]; rfl
      have W1 := bitonicMerge_within k b
      have W2 := bitonicMerge_within k (b + m)
      set h1 := runN (bitonicMerge k b) g with hh1
      have hc := halfClean_bitonic (s := fun i => f (b + i)) (m := m) hf
      simp only [show ∀ i, b + (i + m) = b + i + m from fun i => by omega] at hc
      rcases hc with ⟨htop, hbot⟩ | ⟨hbot, htop⟩
      · -- minima all `0`: the top half stays `0`, the bottom half is sorted
        have hz : ∀ x, b ≤ x → x < b + m → h1 x = false := runN_const W1 g false
          fun x h1 h2 => by
            obtain ⟨i, rfl⟩ : ∃ i, x = b + i := ⟨x - b, by omega⟩
            rw [hgt i (by omega)]; exact htop i (by omega)
        have hB : IsBitonic (fun i => h1 (b + m + i)) m := hbot.congr fun i hi => by
          rw [hh1, runN_of_not_mem W1 g _ (Or.inr (by omega)), hgb i hi]
        have hs := bitonicMerge_sorts k (b + m) h1 hB
        intro i j hij hj
        by_cases hi : i < m
        · rw [runN_of_not_mem W2 h1 _ (Or.inl (by omega)), hz _ (by omega) (by omega)]
          exact Bool.false_le _
        · have := hs (i - m) (j - m) (by omega) (by omega)
          rwa [show b + m + (i - m) = b + i by omega, show b + m + (j - m) = b + j by omega]
            at this
      · -- maxima all `1`: the top half is sorted, the bottom half stays `1`
        have hT : IsBitonic (fun i => g (b + i)) m := htop.congr fun i hi => by rw [hgt i hi]
        have hs := bitonicMerge_sorts k b g hT
        have ho : ∀ x, b + m ≤ x → x < b + m + m → h1 x = true := fun x h1' h2' => by
          obtain ⟨i, rfl⟩ : ∃ i, x = b + m + i := ⟨x - (b + m), by omega⟩
          rw [hh1, runN_of_not_mem W1 g _ (Or.inr (by omega)), hgb i (by omega)]
          exact hbot i (by omega)
        have hz := runN_const W2 h1 true ho
        intro i j hij hj
        by_cases hj' : j < m
        · rw [runN_of_not_mem W2 h1 _ (Or.inl (by omega)),
            runN_of_not_mem W2 h1 _ (Or.inl (by omega))]
          exact hs i j hij hj'
        · rw [hz (b + j) (by omega) (by omega)]
          exact Bool.le_true _

/-! ## The bitonic sorter -/

/-- **Reversing the comparators conjugates the network by complement on Booleans.** Let $ps$ be
a list of comparators on $\mathbb{N}$-indexed wires and let $ps'$ be obtained by replacing each
comparator $(i, j)$ in $ps$ by $(j, i)$. For every input $f : \mathbb{N} \to \mathrm{Bool}$ and
every wire $x$, the value of wire $x$ after running $ps'$ on $f$ is the negation of the value of
wire $x$ after running $ps$ on the complemented input $y \mapsto \lnot f(y)$. -/
theorem runN_swap : ∀ (ps : List (ℕ × ℕ)) (f : ℕ → Bool) (x : ℕ),
    runN (ps.map Prod.swap) f x = !runN ps (fun y => !f y) x
  | [], f, x => by simp
  | c :: ps, f, x => by
      rw [List.map_cons, runN_cons, runN_cons, runN_swap ps]
      congr 2
      funext y
      simp only [cmp, Prod.fst_swap, Prod.snd_swap, Bool.min_eq_and, Bool.max_eq_or]
      by_cases h1 : y = c.1 <;> by_cases h2 : y = c.2
      · subst h1; simp only [h2, ↓reduceIte]
        cases f c.1 <;> cases f c.2 <;> simp_all
      · have h12 : c.2 ≠ c.1 := fun h => h2 (h1.trans h.symm)
        simp only [h1, Ne.symm h12, ↓reduceIte]
        cases f c.1 <;> cases f c.2 <;> rfl
      · have h12 : c.2 ≠ c.1 := fun h => h1 (h2.trans h)
        simp only [h2, h12, ↓reduceIte]
        cases f c.1 <;> cases f c.2 <;> rfl
      · simp only [h1, h2, ↓reduceIte]

theorem within_swap {ps : List (ℕ × ℕ)} {lo hi : ℕ} (h : Within ps lo hi) :
    Within (ps.map Prod.swap) lo hi := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  have := h q hq
  simp only [Prod.fst_swap, Prod.snd_swap]
  omega

/-- A sorted `0`-`1` block is `0`s followed by `1`s. -/
private theorem exists_threshold {s : ℕ → Bool} :
    ∀ {L : ℕ}, (∀ i j, i ≤ j → j < L → s i ≤ s j) → ∃ p ≤ L, ∀ i < L, s i = decide (p ≤ i)
  | 0, _ => ⟨0, le_refl _, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | L + 1, h => by
      obtain ⟨p, hp, hs⟩ := exists_threshold (L := L) fun i j hij hj => h i j hij (by omega)
      by_cases hpL : p < L
      · refine ⟨p, by omega, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact hs i hi
        · have h1 := hs (i - 1) (by omega)
          have h2 := h (i - 1) i (by omega) (by omega)
          have : s (i - 1) = true := by rw [h1]; simp only [decide_eq_true_eq]; omega
          rw [this] at h2
          have : s i = true := by revert h2; cases s i <;> simp
          rw [this]; exact (decide_eq_true (by omega)).symm
      · cases hsL : s L
        · refine ⟨L + 1, le_refl _, fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [hs i hi]; simp only [decide_eq_decide]; omega
          · rw [hsL]; simp only [Bool.false_eq, decide_eq_false_iff_not]; omega
        · refine ⟨L, by omega, fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [hs i hi]; simp only [decide_eq_decide]; omega
          · rw [hsL]; simp

/-- **Batcher's bitonic sorter on a block of wires.** A comparator $(i, j)$ puts the minimum of
the values on wires $i$ and $j$ on wire $i$ and the maximum on wire $j$. Batcher's bitonic sorter
on the block of wires $[b, b + 2^k)$ is the list of comparators defined by recursion on $k$. For
$k = 0$ it is empty. On the block $[b, b + 2^{k+1})$ it is Batcher's bitonic sorter on
$[b, b + 2^k)$, followed by Batcher's bitonic sorter on $[b + 2^k, b + 2^{k+1})$ with every
comparator $(i, j)$ replaced by $(j, i)$, followed by the bitonic merger on $[b, b + 2^{k+1})$.

Reversing the comparators makes the second half sort downwards, so the merger receives a bitonic
sequence. (CLRS's `SORTER` instead sorts both halves up and uses `MERGER`.) -/
def bitonicSortN : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | k + 1, b => bitonicSortN k b ++ (bitonicSortN k (b + 2 ^ k)).map Prod.swap ++
      bitonicMerge (k + 1) b

theorem bitonicSortN_within : ∀ k b, Within (bitonicSortN k b) b (b + 2 ^ k)
  | 0, _ => fun _ hp => absurd hp List.not_mem_nil
  | k + 1, b => by
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [bitonicSortN]
      refine (Within.append ?_ ?_).append (bitonicMerge_within (k + 1) b)
      · exact (bitonicSortN_within k b).mono (Nat.le_refl _) (by omega)
      · exact within_swap ((bitonicSortN_within k (b + 2 ^ k)).mono (by omega) (by omega))

/-- **The bitonic sorter sorts every `0`-`1` input.** Let $k, b \in \mathbb{N}$ and let $f$ assign
a Boolean value to each wire $x \in \mathbb{N}$, with Booleans ordered by
$\mathrm{false} < \mathrm{true}$. Running Batcher's bitonic sorter on the block $[b, b + 2^k)$
on $f$ gives an assignment $g$ that is sorted on that block: $g(b + i) \le g(b + j)$ whenever
$i \le j < 2^k$. -/
theorem bitonicSortN_sorts : ∀ (k b : ℕ) (f : ℕ → Bool),
    SortedOn (runN (bitonicSortN k b) f) b (2 ^ k)
  | 0, b, f => fun i j hij hj => by
      have : i = j := by simp at hj; omega
      subst this; exact le_refl _
  | k + 1, b, f => by
      set m := 2 ^ k with hm
      have h2 : 2 ^ (k + 1) = 2 * m := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [bitonicSortN, ← hm, runN_append, runN_append]
      set g1 := runN (bitonicSortN k b) f with hg1
      set g2 := runN ((bitonicSortN k (b + m)).map Prod.swap) g1 with hg2
      have W2 := within_swap (bitonicSortN_within k (b + m))
      -- the first half is sorted up
      have hup : ∀ i j, i ≤ j → j < m → g2 (b + i) ≤ g2 (b + j) := fun i j hij hj => by
        rw [hg2, runN_of_not_mem W2 g1 _ (Or.inl (by omega)),
          runN_of_not_mem W2 g1 _ (Or.inl (by omega))]
        exact bitonicSortN_sorts k b f i j hij hj
      -- the second half is sorted down
      have hdown : ∀ i j, i ≤ j → j < m → g2 (b + m + j) ≤ g2 (b + m + i) := fun i j hij hj => by
        rw [hg2, runN_swap, runN_swap]
        have := bitonicSortN_sorts k (b + m) (fun y => !g1 y) i j hij hj
        revert this
        cases runN (bitonicSortN k (b + m)) (fun y => !g1 y) (b + m + i) <;>
          cases runN (bitonicSortN k (b + m)) (fun y => !g1 y) (b + m + j) <;> simp
      obtain ⟨p, hp, hps⟩ := exists_threshold (s := fun i => g2 (b + i)) (L := m) hup
      obtain ⟨q, hq, hqs⟩ := exists_threshold (s := fun i => !g2 (b + m + i)) (L := m)
        fun i j hij hj => by
          have := hdown i j hij hj
          revert this; cases g2 (b + m + i) <;> cases g2 (b + m + j) <;> simp
      have hB : IsBitonic (fun i => g2 (b + i)) (2 * m) := Or.inl ⟨p, m + q, by omega, by omega,
        fun i hi => by
          beta_reduce
          by_cases him : i < m
          · rw [hps i him]; simp only [decide_eq_decide]; omega
          · have := hqs (i - m) (by omega)
            simp only [show b + m + (i - m) = b + i by omega] at this
            rw [show g2 (b + i) = !!g2 (b + i) by simp, this, Bool.eq_iff_iff]
            simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
            omega⟩
      rw [h2] at ⊢
      have := bitonicMerge_sorts (k + 1) b g2 (by rw [h2]; exact hB)
      rwa [h2] at this

/-! ## Sizes -/

/-- **Size of the half-cleaner.** For all natural numbers $m$ and $b$, the half-cleaner on the
block of wires $[b, b + 2m)$ has exactly $m$ comparators. -/
theorem length_halfCleaner (m b : ℕ) : (halfCleaner m b).length = m := by
  simp [halfCleaner]

/-- **Size of the bitonic merger.** For all natural numbers $k$ and $b$, the bitonic merger on
the block of wires $[b, b + 2^k)$ has $k \cdot 2^{k-1}$ comparators; precisely, twice its number
of comparators equals $k \cdot 2^k$. -/
theorem length_bitonicMerge : ∀ k b, 2 * (bitonicMerge k b).length = k * 2 ^ k
  | 0, _ => rfl
  | k + 1, b => by
      have h1 := length_bitonicMerge k b
      have h2 := length_bitonicMerge k (b + 2 ^ k)
      simp only [bitonicMerge, List.length_append, length_halfCleaner, Nat.pow_succ]
      linarith

/-- **Size of the bitonic sorter on a block of wires.** For all natural numbers $k$ and $b$, the
bitonic sorter on the block of $\mathbb{N}$-indexed wires $[b, b + 2^k)$ has $k(k+1)2^k/4$
comparators; precisely, four times its number of comparators equals $k(k+1)2^k$. -/
theorem length_bitonicSortN : ∀ k b, 4 * (bitonicSortN k b).length = k * (k + 1) * 2 ^ k
  | 0, _ => rfl
  | k + 1, b => by
      have h1 := length_bitonicSortN k b
      have h2 := length_bitonicSortN k (b + 2 ^ k)
      have h3 := length_bitonicMerge (k + 1) b
      simp only [bitonicSortN, List.length_append, List.length_map] at h3 ⊢
      rw [Nat.pow_succ] at h3 ⊢
      linarith

/-! ## The network on `2 ^ k` wires -/

/-- **Restricting comparators to finitely many wires.** For a natural number $N$ and a list of
comparators on wires indexed by $\mathbb{N}$, this is the network on the $N$ wires
$0, \dots, N - 1$ that keeps, in their original order, the comparators $(i, j)$ with $i < N$
and $j < N$, and drops all the others. -/
def ofPairs (N : ℕ) (ps : List (ℕ × ℕ)) : Network N :=
  ps.filterMap fun p => if h : p.1 < N ∧ p.2 < N then some (⟨p.1, h.1⟩, ⟨p.2, h.2⟩) else none

/-- **Extension of a Boolean vector by false.** For $N \in \mathbb{N}$ and a Boolean vector
$v = (v_0, \dots, v_{N-1})$, its extension by $\mathrm{false}$ is the function on $\mathbb{N}$
that takes the value $v_j$ at each $j < N$ and the value $\mathrm{false}$ at each $j \ge N$. -/
def extendFalse {N : ℕ} (v : Fin N → Bool) : ℕ → Bool :=
  fun j => if h : j < N then v ⟨j, h⟩ else false

private theorem ext_comparator {N : ℕ} (i j : Fin N) (v : Fin N → Bool) :
    extendFalse (comparator i j v) = cmp i.val j.val (extendFalse v) := by
  funext x
  simp only [extendFalse, cmp, comparator, i.isLt, j.isLt, ↓reduceDIte]
  by_cases hx : x < N
  · simp only [hx, ↓reduceDIte, Fin.ext_iff]
  · have h1 : x ≠ i.val := fun h => hx (h ▸ i.isLt)
    have h2 : x ≠ j.val := fun h => hx (h ▸ j.isLt)
    simp only [hx, ↓reduceDIte, h1, h2, ↓reduceIte]

/-- **Transported comparator lists agree with the original on Boolean inputs.** Let
$N \in \mathbb{N}$ and let $P$ be a list of comparators on natural-number-indexed wires, each of
which joins two wires below $N$. For every Boolean input $v$ on the wires $0, \dots, N - 1$, run
the network on $N$ wires obtained from $P$ on $v$ and extend its output by $\mathrm{false}$ to
all wires in $\mathbb{N}$; the result equals the result of running $P$ on the extension of $v$ by
$\mathrm{false}$. -/
theorem ext_run_ofPairs {N : ℕ} : ∀ (ps : List (ℕ × ℕ)), Within ps 0 N →
    ∀ v : Fin N → Bool, extendFalse (run (ofPairs N ps) v) = runN ps (extendFalse v)
  | [], _, _ => rfl
  | c :: ps, h, v => by
      have hc := h c List.mem_cons_self
      have hps : Within ps 0 N := fun p hp => h p (List.mem_cons_of_mem _ hp)
      have hcN : c.1 < N ∧ c.2 < N := ⟨hc.2.1, hc.2.2.2⟩
      simp only [ofPairs, List.filterMap_cons, hcN, and_self, ↓reduceDIte]
      change extendFalse (run (ofPairs N ps) (comparator _ _ v)) = _
      rw [ext_run_ofPairs ps hps, ext_comparator, runN_cons]

theorem length_ofPairs {N : ℕ} : ∀ (ps : List (ℕ × ℕ)), Within ps 0 N →
    (ofPairs N ps).length = ps.length
  | [], _ => rfl
  | c :: ps, h => by
      have hc := h c List.mem_cons_self
      have hcN : c.1 < N ∧ c.2 < N := ⟨hc.2.1, hc.2.2.2⟩
      simp only [ofPairs, List.filterMap_cons, hcN, and_self, ↓reduceDIte, List.length_cons]
      exact congrArg (· + 1) (length_ofPairs ps fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- **Batcher's bitonic sorting network.** For $k \in \mathbb{N}$, Batcher's bitonic sorting
network on $2^k$ wires is the comparator network on the wires $0, 1, \dots, 2^k - 1$ made of the
comparators of Batcher's bitonic sorter on the block $[0, 2^k)$ that join two wires below $2^k$
(in fact all of them), applied in the same order. -/
def bitonicSorter (k : ℕ) : Network (2 ^ k) := ofPairs (2 ^ k) (bitonicSortN k 0)

theorem bitonicSortN_within_zero (k : ℕ) : Within (bitonicSortN k 0) 0 (2 ^ k) := by
  simpa using bitonicSortN_within k 0

/-- **Batcher's bitonic sorter sorts every input over every linear order.** For every
$k \in \mathbb{N}$ and every linearly ordered type $\alpha$, Batcher's bitonic sorting network on
$2^k$ wires sorts inputs over $\alpha$: for every assignment $v$ of elements of $\alpha$ to the
wires $0, 1, \dots, 2^k - 1$, the output of the network on $v$ is monotone in the wire order.

The proof goes through the 0-1 principle. -/
theorem bitonicSorter_sorts (k : ℕ) (α : Type*) [LinearOrder α] : Sorts (bitonicSorter k) α := by
  refine sorts_of_sorts_bool (fun v i j hij => ?_) α
  have hs := bitonicSortN_sorts k 0 (extendFalse v) i.val j.val hij j.isLt
  rw [← ext_run_ofPairs _ (bitonicSortN_within_zero k)] at hs
  simpa [extendFalse, bitonicSorter] using hs

/-- **Comparator count of Batcher's bitonic sorter.** For every natural number $k$, Batcher's
bitonic sorting network on $2^k$ wires has $k(k+1)2^k/4$ comparators; precisely, four times its
number of comparators equals $k(k+1)2^k$. -/
theorem length_bitonicSorter (k : ℕ) : 4 * (bitonicSorter k).length = k * (k + 1) * 2 ^ k := by
  rw [bitonicSorter, length_ofPairs _ (bitonicSortN_within_zero k), length_bitonicSortN]

end Cslib.Algorithms.Lean.SortingNetworks.Bitonic
