/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Iterate
import Mathlib.Order.WellFounded

/-!
# Prefix counts of generalized Hofstadter words

This module defines the generalized Hofstadter functions and their substitution words.
For the fixed point of `k ↦ k 1`, `i ↦ i + 1`, we compare the number of ones in
equal-length prefixes for consecutive alphabet sizes.

The proof follows the simultaneous comparison of substitution lengths in Section 7 of
Letouzey, Li, and Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H,
and Beyond*. Counting the blocks in each prefix then gives the order of the one counts.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fuel-bounded generalized Hofstadter recursion.** For natural numbers $k$, $p$ and $n$, the
value $A_k(p, n)$ is defined by recursion on the fuel $p$, which bounds the recursion depth:
$A_k(0, n) = 0$ and $A_k(p + 1, n) = n - g^k(n - 1)$, where $g^k$ is the $k$-fold iterate of the
function $g(m) = A_k(p, m)$ and both subtractions are truncated at $0$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.4 (Rocq definition `recf`). -/
def hofstadterFAux (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | p + 1, n => n - (hofstadterFAux k p)^[k] (n - 1)

/-- **Generalized Hofstadter function.** For a natural number $k$, the function
$F_k : \mathbb{N} \to \mathbb{N}$ is given by $F_k(0) = 0$ and $F_k(n) = n - F_k^k(n - 1)$ for
$n \ge 1$, where $F_k^k$ is the $k$-fold iterate of $F_k$ (the identity when $k = 0$).

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.1. -/
def hofstadterF (k n : ℕ) : ℕ :=
  hofstadterFAux k n n

/-- **The fuel-bounded Hofstadter recursion is bounded by its argument.** For all natural numbers
$k$, $p$ and $n$, the fuel-bounded value $A_k(p, n)$ of the generalized Hofstadter recursion
satisfies $A_k(p, n) \le n$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.1 (`0 ≤ F_k(n) ≤ n`). -/
theorem hofstadterFAux_le (k p n : ℕ) : hofstadterFAux k p n ≤ n := by
  cases p with
  | zero => simp [hofstadterFAux]
  | succ p => simp only [hofstadterFAux]; omega

private theorem iterate_eq_of_eqOn {f g : ℕ → ℕ} (N : ℕ) (hf : ∀ m, f m ≤ m)
    (hfg : ∀ m ≤ N, f m = g m) : ∀ j x, x ≤ N → f^[j] x = g^[j] x := by
  intro j
  induction j with
  | zero => intro x _; rfl
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hfg x hx]
    exact ih _ ((hf x).trans hx)

private theorem hofstadterFAux_succ_eq (k : ℕ) :
    ∀ p n, n ≤ p → hofstadterFAux k (p + 1) n = hofstadterFAux k p n := by
  intro p
  induction p with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp [hofstadterFAux]
  | succ p ih =>
    intro n hn
    change n - (hofstadterFAux k (p + 1))^[k] (n - 1) = n - (hofstadterFAux k p)^[k] (n - 1)
    rw [iterate_eq_of_eqOn p (hofstadterFAux_le k (p + 1)) ih k (n - 1) (by omega)]

private theorem hofstadterFAux_eq_of_le (k : ℕ) {p n : ℕ} (h : n ≤ p) :
    hofstadterFAux k p n = hofstadterF k n := by
  induction p, h using Nat.le_induction with
  | base => rfl
  | succ p hnp ih => rw [hofstadterFAux_succ_eq k p n hnp, ih]

/-- **The generalized Hofstadter functions vanish at zero.** For every natural number $k$, the
generalized Hofstadter function $F_k$ satisfies $F_k(0) = 0$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.1. -/
theorem hofstadterF_zero (k : ℕ) : hofstadterF k 0 = 0 := rfl

/-- **Recursion for the generalized Hofstadter function.** For every $k \ge 0$ and every $n \ge 1$,
the generalized Hofstadter function $F_k$ satisfies $F_k(n) = n - F_k^k(n - 1)$, where $F_k^k$
is the $k$-fold iterate of $F_k$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.1. -/
theorem hofstadterF_eq (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    hofstadterF k n = n - (hofstadterF k)^[k] (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  change m + 1 - (hofstadterFAux k m)^[k] (m + 1 - 1) = _
  rw [iterate_eq_of_eqOn m (hofstadterFAux_le k m) (fun x hx => hofstadterFAux_eq_of_le k hx)
    k (m + 1 - 1) (by omega)]

/-- **First values of Hofstadter's G and H.** Let $F_k$ denote the generalized Hofstadter
functions. For $n = 0, 1, \dots, 10$ the values $F_2(n)$ are $0, 1, 1, 2, 3, 3, 4, 4, 5, 6, 6$
and the values $F_3(n)$ are $0, 1, 1, 2, 3, 4, 4, 5, 5, 6, 7$.

Here $F_2$ is Hofstadter's $G$ (OEIS A005206) and $F_3$ is Hofstadter's $H$ (OEIS A005374).

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Figure 1. -/
theorem hofstadterF_small_values :
    (List.range 11).map (hofstadterF 2) = [0, 1, 1, 2, 3, 3, 4, 4, 5, 6, 6] ∧
      (List.range 11).map (hofstadterF 3) = [0, 1, 1, 2, 3, 4, 4, 5, 5, 6, 7] := by
  decide

/-- **The Hofstadter substitution on letters.** For a natural number $k$, the substitution
$\tau_k$ sends the letter $k$ to the word $k\,1$ and every other letter $i \in \mathbb{N}$ to the
one-letter word $i + 1$.

The rule $i \mapsto i + 1$ is used only for $1 \le i < k$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2. -/
def hofTau (k i : ℕ) : List ℕ :=
  if i = k then [k, 1] else [i + 1]

/-- **The Hofstadter substitution on finite words.** For a natural number $k$, $\tau_k$ maps a
finite word $w$ over $\mathbb{N}$ to the concatenation, in order, of the words $\tau_k(a)$ for the
letters $a$ of $w$, where $\tau_k(k) = k\,1$ and $\tau_k(i) = i + 1$ for every letter $i \ne k$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2. -/
def hofTauList (k : ℕ) (w : List ℕ) : List ℕ :=
  w.flatMap (hofTau k)

/-- **Letter images under the generalized Hofstadter substitution are nonempty.** For every
natural number $k$, let $\tau_k$ be the substitution on letters in $\mathbb{N}$ sending $k$ to
the two-letter word $k\,1$ and every other letter $m$ to the one-letter word $m + 1$. For every
natural number $i$, the image $\tau_k(i)$ of the letter $i$ has length at least $1$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (definition of `τ_k`). -/
theorem one_le_length_hofTau (k i : ℕ) : 1 ≤ (hofTau k i).length := by
  unfold hofTau
  split <;> simp

/-- **The generalized Hofstadter substitution does not shorten words.** For every natural
number $k$, let $\tau_k$ be the substitution on letters in $\mathbb{N}$ sending $k$ to the
two-letter word $k\,1$ and every other letter $i$ to the one-letter word $i + 1$. For every
finite word $w$ over $\mathbb{N}$, the word $\tau_k(w)$, obtained by replacing each letter of
$w$ by its image under $\tau_k$, is at least as long as $w$: $|w| \le |\tau_k(w)|$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (definition of `τ_k`). -/
theorem length_le_length_hofTauList (k : ℕ) (w : List ℕ) :
    w.length ≤ (hofTauList k w).length := by
  induction w with
  | nil => simp [hofTauList]
  | cons a w ih =>
    simp only [hofTauList, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have := one_le_length_hofTau k a
    omega

/-- **The Hofstadter substitution preserves prefixes.** For a natural number $k$, let $\tau_k$ be
the morphism of finite words over $\mathbb{N}$ that replaces the letter $k$ by the word $k\,1$ and
every other letter $i$ by $i + 1$. For every $k$ and all finite words $u$, $v$ over $\mathbb{N}$,
if $u$ is a prefix of $v$, then $\tau_k(u)$ is a prefix of $\tau_k(v)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (`τ_k` is a morphism). -/
theorem hofTauList_isPrefix {k : ℕ} {u v : List ℕ} (h : u <+: v) :
    hofTauList k u <+: hofTauList k v := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨hofTauList k t, by simp [hofTauList, List.flatMap_append]⟩

/-- **Every iterate $\tau_k^j(k)$ starts with $k$.** Let $\tau_k$ be the substitution sending the
letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, extended letterwise to words. For all
natural numbers $k$ and $j$, the word $\tau_k^j(k)$, obtained by applying $\tau_k$ to the
one-letter word $k$ a total of $j$ times, has the form $k\,r$ for some word $r$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (`τ_k(k) = k 1`). -/
theorem exists_hofTauList_iterate_eq_cons (k j : ℕ) :
    ∃ r, (hofTauList k)^[j] [k] = k :: r := by
  induction j with
  | zero => exact ⟨[], rfl⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨1 :: hofTauList k r, ?_⟩
    rw [Function.iterate_succ_apply', hr]
    simp [hofTauList, hofTau]

/-- **Growth of the iterated generalized Hofstadter substitution.** For natural numbers $k$
and $j$, let $\tau_k$ be the substitution on letters in $\mathbb{N}$ sending $k$ to the
two-letter word $k\,1$ and every other letter $i$ to the one-letter word $i + 1$, extended
letter by letter to finite words. The word $\tau_k^j(k)$, obtained by applying $\tau_k$
$j$ times to the one-letter word $k$, has length at least $j + 1$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (the fixed point `x_k` is the limit of `τ_k^j(k)`). -/
theorem succ_le_length_hofTauList_iterate (k j : ℕ) :
    j + 1 ≤ ((hofTauList k)^[j] [k]).length := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨r, hr⟩ := exists_hofTauList_iterate_eq_cons k j
    rw [Function.iterate_succ_apply', hr]
    rw [hr] at ih
    have := length_le_length_hofTauList k r
    have h2 : (hofTauList k (k :: r)).length = 2 + (hofTauList k r).length := by
      simp [hofTauList, hofTau]
      omega
    rw [h2]
    simp only [List.length_cons] at ih
    omega

/-- **Consecutive iterates of the Hofstadter substitution on $k$ are nested.** For a natural number
$k$, let $\tau_k$ be the morphism of finite words over $\mathbb{N}$ that replaces the letter $k$ by
the word $k\,1$ and every other letter $i$ by $i + 1$, and write $\tau_k^j(k)$ for the word
obtained by applying $\tau_k$ $j$ times to the one-letter word $k$. For all natural numbers $k$
and $j$, $\tau_k^j(k)$ is a prefix of $\tau_k^{j+1}(k)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (the fixed point `x_k` is the limit of `τ_k^j(k)`). -/
theorem hofTauList_iterate_isPrefix_succ (k j : ℕ) :
    (hofTauList k)^[j] [k] <+: (hofTauList k)^[j + 1] [k] := by
  induction j with
  | zero => exact ⟨[1], by simp [hofTauList, hofTau]⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply' (hofTauList k) j,
      Function.iterate_succ_apply' (hofTauList k) (j + 1)]
    exact hofTauList_isPrefix ih

/-- **The iterates of the Hofstadter substitution on $k$ form a chain of prefixes.** For a natural
number $k$, let $\tau_k$ be the morphism of finite words over $\mathbb{N}$ that replaces the letter
$k$ by the word $k\,1$ and every other letter $i$ by $i + 1$, and write $\tau_k^j(k)$ for the word
obtained by applying $\tau_k$ $j$ times to the one-letter word $k$. For every natural number $k$
and all natural numbers $i \le j$, $\tau_k^i(k)$ is a prefix of $\tau_k^j(k)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (the fixed point `x_k` is the limit of `τ_k^j(k)`). -/
theorem hofTauList_iterate_isPrefix (k : ℕ) {i j : ℕ} (hij : i ≤ j) :
    (hofTauList k)^[i] [k] <+: (hofTauList k)^[j] [k] := by
  induction hij with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (hofTauList_iterate_isPrefix_succ k _)

/-- **Bounded growth of a word under $\tau_k$.** Let $\tau_k$ be the substitution sending the
letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, extended letterwise to words. Given
$n$, a bound $f$ and a word $w$, the result is $w$ if $f = 0$ or $w$ has more than $n$ letters,
and otherwise it is the result for the bound $f - 1$ and the word $\tau_k(w)$. Thus $\tau_k$ is
applied to $w$ until the word has more than $n$ letters, at most $f$ times.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (prefixes `τ_k^j(k)` of `x_k`). -/
def hofGrowAux (k n : ℕ) : ℕ → List ℕ → List ℕ
  | 0, w => w
  | f + 1, w => if n < w.length then w else hofGrowAux k n f (hofTauList k w)

/-- **The shortest long iterate $\tau_k^j(k)$.** Let $\tau_k$ be the substitution sending the
letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, extended letterwise to words. For
natural numbers $k$ and $n$, $\mathrm{grow}_k(n)$ is the word obtained from the one-letter word
$k$ by applying $\tau_k$ until it has more than $n$ letters, at most $n$ times. Since
$\tau_k^j(k)$ has at least $j + 1$ letters, this is the shortest iterate $\tau_k^j(k)$ with more
than $n$ letters.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (prefixes `τ_k^j(k)` of `x_k`). -/
def hofGrow (k n : ℕ) : List ℕ :=
  hofGrowAux k n n [k]

/-- **Growing from an iterate of $\tau_k$ gives an iterate of $\tau_k$.** Let $\tau_k$ be the
substitution sending the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, extended
letterwise to words, and let $\mathrm{grow}_{k,n}^f(w)$ be the word obtained from $w$ by applying
$\tau_k$ until it has more than $n$ letters, at most $f$ times. For all $k, n, f, j$ there is an
$m$ with $\mathrm{grow}_{k,n}^f(\tau_k^j(k)) = \tau_k^m(k)$ such that $\tau_k^m(k)$ has more than
$n$ letters or $j + f \le m$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (prefixes `τ_k^j(k)` of `x_k`). -/
theorem hofGrowAux_iterate (k n f j : ℕ) :
    ∃ m, hofGrowAux k n f ((hofTauList k)^[j] [k]) = (hofTauList k)^[m] [k] ∧
      (n < ((hofTauList k)^[m] [k]).length ∨ j + f ≤ m) := by
  induction f generalizing j with
  | zero => exact ⟨j, rfl, Or.inr le_rfl⟩
  | succ f ih =>
    by_cases h : n < ((hofTauList k)^[j] [k]).length
    · exact ⟨j, by simp [hofGrowAux, h], Or.inl h⟩
    · obtain ⟨m, hm, hm'⟩ := ih (j + 1)
      refine ⟨m, ?_, hm'.imp_right fun h' => by omega⟩
      simp only [hofGrowAux, h, ↓reduceIte]
      rw [← Function.iterate_succ_apply' (hofTauList k) j, hm]

/-- **The grown prefix is a long iterate of $\tau_k$.** Let $\tau_k$ be the substitution sending
the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, extended letterwise to words, and
let $\mathrm{grow}_k(n)$ be the word obtained from the one-letter word $k$ by applying $\tau_k$
until it has more than $n$ letters, at most $n$ times. For all natural numbers $k$ and $n$ there
is an $m$ with $\mathrm{grow}_k(n) = \tau_k^m(k)$, and $\mathrm{grow}_k(n)$ has more than $n$
letters.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (prefixes `τ_k^j(k)` of `x_k`). -/
theorem exists_hofGrow_eq (k n : ℕ) :
    ∃ m, hofGrow k n = (hofTauList k)^[m] [k] ∧ n < (hofGrow k n).length := by
  obtain ⟨m, hm, hm'⟩ := hofGrowAux_iterate k n n 0
  refine ⟨m, hm, ?_⟩
  rw [hofGrow, show [k] = (hofTauList k)^[0] [k] from rfl, hm]
  rcases hm' with h | h
  · exact h
  · have := succ_le_length_hofTauList_iterate k m
    omega

/-- **Letters of the Hofstadter fixed-point word.** For natural numbers $k$ and $n$, let $\tau_k$
be the substitution on letters in $\mathbb{N}$ that sends $k$ to the word $k\,1$ and every other
letter $i$ to $i + 1$, applied to words letter by letter, and let $\tau_k^j(k)$ be the word
obtained by applying $\tau_k$ $j$ times to the one-letter word $k$. Then $x_k[n]$ is the letter at
position $n$, counting from $0$, of the shortest word $\tau_k^j(k)$ with $j \ge 0$ that has more
than $n$ letters.

Since each word $\tau_k^j(k)$ is a prefix of $\tau_k^{j+1}(k)$, $x_k[n]$ is the letter at position
$n$ of the fixed point $x_k$ of $\tau_k$ that begins with $k$, and every word $\tau_k^j(k)$ with
more than $n$ letters has $x_k[n]$ at position $n$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2. -/
def hofWord (k n : ℕ) : ℕ :=
  (hofGrow k n).getD n 0

/-- **Letters of $x_k$ from the iterates $\tau_k^j(k)$.** For a natural number $k$, let $\tau_k$ be
the Hofstadter substitution on finite words over $\mathbb{N}$ ($k \mapsto k\,1$, $i \mapsto i + 1$
for $i \ne k$), let $x_k = x_k[0]\,x_k[1] \cdots$ be its fixed point, and write $\tau_k^j(k)$
for the word obtained by applying $\tau_k$ $j$ times to the one-letter word $k$. For all natural
numbers $k$, $n$ and $j$, if $\tau_k^j(k)$ has more than $n$ letters, then $x_k[n]$ is the letter
at position $n$ of $\tau_k^j(k)$, counting positions from $0$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (the fixed point `x_k` is the limit of `τ_k^j(k)`). -/
theorem hofWord_eq_getElem (k n j : ℕ) (h : n < ((hofTauList k)^[j] [k]).length) :
    hofWord k n = ((hofTauList k)^[j] [k])[n] := by
  obtain ⟨m, hm, hlen⟩ := exists_hofGrow_eq k n
  rw [hofWord, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
  simp only [hm] at hlen ⊢
  rcases le_total m j with hmj | hjm
  · exact (hofTauList_iterate_isPrefix k hmj).getElem hlen
  · exact ((hofTauList_iterate_isPrefix k hjm).getElem h).symm

/-- **The letter $x_k[n]$ can be read off $\tau_k^n(k)$.** For a natural number $k$, let $\tau_k$ be
the Hofstadter substitution on finite words over $\mathbb{N}$ ($k \mapsto k\,1$, $i \mapsto i + 1$
for $i \ne k$), let $x_k = x_k[0]\,x_k[1] \cdots$ be its fixed point, and write $\tau_k^n(k)$
for the word obtained by applying $\tau_k$ $n$ times to the one-letter word $k$. For all natural
numbers $k$ and $n$, $x_k[n]$ is the letter at position $n$ of $\tau_k^n(k)$, counting positions
from $0$ (this word has at least $n + 1$ letters).

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2. -/
theorem hofWord_eq_getElem_self (k n : ℕ) :
    hofWord k n = ((hofTauList k)^[n] [k])[n]'(succ_le_length_hofTauList_iterate k n) :=
  hofWord_eq_getElem k n n _

/-- **The prefix $x_k[0:n)$.** For natural numbers $k$ and $n$, let $\tau_k$ be the
substitution $k \mapsto k\,1$, $i \mapsto i + 1$ for $i \ne k$, applied letter by letter to
words, and let $\tau_k^j$ be its $j$-fold iterate. Then $x_k[0:n)$ is the word formed by the
first $n$ letters of the shortest of the words $\tau_k^j(k)$, $j \ge 0$, that has more than $n$
letters.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 2. -/
def hofPrefix (k n : ℕ) : List ℕ :=
  (hofGrow k n).take n

/-- **The prefix $x_k[0:n)$ letter by letter.** Let $k$ and $n$ be natural numbers, let $x_k$ be
the fixed point of the substitution $\tau_k$ with letters $x_k[0], x_k[1], \dots$, and let
$x_k[0:n)$ be the word formed by the first $n$ letters of the shortest word $\tau_k^j(k)$ with
more than $n$ letters. Then $x_k[0:n) = x_k[0]\,x_k[1] \cdots x_k[n-1]$, the empty word when
$n = 0$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 2. -/
theorem hofPrefix_eq_map (k n : ℕ) : hofPrefix k n = (List.range n).map (hofWord k) := by
  obtain ⟨m, hm, hlen⟩ := exists_hofGrow_eq k n
  apply List.ext_getElem
  · simp [hofPrefix]
    omega
  · intro i h₁ h₂
    simp only [hofPrefix, List.getElem_take, List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h₂
    rw [hm] at hlen
    rw [hofWord_eq_getElem k i m (by omega)]
    simp only [hm]

/-- **The image length $L_k$.** For natural numbers $k$ and $n$, $L_k(n) = |\tau_k(x_k[0:n))|$
is the length of the word obtained by applying the substitution $\tau_k$, letter by letter, to
the prefix $x_k[0:n)$ formed by the first $n$ letters of the fixed point $x_k$ of $\tau_k$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 2. -/
def hofL (k n : ℕ) : ℕ :=
  (hofTauList k (hofPrefix k n)).length

/-- **Letter counts in the Hofstadter word.** Let $x_k$ be the fixed point, starting with $k$, of
the substitution sending the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, and write
$x_k[j]$ for its letter at index $j$. For a predicate $P$ on letters, $C_k^{(P)}(n)$ is the number
of letters satisfying $P$ in the prefix $x_k[0] \cdots x_k[n-1]$, that is,
$C_k^{(P)}(n) = \#\{0 \le j < n : P(x_k[j])\}$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 4. -/
def hofCount (k : ℕ) (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ :=
  (hofPrefix k n).countP fun a => decide (P a)

/-- **Letter counts of the Hofstadter word as cardinalities.** Let $x_k$ be the fixed point,
starting with $k$, of the substitution sending the letter $k$ to $k\,1$ and every other letter
$i$ to $i + 1$, and write $x_k[j]$ for its letter at index $j$. For every predicate $P$ on letters
and every $n$, the number $C_k^{(P)}(n)$ of letters satisfying $P$ in the prefix
$x_k[0] \cdots x_k[n-1]$ equals the number of indices $j < n$ with $P(x_k[j])$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 4. -/
theorem hofCount_eq_card (k : ℕ) (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    hofCount k P n = ((Finset.range n).filter fun j => P (hofWord k j)).card := by
  rw [hofCount, hofPrefix_eq_map, List.countP_map, List.countP_eq_length_filter]
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  rfl

/-- **First values of $x_2$, $x_3$ and $L_2$.** For a natural number $k$, let $x_k$ be the fixed
point of the Hofstadter substitution $\tau_k$ ($k \mapsto k\,1$, $i \mapsto i + 1$ for $i \ne k$),
and let $L_2(n)$ be the length of $\tau_2(x_2[0] \cdots x_2[n-1])$. The first eight letters of
the Fibonacci word $x_2$ are $2, 1, 2, 2, 1, 2, 1, 2$; the first eight letters of $x_3$ are
$3, 1, 2, 3, 3, 1, 3, 1$; and $L_2(0), \dots, L_2(5)$ are $0, 2, 3, 5, 7, 8$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Figure 2. -/
theorem hofWord_small_values :
    (List.range 8).map (hofWord 2) = [2, 1, 2, 2, 1, 2, 1, 2] ∧
      (List.range 8).map (hofWord 3) = [3, 1, 2, 3, 3, 1, 3, 1] ∧
      (List.range 6).map (hofL 2) = [0, 2, 3, 5, 7, 8] := by
  decide

namespace hofCount_one_succ_le

/-- **Iterated substitution distributes over concatenation.** Let $\tau_k$ be the substitution of
finite words over $\mathbb{N}$ that replaces the letter $k$ by $k\,1$ and every other letter $i$ by
$i + 1$, and let $\tau_k^j$ be its $j$-fold iterate. For all natural numbers $k$ and $j$ and all
finite words $u$ and $v$, $\tau_k^j(u\,v) = \tau_k^j(u)\,\tau_k^j(v)$. -/
theorem iterate_append (k j : ℕ) (u v : List ℕ) :
    (hofTauList k)^[j] (u ++ v) = (hofTauList k)^[j] u ++ (hofTauList k)^[j] v := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, hofTauList, List.flatMap_append]

private theorem iterate_before_top {k a : ℕ} (j : ℕ) (h : a + j ≤ k) :
    (hofTauList k)^[j] [a] = [a + j] := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp [hofTauList, hofTau, show a + j ≠ k by omega, Nat.add_assoc]

private theorem iterate_top {k : ℕ} (j : ℕ) (hj : j ≤ k) :
    (hofTauList k)^[j] [k] = k :: List.range' 1 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    rw [show hofTauList k [k] = [k] ++ [1] by simp [hofTauList, hofTau],
      iterate_append, ih (by omega), iterate_before_top j (by omega), List.range'_concat]
    simp

/-- **Iterated substitution of a letter that reaches $k$.** Let $\tau_k$ be the substitution of
finite words over $\mathbb{N}$ that replaces the letter $k$ by $k\,1$ and every other letter $i$ by
$i + 1$, and let $\tau_k^j$ be its $j$-fold iterate. For natural numbers $a \le k$ and $j \le k$
with $k \le a + j$, the word $\tau_k^j(a)$ is the letter $k$ followed by
$1, 2, \dots, a + j - k$. -/
theorem iterate_letter {k a j : ℕ} (ha : a ≤ k) (hj : j ≤ k) (h : k ≤ a + j) :
    (hofTauList k)^[j] [a] = k :: List.range' 1 (a + j - k) := by
  have e : a + (k - a) = k := by omega
  calc
    _ = (hofTauList k)^[a + j - k] ((hofTauList k)^[k - a] [a]) := by
      rw [← Function.iterate_add_apply, show a + j - k + (k - a) = j by omega]
    _ = _ := by rw [iterate_before_top _ e.le, e, iterate_top _ (by omega)]

private theorem block_length {k a j : ℕ} (ha : a ≤ k) (hj : j ≤ k) :
    ((hofTauList k)^[j] [a]).length = 1 + (a + j - k) := by
  rcases le_total (a + j) k with h | h
  · rw [iterate_before_top _ h]
    simp [Nat.sub_eq_zero_of_le h]
  · simp [iterate_letter ha hj h, Nat.add_comm]

/-- **Letters of the Hofstadter word lie between $1$ and $k$.** Let $k \ge 1$ and let $x_k$ be
the fixed point, starting with $k$, of the substitution sending the letter $k$ to $k\,1$ and every
other letter $i$ to $i + 1$. For every natural number $n$, $1 \le x_k[n] \le k$. -/
theorem letter_bounds {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    1 ≤ hofWord k n ∧ hofWord k n ≤ k := by
  have bounds (j : ℕ) : ∀ a ∈ (hofTauList k)^[j] [k], 1 ≤ a ∧ a ≤ k := by
    induction j with
    | zero => simpa using And.intro hk (le_refl k)
    | succ j ih =>
      intro a ha
      rw [Function.iterate_succ_apply'] at ha
      obtain ⟨b, hb, hab⟩ := List.mem_flatMap.mp ha
      obtain ⟨hb₁, hb₂⟩ := ih b hb
      by_cases h : b = k
      · simp [hofTau, h] at hab
        omega
      · simp [hofTau, h] at hab
        omega
  rw [hofWord_eq_getElem_self]
  exact bounds _ _ (List.getElem_mem ..)

/-- **A prefix of the Hofstadter word grows by one letter.** Let $x_k$ be the fixed point,
starting with $k$, of the substitution sending the letter $k$ to $k\,1$ and every other letter
$i$ to $i + 1$. For all natural numbers $k$ and $n$, the prefix $x_k[0] \cdots x_k[n]$ of length
$n + 1$ is the prefix $x_k[0] \cdots x_k[n-1]$ of length $n$ followed by the letter $x_k[n]$. -/
theorem prefix_succ (k n : ℕ) :
    hofPrefix k (n + 1) = hofPrefix k n ++ [hofWord k n] := by
  simp [hofPrefix_eq_map, List.range_succ]

/-- **Length of a prefix of the Hofstadter word.** Let $x_k$ be the fixed point, starting with
$k$, of the substitution sending the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$.
For all natural numbers $k$ and $n$, the prefix $x_k[0] \cdots x_k[n-1]$ has length $n$. -/
theorem prefix_length (k n : ℕ) : (hofPrefix k n).length = n := by
  simp [hofPrefix_eq_map]

/-- **Image length of a prefix under iterated substitution.** Let $\tau_k$ be the substitution
of finite words over $\mathbb{N}$ that replaces the letter $k$ by $k\,1$ and every other letter $i$
by $i + 1$, let $\tau_k^j$ be its $j$-fold iterate, and let $x_k$ be its fixed point starting
with $k$. For natural numbers $k$, $j$ and $n$, `imageLength k j n` is
$|\tau_k^j(x_k[0] \cdots x_k[n-1])|$, the length of the word obtained by applying $\tau_k$ $j$
times to the prefix of $x_k$ of length $n$. -/
def imageLength (k j n : ℕ) := ((hofTauList k)^[j] (hofPrefix k n)).length

/-- **Image length of a prefix one letter longer.** Let $\tau_k$ be the substitution sending the
letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $\tau_k^j$ be its $j$-fold
iterate, let $x_k$ be its fixed point starting with $k$, and let
$L_k^{(j)}(n) = |\tau_k^j(x_k[0] \cdots x_k[n-1])|$. For all natural numbers $k$, $j$ and $n$,
$L_k^{(j)}(n + 1) = L_k^{(j)}(n) + |\tau_k^j(x_k[n])|$. -/
theorem image_succ (k j n : ℕ) :
    imageLength k j (n + 1) = imageLength k j n + ((hofTauList k)^[j] [hofWord k n]).length := by
  simp only [imageLength, prefix_succ, iterate_append, List.length_append]

/-- **Image length of the empty prefix.** Let $\tau_k$ be the substitution sending the letter
$k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $\tau_k^j$ be its $j$-fold iterate, let
$x_k$ be its fixed point starting with $k$, and let
$L_k^{(j)}(n) = |\tau_k^j(x_k[0] \cdots x_k[n-1])|$. For all natural numbers $k$ and $j$,
$L_k^{(j)}(0) = 0$. -/
theorem image_zero (k j : ℕ) : imageLength k j 0 = 0 := by
  have h : (hofTauList k)^[j] [] = [] := Function.iterate_fixed (show hofTauList k [] = [] by rfl) j
  simpa [imageLength, hofPrefix_eq_map] using congrArg List.length h

/-- **Image length of the one-letter prefix.** Let $\tau_k$ be the substitution sending the
letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $\tau_k^j$ be its $j$-fold
iterate, let $x_k$ be its fixed point starting with $k$, and let
$L_k^{(j)}(n) = |\tau_k^j(x_k[0] \cdots x_k[n-1])|$. For natural numbers $j \le k$,
$L_k^{(j)}(1) = j + 1$. -/
theorem image_one {k j : ℕ} (hj : j ≤ k) : imageLength k j 1 = j + 1 := by
  have h : hofPrefix k 1 = [k] := by simp [hofPrefix_eq_map, hofWord, hofGrow, hofGrowAux]
  rw [imageLength, h, iterate_top _ hj, List.length_cons, List.length_range']

/-- **Image lengths of prefixes increase strictly.** Let $\tau_k$ be the substitution sending
the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $\tau_k^j$ be its $j$-fold
iterate, let $x_k$ be its fixed point starting with $k$, and let
$L_k^{(j)}(n) = |\tau_k^j(x_k[0] \cdots x_k[n-1])|$. For natural numbers $k \ge 1$ and
$j \le k$, the function $n \mapsto L_k^{(j)}(n)$ is strictly increasing. -/
theorem image_strictMono {k j : ℕ} (hk : 1 ≤ k) (hj : j ≤ k) :
    StrictMono (imageLength k j) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [image_succ, block_length (letter_bounds hk n).2 hj]
  omega

/-- **The image of a prefix is a prefix.** Let $\tau_k$ be the substitution sending the letter
$k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $\tau_k^j$ be its $j$-fold iterate, let
$x_k$ be its fixed point starting with $k$, and let
$L_k^{(j)}(n) = |\tau_k^j(x_k[0] \cdots x_k[n-1])|$. For all natural numbers $k$, $j$ and $n$,
$\tau_k^j(x_k[0] \cdots x_k[n-1])$ is the prefix of $x_k$ of length $L_k^{(j)}(n)$. -/
theorem iterate_prefix {k j n : ℕ} :
    (hofTauList k)^[j] (hofPrefix k n) = hofPrefix k (imageLength k j n) := by
  obtain ⟨r, hr, _⟩ := exists_hofGrow_eq k n
  have h : hofPrefix k n <+: (hofTauList k)^[r] [k] := by
    rw [hofPrefix, hr]
    apply List.take_prefix
  have h' : (hofTauList k)^[j] (hofPrefix k n) <+: (hofTauList k)^[j + r] [k] := by
    rw [Function.iterate_add_apply]
    induction j with
    | zero => exact h
    | succ j ih => simpa only [Function.iterate_succ_apply'] using hofTauList_isPrefix ih
  conv_rhs => rw [hofPrefix_eq_map]
  apply List.ext_getElem
  · simp [imageLength]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range]
    rw [hofWord_eq_getElem k i (j + r) (lt_of_lt_of_le hi h'.length_le)]
    exact h'.getElem hi

private theorem image_comp (k j n : ℕ) :
    imageLength k j (imageLength k 1 n) = imageLength k (j + 1) n := by
  change ((hofTauList k)^[j] (hofPrefix k (imageLength k 1 n))).length = _
  rw [← iterate_prefix]
  rfl

/-- **The prefix at the next image length.** Let $\tau_k$ be the substitution sending the
letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $\tau_k^j$ be its $j$-fold
iterate, let $x_k$ be its fixed point starting with $k$, and let
$L_k^{(j)}(n) = |\tau_k^j(x_k[0] \cdots x_k[n-1])|$. For all natural numbers $k$, $j$ and $n$,
the prefix of $x_k$ of length $L_k^{(j)}(n + 1)$ is the prefix of length $L_k^{(j)}(n)$
followed by the word $\tau_k^j(x_k[n])$. -/
theorem prefix_image_succ (k j n : ℕ) :
    hofPrefix k (imageLength k j (n + 1)) =
      hofPrefix k (imageLength k j n) ++ (hofTauList k)^[j] [hofWord k n] := by
  rw [← iterate_prefix, prefix_succ, iterate_append, iterate_prefix (n := n)]

/-- **The letter at an image length.** Let $\tau_k$ be the substitution sending the letter $k$
to $k\,1$ and every other letter $i$ to $i + 1$, let $\tau_k^j$ be its $j$-fold iterate, let
$x_k$ be its fixed point starting with $k$, and let
$L_k^{(j)}(n) = |\tau_k^j(x_k[0] \cdots x_k[n-1])|$. For natural numbers $k$, $j$, $n$ and $a$
and a finite word $t$, if $\tau_k^j(x_k[n]) = a\,t$, then $x_k[L_k^{(j)}(n)] = a$. -/
theorem word_at_image {k j n a : ℕ} {t : List ℕ}
    (h : (hofTauList k)^[j] [hofWord k n] = a :: t) : hofWord k (imageLength k j n) = a := by
  have he := prefix_image_succ k j n
  rw [h] at he
  have hl := congrArg List.length he
  simp only [prefix_length, List.length_append, List.length_cons] at hl
  have he' := congrArg (fun w : List ℕ => w[imageLength k j n]?) he
  simpa [hofPrefix_eq_map, List.getElem?_append_right, show
    imageLength k j n < imageLength k j (n + 1) by omega] using he'

/-- **Letter counts are monotone.** Let $x_k$ be the fixed point, starting with $k$, of the
substitution sending the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$. For every
natural number $k$ and every decidable predicate $P$ on letters, the count
$C_k^{(P)}(n) = \#\{0 \le i < n : P(x_k[i])\}$ is a monotone function of $n$. -/
theorem count_mono (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Monotone (hofCount k P) := by
  apply monotone_nat_of_le_succ
  intro n
  simp [hofCount, prefix_succ]

/-- If each image block starts with its only marked letter, the count at a block boundary
is the number of complete blocks, and it increases at the next position. -/
private theorem count_boundary {k j : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (h : ∀ n, ∃ a t, (hofTauList k)^[j] [hofWord k n] = a :: t ∧ P a ∧ ∀ b ∈ t, ¬ P b)
    (n : ℕ) :
    hofCount k P (imageLength k j n) = n ∧ hofCount k P (imageLength k j n + 1) = n + 1 := by
  have count (m : ℕ) : hofCount k P (imageLength k j m) = m := by
    induction m with
    | zero => simp [image_zero, hofCount, hofPrefix_eq_map]
    | succ m ih =>
      obtain ⟨a, t, ht, ha, hbs⟩ := h m
      have hc : t.countP (fun b => decide (P b)) = 0 := List.countP_eq_zero.mpr (by simpa using hbs)
      simpa [hofCount, prefix_image_succ, ht, ha, hc, List.countP_cons] using ih
  obtain ⟨a, t, ht, ha, _⟩ := h n
  exact ⟨count n, by simpa [hofCount, prefix_succ, word_at_image ht, ha] using count n⟩

/-- **An image length at the count bounds the position.** Let $\tau_k$ be the substitution
sending the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $\tau_k^j$ be its
$j$-fold iterate, let $x_k$ be its fixed point starting with $k$, let
$L_k^{(j)}(n) = |\tau_k^j(x_k[0] \cdots x_k[n-1])|$, and for a decidable predicate $P$ on letters
let $C_k^{(P)}(n) = \#\{0 \le i < n : P(x_k[i])\}$. If $C_k^{(P)}(L_k^{(j)}(c) + 1) = c + 1$ for
every natural number $c$, then $n \le L_k^{(j)}(C_k^{(P)}(n))$ for every natural number $n$. -/
theorem count_covers {k j : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (h : ∀ c, hofCount k P (imageLength k j c + 1) = c + 1) (n : ℕ) :
    n ≤ imageLength k j (hofCount k P n) := by
  by_contra! hlt
  have := count_mono k P (Nat.succ_le_of_lt hlt)
  rw [h] at this
  omega

/-- **Counts of the letter $k$ at the image lengths of $\tau_k^{k-1}$.** Let $k \ge 1$, let
$\tau_k$ be the substitution sending the letter $k$ to $k\,1$ and every other letter $i$ to
$i + 1$, let $\tau_k^{k-1}$ be its $(k-1)$-fold iterate, let $x_k$ be its fixed point starting
with $k$, let $M(n) = |\tau_k^{k-1}(x_k[0] \cdots x_k[n-1])|$, and let $C_k^{(=k)}(m)$ be the
number of indices $0 \le i < m$ with $x_k[i] = k$. For every natural number $n$,
$C_k^{(=k)}(M(n)) = n$ and $C_k^{(=k)}(M(n) + 1) = n + 1$. -/
theorem top_boundary {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    hofCount k (· = k) (imageLength k (k - 1) n) = n ∧
      hofCount k (· = k) (imageLength k (k - 1) n + 1) = n + 1 := by
  apply count_boundary
  intro m
  obtain ⟨ha, ha'⟩ := letter_bounds hk m
  refine ⟨k, _, iterate_letter ha' (by omega) (by omega), rfl, ?_⟩
  intro b hb
  have := List.mem_range'_1.mp hb
  omega

private theorem nonone_boundary {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    hofCount k (· ≠ 1) (imageLength k 1 n) = n ∧
      hofCount k (· ≠ 1) (imageLength k 1 n + 1) = n + 1 := by
  apply count_boundary
  intro m
  obtain ⟨ha, _⟩ := letter_bounds (by omega : 1 ≤ k) m
  by_cases h : hofWord k m = k
  · exact ⟨k, [1], by simp [hofTauList, hofTau, h], by omega, by simp⟩
  · exact ⟨hofWord k m + 1, [], by simp [hofTauList, hofTau, h], by omega, by simp⟩

/-- **The image length under $\tau_k$ counts the letters $k$.** Let $\tau_k$ be the substitution
sending the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $x_k$ be its fixed
point starting with $k$, and let $C_k^{(=k)}(n)$ be the number of indices $0 \le i < n$ with
$x_k[i] = k$. For all natural numbers $k$ and $n$,
$|\tau_k(x_k[0] \cdots x_k[n-1])| = n + C_k^{(=k)}(n)$. -/
theorem image_eq_add_count (k n : ℕ) :
    imageLength k 1 n = n + hofCount k (· = k) n := by
  induction n with
  | zero => simp [image_zero, hofCount, hofPrefix_eq_map]
  | succ n ih =>
    rw [image_succ, ih]
    by_cases h : hofWord k n = k <;> simp [hofCount, prefix_succ, hofTauList, hofTau, h] <;> omega

private theorem image_last {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    imageLength k k n = imageLength k (k - 1) n + n := by
  induction n with
  | zero => simp [image_zero]
  | succ n ih =>
    obtain ⟨ha, ha'⟩ := letter_bounds hk n
    rw [image_succ, image_succ k (k - 1), ih, block_length ha' le_rfl,
      block_length ha' (by omega)]
    omega

private theorem lt_image {k j n : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) (hn : 1 ≤ n) :
    n < imageLength k j n := by
  induction n, hn using Nat.le_induction with
  | base => rw [image_one hjk]; omega
  | succ n hn ih =>
    exact (Nat.succ_le_of_lt ih).trans_lt (image_strictMono hk hjk (Nat.lt_succ_self n))

/-- A prefix ending inside a substitution block ends with `k`, the first letter of `k 1`.
At every other endpoint the whole prefix is the image of a shorter prefix. -/
private theorem endpoint {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    hofWord k m = k ∨ ∃ c, 0 < c ∧ c < m + 1 ∧ imageLength k 1 c = m + 1 := by
  have hex : ∃ c, m + 1 ≤ imageLength k 1 c :=
    ⟨m + 1, (lt_image hk le_rfl hk (by omega)).le⟩
  have hi := Nat.find_spec hex
  obtain ⟨c, hc⟩ : ∃ c, Nat.find hex = c + 1 := by
    cases h : Nat.find hex with
    | zero => simp [h, image_zero] at hi
    | succ c => exact ⟨c, rfl⟩
  have lo := Nat.find_min hex (show c < Nat.find hex by omega)
  rw [hc] at hi
  by_cases he : imageLength k 1 (c + 1) = m + 1
  · exact Or.inr ⟨c + 1, by omega, he ▸ lt_image hk le_rfl hk (by omega), he⟩
  · left
    by_cases ht : hofWord k c = k
    · have hb : (hofTauList k)^[1] [hofWord k c] = [k, 1] := by simp [hofTauList, hofTau, ht]
      rw [image_succ, hb, List.length_cons, List.length_cons, List.length_nil] at hi he
      have e : m = imageLength k 1 c := by omega
      exact e ▸ word_at_image hb
    · rw [image_succ] at hi he
      simp [hofTauList, hofTau, ht] at hi he
      omega

/-- Compare image lengths simultaneously. The shifted comparison at shorter prefixes
controls the number of top letters, which in turn controls the one-step image length. -/
private theorem compare_images {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    imageLength (k + 1) 1 n ≤ imageLength k 1 n ∧
      ∀ j ≤ k, 0 < n → imageLength k j n < imageLength (k + 1) (j + 1) n := by
  have hk₁ : 1 ≤ k := by omega
  have hs : 1 ≤ k + 1 := by omega
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp [image_zero]
    | succ m =>
      by_cases hm : m = 0
      · subst m
        refine ⟨by rw [image_one hs, image_one hk₁], fun j hj _ => ?_⟩
        rw [image_one hj, image_one (by omega : j + 1 ≤ k + 1)]
        omega
      constructor
      · -- Each block of order k - 1 starts with its only top letter.
        let c := hofCount k (· = k) (m + 1)
        have hcover : m + 1 ≤ imageLength k (k - 1) c :=
          count_covers _ (fun t => (top_boundary hk₁ t).2) _
        have hc₀ : 0 < c := by
          by_contra! h
          simp [show c = 0 by omega, image_zero] at hcover
        have hcm : m + 1 ≤ imageLength k (k - 1) m :=
          lt_image hk₁ (by omega) (by omega) (by omega)
        have hc : c ≤ m :=
          (count_mono k (· = k) hcm).trans_eq (top_boundary hk₁ m).1
        have hshift := (ih c (by omega)).2 (k - 1) (by omega) hc₀
        rw [show k - 1 + 1 = k by omega] at hshift
        have htop := (top_boundary hs c).1
        rw [Nat.add_sub_cancel] at htop
        have hcount := count_mono (k + 1) (· = k + 1) (hcover.trans hshift.le)
        rw [htop] at hcount
        rw [image_eq_add_count, image_eq_add_count]
        exact Nat.add_le_add_left hcount _
      · -- Prove the shifts below k first. The last shift follows by adding n.
        have shift (j : ℕ) (hj : j < k) :
            imageLength k j (m + 1) < imageLength (k + 1) (j + 1) (m + 1) := by
          rcases endpoint hs m with ht | ⟨c, hc, hcm, he⟩
          · have hprev := (ih m (by omega)).2 j hj.le (by omega)
            rw [image_succ, image_succ, ht, iterate_top _ (by omega : j + 1 ≤ k + 1),
              List.length_cons, List.length_range', block_length (letter_bounds hk₁ m).2 hj.le]
            have := (letter_bounds hk₁ m).2
            omega
          · rw [← he, image_comp]
            calc
              _ ≤ imageLength k j (imageLength k 1 c) :=
                (image_strictMono hk₁ hj.le).monotone (ih c hcm).1
              _ = _ := image_comp k j c
              _ < _ := (ih c hcm).2 (j + 1) (by omega) hc
        intro j hj _
        rcases lt_or_eq_of_le hj with hj | heq
        · exact shift j hj
        · subst j
          have hprev := shift (k - 1) (by omega)
          rw [show k - 1 + 1 = k by omega] at hprev
          rw [image_last hk₁, image_last hs, Nat.add_sub_cancel]
          omega

private theorem count_partition (k n : ℕ) :
    hofCount k (· = 1) n + hofCount k (· ≠ 1) n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : hofWord k n = 1 <;> simp [hofCount, prefix_succ, h] at ih ⊢ <;> omega

end hofCount_one_succ_le

open hofCount_one_succ_le in
/-- **Bracketing by the iterates of $L_k$.** For $k \ge 1$, let $\tau_k$ be the substitution
sending the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $x_k$ be its fixed
point starting with $k$, and let $L_k(n)$ be the length of the image under $\tau_k$ of the first
$n$ letters of $x_k$; write $L_k^j$ for the $j$-fold iterate of $L_k$. For all $j \ge 0$ and
$m \ge 1$ there is a unique $n \ge 1$ with $L_k^j(n - 1) < m \le L_k^j(n)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 2.4 (`jis-2026-26.3.3-prop-5`). -/
theorem existsUnique_hofL_iterate_bracket {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (j : ℕ) :
    ∃! n, 1 ≤ n ∧ (hofL k)^[j] (n - 1) < m ∧ m ≤ (hofL k)^[j] n := by
  let f := (hofL k)^[j]
  have hL : StrictMono (hofL k) := image_strictMono (j := 1) hk hk
  have hmono : StrictMono f := hL.iterate j
  have hzero : f 0 = 0 := Function.iterate_fixed (show hofL k 0 = 0 from image_zero k 1) j
  have hex : ∃ n, m ≤ f n := ⟨m, hmono.le_apply⟩
  let n := Nat.find hex
  have hn : m ≤ f n := Nat.find_spec hex
  have hnpos : 1 ≤ n := by
    by_contra! h
    rw [show n = 0 by omega, hzero] at hn
    omega
  have hlo : f (n - 1) < m := lt_of_not_ge (Nat.find_min hex (by omega : n - 1 < n))
  refine ⟨n, ⟨hnpos, hlo, hn⟩, ?_⟩
  intro a ha
  have hna : n ≤ a := Nat.find_min' hex ha.2.2
  refine le_antisymm ?_ hna
  by_contra! h
  exact (not_lt_of_ge (hn.trans (hmono.monotone (by omega : n ≤ a - 1)))) ha.2.1

open hofCount_one_succ_le in
/-- **Iterates of the Hofstadter substitution on the letter $k$.** Let $k \ge 1$, let $\tau_k$ be
the morphism of finite words over $\mathbb{N}$ that replaces the letter $k$ by the word $k\,1$ and
every other letter $i$ by $i + 1$, and write $\tau_k^j(k)$ for the word obtained by applying
$\tau_k$ $j$ times to the one-letter word $k$. For every natural number $j$: if $j \le k$, then
$\tau_k^j(k) = k\,1\,2 \cdots j$, the letter $k$ followed by $1, 2, \dots, j$; and if $j \ge k$,
then $\tau_k^j(k)$ is the concatenation $\tau_k^{j-1}(k)\,\tau_k^{j-k}(k)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 2.2 (`jis-2026-26.3.3-prop-3`). -/
theorem hofTauList_iterate_self {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (j ≤ k → (hofTauList k)^[j] [k] = k :: List.range' 1 j) ∧
      (k ≤ j → (hofTauList k)^[j] [k] =
        (hofTauList k)^[j - 1] [k] ++ (hofTauList k)^[j - k] [k]) := by
  refine ⟨iterate_top j, fun hj => ?_⟩
  have h₁ : 1 + (k - 1) = k := by omega
  calc
    _ = (hofTauList k)^[j - 1] (hofTauList k [k]) := by
      rw [← Function.iterate_succ_apply, show (j - 1).succ = j by omega]
    _ = (hofTauList k)^[j - 1] [k] ++ (hofTauList k)^[j - 1] [1] := by
      rw [show hofTauList k [k] = [k] ++ [1] by simp [hofTauList, hofTau], iterate_append]
    _ = _ := by
      congr 1
      rw [show j - 1 = (j - k) + (k - 1) by omega, Function.iterate_add_apply,
        iterate_before_top _ h₁.le, h₁]

open hofCount_one_succ_le in
/-- **Prefixes of $x_{k+1}$ contain no more letters $1$ than those of $x_k$.** Let $x_k$ be the
fixed point, starting with $k$, of the substitution sending the letter $k$ to $k\,1$ and every
other letter $i$ to $i + 1$, and let $C_k^{(=1)}(n)$ be the number of indices $j < n$ with
$x_k[j] = 1$. For $k \ge 1$ and every $n \ge 0$, $C_{k+1}^{(=1)}(n) \le C_k^{(=1)}(n)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 26 (`jis-2026-26.3.3-prop-26`). -/
theorem hofCount_one_succ_le {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    hofCount (k + 1) (· = 1) n ≤ hofCount k (· = 1) n := by
  by_cases h : k = 1
  · subst k
    have hall : hofCount 1 (· = 1) n = n := by
      rw [hofCount]
      refine Eq.trans ?_ (prefix_length 1 n)
      apply List.countP_eq_length.mpr
      intro a ha
      rw [hofPrefix_eq_map] at ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      have := letter_bounds (k := 1) le_rfl i
      simp only [decide_eq_true_eq]
      omega
    rw [hall, hofCount]
    exact List.countP_le_length.trans_eq (prefix_length _ _)
  · have hk₂ : 2 ≤ k := by omega
    let c := hofCount (k + 1) (· ≠ 1) n
    have hcover : n ≤ imageLength (k + 1) 1 c :=
      count_covers _ (fun t => (nonone_boundary (by omega : 2 ≤ k + 1) t).2) _
    have hc := count_mono k (· ≠ 1) (hcover.trans (compare_images hk₂ c).1)
    rw [(nonone_boundary hk₂ c).1] at hc
    have := count_partition k n
    have := count_partition (k + 1) n
    dsimp only [c] at hc
    omega

open hofCount_one_succ_le in
/-- **Iterates of $L_{k+1}$ lie below iterates of $L_k$.** Let $x_k[0]\,x_k[1] \cdots$ be the
fixed point, beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every
other letter $i$ to $i + 1$, let $L_k(n)$ be the length of the word
$\tau_k(x_k[0] \cdots x_k[n-1])$, and write $L_k^j$ for the $j$-fold iterate of $L_k$. For
every $k \ge 1$, every $j \ge 0$ and every natural number $n$, $L_{k+1}^j(n) \le L_k^j(n)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Corollary 21 (`jis-2026-26.3.3-cor-21`). -/
theorem hofL_iterate_succ_le {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (hofL (k + 1))^[j] ≤ (hofL k)^[j] := by
  have hmono : Monotone (hofL (k + 1)) :=
    (image_strictMono (k := k + 1) (j := 1) (by omega) (by omega)).monotone
  apply hmono.iterate_le_of_le _ j
  intro n
  rcases eq_or_lt_of_le hk with rfl | hk'
  · calc
      hofL 2 n = n + hofCount 2 (· = 2) n := image_eq_add_count 2 n
      _ ≤ n + n := Nat.add_le_add_left (List.countP_le_length.trans_eq (prefix_length 2 n)) _
      _ = hofL 1 n := by
        simpa [imageLength, hofL, prefix_length] using (image_last (k := 1) le_rfl n).symm
  · exact (compare_images hk' n).1

end

end MetaMathlibExt
