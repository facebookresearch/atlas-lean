/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Leonardo `p`-numbers and Lucas-Leonardo `p`-numbers: tilings, incomplete and hyper analogs

Statements from Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo
`p`-Numbers and Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57
(<https://math.colgate.edu/~integers/z57/z57.pdf>).

The Leonardo `p`-numbers `𝓛_{p,n}` (`1` on `[0, p]`, `𝓛_{p,n} = 𝓛_{p,n-1} + 𝓛_{p,n-p-1} + p`)
are the generalized Leonardo `p`-numbers `leonardoPK p p` of
`WantedExt.NumberTheory.LeonardoPWanted`. Propositions 3, 4 and 5 of the paper are the
`k = p` cases of `leonardoPK_eq`, `sum_leonardoPK` and `sum_leonardoPK_stride` there, and
are not restated.

New here: the Lucas `p`-numbers `lucasP`, the Lucas-Leonardo `p`-numbers
`lucasLeonardoP`, the incomplete Leonardo and Lucas-Leonardo `p`-numbers (the paper's
displays (4) and (8)), the hyper Leonardo `p`-numbers (display (12)), the hyper
Lucas-Leonardo `p`-numbers (Definition 2), the tiling sets `K_{p,n}` and the bracelet sets
`B_{p,n}`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import WantedExt.NumberTheory.LeonardoPWanted

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.NumberTheory.LeonardoPWanted

/-- **Lucas-type recurrence lists.** Let $\alpha$ be a type with a zero, a one and an addition, let
$p$ be a natural number and let $a_0, c \in \alpha$. Define $a_i = 1$ for $1 \le i \le p$ and
$a_n = a_{n-1} + a_{n-p-1} + c$ for $n > p$. For every natural number $n$, the Lucas-type list
with parameters $p$, $a_0$, $c$ ending at index $n$ is $[a_0, a_1, \dots, a_n]$.

The list is built by appending one value per step, so each earlier value is computed once and
evaluation is quadratic in $n$, not exponential as with the naive two-branch recursion. The
Lucas and Lucas-Leonardo $p$-numbers are the cases $c = 0$ and $c = p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Section 1, display (5). -/
def lucasTypeSeq {α : Type*} [Zero α] [One α] [Add α] (p : ℕ) (a₀ c : α) : ℕ → List α
  | 0 => [a₀]
  | n + 1 =>
      let prev := lucasTypeSeq p a₀ c n
      prev ++ [if n + 1 ≤ p then 1 else prev.getD n 0 + prev.getD (n - p) 0 + c]

/-- **Length of a Lucas-type list.** For every type $\alpha$ with a zero, a one and an addition,
every natural number $p$, all $a_0, c \in \alpha$ and every natural number $n$, the Lucas-type
list with parameters $p$, $a_0$, $c$ ending at index $n$ has exactly $n + 1$ entries.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasTypeSeq_length {α : Type*} [Zero α] [One α] [Add α] (p : ℕ) (a₀ c : α)
    (n : ℕ) : (lucasTypeSeq p a₀ c n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lucasTypeSeq, ih]

/-- **Entries of a Lucas-type list do not depend on its length.** Let $\alpha$ be a type with a
zero, a one and an addition, let $p$ be a natural number and let $a_0, c \in \alpha$. For natural
numbers $i \le n$, the entry at index $i$ of the Lucas-type list with parameters $p$, $a_0$, $c$
ending at index $n$ equals the entry at index $i$ of the Lucas-type list ending at index $i$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasTypeSeq_getD {α : Type*} [Zero α] [One α] [Add α] (p : ℕ) (a₀ c : α)
    {i n : ℕ} (h : i ≤ n) :
    (lucasTypeSeq p a₀ c n).getD i 0 = (lucasTypeSeq p a₀ c i).getD i 0 := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    rcases Nat.lt_or_ge i (n + 1) with hi | hi
    · have h' := ih (by omega)
      rw [lucasTypeSeq]
      simp only [List.getD_eq_getElem?_getD] at h' ⊢
      rw [List.getElem?_append_left (by rw [lucasTypeSeq_length]; omega)]
      exact h'
    · obtain rfl : i = n + 1 := by omega
      rfl

/-- **Last entry of a Lucas-type list.** Let $\alpha$ be a type with a zero, a one and an
addition, let $p$ be a natural number and let $a_0, c \in \alpha$. Write $S_m$ for the Lucas-type
list with parameters $p$, $a_0$, $c$ ending at index $m$, and $S_m[i]$ for its entry at index $i$.
Then for every natural number $n$, $S_{n+1}[n+1] = 1$ if $n + 1 \le p$, and otherwise
$S_{n+1}[n+1] = S_n[n] + S_{n-p}[n-p] + c$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasTypeSeq_getD_succ {α : Type*} [Zero α] [One α] [Add α] (p : ℕ) (a₀ c : α)
    (n : ℕ) :
    (lucasTypeSeq p a₀ c (n + 1)).getD (n + 1) 0 =
      if n + 1 ≤ p then 1
      else (lucasTypeSeq p a₀ c n).getD n 0 +
        (lucasTypeSeq p a₀ c (n - p)).getD (n - p) 0 + c := by
  have h := lucasTypeSeq_getD p a₀ c (show n - p ≤ n by omega)
  rw [lucasTypeSeq]
  simp only [List.getD_eq_getElem?_getD] at h ⊢
  rw [List.getElem?_append_right (by rw [lucasTypeSeq_length]), h]
  simp [lucasTypeSeq_length]

/-- **Lucas $p$-numbers.** For a natural number $p$, the Lucas $p$-numbers are the natural numbers
$L_{p,n}$ given by $L_{p,0} = p + 1$, $L_{p,i} = 1$ for $1 \le i \le p$, and
$L_{p,n} = L_{p,n-1} + L_{p,n-p-1}$ for $n > p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Section 1 (after (6)). -/
def lucasP (p n : ℕ) : ℕ := (lucasTypeSeq p (p + 1) 0 n).getD n 0

/-- **Initial Lucas $p$-number.** For every natural number $p$, the Lucas $p$-number $L_{p,0}$
equals $p + 1$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasP_zero (p : ℕ) : lucasP p 0 = p + 1 := rfl

/-- **Lucas $p$-numbers at indices $1$ to $p$.** For every natural number $p$ and every $n$ with
$1 \le n \le p$, the Lucas $p$-number $L_{p,n}$ equals $1$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasP_of_le (p : ℕ) {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ p) : lucasP p n = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasP, lucasTypeSeq_getD_succ]
  simp [hn]

/-- **Recurrence for the Lucas $p$-numbers.** For every natural number $p$, write $L_{p,n}$ for
the Lucas $p$-numbers. Then $L_{p,n} = L_{p,n-1} + L_{p,n-p-1}$ for every $n > p$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasP_of_lt (p : ℕ) {n : ℕ} (hn : p < n) :
    lucasP p n = lucasP p (n - 1) + lucasP p (n - p - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasP, lucasTypeSeq_getD_succ]
  simp [lucasP, show ¬m + 1 ≤ p by omega, show m + 1 - p - 1 = m - p by omega]

/-- **Lucas-Leonardo $p$-numbers.** For a natural number $p$, the Lucas-Leonardo $p$-numbers are
the integers $R_{p,n}$ given by $R_{p,0} = p^2 + p + 1$, $R_{p,i} = 1$ for $1 \le i \le p$, and
$R_{p,n} = R_{p,n-1} + R_{p,n-p-1} + p$ for $n > p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Section 1, display (5). -/
def lucasLeonardoP (p n : ℕ) : ℤ :=
  (lucasTypeSeq p ((p : ℤ) ^ 2 + p + 1) (p : ℤ) n).getD n 0

/-- **Initial Lucas-Leonardo $p$-number.** For every natural number $p$, the Lucas-Leonardo
$p$-number $R_{p,0}$ equals $p^2 + p + 1$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (5). -/
theorem lucasLeonardoP_zero (p : ℕ) : lucasLeonardoP p 0 = (p : ℤ) ^ 2 + p + 1 := rfl

/-- **Lucas-Leonardo $p$-numbers at indices $1$ to $p$.** For every natural number $p$ and every
$n$ with $1 \le n \le p$, the Lucas-Leonardo $p$-number $R_{p,n}$ equals $1$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (5). -/
theorem lucasLeonardoP_of_le (p : ℕ) {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ p) :
    lucasLeonardoP p n = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasLeonardoP, lucasTypeSeq_getD_succ]
  simp [hn]

/-- **Recurrence for the Lucas-Leonardo $p$-numbers.** For every natural number $p$, write
$R_{p,n}$ for the Lucas-Leonardo $p$-numbers. Then $R_{p,n} = R_{p,n-1} + R_{p,n-p-1} + p$ for
every $n > p$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (5). -/
theorem lucasLeonardoP_of_lt (p : ℕ) {n : ℕ} (hn : p < n) :
    lucasLeonardoP p n = lucasLeonardoP p (n - 1) + lucasLeonardoP p (n - p - 1) + p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasLeonardoP, lucasTypeSeq_getD_succ]
  simp [lucasLeonardoP, show ¬m + 1 ≤ p by omega, show m + 1 - p - 1 = m - p by omega]

/-- **First values of the Lucas and Lucas-Leonardo $1$-numbers.** The Lucas $1$-numbers
$L_{1,0}, \dots, L_{1,5}$ are $2, 1, 3, 4, 7, 11$, and the Lucas-Leonardo $1$-numbers
$R_{1,0}, \dots, R_{1,5}$ are $3, 1, 5, 7, 13, 21$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasP_lucasLeonardoP_one_values :
    (List.range 6).map (lucasP 1) = [2, 1, 3, 4, 7, 11] ∧
      (List.range 6).map (lucasLeonardoP 1) = [3, 1, 5, 7, 13, 21] := by
  decide

/-- **Incomplete Leonardo p-numbers.** For natural numbers $p$, $n$ and $k$, the incomplete
Leonardo $p$-number is the integer
$$
\mathcal{L}_{p,n}(k) = (p + 1) \sum_{i=0}^{k} \binom{\max(n - pi, 0)}{i} - p.
$$
On the paper's range $0 \le k \le \lfloor n/(p+1) \rfloor$ the maximum is always $n - pi$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, display (4). -/
def incompleteLeonardoP (p n k : ℕ) : ℤ :=
  (p + 1) * ∑ i ∈ Finset.range (k + 1), ((n - p * i).choose i : ℤ) - p

/-- **Incomplete Leonardo p-numbers at zero.** For all natural numbers $p$ and $n$, the
incomplete Leonardo $p$-number $\mathcal{L}_{p,n}(0)$ equals $1$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (4). -/
theorem incompleteLeonardoP_zero (p n : ℕ) : incompleteLeonardoP p n 0 = 1 := by
  simp [incompleteLeonardoP]

/-- **Incomplete Lucas-Leonardo p-numbers.** For natural numbers $p$, $n$ and $k$, the
incomplete Lucas-Leonardo $p$-number is the rational number
$$
R_{p,n}(k) = (p + 1) \sum_{i=0}^{k} \frac{n}{m_i} \binom{m_i}{i} - p, \qquad m_i = \max(n - pi, 0),
$$
where a summand with $m_i = 0$ is taken to be $0$. On the paper's range
$0 \le k \le \lfloor n/(p+1) \rfloor$ with $n \ge 1$, every $m_i$ is positive.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, display (8). -/
def incompleteLucasLeonardoP (p n k : ℕ) : ℚ :=
  (p + 1) * ∑ i ∈ Finset.range (k + 1),
    (n : ℚ) / ((n - p * i : ℕ) : ℚ) * ((n - p * i).choose i : ℚ) - p

/-- **Incomplete Lucas-Leonardo p-numbers at zero.** For every natural number $p$ and every
natural number $n \ge 1$, the incomplete Lucas-Leonardo $p$-number $R_{p,n}(0)$ equals $1$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (8). -/
theorem incompleteLucasLeonardoP_zero (p n : ℕ) (hn : 1 ≤ n) :
    incompleteLucasLeonardoP p n 0 = 1 := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp [incompleteLucasLeonardoP, hn']

/-- **Hyper Leonardo $p$-numbers.** For natural numbers $p$, $n$ and $k$, the hyper Leonardo
$p$-number is the integer

$$\mathcal{L}^{(k)}_{p,n} = (p + 1) \sum_{i=0}^{\lfloor n/(p+1) \rfloor}
\binom{n + k - pi}{i + k} - p \binom{n + k}{k}.$$

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, display (12) (quoting
Belaggoun and Belbachir). -/
def hyperLeonardoP (p n k : ℕ) : ℤ :=
  (p + 1) * ∑ i ∈ Finset.range (n / (p + 1) + 1), ((n + k - p * i).choose (i + k) : ℤ) -
    p * ((n + k).choose k : ℤ)

/-- **Hyper Leonardo $p$-numbers at $n = 0$.** For all natural numbers $p$ and $k$, the hyper
Leonardo $p$-number $\mathcal{L}^{(k)}_{p,0}$ equals $1$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (12) and
Proposition 10. -/
theorem hyperLeonardoP_zero_left (p k : ℕ) : hyperLeonardoP p 0 k = 1 := by
  simp [hyperLeonardoP]

/-- **Hyper Lucas-Leonardo p-numbers.** For natural numbers $p$, $n$ and $k$, the hyper
Lucas-Leonardo $p$-number $R^{(k)}_{p,n}$ is the rational number defined by
$R^{(0)}_{p,n} = R_{p,n}$, the Lucas-Leonardo $p$-number; $R^{(k)}_{p,0} = p^2 + p + 1$ for
$k \ge 1$; and, for $n \ge 1$ and $k \ge 1$,
$$
R^{(k)}_{p,n} = (p + 1) \sum_{i=0}^{\lfloor n/(p+1) \rfloor} \frac{n + (p+1)k}{n + k - pi}
\binom{n + k - pi}{i + k} - p \binom{n + k}{k}.
$$

For $p = 2$ this reproduces the values listed in the paper. For $p = 1$ the listed values $122$
(for $R^{(1)}_{1,7}$), $101, 186, 308$ (for $R^{(2)}_{1,5}, R^{(2)}_{1,6}, R^{(2)}_{1,7}$) and
$220, 406, 714$ (for $R^{(3)}_{1,5}, R^{(3)}_{1,6}, R^{(3)}_{1,7}$) are misprints: the definition
gives $142$; $111, 196, 338$; and $230, 426, 764$, the values that the recurrence
$R^{(k)}_{1,n} = R^{(k)}_{1,n-1} + R^{(k-1)}_{1,n}$ produces from the paper's own earlier
entries.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Definition 2. -/
def hyperLucasLeonardoP (p n k : ℕ) : ℚ :=
  if k = 0 then (lucasLeonardoP p n : ℚ)
  else if n = 0 then (p : ℚ) ^ 2 + p + 1
  else (p + 1) * ∑ i ∈ Finset.range (n / (p + 1) + 1),
      ((n + (p + 1) * k : ℕ) : ℚ) / ((n + k - p * i : ℕ) : ℚ) *
        ((n + k - p * i).choose (i + k) : ℚ) -
    p * ((n + k).choose k : ℚ)

/-- **Hyper Lucas–Leonardo $p$-numbers at $n = 0$.** For all natural numbers $p$ and $k$, the
hyper Lucas–Leonardo $p$-number $R^{(k)}_{p,0}$ equals $p^2 + p + 1$.

For $k = 0$ this is the initial value $R_{p,0} = p^2 + p + 1$ of the Lucas–Leonardo $p$-numbers.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Definition 2. -/
theorem hyperLucasLeonardoP_zero_left (p k : ℕ) :
    hyperLucasLeonardoP p 0 k = (p : ℚ) ^ 2 + p + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hyperLucasLeonardoP, lucasLeonardoP_zero]
  · simp [hyperLucasLeonardoP, show k ≠ 0 by omega]

/-- **Hyper Lucas-Leonardo p-numbers of order zero.** For all natural numbers $p$ and $n$, the
hyper Lucas-Leonardo $p$-number of order $0$ equals the Lucas-Leonardo $p$-number:
$R^{(0)}_{p,n} = R_{p,n}$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Definition 2. -/
theorem hyperLucasLeonardoP_zero_right (p n : ℕ) :
    hyperLucasLeonardoP p n 0 = lucasLeonardoP p n := by
  simp [hyperLucasLeonardoP]

/-- **Leonardo $p$-tilings.** For natural numbers $p$ and $n$, the tiling set $K_{p,n}$ consists
of the linear tilings of an $n$-board by squares (length $1$), $p$-minos (length $p + 1$) and at
most one $p$-tile, which comes in one of $p$ colors, has length at least $p + 1$, and can only be
the initial piece. A tiling is recorded as its initial $p$-tile, given by its color and length,
if there is one, followed by the sequence of the remaining pieces read from left to right, each a
square or a $p$-mino; the lengths of all pieces sum to $n$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Definition 1 and the set
`K_{p,n}` before Proposition 1. -/
def leonardoPTilings (p n : ℕ) : Set (Option (Fin p × ℕ) × List Bool) :=
  {t | (∀ c l, t.1 = some (c, l) → p + 1 ≤ l) ∧
    t.1.elim 0 Prod.snd + (t.2.map fun b => if b then p + 1 else 1).sum = n}

/-- **The all-squares tiling is a Leonardo $p$-tiling.** For all natural numbers $p$ and $n$, the
linear tiling of an $n$-board by $n$ squares, with no $p$-tile, lies in the tiling set $K_{p,n}$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 2. -/
theorem replicate_mem_leonardoPTilings (p n : ℕ) :
    ((none : Option (Fin p × ℕ)), List.replicate n false) ∈ leonardoPTilings p n := by
  simp [leonardoPTilings, List.map_replicate, List.sum_replicate]

/-- **First tile of a bracelet.** For a natural number $p$, a first tile records the tile of a
bracelet that covers cell $1$ of the circular board, together with its phase (which cell of the
tile covers cell $1$). It is one of: a curved square, in phase $1$; a curved $p$-mino of length
$p + 1$ in phase $r + 1$ for some $0 \le r \le p$; a curved $p$-tile of length $p + 1$ in color
$c$ for some $0 \le c < p$ and phase $r + 1$ for some $0 \le r \le p$; or a curved $p$-tile of
length $l$ in color $c$ for some $0 \le c < p$ and some natural number $l$, starting at cell $1$
(phase $1$).

The restriction $l \ge p + 2$ on the last kind is not part of this type; the bracelet sets
impose it.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Section 3. -/
inductive BraceletFirstTile (p : ℕ) where
  /-- A curved square (phase `1`). -/
  | square
  /-- A curved `p`-mino (length `p + 1`) in phase `r + 1`. -/
  | mino (r : Fin (p + 1))
  /-- A curved `p`-tile of length `p + 1`, in color `c` and phase `r + 1`. -/
  | shortTile (c : Fin p) (r : Fin (p + 1))
  /-- A curved `p`-tile of length `l` in color `c`, starting at cell `1` (phase `1`). -/
  | longTile (c : Fin p) (l : ℕ)

/-- **Length of the first tile of a bracelet.** For a natural number $p$, the length of the first
tile of a bracelet is $1$ for a curved square, $p + 1$ for a curved $p$-mino in any phase,
$p + 1$ for a curved $p$-tile of length $p + 1$ in any color and phase, and $l$ for a curved
$p$-tile of length $l$ (in any color) starting at cell $1$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 3. -/
def BraceletFirstTile.length {p : ℕ} : BraceletFirstTile p → ℕ
  | .square => 1
  | .mino _ => p + 1
  | .shortTile _ _ => p + 1
  | .longTile _ l => l

/-- **Lucas–Leonardo bracelets.** For natural numbers $p$ and $n$, the bracelet set $B_{p,n}$
consists of the tilings of a circular $n$-board by curved squares (length $1$), curved $p$-minos
(length $p + 1$) and at most one curved $p$-tile, which comes in one of $p$ colors and has either
length $p + 1$, in any of its $p + 1$ phases, or length $l \ge p + 2$, starting at cell $1$; a
$p$-tile, if present, is the first tile. A bracelet is recorded as its first tile, the one
covering cell $1$, together with its phase, followed by the sequence of the remaining pieces read
clockwise, each a curved square or a curved $p$-mino; the lengths of all pieces sum to $n$. In
particular $B_{p,0}$ is empty.

The source sets $|B_{p,0}| = p^2 + p + 1$ by convention; that value is not modelled here.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Section 3, the set
`B_{p,n}` before Proposition 12. -/
def lucasLeonardoBracelets (p n : ℕ) : Set (BraceletFirstTile p × List Bool) :=
  {b | (∀ c l, b.1 = .longTile c l → p + 2 ≤ l) ∧
    b.1.length + (b.2.map fun t => if t then p + 1 else 1).sum = n}

/-- **The all-squares bracelet is a Lucas–Leonardo bracelet.** For every natural number $p$ and
every natural number $n \ge 1$, the bracelet whose first tile is a curved square covering cell $1$
and whose remaining $n - 1$ pieces are all curved squares lies in the bracelet set $B_{p,n}$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 3. -/
theorem square_replicate_mem_lucasLeonardoBracelets (p n : ℕ) (hn : 1 ≤ n) :
    ((.square : BraceletFirstTile p), List.replicate (n - 1) false) ∈
      lucasLeonardoBracelets p n := by
  simp [lucasLeonardoBracelets, BraceletFirstTile.length, List.map_replicate,
    List.sum_replicate]
  omega

/-- **Counting Leonardo $p$-tilings.** For all natural numbers $p \ge 1$ and $n$, let $K_{p,n}$ be
the set of linear tilings of an $n$-board by squares (length $1$), $p$-minos (length $p + 1$) and
at most one $p$-tile, which comes in one of $p$ colors, has length at least $p + 1$ and can only
be the initial piece. Then the number of tilings in $K_{p,n}$ equals the Leonardo $p$-number
$\mathcal{L}_{p,n}$, the generalized Leonardo $p$-number $\mathcal{L}_{p,k}(n)$ at $k = p$:
$\mathcal{L}_{p,n} = 1$ for $n \le p$ and
$\mathcal{L}_{p,n} = \mathcal{L}_{p,n-1} + \mathcal{L}_{p,n-p-1} + p$ for $n > p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 1. -/
public theorem_wanted card_leonardoPTilings (p n : ℕ) (hp : 1 ≤ p) :
    (Nat.card (leonardoPTilings p n) : ℤ) = leonardoPK p p n

/-- **Homogeneous recurrence for the Leonardo $p$-numbers.** Let $p \ge 1$ and write
$\mathcal{L}_{p,n}$ for the Leonardo $p$-number $\mathcal{L}_{p,p}(n)$, the generalized Leonardo
$p$-number with $k = p$. Then $\mathcal{L}_{p,n} = \mathcal{L}_{p,n-1} + \mathcal{L}_{p,n-p} -
\mathcal{L}_{p,n-2p-1}$ for every $n \ge 2p + 1$, $\mathcal{L}_{p,i} = 1$ for every $i \le p$,
and $\mathcal{L}_{p,p+j} = (j + 1) + jp$ for every $j$ with $1 \le j \le p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 2. -/
public theorem_wanted leonardoPK_self_homogeneous (p : ℕ) (hp : 1 ≤ p) :
    (∀ n, 2 * p + 1 ≤ n →
      leonardoPK p p n =
        leonardoPK p p (n - 1) + leonardoPK p p (n - p) - leonardoPK p p (n - 2 * p - 1)) ∧
    (∀ i, i ≤ p → leonardoPK p p i = 1) ∧
    (∀ j, 1 ≤ j → j ≤ p → leonardoPK p p (p + j) = (j : ℤ) + 1 + j * p)

/-- **Recurrence for incomplete Leonardo p-numbers.** For natural numbers $p \ge 1$, $n > p$ and
$k \le \lfloor n/(p+1) \rfloor$, the incomplete Leonardo $p$-numbers $\mathcal{L}_{p,m}(j)$
satisfy
$$
\mathcal{L}_{p,n}(k + 1) = \mathcal{L}_{p,n-1}(k + 1) + \mathcal{L}_{p,n-p-1}(k) + p.
$$

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 6. -/
public theorem_wanted incompleteLeonardoP_succ (p n k : ℕ) (hp : 1 ≤ p) (hn : p < n)
    (hk : k ≤ n / (p + 1)) :
    incompleteLeonardoP p n (k + 1) =
      incompleteLeonardoP p (n - 1) (k + 1) + incompleteLeonardoP p (n - p - 1) k + p

/-- **Binomial sum identity for incomplete Leonardo p-numbers.** For natural numbers $p \ge 1$,
$n$, $r$ and $k$ with $n \ge p + r$ and $k \le \lfloor (n - p - r)/(p + 1) \rfloor$, the
incomplete Leonardo $p$-numbers $\mathcal{L}_{p,m}(j)$ satisfy
$$
\sum_{i=0}^{r} \binom{r}{i} \mathcal{L}_{p,n+pi}(k + i) + (2^r - 1) p =
\mathcal{L}_{p,n+(p+1)r}(k + r).
$$

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 7. -/
public theorem_wanted sum_choose_mul_incompleteLeonardoP (p n r k : ℕ) (hp : 1 ≤ p)
    (hnr : p + r ≤ n) (hk : k ≤ (n - p - r) / (p + 1)) :
    ∑ i ∈ Finset.range (r + 1), (r.choose i : ℤ) * incompleteLeonardoP p (n + p * i) (k + i) +
        ((2 : ℤ) ^ r - 1) * p =
      incompleteLeonardoP p (n + (p + 1) * r) (k + r)

/-- **Partial sums of incomplete Leonardo p-numbers.** For natural numbers $p \ge 1$, $n$, $k$ and
$r$ with $n \ge (p + 1)(k + 1)$, the incomplete Leonardo $p$-numbers $\mathcal{L}_{p,m}(j)$
satisfy
$$
\sum_{i=0}^{r-1} \mathcal{L}_{p,n-p+i}(k) + rp =
\mathcal{L}_{p,n+r}(k + 1) - \mathcal{L}_{p,n}(k + 1),
$$
where the sum is empty when $r = 0$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 8. -/
public theorem_wanted sum_incompleteLeonardoP (p n k r : ℕ) (hp : 1 ≤ p)
    (hn : (p + 1) * (k + 1) ≤ n) :
    ∑ i ∈ Finset.range r, incompleteLeonardoP p (n - p + i) k + (r : ℤ) * p =
      incompleteLeonardoP p (n + r) (k + 1) - incompleteLeonardoP p n (k + 1)

/-- **Binomial addition formula for hyper Leonardo $p$-numbers.** For natural numbers $p \ge 1$,
$n \ge 1$, $m \ge 1$ and $k \ge m$, the hyper Leonardo $p$-numbers satisfy
$$\mathcal{L}^{(k)}_{p,n+m} = \sum_{i=0}^{m} \binom{m}{i} \mathcal{L}^{(k-i)}_{p,n+i}.$$

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 9. -/
public theorem_wanted hyperLeonardoP_add (p n m k : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hmk : m ≤ k) :
    hyperLeonardoP p (n + m) k =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℤ) * hyperLeonardoP p (n + i) (k - i)

/-- **Recurrence for the hyper Leonardo $p$-numbers.** Let $p \ge 1$ be a natural number. For all
natural numbers $n \ge 1$ and $k \ge 1$, the hyper Leonardo $p$-numbers satisfy
$\mathcal{L}^{(k)}_{p,n} = \mathcal{L}^{(k)}_{p,n-1} + \mathcal{L}^{(k-1)}_{p,n}$, and for every
natural number $n$, $\mathcal{L}^{(0)}_{p,n} = \mathcal{L}_{p,n}$, where $\mathcal{L}_{p,n}$ is the
Leonardo $p$-number: $\mathcal{L}_{p,n} = 1$ for $n \le p$ and
$\mathcal{L}_{p,n} = \mathcal{L}_{p,n-1} + \mathcal{L}_{p,n-p-1} + p$ for $n > p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 10. -/
public theorem_wanted hyperLeonardoP_rec (p : ℕ) (hp : 1 ≤ p) :
    (∀ n k, 1 ≤ n → 1 ≤ k →
      hyperLeonardoP p n k = hyperLeonardoP p (n - 1) k + hyperLeonardoP p n (k - 1)) ∧
    ∀ n, hyperLeonardoP p n 0 = leonardoPK p p n

/-- **Leonardo p-numbers split into incomplete and hyper parts.** For natural numbers $p \ge 1$,
$n > p$ and $k \ge 1$, let $N = n + (p + 1)k$. Then
$$
\mathcal{L}_{p,N} = \mathcal{L}_{p,N}(k - 1) + \mathcal{L}^{(k)}_{p,n} + p \binom{n + k}{k},
$$
where $\mathcal{L}_{p,N}$ is the Leonardo $p$-number (the generalized Leonardo $p$-numbers with
additive constant $p$: $\mathcal{L}_{p,m} = 1$ for $m \le p$ and
$\mathcal{L}_{p,m} = \mathcal{L}_{p,m-1} + \mathcal{L}_{p,m-p-1} + p$ for $m > p$),
$\mathcal{L}_{p,N}(k - 1)$ is the incomplete Leonardo $p$-number and $\mathcal{L}^{(k)}_{p,n}$ is
the hyper Leonardo $p$-number.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 11. -/
public theorem_wanted leonardoPK_eq_incomplete_add_hyper (p n k : ℕ) (hp : 1 ≤ p)
    (hn : p < n) (hk : 1 ≤ k) :
    leonardoPK p p (n + (p + 1) * k) =
      incompleteLeonardoP p (n + (p + 1) * k) (k - 1) + hyperLeonardoP p n k +
        p * ((n + k).choose k : ℤ)

/-- **Counting Lucas–Leonardo bracelets.** For all natural numbers $p \ge 1$ and $n \ge 1$, let
$B_{p,n}$ be the set of tilings of a circular $n$-board by curved squares (length $1$), curved
$p$-minos (length $p + 1$) and at most one curved $p$-tile in one of $p$ colors, which if present
is the tile covering cell $1$ and either has length $p + 1$, in any of its $p + 1$ phases, or has
length at least $p + 2$ and starts at cell $1$. Then the number of bracelets in $B_{p,n}$ equals
the Lucas–Leonardo $p$-number $R_{p,n}$, given by $R_{p,0} = p^2 + p + 1$, $R_{p,i} = 1$ for
$1 \le i \le p$ and $R_{p,n} = R_{p,n-1} + R_{p,n-p-1} + p$ for $n > p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 12. -/
public theorem_wanted card_lucasLeonardoBracelets (p n : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (Nat.card (lucasLeonardoBracelets p n) : ℤ) = lucasLeonardoP p n

/-- **Lucas-Leonardo $p$-numbers from Lucas $p$-numbers.** For every $p \ge 1$ and every
natural number $n$, the Lucas-Leonardo $p$-number $R_{p,n}$ and the Lucas $p$-number $L_{p,n}$
satisfy $R_{p,n} = (p + 1) L_{p,n} - p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 13. -/
public theorem_wanted lucasLeonardoP_eq_lucasP (p n : ℕ) (hp : 1 ≤ p) :
    lucasLeonardoP p n = ((p : ℤ) + 1) * lucasP p n - p

/-- **Lucas-Leonardo $p$-numbers from Leonardo $p$-numbers.** Let $p \ge 1$, let $R_{p,n}$ denote
the Lucas-Leonardo $p$-numbers, and let $\mathcal{L}_{p,n}$ denote the Leonardo $p$-numbers
$\mathcal{L}_{p,p}(n)$ (the generalized Leonardo $p$-numbers with $k = p$), extended to $n = -1$
by $\mathcal{L}_{p,-1} = -p$. Then $R_{p,n} = (p + 1) \mathcal{L}_{p,n} - p \mathcal{L}_{p,n-1}$
for every natural number $n$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 14. -/
public theorem_wanted lucasLeonardoP_eq_leonardoPK (p n : ℕ) (hp : 1 ≤ p) :
    lucasLeonardoP p n = ((p : ℤ) + 1) * leonardoPK p p n - p * leonardoPKZ p p ((n : ℤ) - 1)

/-- **Sum of the Lucas-Leonardo p-numbers.** For every natural number $p \ge 1$ and every natural
number $n$, the Lucas-Leonardo $p$-numbers $R_{p,m}$ satisfy
$\sum_{i=0}^{n} R_{p,i} = R_{p,n+p+1} - p(n + 1) - 1$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 15. -/
public theorem_wanted sum_lucasLeonardoP (p n : ℕ) (hp : 1 ≤ p) :
    ∑ i ∈ Finset.range (n + 1), lucasLeonardoP p i =
      lucasLeonardoP p (n + p + 1) - p * ((n : ℤ) + 1) - 1

/-- **Sum of the Lucas-Leonardo p-numbers at multiples of $p + 1$.** For every natural number
$p \ge 1$ and every natural number $n$, the Lucas-Leonardo $p$-numbers $R_{p,m}$ satisfy
$\sum_{i=0}^{n} R_{p,(p+1)i} = R_{p,(p+1)n+1} - p(n - p - 1)$, an identity of integers.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 16. -/
public theorem_wanted sum_lucasLeonardoP_stride (p n : ℕ) (hp : 1 ≤ p) :
    ∑ i ∈ Finset.range (n + 1), lucasLeonardoP p ((p + 1) * i) =
      lucasLeonardoP p ((p + 1) * n + 1) - p * ((n : ℤ) - p - 1)

/-- **Recurrence for incomplete Lucas-Leonardo p-numbers.** For natural numbers $p \ge 1$,
$n > p + 1$ and $k \le \lfloor n/(p+1) \rfloor$, the incomplete Lucas-Leonardo $p$-numbers
$R_{p,m}(j)$ satisfy
$$
R_{p,n}(k + 1) = R_{p,n-1}(k + 1) + R_{p,n-p-1}(k) + p.
$$

At $n = p + 1$ the term $R_{p,0}(k)$ would contain the undefined summand
$\frac{0}{0} \binom{0}{0}$, so that case is excluded.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 17. -/
public theorem_wanted incompleteLucasLeonardoP_succ (p n k : ℕ) (hp : 1 ≤ p)
    (hn : p + 1 < n) (hk : k ≤ n / (p + 1)) :
    incompleteLucasLeonardoP p n (k + 1) =
      incompleteLucasLeonardoP p (n - 1) (k + 1) + incompleteLucasLeonardoP p (n - p - 1) k +
        p

/-- **Binomial sum identity for incomplete Lucas-Leonardo p-numbers.** For natural numbers
$p \ge 1$, $n$, $r$ and $k$ with $n \ge p + r$ and $k \le \lfloor (n - p - r)/(p + 1) \rfloor$,
the incomplete Lucas-Leonardo $p$-numbers $R_{p,m}(j)$ satisfy, as rational numbers,
$$
\sum_{i=0}^{r} \binom{r}{i} R_{p,n+pi}(k + i) + (2^r - 1) p = R_{p,n+(p+1)r}(k + r).
$$

The paper prints the range as $0 \le n \le \lfloor (n - p - r)/(p + 1) \rfloor$; the first $n$
is read as $k$, as in Proposition 7.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 18. -/
public theorem_wanted sum_choose_mul_incompleteLucasLeonardoP (p n r k : ℕ) (hp : 1 ≤ p)
    (hnr : p + r ≤ n) (hk : k ≤ (n - p - r) / (p + 1)) :
    ∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℚ) * incompleteLucasLeonardoP p (n + p * i) (k + i) +
        ((2 : ℚ) ^ r - 1) * p =
      incompleteLucasLeonardoP p (n + (p + 1) * r) (k + r)

/-- **Hyper Lucas–Leonardo numbers from incomplete ones.** For natural numbers $p \ge 1$, $n > p$
and $k \ge 1$, write $R_{p,m}$ for the Lucas–Leonardo $p$-numbers and $R_{p,m}(j)$ for the
incomplete Lucas–Leonardo $p$-numbers. Then the hyper Lucas–Leonardo $p$-number $R^{(k)}_{p,n}$
satisfies

$$R^{(k)}_{p,n} = R_{p,n+(p+1)k} - R_{p,n+(p+1)k}(k - 1) - p \binom{n + k}{k}.$$

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 19. -/
public theorem_wanted hyperLucasLeonardoP_eq (p n k : ℕ) (hp : 1 ≤ p) (hn : p < n)
    (hk : 1 ≤ k) :
    hyperLucasLeonardoP p n k =
      lucasLeonardoP p (n + (p + 1) * k) -
        incompleteLucasLeonardoP p (n + (p + 1) * k) (k - 1) - p * ((n + k).choose k : ℚ)

/-- **Hyper Lucas–Leonardo numbers from hyper Leonardo numbers.** For natural numbers $p \ge 1$,
$n > p$ and $k \ge 1$, the hyper Lucas–Leonardo $p$-number $R^{(k)}_{p,n}$ and the hyper
Leonardo $p$-numbers $\mathcal{L}^{(k)}_{p,n}$ satisfy

$$R^{(k)}_{p,n} = (p + 1) \mathcal{L}^{(k)}_{p,n} - p \mathcal{L}^{(k)}_{p,n-1} +
p^2 \binom{n + k - 1}{k - 1}.$$

The paper prints the binomial as $\binom{n + k - 1}{k}$, which is false: at $p = 1$, $n = 2$,
$k = 1$ one has $R^{(1)}_{1,2} = 9$ while the printed right side is $10$. The paper's own proof
ends with $p^2 \binom{n + k - 1}{k - 1}$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 20. -/
public theorem_wanted hyperLucasLeonardoP_eq_hyperLeonardoP (p n k : ℕ) (hp : 1 ≤ p)
    (hn : p < n) (hk : 1 ≤ k) :
    hyperLucasLeonardoP p n k =
      ((p : ℚ) + 1) * hyperLeonardoP p n k - p * hyperLeonardoP p (n - 1) k +
        (p : ℚ) ^ 2 * ((n + k - 1).choose (k - 1) : ℚ)

end

end MetaMathlibExt
