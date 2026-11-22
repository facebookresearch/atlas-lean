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

/-- Shared-prefix evaluation of the recurrence `a_0 = a₀`, `a_i = 1` for `1 ≤ i ≤ p`,
`a_n = a_{n-1} + a_{n-p-1} + c` for `n > p`: `lucasTypeSeq p a₀ c n` is the list
`[a_0, …, a_n]`, built by appending one value per step to the previous list, so each
earlier value is computed once and evaluation is quadratic in `n` (list append and lookups
are linear), not exponential as with the naive two-branch recursion. The Lucas and
Lucas-Leonardo `p`-numbers are the cases `c = 0` and `c = p`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Section 1, display (5). -/
def lucasTypeSeq {α : Type*} [Zero α] [One α] [Add α] (p : ℕ) (a₀ c : α) : ℕ → List α
  | 0 => [a₀]
  | n + 1 =>
      let prev := lucasTypeSeq p a₀ c n
      prev ++ [if n + 1 ≤ p then 1 else prev.getD n 0 + prev.getD (n - p) 0 + c]

/-- `lucasTypeSeq p a₀ c n` has `n + 1` entries.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasTypeSeq_length {α : Type*} [Zero α] [One α] [Add α] (p : ℕ) (a₀ c : α)
    (n : ℕ) : (lucasTypeSeq p a₀ c n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lucasTypeSeq, ih]

/-- Entry `i ≤ n` of `lucasTypeSeq p a₀ c n` does not depend on `n`.

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

/-- The last entry of `lucasTypeSeq p a₀ c (n + 1)` is the recurrence step.

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

/-- The Lucas `p`-numbers: `L_{p,0} = p + 1`, `L_{p,i} = 1` for `1 ≤ i ≤ p`, and
`L_{p,n} = L_{p,n-1} + L_{p,n-p-1}` for `n > p` (evaluated by `lucasTypeSeq`).

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Section 1 (after (6)). -/
def lucasP (p n : ℕ) : ℕ := (lucasTypeSeq p (p + 1) 0 n).getD n 0

/-- `L_{p,0} = p + 1`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasP_zero (p : ℕ) : lucasP p 0 = p + 1 := rfl

/-- `L_{p,n} = 1` for `1 ≤ n ≤ p`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasP_of_le (p : ℕ) {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ p) : lucasP p n = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasP, lucasTypeSeq_getD_succ]
  simp [hn]

/-- `L_{p,n} = L_{p,n-1} + L_{p,n-p-1}` for `n > p`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasP_of_lt (p : ℕ) {n : ℕ} (hn : p < n) :
    lucasP p n = lucasP p (n - 1) + lucasP p (n - p - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasP, lucasTypeSeq_getD_succ]
  simp [lucasP, show ¬m + 1 ≤ p by omega, show m + 1 - p - 1 = m - p by omega]

/-- The Lucas-Leonardo `p`-numbers: `R_{p,0} = p² + p + 1`, `R_{p,i} = 1` for
`1 ≤ i ≤ p`, and `R_{p,n} = R_{p,n-1} + R_{p,n-p-1} + p` for `n > p` (evaluated by
`lucasTypeSeq`).

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Section 1, display (5). -/
def lucasLeonardoP (p n : ℕ) : ℤ :=
  (lucasTypeSeq p ((p : ℤ) ^ 2 + p + 1) (p : ℤ) n).getD n 0

/-- `R_{p,0} = p² + p + 1`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (5). -/
theorem lucasLeonardoP_zero (p : ℕ) : lucasLeonardoP p 0 = (p : ℤ) ^ 2 + p + 1 := rfl

/-- `R_{p,n} = 1` for `1 ≤ n ≤ p`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (5). -/
theorem lucasLeonardoP_of_le (p : ℕ) {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ p) :
    lucasLeonardoP p n = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasLeonardoP, lucasTypeSeq_getD_succ]
  simp [hn]

/-- `R_{p,n} = R_{p,n-1} + R_{p,n-p-1} + p` for `n > p`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (5). -/
theorem lucasLeonardoP_of_lt (p : ℕ) {n : ℕ} (hn : p < n) :
    lucasLeonardoP p n = lucasLeonardoP p (n - 1) + lucasLeonardoP p (n - p - 1) + p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasLeonardoP, lucasTypeSeq_getD_succ]
  simp [lucasLeonardoP, show ¬m + 1 ≤ p by omega, show m + 1 - p - 1 = m - p by omega]

/-- Values check against the recurrence: `L_{1,·} = 2, 1, 3, 4, 7, 11` and
`R_{1,·} = 3, 1, 5, 7, 13, 21`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 1. -/
theorem lucasP_lucasLeonardoP_one_values :
    (List.range 6).map (lucasP 1) = [2, 1, 3, 4, 7, 11] ∧
      (List.range 6).map (lucasLeonardoP 1) = [3, 1, 5, 7, 13, 21] := by
  decide

/-- The incomplete Leonardo `p`-numbers
`𝓛_{p,n}(k) = (p + 1) ∑_{i=0}^{k} C(n - pi, i) - p` (natural-number subtraction; the
paper uses `0 ≤ k ≤ ⌊n/(p+1)⌋`, where it does not truncate).

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, display (4). -/
def incompleteLeonardoP (p n k : ℕ) : ℤ :=
  (p + 1) * ∑ i ∈ Finset.range (k + 1), ((n - p * i).choose i : ℤ) - p

/-- `𝓛_{p,n}(0) = 1`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (4). -/
theorem incompleteLeonardoP_zero (p n : ℕ) : incompleteLeonardoP p n 0 = 1 := by
  simp [incompleteLeonardoP]

/-- The incomplete Lucas-Leonardo `p`-numbers
`R_{p,n}(k) = (p + 1) ∑_{i=0}^{k} (n / (n - pi)) C(n - pi, i) - p`, over `ℚ` (natural
subtraction in `n - pi`, and division by zero gives `0`; on the paper's range
`0 ≤ k ≤ ⌊n/(p+1)⌋` with `n ≥ 1` every denominator is positive).

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, display (8). -/
def incompleteLucasLeonardoP (p n k : ℕ) : ℚ :=
  (p + 1) * ∑ i ∈ Finset.range (k + 1),
    (n : ℚ) / ((n - p * i : ℕ) : ℚ) * ((n - p * i).choose i : ℚ) - p

/-- `R_{p,n}(0) = 1` for `n ≥ 1`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (8). -/
theorem incompleteLucasLeonardoP_zero (p n : ℕ) (hn : 1 ≤ n) :
    incompleteLucasLeonardoP p n 0 = 1 := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp [incompleteLucasLeonardoP, hn']

/-- The hyper Leonardo `p`-numbers
`𝓛^{(k)}_{p,n} = (p + 1) ∑_{i=0}^{⌊n/(p+1)⌋} C(n + k - pi, i + k) - p C(n + k, k)`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, display (12) (quoting
Belaggoun and Belbachir). -/
def hyperLeonardoP (p n k : ℕ) : ℤ :=
  (p + 1) * ∑ i ∈ Finset.range (n / (p + 1) + 1), ((n + k - p * i).choose (i + k) : ℤ) -
    p * ((n + k).choose k : ℤ)

/-- `𝓛^{(k)}_{p,0} = 1`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (12) and
Proposition 10. -/
theorem hyperLeonardoP_zero_left (p k : ℕ) : hyperLeonardoP p 0 k = 1 := by
  simp [hyperLeonardoP]

/-- The hyper Lucas-Leonardo `p`-numbers (Definition 2), over `ℚ`: `R^{(0)}_{p,n} = R_{p,n}`,
`R^{(k)}_{p,0} = p² + p + 1`, and for `n, k ≥ 1`
`R^{(k)}_{p,n} = (p + 1) ∑_{i=0}^{⌊n/(p+1)⌋} ((n + (p+1)k) / (n + k - pi)) C(n + k - pi, i + k)
- p C(n + k, k)`. This reproduces the paper's listed values for `p = 2`; for `p = 1` the
listed values `122` (`R^{(1)}_7`), `101, 186, 308` (`R^{(2)}_5, …, R^{(2)}_7`) and
`220, 406, 714` (`R^{(3)}_5, …, R^{(3)}_7`) are misprints: Definition 2 gives `142`,
`111, 196, 338` and `230, 426, 764`, the values the recurrence
`R^{(k)}_{1,n} = R^{(k)}_{1,n-1} + R^{(k-1)}_{1,n}` produces from the paper's own earlier
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

/-- `R^{(k)}_{p,0} = p² + p + 1` for every `k` (for `k = 0` via `R_{p,0}`).

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Definition 2. -/
theorem hyperLucasLeonardoP_zero_left (p k : ℕ) :
    hyperLucasLeonardoP p 0 k = (p : ℚ) ^ 2 + p + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hyperLucasLeonardoP, lucasLeonardoP_zero]
  · simp [hyperLucasLeonardoP, show k ≠ 0 by omega]

/-- `R^{(0)}_{p,n} = R_{p,n}`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Definition 2. -/
theorem hyperLucasLeonardoP_zero_right (p n : ℕ) :
    hyperLucasLeonardoP p n 0 = lucasLeonardoP p n := by
  simp [hyperLucasLeonardoP]

/-- The tiling set `K_{p,n}` (Definition 1): linear `n`-tilings by squares (length `1`),
`p`-minos (length `p + 1`) and at most one `p`-tile, which comes in one of `p` colors, has
length at least `p + 1`, and can only be the initial piece. A tiling is encoded as its
optional initial `p`-tile `(color, length)` followed by the remaining pieces read left to
right (`false` a square, `true` a `p`-mino).

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Definition 1 and the set
`K_{p,n}` before Proposition 1. -/
def leonardoPTilings (p n : ℕ) : Set (Option (Fin p × ℕ) × List Bool) :=
  {t | (∀ c l, t.1 = some (c, l) → p + 1 ≤ l) ∧
    t.1.elim 0 Prod.snd + (t.2.map fun b => if b then p + 1 else 1).sum = n}

/-- The all-squares tiling lies in `K_{p,n}`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 2. -/
theorem replicate_mem_leonardoPTilings (p n : ℕ) :
    ((none : Option (Fin p × ℕ)), List.replicate n false) ∈ leonardoPTilings p n := by
  simp [leonardoPTilings, List.map_replicate, List.sum_replicate]

/-- The tile of an `n`-bracelet that covers cell `1`, with its phase (the cell of the tile
that covers cell `1`, stored `0`-based).

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

/-- The length of a bracelet's first tile.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 3. -/
def BraceletFirstTile.length {p : ℕ} : BraceletFirstTile p → ℕ
  | .square => 1
  | .mino _ => p + 1
  | .shortTile _ _ => p + 1
  | .longTile _ l => l

/-- The bracelet set `B_{p,n}` for `n ≥ 1`: tilings of a circular `n`-board by curved
squares, `p`-minos and at most one `p`-tile (`p` colors; length `p + 1` in any of the
`p + 1` phases, or length `l ≥ p + 2` starting at cell `1`), the `p`-tile being the first
tile if present. A bracelet is encoded as its first tile (the one covering cell `1`) with
its phase, followed by the remaining pieces read clockwise (`false` a square, `true` a
`p`-mino); the paper's value `|B_{p,0}| = p² + p + 1` is a convention not modelled here.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Section 3, the set
`B_{p,n}` before Proposition 12. -/
def lucasLeonardoBracelets (p n : ℕ) : Set (BraceletFirstTile p × List Bool) :=
  {b | (∀ c l, b.1 = .longTile c l → p + 2 ≤ l) ∧
    b.1.length + (b.2.map fun t => if t then p + 1 else 1).sum = n}

/-- The all-squares bracelet lies in `B_{p,n}` for `n ≥ 1`.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, Section 3. -/
theorem square_replicate_mem_lucasLeonardoBracelets (p n : ℕ) (hn : 1 ≤ n) :
    ((.square : BraceletFirstTile p), List.replicate (n - 1) false) ∈
      lucasLeonardoBracelets p n := by
  simp [lucasLeonardoBracelets, BraceletFirstTile.length, List.map_replicate,
    List.sum_replicate]
  omega

/-- **Proposition 1**: `|K_{p,n}| = 𝓛_{p,n}`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 1. -/
public theorem_wanted card_leonardoPTilings (p n : ℕ) (hp : 1 ≤ p) :
    (Nat.card (leonardoPTilings p n) : ℤ) = leonardoPK p p n

/-- **Proposition 2**: the homogeneous recurrence
`𝓛_{p,n} = 𝓛_{p,n-1} + 𝓛_{p,n-p} - 𝓛_{p,n-2p-1}` for `n ≥ 2p + 1`, with initial values
`𝓛_{p,i} = 1` for `i ≤ p` and `𝓛_{p,p+j} = (j + 1) + jp` for `1 ≤ j ≤ p`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 2. -/
public theorem_wanted leonardoPK_self_homogeneous (p : ℕ) (hp : 1 ≤ p) :
    (∀ n, 2 * p + 1 ≤ n →
      leonardoPK p p n =
        leonardoPK p p (n - 1) + leonardoPK p p (n - p) - leonardoPK p p (n - 2 * p - 1)) ∧
    (∀ i, i ≤ p → leonardoPK p p i = 1) ∧
    (∀ j, 1 ≤ j → j ≤ p → leonardoPK p p (p + j) = (j : ℤ) + 1 + j * p)

/-- **Proposition 6**: for `n > p` and `0 ≤ k ≤ ⌊n/(p+1)⌋`,
`𝓛_{p,n}(k + 1) = 𝓛_{p,n-1}(k + 1) + 𝓛_{p,n-p-1}(k) + p`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 6. -/
public theorem_wanted incompleteLeonardoP_succ (p n k : ℕ) (hp : 1 ≤ p) (hn : p < n)
    (hk : k ≤ n / (p + 1)) :
    incompleteLeonardoP p n (k + 1) =
      incompleteLeonardoP p (n - 1) (k + 1) + incompleteLeonardoP p (n - p - 1) k + p

/-- **Proposition 7**: for `n ≥ p + r` and `0 ≤ k ≤ ⌊(n - p - r)/(p+1)⌋`,
`∑_{i=0}^{r} C(r, i) 𝓛_{p,n+pi}(k + i) + (2^r - 1) p = 𝓛_{p,n+(p+1)r}(k + r)`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 7. -/
public theorem_wanted sum_choose_mul_incompleteLeonardoP (p n r k : ℕ) (hp : 1 ≤ p)
    (hnr : p + r ≤ n) (hk : k ≤ (n - p - r) / (p + 1)) :
    ∑ i ∈ Finset.range (r + 1), (r.choose i : ℤ) * incompleteLeonardoP p (n + p * i) (k + i) +
        ((2 : ℤ) ^ r - 1) * p =
      incompleteLeonardoP p (n + (p + 1) * r) (k + r)

/-- **Proposition 8**: for `n ≥ (p + 1)(k + 1)`,
`∑_{i=0}^{r-1} 𝓛_{p,n-p+i}(k) + rp = 𝓛_{p,n+r}(k + 1) - 𝓛_{p,n}(k + 1)`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 8. -/
public theorem_wanted sum_incompleteLeonardoP (p n k r : ℕ) (hp : 1 ≤ p)
    (hn : (p + 1) * (k + 1) ≤ n) :
    ∑ i ∈ Finset.range r, incompleteLeonardoP p (n - p + i) k + (r : ℤ) * p =
      incompleteLeonardoP p (n + r) (k + 1) - incompleteLeonardoP p n (k + 1)

/-- **Proposition 9**: for `m, n ≥ 1` with `m ≤ k`,
`𝓛^{(k)}_{p,n+m} = ∑_{i=0}^{m} C(m, i) 𝓛^{(k-i)}_{p,n+i}`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 9. -/
public theorem_wanted hyperLeonardoP_add (p n m k : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hmk : m ≤ k) :
    hyperLeonardoP p (n + m) k =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℤ) * hyperLeonardoP p (n + i) (k - i)

/-- **Proposition 10**: `𝓛^{(k)}_{p,n} = 𝓛^{(k)}_{p,n-1} + 𝓛^{(k-1)}_{p,n}` for `n, k ≥ 1`,
with `𝓛^{(0)}_{p,n} = 𝓛_{p,n}` (and `𝓛^{(k)}_{p,0} = 1`, proved as
`hyperLeonardoP_zero_left`).

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 10. -/
public theorem_wanted hyperLeonardoP_rec (p : ℕ) (hp : 1 ≤ p) :
    (∀ n k, 1 ≤ n → 1 ≤ k →
      hyperLeonardoP p n k = hyperLeonardoP p (n - 1) k + hyperLeonardoP p n (k - 1)) ∧
    ∀ n, hyperLeonardoP p n 0 = leonardoPK p p n

/-- **Proposition 11**: for `n > p` and `k ≥ 1`,
`𝓛_{p,n+(p+1)k} = 𝓛_{p,n+(p+1)k}(k - 1) + 𝓛^{(k)}_{p,n} + p C(n + k, k)`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 11. -/
public theorem_wanted leonardoPK_eq_incomplete_add_hyper (p n k : ℕ) (hp : 1 ≤ p)
    (hn : p < n) (hk : 1 ≤ k) :
    leonardoPK p p (n + (p + 1) * k) =
      incompleteLeonardoP p (n + (p + 1) * k) (k - 1) + hyperLeonardoP p n k +
        p * ((n + k).choose k : ℤ)

/-- **Proposition 12**: `|B_{p,n}| = R_{p,n}` for `n ≥ 1`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 12. -/
public theorem_wanted card_lucasLeonardoBracelets (p n : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (Nat.card (lucasLeonardoBracelets p n) : ℤ) = lucasLeonardoP p n

/-- **Proposition 13**: `R_{p,n} = (p + 1) L_{p,n} - p`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 13. -/
public theorem_wanted lucasLeonardoP_eq_lucasP (p n : ℕ) (hp : 1 ≤ p) :
    lucasLeonardoP p n = ((p : ℤ) + 1) * lucasP p n - p

/-- **Proposition 14**: `R_{p,n} = (p + 1) 𝓛_{p,n} - p 𝓛_{p,n-1}`, with
`𝓛_{p,-1} = -p` (the backward value of the recurrence, `leonardoPKZ`) at `n = 0`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 14. -/
public theorem_wanted lucasLeonardoP_eq_leonardoPK (p n : ℕ) (hp : 1 ≤ p) :
    lucasLeonardoP p n = ((p : ℤ) + 1) * leonardoPK p p n - p * leonardoPKZ p p ((n : ℤ) - 1)

/-- **Proposition 15**: `∑_{i=0}^{n} R_{p,i} = R_{p,n+p+1} - p(n + 1) - 1`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 15. -/
public theorem_wanted sum_lucasLeonardoP (p n : ℕ) (hp : 1 ≤ p) :
    ∑ i ∈ Finset.range (n + 1), lucasLeonardoP p i =
      lucasLeonardoP p (n + p + 1) - p * ((n : ℤ) + 1) - 1

/-- **Proposition 16**: `∑_{i=0}^{n} R_{p,(p+1)i} = R_{p,(p+1)n+1} - p(n - p - 1)`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 16. -/
public theorem_wanted sum_lucasLeonardoP_stride (p n : ℕ) (hp : 1 ≤ p) :
    ∑ i ∈ Finset.range (n + 1), lucasLeonardoP p ((p + 1) * i) =
      lucasLeonardoP p ((p + 1) * n + 1) - p * ((n : ℤ) - p - 1)

/-- **Proposition 17**: for `n > p + 1` and `0 ≤ k ≤ ⌊n/(p+1)⌋`,
`R_{p,n}(k + 1) = R_{p,n-1}(k + 1) + R_{p,n-p-1}(k) + p`. At `n = p + 1` the term
`R_{p,0}(k)` has the undefined summand `0/0 · C(0, 0)` and is excluded.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 17. -/
public theorem_wanted incompleteLucasLeonardoP_succ (p n k : ℕ) (hp : 1 ≤ p)
    (hn : p + 1 < n) (hk : k ≤ n / (p + 1)) :
    incompleteLucasLeonardoP p n (k + 1) =
      incompleteLucasLeonardoP p (n - 1) (k + 1) + incompleteLucasLeonardoP p (n - p - 1) k +
        p

/-- **Proposition 18**: for `n ≥ p + r` and `0 ≤ k ≤ ⌊(n - p - r)/(p+1)⌋`,
`∑_{i=0}^{r} C(r, i) R_{p,n+pi}(k + i) + (2^r - 1) p = R_{p,n+(p+1)r}(k + r)` (the printed
range `0 ≤ n ≤ ⌊(n-p-r)/(p+1)⌋` is read with `k` for the first `n`, as in
Proposition 7).

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 18. -/
public theorem_wanted sum_choose_mul_incompleteLucasLeonardoP (p n r k : ℕ) (hp : 1 ≤ p)
    (hnr : p + r ≤ n) (hk : k ≤ (n - p - r) / (p + 1)) :
    ∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℚ) * incompleteLucasLeonardoP p (n + p * i) (k + i) +
        ((2 : ℚ) ^ r - 1) * p =
      incompleteLucasLeonardoP p (n + (p + 1) * r) (k + r)

/-- **Proposition 19**: for `n > p ≥ 1` and `k ≥ 1`,
`R^{(k)}_{p,n} = R_{p,n+(p+1)k} - R_{p,n+(p+1)k}(k - 1) - p C(n + k, k)`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 19. -/
public theorem_wanted hyperLucasLeonardoP_eq (p n k : ℕ) (hp : 1 ≤ p) (hn : p < n)
    (hk : 1 ≤ k) :
    hyperLucasLeonardoP p n k =
      lucasLeonardoP p (n + (p + 1) * k) -
        incompleteLucasLeonardoP p (n + (p + 1) * k) (k - 1) - p * ((n + k).choose k : ℚ)

/-- **Proposition 20** (binomial corrected): for `n > p ≥ 1` and `k ≥ 1`,
`R^{(k)}_{p,n} = (p + 1) 𝓛^{(k)}_{p,n} - p 𝓛^{(k)}_{p,n-1} + p² C(n + k - 1, k - 1)`. The
printed binomial `C(n + k - 1, k)` is false (at `p = 1`, `n = 2`, `k = 1`:
`R^{(1)}_{1,2} = 9` but the printed right side is `10`); the paper's own proof ends with
`p² C(n + k - 1, k - 1)`.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 20. -/
public theorem_wanted hyperLucasLeonardoP_eq_hyperLeonardoP (p n k : ℕ) (hp : 1 ≤ p)
    (hn : p < n) (hk : 1 ≤ k) :
    hyperLucasLeonardoP p n k =
      ((p : ℚ) + 1) * hyperLeonardoP p n k - p * hyperLeonardoP p (n - 1) k +
        (p : ℚ) ^ 2 * ((n + k - 1).choose (k - 1) : ℚ)

end

end MetaMathlibExt
