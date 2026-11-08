/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Allowing or prohibiting two consecutive colors in `n`-color
compositions

Statements from Brian Hopkins and Hua Wang, "Allowing or
Prohibiting Two Consecutive Colors in `n`-Color Compositions",
*Journal of Integer Sequences* 27 (2024), Article 24.7.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Hopkins/hopkins8.tex>).

An `n`-color composition (Agarwal) is a list of parts `k_c`
with `1 ≤ c ≤ k`; below a colored part is a pair `(k, c)`, the
paper's sets `CCo_{b,b+1}(n)` (only colors `b, b+1`),
`CCo_{\widehat{b,b+1}}(n)` (colors `b, b+1` prohibited), and
`CCo_{\hat 2}(n)` (color `2` prohibited) are the subtypes
`ColorCompAllowed`, `ColorCompProhibited`, and
`ColorCompProhibit2`, and their counts `cco` are `Nat.card`s,
extended to `ℤ` by `0` at negative arguments (with the empty
composition giving count `1` at `n = 0`). Ordinary
compositions are Mathlib's `Composition`. The tribonacci
numbers `t(n)` (`t(0) = 1`, `t(1) = 0`, `t(2) = 1`) are `trib`,
extended by `0` to negative integers as in the paper, and
`f` is `Nat.fib`.

Two printed statements need range qualifications that brute
force exposes: the recurrence of Proposition 1 fails at
`n = 1` (it is stated for `2 ≤ n`), and the recurrence of
Proposition 11 fails at `n ≤ 2` (stated for `3 ≤ n`).
Theorem 2's ternary-string conditions are given in the
equivalent zero-split segment form forced by its proof (each
maximal zero-free segment, including end segments, is all-`1`
of length `≥ b-1` or all-`2` of length `≥ b`); with the
conditions read literally without end segments, the string
`0` would be a counterexample at `n = 2`, `b = 3`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted

/-- The paper's `CCo_{b,b+1}(n)`: `n`-color compositions of
`n` with only colors `b` and `b+1` allowed, as lists of pairs
`(part, color)`. -/
def ColorCompAllowed (b n : ℕ) : Type :=
  { l : List (ℕ × ℕ) //
    (∀ pc ∈ l, 1 ≤ pc.2 ∧ pc.2 ≤ pc.1 ∧ (pc.2 = b ∨ pc.2 = b + 1)) ∧
      (l.map Prod.fst).sum = n }

/-- The paper's `CCo_{\widehat{b,b+1}}(n)`: `n`-color
compositions of `n` with colors `b` and `b+1` prohibited. -/
def ColorCompProhibited (b n : ℕ) : Type :=
  { l : List (ℕ × ℕ) //
    (∀ pc ∈ l, 1 ≤ pc.2 ∧ pc.2 ≤ pc.1 ∧ pc.2 ≠ b ∧ pc.2 ≠ b + 1) ∧
      (l.map Prod.fst).sum = n }

/-- The paper's `CCo_{\hat 2}(n)`: `n`-color compositions of
`n` with the color `2` prohibited. -/
def ColorCompProhibit2 (n : ℕ) : Type :=
  { l : List (ℕ × ℕ) //
    (∀ pc ∈ l, 1 ≤ pc.2 ∧ pc.2 ≤ pc.1 ∧ pc.2 ≠ 2) ∧
      (l.map Prod.fst).sum = n }

/-- The paper's count `cco_{b,b+1}(n)`. -/
noncomputable def ccoAllowed (b n : ℕ) : ℕ :=
  Nat.card (ColorCompAllowed b n)

/-- The paper's count `cco_{\widehat{b,b+1}}(n)`. -/
noncomputable def ccoProhibited (b n : ℕ) : ℕ :=
  Nat.card (ColorCompProhibited b n)

/-- The paper's count `cco_{\hat 2}(n)`. -/
noncomputable def ccoProhibit2 (n : ℕ) : ℕ :=
  Nat.card (ColorCompProhibit2 n)

/-- `cco_{b,b+1}` extended to `ℤ` by `0` at negative
arguments. -/
noncomputable def ccoAllowedZ (b : ℕ) (n : ℤ) : ℤ :=
  if 0 ≤ n then (ccoAllowed b n.toNat : ℤ) else 0

/-- `cco_{\widehat{b,b+1}}` extended to `ℤ` by `0` at negative
arguments. -/
noncomputable def ccoProhibitedZ (b : ℕ) (n : ℤ) : ℤ :=
  if 0 ≤ n then (ccoProhibited b n.toNat : ℤ) else 0

/-- Split a ternary string at its `0`s, keeping the (possibly
empty) segments in order. -/
def splitZerosAux : List (Fin 3) → List (Fin 3) → List (List (Fin 3))
  | [], acc => [acc]
  | x :: xs, acc =>
      if x = 0 then acc :: splitZerosAux xs [] else
        splitZerosAux xs (acc ++ [x])

/-- The zero-free segments of a ternary string, in order. -/
def splitZeros (w : List (Fin 3)) : List (List (Fin 3)) :=
  splitZerosAux w []

/-- The ternary strings of Theorem 2: length `n - 1`, and
every zero-free segment is all `1`s of length `≥ b - 1` or
all `2`s of length `≥ b` (the paper's no-`12`/`21`, run-length,
and zero-separation conditions in segment form). -/
def TernaryAdmissible (b n : ℕ) : Type :=
  { w : List (Fin 3) // w.length = n - 1 ∧
    ∀ seg ∈ splitZeros w,
      ((∀ x ∈ seg, x = 1) ∧ b - 1 ≤ seg.length) ∨
        ((∀ x ∈ seg, x = 2) ∧ b ≤ seg.length) }

/-- The paper's `C^*_{1,2}(n)`: compositions of `n` with parts
`1₁, 1₂, 2` (symbols `0, 1` of size `1` and symbol `2` of
size `2`) and no adjacent parts `1` of the same type. -/
def TwoTypeComp (n : ℕ) : Type :=
  { l : List (Fin 3) //
    (l.map (fun s => if s.val < 2 then 1 else 2)).sum = n ∧
      l.IsChain (fun x y => 2 ≤ x.val ∨ 2 ≤ y.val ∨ x ≠ y) }

/-- The paper's tribonacci numbers on `ℕ`: `t(0) = 1`,
`t(1) = 0`, `t(2) = 1`, `t(n) = t(n-1) + t(n-2) + t(n-3)`. -/
def tribNat : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | n + 3 => tribNat (n + 2) + tribNat (n + 1) + tribNat n

/-- The paper's `t(n)` on `ℤ`, extended by `t(n) = 0` for
`n < 0`. -/
def trib (n : ℤ) : ℤ :=
  if 0 ≤ n then tribNat n.toNat else 0

/-- **Proposition 1**, recurrence: for `b ≥ 1` and `n ≥ 2`,
`cco_{b,b+1}(n) = cco_{b,b+1}(n-1) + cco_{b,b+1}(n-b) +
cco_{b,b+1}(n-b-1)` (the printed statement says positive `n`;
at `n = 1` the identity fails, e.g. `cco_{1,2}(1) = 1 ≠ 2`).

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 1. -/
theorem_wanted ccoAllowedZ_recurrence (b : ℕ) (hb : 1 ≤ b)
    (n : ℤ) (hn : 2 ≤ n) :
    ccoAllowedZ b n = ccoAllowedZ b (n - 1) +
      ccoAllowedZ b (n - b) + ccoAllowedZ b (n - b - 1)

/-- **Proposition 1**, direct formula:
`cco_{b,b+1}(n) = ∑_{m=1}^n ∑_{i=0}^{n-bm}
\binom{i+m-1}{m-1} \binom{m}{n-bm-i}` (terms with `bm + i > n`
contribute `0`).

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 1. -/
theorem_wanted ccoAllowed_eq_sum (b n : ℕ) (hb : 1 ≤ b) (hn : 1 ≤ n) :
    ccoAllowed b n =
      ∑ m ∈ Finset.Icc 1 n,
        ∑ i ∈ Finset.Icc 0 (n - b * m),
          if b * m + i ≤ n then
            Nat.choose (i + m - 1) (m - 1) *
              Nat.choose m (n - b * m - i)
          else 0

/-- **Theorem 2**: there is a bijection between
`CCo_{b,b+1}(n)` and the length-`n-1` ternary strings with no
`12`/`21` subwords, runs of `1`s of length `≥ b-1`, runs of
`2`s of length `≥ b`, and successive `0`s separated by
`≥ b-1` digits (segment form).

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 2. -/
theorem_wanted nonempty_equiv_colorCompAllowed_ternary
    (b n : ℕ) (hb : 1 ≤ b) (hn : 1 ≤ n) :
    Nonempty (ColorCompAllowed b n ≃ TernaryAdmissible b n)

/-- **Theorem 3**:
`cco_{1,2}(n) = ∑_{m=0}^{⌊n/2⌋} 2^m \binom{n}{2m}`.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 3. -/
theorem_wanted ccoAllowed_one_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    ccoAllowed 1 n =
      ∑ m ∈ Finset.range (n / 2 + 1), 2 ^ m * Nat.choose n (2 * m)

/-- **Theorem 4**: there is a bijection between `n`-color
compositions of `n+1` with only colors `2, 3` and compositions
of `n` with all parts `≡ 1, 2 (mod 3)`.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 4. -/
theorem_wanted nonempty_equiv_colorCompAllowed_two_composition_mod_three
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ColorCompAllowed 2 (n + 1) ≃
      { c : Composition n // ∀ k ∈ c.blocks, k % 3 = 1 ∨ k % 3 = 2 })

/-- **Theorem 5**: there is a bijection between `n`-color
compositions of `n+2` with only colors `2, 3` and
compositions of `n` with parts `2` and two types of parts
`1`, no adjacent parts `1` of the same type.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 5. -/
theorem_wanted nonempty_equiv_colorCompAllowed_two_twoTypeComp
    (n : ℕ) :
    Nonempty (ColorCompAllowed 2 (n + 2) ≃ TwoTypeComp n)

/-- **Proposition 6**: for `n ≥ 3`,
`t(n) = t(n-2) + 2 ∑_{i=3}^n t(n-i)`.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 6. -/
theorem_wanted trib_eq_add_sum (n : ℤ) (hn : 3 ≤ n) :
    trib n = trib (n - 2) +
      2 * ∑ i ∈ Finset.Icc 3 n, trib (n - i)

/-- **Proposition 7**: for `n ≥ 3`,
`t(n) = t(n-1) + 1 + 2 ∑_{i=1}^{⌊n/2⌋-1} t(n-2i-1)`.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 7. -/
theorem_wanted trib_eq_add_one_add_sum (n : ℤ) (hn : 3 ≤ n) :
    trib n = trib (n - 1) + 1 +
      2 * ∑ i ∈ Finset.Icc 1 (n / 2 - 1), trib (n - 2 * i - 1)

/-- **Theorem 8**, case `n = 3k`:
`t(3k) = 1 + ∑_{i=0}^k (t(3k-3i-1) + t(3k-3i-2))`.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 8. -/
theorem_wanted trib_three_mul (k : ℕ) :
    trib (3 * (k : ℤ)) = 1 +
      ∑ i ∈ Finset.range (k + 1),
        (trib (3 * (k : ℤ) - 3 * (i : ℤ) - 1) +
          trib (3 * (k : ℤ) - 3 * (i : ℤ) - 2))

/-- **Theorem 8**, case `n = 3k+1`:
`t(3k+1) = -1 + ∑_{i=0}^k (t(3k-3i) + t(3k-3i-1))`.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 8. -/
theorem_wanted trib_three_mul_add_one (k : ℕ) :
    trib (3 * (k : ℤ) + 1) = -1 +
      ∑ i ∈ Finset.range (k + 1),
        (trib (3 * (k : ℤ) + 1 - 3 * (i : ℤ) - 1) +
          trib (3 * (k : ℤ) + 1 - 3 * (i : ℤ) - 2))

/-- **Theorem 8**, case `n = 3k+2`:
`t(3k+2) = ∑_{i=0}^k (t(3k-3i+1) + t(3k-3i))`.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 8. -/
theorem_wanted trib_three_mul_add_two (k : ℕ) :
    trib (3 * (k : ℤ) + 2) =
      ∑ i ∈ Finset.range (k + 1),
        (trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 1) +
          trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 2))

/-- **Theorem 9**, cases `n = 3k` and `n = 3k+1` (with
`n ≥ 3`): `t(n) + t(n-2) = 2 ∑_{i=0}^{k-1} t(n-3i-1)`.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 9. -/
theorem_wanted trib_add_two_sub_three_mul (k : ℕ) (hk : 1 ≤ k) :
    trib (3 * (k : ℤ)) + trib (3 * (k : ℤ) - 2) =
        2 * ∑ i ∈ Finset.range k,
          trib (3 * (k : ℤ) - 3 * (i : ℤ) - 1) ∧
      trib (3 * (k : ℤ) + 1) + trib (3 * (k : ℤ) + 1 - 2) =
        2 * ∑ i ∈ Finset.range k,
          trib (3 * (k : ℤ) + 1 - 3 * (i : ℤ) - 1)

/-- **Theorem 9**, case `n = 3k+2` (with `n ≥ 3`):
`t(n) + t(n-2) = 2 + 2 ∑_{i=0}^{k-1} t(n-3i-1)`.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 9. -/
theorem_wanted trib_add_two_sub_three_mul_add_two (k : ℕ)
    (hk : 1 ≤ k) :
    trib (3 * (k : ℤ) + 2) + trib (3 * (k : ℤ) + 2 - 2) =
      2 + 2 * ∑ i ∈ Finset.range k,
        trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 1)

/-- **Proposition 10**: for `n ≥ 3`,
`cco_{3,4}(n) + cco_{3,4}(n-2) = f(n-1)` with `f` Fibonacci.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 10. -/
theorem_wanted ccoAllowed_three_add (n : ℕ) (hn : 3 ≤ n) :
    ccoAllowed 3 n + ccoAllowed 3 (n - 2) = Nat.fib (n - 1)

/-- **Proposition 11**: for `b ≥ 1` and `n ≥ 3`,
`cco_{\widehat{b,b+1}}(n) = 3 cco_{\widehat{b,b+1}}(n-1) -
cco_{\widehat{b,b+1}}(n-2) - cco_{\widehat{b,b+1}}(n-b) +
cco_{\widehat{b,b+1}}(n-b-2)` (the printed statement has no
range; the identity fails at `n ≤ 2`).

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 11. -/
theorem_wanted ccoProhibitedZ_recurrence (b : ℕ) (hb : 1 ≤ b)
    (n : ℤ) (hn : 3 ≤ n) :
    ccoProhibitedZ b n = 3 * ccoProhibitedZ b (n - 1) -
      ccoProhibitedZ b (n - 2) - ccoProhibitedZ b (n - b) +
      ccoProhibitedZ b (n - b - 2)

/-- **Theorem 12**: there is a bijection between `n`-color
compositions of `n+2` with colors `1, 2` prohibited and
compositions of `n` with parts `≡ 1, 2 (mod 4)` (for
`n ≥ 1`; at `n = 0` the counts are `0` and `1`).

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 12. -/
theorem_wanted nonempty_equiv_colorCompProhibited_one_composition_mod_four
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ColorCompProhibited 1 (n + 2) ≃
      { c : Composition n // ∀ k ∈ c.blocks, k % 4 = 1 ∨ k % 4 = 2 })

/-- **Theorem 13**: there is a bijection between `n`-color
compositions of `n` with colors `1, 2` prohibited and
palindromic compositions of `2n-5` with no parts `2` and an
odd number of parts (for `n ≥ 1`).

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 13. -/
theorem_wanted nonempty_equiv_colorCompProhibited_one_palindromic
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ColorCompProhibited 1 n ≃
      { c : Composition (2 * n - 5) //
        (∀ k ∈ c.blocks, k ≠ 2) ∧ c.blocks = c.blocks.reverse ∧
          Odd c.blocks.length })

/-- **Theorem 14**: for positive `k`,
`cco_{\widehat{1,2}}(3k) = cco_{\hat 2}(2k-1)`.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 14. -/
theorem_wanted ccoProhibited_one_three_mul (k : ℕ) (hk : 1 ≤ k) :
    ccoProhibited 1 (3 * k) = ccoProhibit2 (2 * k - 1)

end MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted
