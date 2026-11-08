/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On generalized Leonardo `p`-numbers

Statements from Kusrini, A. Putra, and K. Kuhapatanakul
as presented in "On Generalized Leonardo `p`-Numbers",
*Journal of Integer Sequences* 27 (2024), Article 24.4.6
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Kuhapatanakul/kuha13.tex>).

The Fibonacci `p`-numbers `F_p` (`F_p(0) = 0`,
`F_p(1) = ⋯ = F_p(p) = 1`, `F_p(n) = F_p(n-1) +
F_p(n-p-1)`), the generalized Leonardo `p`-numbers
`ℒ_{p,k}` (`1` on `[0, p]`,
`ℒ(n) = ℒ(n-1) + ℒ(n-p-1) + k`), and the two-sided
auxiliary sequences `A_p`, `B_p` (elements of the paper's
`H(p)`: `H(n) = H(n-1) + H(n-p) - H(n-2p-1)` on `ℤ`, with
the initial values on `[-p, p]` given in the paper) are
`leonardoPK`, `seqAZ`, `seqBZ` (the Fibonacci `p`-numbers are the existing `MetaMathlibExt.fibonacciP`, cast to `ℤ`). The companion
matrix `Q_p` (for `p ≥ 2`) is `companionQ`, from the
paper's displayed examples; Theorem 9's entry formula for
`Q_p^n` is `qPowEntry` (the paper's display of the `B`
rows has the index direction after the first entry
reversed relative to the actual powers; the formula here
is the one matching `Q_p^n`, verified entrywise). `R_{p,m}`
for `ℋ ∈ H(p)` is `rMatrix`. Proposition 7 and the matrix
results are stated for `p ≥ 2`, the range of the paper's
main-results section (Proposition 7(i) fails at `p = 1`).
Theorem 13's summation index `j` in `ℒ_{p,k}(m-j)` is the
printed typo for `i`.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Recurrences.HonsbergerFibonacciP
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.LeonardoPWanted

/-- Initial segment of the generalized Leonardo
`p`-numbers `ℒ_{p,k}`. -/
def leonardoPKSeq (p k : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
      let prev := leonardoPKSeq p k n
      prev ++ [if n + 1 ≤ p then 1
        else prev.getD n 0 + prev.getD (n - p) 0 + (k : ℤ)]

/-- The generalized Leonardo `p`-numbers `ℒ_{p,k}(n)`. -/
def leonardoPK (p k n : ℕ) : ℤ := (leonardoPKSeq p k n).getD n 0

/-- Forward evaluation of the `H(p)` recurrence
`H(n) = H(n-1) + H(n-p) - H(n-2p-1)`: `hSeqForward seedA p n`
is the list of values at `-p, -p+1, …, p+n`, starting from
the seeds `seedA` on `[-p, p]` and appending one value per
step (position `i` holds the value at `i - p`). Evaluation
is polynomial: each step reuses the shared prefix list. -/
def hSeqForward (seedA : ℤ → ℤ) (p : ℕ) : ℕ → List ℤ
  | 0 => (List.range (2 * p + 1)).map fun i => seedA ((i : ℤ) - p)
  | n + 1 =>
      let prev := hSeqForward seedA p n
      prev ++ [prev.getD (2 * p + n) 0 + prev.getD (p + 1 + n) 0 -
        prev.getD n 0]

/-- Backward evaluation of the `H(p)` recurrence:
`hSeqBackward seedA p n` is the list of values at
`-p-n, …, p`, starting from the seeds on `[-p, p]` and
prepending one value per step via
`H(t) = H(t+2p) + H(t+p+1) - H(t+2p+1)`. -/
def hSeqBackward (seedA : ℤ → ℤ) (p : ℕ) : ℕ → List ℤ
  | 0 => (List.range (2 * p + 1)).map fun i => seedA ((i : ℤ) - p)
  | n + 1 =>
      let prev := hSeqBackward seedA p n
      (prev.getD (2 * p - 1) 0 + prev.getD p 0 - prev.getD (2 * p) 0) ::
        prev

/-- The two-sided `H(p)` extension of the seed values
`seedA` on `[-p, p]`, evaluated through the shared forward
and backward lists above. -/
def hSeqZ (seedA : ℤ → ℤ) (p : ℕ) (z : ℤ) : ℤ :=
  if -(p : ℤ) ≤ z then
    (hSeqForward seedA p (z + p).toNat).getD (z + p).toNat 0
  else
    (hSeqBackward seedA p (-(z + p)).toNat).getD 0 0

/-- The paper's sequence `A_p` on `ℤ`: the element of
`H(p)` with `A_p(n) = 1` for `1 ≤ n ≤ p` and `A_p(n) = 0`
for `-p ≤ n ≤ 0`. -/
def seqAZ (p : ℕ) (z : ℤ) : ℤ :=
  hSeqZ (fun w => if w ≤ 0 then 0 else 1) p z

/-- The paper's sequence `B_p` on `ℤ`: the element of
`H(p)` with `B_p(n) = 1` for `1 ≤ n ≤ p` and
`B_p(-p+1) = 1`, `B_p(n) = 0` for the other
`-p ≤ n ≤ 0`. -/
def seqBZ (p : ℕ) (z : ℤ) : ℤ :=
  hSeqZ (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then 1 else 0)
    else 1) p z

/-- The `(2p+1) × (2p+1)` companion matrix `Q_p`
(0-based): `1` at `(0,0)`, `(p-1,0)` and on the
superdiagonal, `-1` at `(2p, 0)`, `0` elsewhere. -/
def companionQ (p : ℕ) : Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℤ :=
  Matrix.of fun i j =>
    if j.val = 0 ∧ i.val = 2 * p then -1
    else if (j.val = 0 ∧ (i.val = 0 ∨ i.val = p - 1)) ∨
        j.val = i.val + 1 then 1
    else 0

/-- The entry formula of Theorem 9 for `Q_p^n`
(0-based): first row `A_p`, next `p - 1` rows `B_p`,
remaining rows `-A_p`, indices decreasing along rows. -/
def qPowEntry (p n : ℕ) (a b : Fin (2 * p + 1)) : ℤ :=
  if a.val = 0 then seqAZ p ((n : ℤ) + 1 - b.val)
  else if a.val ≤ p - 1 then seqBZ p ((n : ℤ) - p + 1 + a.val - b.val)
  else -seqAZ p ((n : ℤ) - (2 * p - a.val) - b.val)

/-- The paper's Hankel matrix `R_{p,m}` for a sequence
`H : ℤ → ℤ`: entry `(a, b)` is `H(m - a - b)`. -/
def rMatrix (p : ℕ) (H : ℤ → ℤ) (m : ℕ) :
    Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℤ :=
  Matrix.of fun a b => H ((m : ℤ) - a.val - b.val)

/-- **Theorem 2**: `ℒ_{p,k}(n) = (k+1)F_p(n+1) - k`.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 2. -/
theorem_wanted leonardoPK_eq (p k n : ℕ) (hp : 1 ≤ p)
    (hk : 1 ≤ k) :
    leonardoPK p k n = ((k : ℤ) + 1) * (MetaMathlibExt.fibonacciP p (n + 1) : ℤ) - (k : ℤ)

/-- **Theorem 3**: `∑_{i=0}^n ℒ_{p,k}(i) =
ℒ_{p,k}(n+p+1) - k(n+1) - 1`.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 3. -/
theorem_wanted sum_leonardoPK (p k n : ℕ) (hp : 1 ≤ p)
    (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range (n + 1), leonardoPK p k i =
      leonardoPK p k (n + p + 1) - (k : ℤ) * (n + 1) - 1

/-- **Theorem 4**: stride sums of `ℒ_{p,k}`:
`∑_{i=0}^n ℒ_{p,k}((p+1)i + m)` equals
`ℒ_{p,k}((p+1)n + m + 1) - kn` for `m < p` and
`ℒ_{p,k}((p+1)(n+1)) - k(n+1) - 1` for `m = p`.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 4. -/
theorem_wanted sum_leonardoPK_stride (p k m n : ℕ)
    (hp : 1 ≤ p) (hk : 1 ≤ k) (hm : m ≤ p) :
    ∑ i ∈ Finset.range (n + 1), leonardoPK p k ((p + 1) * i + m) =
      if m < p then
        leonardoPK p k ((p + 1) * n + m + 1) - (k : ℤ) * n
      else
        leonardoPK p k ((p + 1) * (n + 1)) - (k : ℤ) * (n + 1) - 1

/-- **Theorem 5**: `F_p(n) = A_p(n) - A_p(n-p)` for
positive `n` (with `A_p` at nonpositive arguments as in
`seqAZ`).

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 5. -/
theorem_wanted fibonacciP_eq_seqAZ_sub (p n : ℕ) (hp : 1 ≤ p)
    (hn : 1 ≤ n) :
    (MetaMathlibExt.fibonacciP p n : ℤ) = seqAZ p (n : ℤ) - seqAZ p ((n : ℤ) - p)

/-- **Corollary 6**: for `0 ≤ j < p`,
`A_p(mp + j) = ∑_{i=0}^m F_p(ip + j)`.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Corollary 6. -/
theorem_wanted seqAZ_eq_sum_fibonacciP (p j m : ℕ) (hp : 1 ≤ p)
    (hj : j < p) :
    seqAZ p ((m * p + j : ℕ) : ℤ) =
      ∑ i ∈ Finset.range (m + 1), (MetaMathlibExt.fibonacciP p (i * p + j) : ℤ)

/-- **Proposition 7**(i): for `p ≥ 2` and `n ≥ 1`,
`A_p(n) = A_p(n-1) + A_p(n-p-1) + 1` if `n ≡ 1 (mod p)`,
else `A_p(n-1) + A_p(n-p-1)` (fails at `p = 1`).

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Proposition 7. -/
theorem_wanted seqAZ_recurrence (p n : ℕ) (hp : 2 ≤ p)
    (hn : 1 ≤ n) :
    seqAZ p (n : ℤ) =
      seqAZ p ((n : ℤ) - 1) + seqAZ p ((n : ℤ) - p - 1) +
        (if n % p = 1 % p then 1 else 0)

/-- **Proposition 7**(ii): for `p ≥ 2` and `n ≥ 1`,
`B_p(n)` is `B_p(n-1) + B_p(n-p-1)` plus `1` if
`n ≡ 1 (mod p)`, minus `1` if `n ≡ 2 (mod p)`, else `0`;
the congruences are read as `n % p = c % p`, so at
`p = 2` the increment is `+1` for odd `n` and `-1` for
even `n` (e.g. `B_2(2) - B_2(1) - B_2(-1) = -1`).

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Proposition 7. -/
theorem_wanted seqBZ_recurrence (p n : ℕ) (hp : 2 ≤ p)
    (hn : 1 ≤ n) :
    seqBZ p (n : ℤ) =
      seqBZ p ((n : ℤ) - 1) + seqBZ p ((n : ℤ) - p - 1) +
        (if n % p = 1 % p then 1 else if n % p = 2 % p then -1 else 0)

/-- **Proposition 8**: `A_p(n) = B_p(n+1) - 1` if
`n ≡ 0 (mod p)`, else `B_p(n+1)`.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Proposition 8. -/
theorem_wanted seqAZ_eq_seqBZ (p n : ℕ) (hp : 2 ≤ p) :
    seqAZ p (n : ℤ) =
      if n % p = 0 then seqBZ p ((n : ℤ) + 1) - 1
      else seqBZ p ((n : ℤ) + 1)

/-- **Theorem 9**: the entries of `Q_p^n` are given by
`qPowEntry`.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 9. -/
theorem_wanted companionQ_pow_apply (p n : ℕ) (hp : 2 ≤ p)
    (a b : Fin (2 * p + 1)) :
    (companionQ p ^ n) a b = qPowEntry p n a b

/-- **Theorem 10**: `R_{p,m} Q_p^n = R_{p,m+n}` for every
`ℋ ∈ H(p)` (here: every `H : ℤ → ℤ` satisfying the
`H(p)` recurrence at all integers) and positive `m`.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Theorem 10. -/
theorem_wanted rMatrix_mul_companionQ_pow (p : ℕ) (hp : 2 ≤ p)
    (H : ℤ → ℤ)
    (hH : ∀ n : ℤ, H n = H (n - 1) + H (n - p) - H (n - 2 * p - 1))
    (m n : ℕ) (hm : 1 ≤ m) :
    rMatrix p H m * companionQ p ^ n = rMatrix p H (m + n)

/-- **Corollary 11** (convolution identity): for
`ℋ ∈ H(p)` and `m, n > 0`,
`ℋ(m+n) = ℋ(m)A_p(n+1) + ∑_{i=1}^{p-1} ℋ(m-i)B_p(n-p+i+1)
- ∑_{i=0}^p ℋ(m-p-i)A_p(n-p+i)`.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Corollary 11. -/
theorem_wanted h_add_eq (p : ℕ) (hp : 2 ≤ p) (H : ℤ → ℤ)
    (hH : ∀ n : ℤ, H n = H (n - 1) + H (n - p) - H (n - 2 * p - 1))
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    H ((m : ℤ) + n) =
      H (m : ℤ) * seqAZ p ((n : ℤ) + 1) +
        ∑ i ∈ Finset.Icc 1 (p - 1), H ((m : ℤ) - i) *
          seqBZ p ((n : ℤ) - p + i + 1) -
        ∑ i ∈ Finset.range (p + 1), H ((m : ℤ) - p - i) *
          seqAZ p ((n : ℤ) - p + i)

/-- **Lemma 12**: `(k+1) ∑_{i=0}^p F_p(n+i) =
ℒ_{p,k}(n+2p-1) + k` for positive `n`.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Lemma 12. -/
theorem_wanted succ_mul_sum_fibonacciP (p k n : ℕ) (hp : 1 ≤ p)
    (hn : 1 ≤ n) :
    ((k : ℤ) + 1) * ∑ i ∈ Finset.range (p + 1), (MetaMathlibExt.fibonacciP p (n + i) : ℤ) =
      leonardoPK p k (n + 2 * p - 1) + (k : ℤ)

/-- `ℒ_{p,k}` at integer arguments, with the paper's
values `ℒ_{p,k}(-i) = -k` for `1 ≤ i ≤ p` (accurate on
`[-p, ∞)`, the range occurring in Theorem 13). -/
def leonardoPKZ (p k : ℕ) (z : ℤ) : ℤ :=
  if 0 ≤ z then leonardoPK p k z.toNat else -(k : ℤ)

/-- **Theorem 13** (Honsberger-type identity, index
corrected): for positive `m, n`,
`ℒ_{p,k}(m)ℒ_{p,k}(n+1) + ∑_{i=1}^p ℒ_{p,k}(m-i)
ℒ_{p,k}(n-p+i) = (k+1)ℒ_{p,k}(m+n+1) -
k(ℒ_{p,k}(m+p) + ℒ_{p,k}(n+p+1)) + pk² + k`, with
`ℒ_{p,k}` at negative arguments read through the same
recurrence (here `leonardoPK` at truncated indices,
where the paper's values at negative arguments in
`[-p, -1]` are `-k`; the statement is stated with the
`ℤ`-extension `leonardoPKZ` below).

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Theorem 13. -/

theorem_wanted leonardoPK_honsberger (p k m n : ℕ)
    (hp : 1 ≤ p) (hk : 1 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    leonardoPK p k m * leonardoPK p k (n + 1) +
        ∑ i ∈ Finset.Icc 1 p, leonardoPKZ p k ((m : ℤ) - i) *
          leonardoPKZ p k ((n : ℤ) - p + i) =
      ((k : ℤ) + 1) * leonardoPK p k (m + n + 1) -
        (k : ℤ) * (leonardoPK p k (m + p) +
          leonardoPK p k (n + p + 1)) +
        (p : ℤ) * k ^ 2 + (k : ℤ)

end MathlibExt.NumberTheory.LeonardoPWanted
