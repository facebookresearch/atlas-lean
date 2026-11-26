/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Rayleigh
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.Beatty.ComplBetween
public import MathlibExt.NumberTheory.Beatty.CountIncrement
public import MathlibExt.NumberTheory.Beatty.FloorFiber
public import MathlibExt.NumberTheory.Beatty.FloorFiberIndicator
public import MathlibExt.NumberTheory.Beatty.FloorFiberSets
public import MathlibExt.NumberTheory.Beatty.FloorSubTwoIdentity
public import MathlibExt.NumberTheory.Beatty.FloorTwoSubIdentity
public import MathlibExt.NumberTheory.Beatty.SelfBetween
public import MathlibExt.NumberTheory.Beatty.SelfBetweenIncrement
public import MathlibExt.NumberTheory.BeattyDecompositionBeattyFloorFiberCardEqOrEqSucc
public import MathlibExt.NumberTheory.BeattyDecompositionBeattyCardComplBetweenIsBeatty

/-! # Decomposition of Beatty and complementary sequences (Polanco)

Statements from G. Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104 (arXiv:2305.15361). Beatty sets are written with
Mathlib's `beattySeq r k = ⌊k * r⌋` over positive indices `k`. For complementary
Beatty sequences `A = {⌊nα⌋}` and `B = {⌊nβ⌋}`, the paper's sequences `r n` and `c n`
count the elements of `B`, respectively `A`, strictly between `a n = ⌊nα⌋` and
`b n = ⌊nβ⌋`; by part (3) of the paper's main theorem these are the auxiliary and
skipping sequences of its MES algorithm. "Complementary Beatty sequences" is
encoded through Beatty's theorem as `Irrational α`, `1 < α` and `α⁻¹ + β⁻¹ = 1`.
-/

namespace MetaMathlibExt

@[expose] public section

open Set

/-- **Beatty's theorem and its converse.** Let $\alpha$ and $\beta$ be positive real numbers. The
set of the numbers $\lfloor k\alpha\rfloor$ for positive integers $k$ and the set of the numbers
$\lfloor k\beta\rfloor$ for positive integers $k$ are disjoint and their union is the set of
positive integers if and only if $\alpha$ is irrational and $\alpha^{-1} + \beta^{-1} = 1$.

The hypothesis $\beta > 0$ cannot be dropped: for irrational $0 < \alpha < 1$ the number $\beta$
with $\alpha^{-1} + \beta^{-1} = 1$ is negative, and the two sets do not partition the positive
integers.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 1 (Beatty–Rayleigh) (`integers-2025-A104-thm-1`). -/
public theorem_wanted beatty_complementary_iff_irrational_inv_add_inv {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    (Disjoint {beattySeq α k | k > 0} {beattySeq β k | k > 0} ∧
        {beattySeq α k | k > 0} ∪ {beattySeq β k | k > 0} = {n : ℤ | 0 < n}) ↔
      (Irrational α ∧ α⁻¹ + β⁻¹ = 1)

/-- **Multiplicities of Polanco's skipping sequence.** Let $k \ge 1$ be an integer, let
$\alpha$ be an irrational real number with $(2k - 1)/k < \alpha < (2k + 1)/(k + 1)$, and let
$\beta$ be a real number with $\alpha^{-1} + \beta^{-1} = 1$. Let
$A = \{\lfloor j\alpha \rfloor : j \ge 1\}$ and, for each positive integer $n$, let $c_n$ be
the number of elements of $A$ strictly between $\lfloor n\alpha \rfloor$ and
$\lfloor n\beta \rfloor$. Let $f(x) = 2 - 1/x$, let $f^{k-1}$ be its $(k-1)$-fold iterate, and
let $\delta = -1 + 1/f^{k-1}(\alpha - 1)$, that is,
$\delta = -1 + 1/(2 - 1/(2 - \cdots - 1/(\alpha - 1)))$ with $k - 1$ twos. Then for every
non-negative integer $m$, the number of positive integers $n$ with $c_n = m$ is $k$ if
$m = \lfloor j\delta \rfloor$ for some integer $j \ge 1$, and $k - 1$ otherwise, where an
infinite set is counted as having $0$ elements.

For $k = 1$ this gives $\delta = 1/(\alpha - 1) - 1 = \beta - 2$, and the multiplicity is one
or zero.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 6 (`integers-2025-A104-lem-6`). -/
public theorem_wanted beatty_skipping_card_eq_add_indicator {α β : ℝ} {k : ℕ}
    (hirr : Irrational α) (hk : 1 ≤ k) (hk1 : (2 * (k : ℝ) - 1) / k < α)
    (hk2 : α < (2 * (k : ℝ) + 1) / ((k : ℝ) + 1)) (hαβ : α⁻¹ + β⁻¹ = 1) (m : ℕ) :
    {n : ℤ | 0 < n ∧
        (Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq α j | j > 0}).ncard = m}.ncard =
      (k - 1) + {beattySeq (-1 + 1 / (fun x : ℝ ↦ 2 - 1 / x)^[k - 1] (α - 1)) j | j > 0}.indicator
        (1 : ℤ → ℕ) m

end

end MetaMathlibExt
