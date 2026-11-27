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
public import MathlibExt.NumberTheory.Beatty.SkippingFiberIndicator
public import MathlibExt.NumberTheory.BeattyDecompositionBeattyFloorFiberCardEqOrEqSucc

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

/-- **The $\beta$-Beatty counts between $\lfloor n\alpha\rfloor$ and $\lfloor n\beta\rfloor$ form a
Beatty sequence.** Let $\alpha$ be an irrational number with $1 < \alpha < 2$, let $\beta$ be a
real number with $\alpha^{-1} + \beta^{-1} = 1$, and let $B$ be the set of the numbers
$\lfloor k\beta\rfloor$ for positive integers $k$. Then there is a real number $r$ with
$0 < r < 1$ such that for every positive integer $n$, the number of elements of $B$ in the open
interval $(\lfloor n\alpha\rfloor, \lfloor n\beta\rfloor)$ equals $\lfloor nr\rfloor$.

By Beatty's theorem, the Beatty sequences of $\alpha$ and $\beta$ are then complementary.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Corollary 3 (`integers-2025-A104-cor-3`). -/
public theorem_wanted beatty_card_compl_between_isBeatty {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ n : ℤ, 0 < n →
      ((Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq β k | k > 0}).ncard : ℤ) =
        beattySeq r n

end

end MetaMathlibExt
