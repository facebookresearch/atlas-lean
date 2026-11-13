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

/-- **Counting $\beta$-Beatty terms between $\lfloor n\alpha\rfloor$ and $\lfloor n\beta\rfloor$.**
Let $\alpha$ be an irrational number with $1 < \alpha < 2$, let $\beta$ be a real number with
$\alpha^{-1} + \beta^{-1} = 1$, and let $B$ be the set of the numbers $\lfloor k\beta\rfloor$ for
positive integers $k$. Then for every positive integer $n$, the number of elements of $B$ in the
open interval $(\lfloor n\alpha\rfloor, \lfloor n\beta\rfloor)$ equals
$\lfloor n(2 - \alpha)\rfloor$.

By Beatty's theorem, the Beatty sequences of $\alpha$ and $\beta$ are then complementary.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 3 (`integers-2025-A104-thm-3`). -/
public theorem_wanted beatty_card_compl_between_eq_floor {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ((Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq β k | k > 0}).ncard : ℤ) =
      beattySeq (2 - α) n

/-- **Counting $\alpha$-Beatty terms between $\lfloor n\alpha\rfloor$ and $\lfloor n\beta\rfloor$.**
Let $\alpha$ be an irrational number with $1 < \alpha < 2$, let $\beta$ be a real number with
$\alpha^{-1} + \beta^{-1} = 1$, and let $A$ be the set of the numbers $\lfloor k\alpha\rfloor$ for
positive integers $k$. Then for every positive integer $n$, the number of elements of $A$ in the
open interval $(\lfloor n\alpha\rfloor, \lfloor n\beta\rfloor)$ equals
$\lfloor n(\beta - 2)\rfloor$.

By Beatty's theorem, the Beatty sequences of $\alpha$ and $\beta$ are then complementary.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 4 (`integers-2025-A104-thm-4`). -/
public theorem_wanted beatty_card_self_between_eq_floor {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ((Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq α k | k > 0}).ncard : ℤ) =
      beattySeq (β - 2) n

/-- **Polanco's floor identity for $\lfloor (2 - \alpha) n \rfloor$.** Let $\alpha$ be an
irrational real number with $1 < \alpha < 2$, let $\beta$ be a real number with
$\alpha^{-1} + \beta^{-1} = 1$, and write $a_m = \lfloor m\alpha \rfloor$ and
$b_m = \lfloor m\beta \rfloor$ for integers $m$ (so $b_0 = 0$). Then for every positive
integer $n$,
$$
\lfloor \beta^{-1} (b_{n-1} + 1) \rfloor - \lfloor \beta^{-1} a_n \rfloor
= \lfloor (2 - \alpha) n \rfloor.
$$

Since $\alpha > 1$, Beatty's theorem says that the conditions "$\alpha$ is irrational and
$\alpha^{-1} + \beta^{-1} = 1$" mean exactly that $(a_n)_{n \ge 1}$ and $(b_n)_{n \ge 1}$ are
complementary Beatty sequences.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 5, identity (7) (`integers-2025-A104-thm-5`). -/
public theorem_wanted beatty_floor_inv_sub_eq_floor_two_sub {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ⌊β⁻¹ * ((beattySeq β (n - 1) + 1 : ℤ) : ℝ)⌋ - ⌊β⁻¹ * (beattySeq α n : ℝ)⌋ =
      beattySeq (2 - α) n

/-- **Polanco's floor identity for $\lfloor (\beta - 2) n \rfloor$.** Let $\alpha$ be an
irrational real number with $1 < \alpha < 2$, let $\beta$ be a real number with
$\alpha^{-1} + \beta^{-1} = 1$, and write $a_n = \lfloor n\alpha \rfloor$ and
$b_n = \lfloor n\beta \rfloor$. Then for every positive integer $n$,
$$
\lfloor \alpha^{-1} b_n \rfloor - \lfloor \alpha^{-1} (a_n + 1) \rfloor
= \lfloor (\beta - 2) n \rfloor.
$$

Since $\alpha > 1$, Beatty's theorem says that the conditions "$\alpha$ is irrational and
$\alpha^{-1} + \beta^{-1} = 1$" mean exactly that $(a_n)_{n \ge 1}$ and $(b_n)_{n \ge 1}$ are
complementary Beatty sequences.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 5, identity (8) (`integers-2025-A104-thm-5`). -/
public theorem_wanted beatty_floor_inv_sub_eq_floor_sub_two {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    ⌊α⁻¹ * (beattySeq β n : ℝ)⌋ - ⌊α⁻¹ * ((beattySeq α n + 1 : ℤ) : ℝ)⌋ =
      beattySeq (β - 2) n

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

/-- **Multiplicities of the values of $\lfloor n\alpha\rfloor$ for $1/(k + 1) < \alpha < 1/k$.**
Let $k$ be a positive integer and let $\alpha$ be a real number with
$1/(k + 1) < \alpha < 1/k$. Then every non-negative integer $t$ equals $\lfloor n\alpha\rfloor$
for exactly $k$ or exactly $k + 1$ positive integers $n$, there are infinitely many $t$ for which
it is exactly $k$, and there are infinitely many $t$ for which it is exactly $k + 1$.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 1 (`integers-2025-A104-lem-1`). -/
public theorem_wanted beatty_floor_fiber_card_eq_or_eq_succ {α : ℝ} {k : ℕ}
    (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) :
    (∀ t : ℕ, {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k ∨
        {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1) ∧
      {t : ℕ | {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k}.Infinite ∧
      {t : ℕ | {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1}.Infinite

/-- **Multiplicity $k + 1$ for $\alpha$ is multiplicity $k$ for $\alpha/(1 - \alpha)$.** Let $k$ be
a positive integer, let $\alpha$ be a real number with $1/(k + 1) < \alpha < 1/k$, and let
$\beta = \alpha/(1 - \alpha)$. Then a non-negative integer $t$ equals $\lfloor n\alpha\rfloor$ for
exactly $k + 1$ positive integers $n$ if and only if it equals $\lfloor n\beta\rfloor$ for exactly
$k$ positive integers $n$.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 2 (`integers-2025-A104-lem-2`). -/
public theorem_wanted beatty_floor_fiber_card_succ_iff {α : ℝ} {k : ℕ}
    (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) (t : ℕ) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1 ↔
      {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (α / (1 - α))⌋ = t}.ncard = k

/-- **The values of $\lfloor n\alpha\rfloor$ of each multiplicity form Beatty sets.** Let $k$ be a
positive integer and let $\alpha$ be an irrational number with $1/(k + 1) < \alpha < 1/k$. Then
there are real numbers $\gamma > 0$ and $\delta > 0$ such that the positive integers $t$ that
equal $\lfloor n\alpha\rfloor$ for exactly $k + 1$ positive integers $n$ are exactly the numbers
$\lfloor m\gamma\rfloor$ for positive integers $m$, and the positive integers $t$ that equal
$\lfloor n\alpha\rfloor$ for exactly $k$ positive integers $n$ are exactly the numbers
$\lfloor m\delta\rfloor$ for positive integers $m$.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Corollary 1 (`integers-2025-A104-cor-1`). -/
public theorem_wanted beatty_floor_fiber_card_sets_isBeatty {α : ℝ} {k : ℕ}
    (hirr : Irrational α) (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) :
    ∃ γ δ : ℝ, 0 < γ ∧ 0 < δ ∧
      {t : ℤ | 0 < t ∧ {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1} =
        {beattySeq γ m | m > 0} ∧
      {t : ℤ | 0 < t ∧ {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k} =
        {beattySeq δ m | m > 0}

/-- **Multiplicities of $\lfloor n\alpha\rfloor$ are $k$ plus the indicator of a Beatty set.** Let
$k$ be a positive integer and let $\alpha$ be an irrational number with
$1/(k + 1) < \alpha < 1/k$. Then there is a real number $\delta > 0$ such that, writing $D$ for
the set of the numbers $\lfloor m\delta\rfloor$ for positive integers $m$, every non-negative
integer $t$ equals $\lfloor n\alpha\rfloor$ for exactly $k + 1$ positive integers $n$ if $t \in D$,
and for exactly $k$ positive integers $n$ if $t \notin D$.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Corollary 2 (`integers-2025-A104-cor-2`). -/
public theorem_wanted beatty_floor_fiber_card_eq_add_indicator {α : ℝ} {k : ℕ}
    (hirr : Irrational α) (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℕ, {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard =
      k + {beattySeq δ m | m > 0}.indicator (1 : ℤ → ℕ) t

/-- **Increments of the $\beta$-Beatty counts between $\lfloor n\alpha\rfloor$ and
$\lfloor n\beta\rfloor$.** Let $\alpha$ be an irrational number with $1 < \alpha < 2$, let $\beta$
be a real number with $\alpha^{-1} + \beta^{-1} = 1$, let $B$ be the set of the numbers
$\lfloor k\beta\rfloor$ for positive integers $k$, and for an integer $m$ let $r(m)$ be the number
of elements of $B$ in the open interval $(\lfloor m\alpha\rfloor, \lfloor m\beta\rfloor)$. Then for
every positive integer $n$, the difference $r(n + 1) - r(n)$ is $0$ or $1$, and it equals $1$ if
and only if $\lfloor (n + 1)\alpha\rfloor - \lfloor n\alpha\rfloor = 1$.

By Beatty's theorem, the Beatty sequences of $\alpha$ and $\beta$ are then complementary.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 4 (`integers-2025-A104-lem-4`). -/
public theorem_wanted beatty_card_compl_between_succ_sub {α β : ℝ} (hirr : Irrational α)
    (hα1 : 1 < α) (hα2 : α < 2) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    let r : ℤ → ℤ := fun m ↦
      ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq β k | k > 0}).ncard : ℤ)
    (r (n + 1) - r n = 0 ∨ r (n + 1) - r n = 1) ∧
      (r (n + 1) - r n = 1 ↔ beattySeq α (n + 1) - beattySeq α n = 1)

/-- **Increments of the $\alpha$-Beatty counts between $\lfloor n\alpha\rfloor$ and
$\lfloor n\beta\rfloor$.** Let $\beta$ be an irrational number with $\beta > 2$, let $\alpha$ be a
real number with $\alpha^{-1} + \beta^{-1} = 1$, let $A$ be the set of the numbers
$\lfloor k\alpha\rfloor$ for positive integers $k$, and for an integer $m$ let $c(m)$ be the number
of elements of $A$ in the open interval $(\lfloor m\alpha\rfloor, \lfloor m\beta\rfloor)$. Then for
every positive integer $n$, the difference $c(n + 1) - c(n)$ is $\lfloor\beta\rfloor - 2$ or
$\lfloor\beta\rfloor - 1$, and it equals $\lfloor\beta\rfloor - 2$ if and only if
$\lfloor (n + 1)\beta\rfloor - \lfloor n\beta\rfloor = \lfloor\beta\rfloor$.

By Beatty's theorem, the Beatty sequences of $\alpha$ and $\beta$ are then complementary.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 5 (`integers-2025-A104-lem-5`). -/
public theorem_wanted beatty_card_self_between_succ_sub {α β : ℝ} (hirr : Irrational β)
    (hβ : 2 < β) (hαβ : α⁻¹ + β⁻¹ = 1) {n : ℤ} (hn : 0 < n) :
    let c : ℤ → ℤ := fun m ↦
      ((Ioo (beattySeq α m) (beattySeq β m) ∩ {beattySeq α k | k > 0}).ncard : ℤ)
    (c (n + 1) - c n = ⌊β⌋ - 2 ∨ c (n + 1) - c n = ⌊β⌋ - 1) ∧
      (c (n + 1) - c n = ⌊β⌋ - 2 ↔ beattySeq β (n + 1) - beattySeq β n = ⌊β⌋)

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
