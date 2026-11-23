/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.RingTheory.PowerSeries.Binomial

namespace MetaMathlibExt

@[expose] public section

open Equiv Finset

/-- **Increasing-cycle permutation.** A permutation $\tau$ of $\{0, \dots, n-1\}$ is an
increasing-cycle permutation when, for all $x$ and $y$ in $\{0, \dots, n-1\}$ such that
$\tau(x) \le x$ and $y$ lies in the same cycle of $\tau$ as $x$, we have $\tau(x) \le y$. That
is, whenever $\tau(x) \le x$, the value $\tau(x)$ is the least element of the cycle of $x$;
equivalently, each cycle of $\tau$ runs through its elements in increasing order and returns from
the largest to the least.

Set partitions of $\{0, \dots, n-1\}$ correspond bijectively to increasing-cycle permutations,
the blocks being the cycles (fixed points give singleton blocks), and partitions are counted
through this encoding.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4 (the permutation `τ`
whose cycles are the parts, with their elements in increasing order). -/
def IsIncreasingCyclePerm {n : ℕ} (τ : Perm (Fin n)) : Prop :=
  ∀ x y, τ x ≤ x → τ.SameCycle x y → τ x ≤ y

instance {n : ℕ} : DecidablePred (IsIncreasingCyclePerm (n := n)) := fun τ => by
  unfold IsIncreasingCyclePerm
  infer_instance

/-- **Genus of a set partition.** Let $\sigma$ be the cyclic permutation $i \mapsto i + 1 \pmod n$
of $\{0, \dots, n-1\}$. For a permutation $\tau$ of $\{0, \dots, n-1\}$, thought of as encoding the
set partition whose blocks are its cycles, let $|\alpha|$ be the number of cycles of $\tau$ and $c$
the number of cycles of $\sigma \circ \tau^{-1}$, fixed points counted as cycles in both. The genus
of $\tau$ is the integer part of $\frac{1}{2} \max(0,\ n + 1 - |\alpha| - c)$.

For $n \ge 1$ the number $n + 1 - |\alpha| - c$ is nonnegative and even, so the genus is the
number $g$ with $-2g = |\alpha| - 1 - n + c$; for $n = 0$ the genus is $0$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4, equation (genus). -/
def setPartitionGenus {n : ℕ} (τ : Perm (Fin n)) : ℕ :=
  (n + 1 - τ.partition.parts.card - (finRotate n * τ⁻¹).partition.parts.card) / 2

/-- **Number of set partitions of given type and genus.** For natural numbers $n$ and $g$ and a
multiset $\alpha$ of natural numbers, $C_{n,[\alpha]}^{(g)}$ is the number of increasing-cycle
permutations $\tau$ of $\{0, \dots, n-1\}$ whose multiset of cycle lengths, fixed points counted
as cycles of length $1$, is $\alpha$ and whose genus is $g$.

Through the encoding of set partitions by increasing-cycle permutations, this is the number of
set partitions of $\{0, \dots, n-1\}$ of type $[\alpha]$ (multiset of block sizes $\alpha$) and
genus $g$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4 (the numbers
`C_{n,[α]}^{(g)}`). -/
def partitionGenusCount (n : ℕ) (α : Multiset ℕ) (g : ℕ) : ℕ :=
  #{τ : Perm (Fin n) | IsIncreasingCyclePerm τ ∧ τ.partition.parts = α ∧
    setPartitionGenus τ = g}

/-- **The identity is an increasing-cycle permutation.** For every natural number $n$, the
identity permutation of $\{0, \dots, n-1\}$ is an increasing-cycle permutation.

Its cycles are the singletons, so it encodes the partition of $\{0, \dots, n-1\}$ into
singletons.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4. -/
theorem isIncreasingCyclePerm_one (n : ℕ) : IsIncreasingCyclePerm (1 : Perm (Fin n)) := by
  intro x y _ h
  rw [Perm.sameCycle_one] at h
  simp [h]

/-- **The partition into singletons has genus zero.** For every natural number $n$, the genus of
the identity permutation of $\{0, \dots, n-1\}$ is $0$; the identity encodes the partition of
$\{0, \dots, n-1\}$ into singletons.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4. -/
theorem setPartitionGenus_one (n : ℕ) : setPartitionGenus (1 : Perm (Fin n)) = 0 := by
  have h : (1 : Perm (Fin n)).partition.parts.card = n := by
    simp [Perm.parts_partition]
  unfold setPartitionGenus
  rw [h]
  omega

/-- **The cyclic rotation is an increasing-cycle permutation.** For every natural number $n$,
the cyclic permutation $i \mapsto i + 1 \pmod n$ of $\{0, \dots, n-1\}$ is an increasing-cycle
permutation.

For $n \ge 1$ its only cycle is all of $\{0, \dots, n-1\}$, so it encodes the set partition with a
single block.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4. -/
theorem isIncreasingCyclePerm_finRotate (n : ℕ) : IsIncreasingCyclePerm (finRotate n) := by
  cases n with
  | zero => intro x; exact x.elim0
  | succ m =>
    intro x y hx _
    by_cases hl : x = Fin.last m
    · subst hl
      rw [finRotate_last]
      exact Fin.zero_le y
    · exfalso
      have h1 := coe_finRotate_of_ne_last hl
      rw [Fin.le_def, h1] at hx
      omega

/-- **The one-block partition has genus zero.** For every natural number $n$, the genus of the
cyclic permutation $i \mapsto i + 1 \pmod n$ of $\{0, \dots, n-1\}$ is $0$.

For $n \ge 1$ its only cycle is all of $\{0, \dots, n-1\}$, so this says that the partition with a
single block has genus $0$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4 ("one-part partitions
(`k = 1`) necessarily have genus 0"). -/
theorem setPartitionGenus_finRotate (n : ℕ) : setPartitionGenus (finRotate n) = 0 := by
  have h : (finRotate n * (finRotate n)⁻¹).partition.parts.card = n := by
    simp [Perm.parts_partition]
  unfold setPartitionGenus
  rw [h]
  omega

/-- **Genus generating function of pairings.** Let $g \ge 1$, and for $k \ge 0$ let
$C_{2k,[2^k]}^{(g)}$ be the number of genus-$g$ set partitions of $\{0, \dots, 2k-1\}$ into $k$
blocks of size $2$. There is a polynomial $Q^{(g)}$ with rational coefficients, of degree
$g - 1$, with $Q^{(g)}(0) = \frac{(4g)!}{2^{2g}\,(2g+1)!}$, such that, as formal power series
in $u$ over $\mathbb{Q}$,
$$\sum_{k \ge 0} C_{2k,[2^k]}^{(g)}\, u^k = u^{2g}\, Q^{(g)}(u)\, (1 - 4u)^{-(6g-1)/2}.$$

Here $(1 - 4u)^{-(6g-1)/2}$ is the binomial series $(1 + X)^r = \sum_{m \ge 0} \binom{r}{m} X^m$
with $r = -(6g-1)/2$, evaluated at $X = -4u$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Proposition 11
(`jis-2024-24.2.6-prop-11`). -/
public theorem_wanted pairing_genus_generatingFunction (g : ℕ) (hg : 0 < g) :
    ∃ Q : Polynomial ℚ, Q.natDegree = g - 1 ∧
      Q.eval 0 = ((4 * g).factorial : ℚ) / (2 ^ (2 * g) * ((2 * g + 1).factorial : ℚ)) ∧
      PowerSeries.mk (fun k => (partitionGenusCount (2 * k) (Multiset.replicate k 2) g : ℚ)) =
        PowerSeries.X ^ (2 * g) * (Q : PowerSeries ℚ) *
          PowerSeries.rescale (-4 : ℚ)
            (PowerSeries.binomialSeries ℚ (-((6 * (g : ℚ) - 1) / 2)))

/-- **Genus of two-block partitions.** Let $\sigma$ be the cyclic permutation
$i \mapsto i + 1 \pmod n$ of $\{0, \dots, n-1\}$, and let $\tau$ be an increasing-cycle permutation
of $\{0, \dots, n-1\}$ with exactly two cycles, fixed points counted as cycles (so $\tau$ encodes a
set partition into two blocks). Then $\sigma \circ \tau^{-1}$ has exactly one cycle of length at
least $2$. Moreover, for every $x_0$ in $\{0, \dots, n-1\}$, if $B$ is the cycle of $\tau$
containing $x_0$ and $s$ is the number of elements of $B$ fixed by $\sigma \circ \tau^{-1}$, then
the genus $g$ of $\tau$ satisfies $g + 1 + s = |B|$.

Taking $x_0$ in each of the two blocks, of sizes $p$ and $n - p$, and writing $s_1$ and $s_2$ for
the corresponding values of $s$, gives $g = p - s_1 - 1 = (n - p) - s_2 - 1$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Lemma 13
(`jis-2024-24.2.6-lem-13`). -/
public theorem_wanted twoBlock_oneFace_and_genus {n : ℕ} (τ : Perm (Fin n))
    (hτ : IsIncreasingCyclePerm τ) (h2 : τ.partition.parts.card = 2) (x₀ : Fin n) :
    (finRotate n * τ⁻¹).cycleType.card = 1 ∧
      setPartitionGenus τ + 1 + #{x | τ.SameCycle x₀ x ∧ (finRotate n * τ⁻¹) x = x} =
        #{x | τ.SameCycle x₀ x}

/-- **Genus count of two-block partitions.** Let $n$, $p$ and $g$ be natural numbers with
$2 \le p < n$. The number $C_{n,[p,\,n-p]}^{(g)}$ of genus-$g$ set partitions of
$\{0, \dots, n-1\}$ into two blocks of sizes $p$ and $n - p$ equals
$$\frac{n}{g+1} \binom{p-1}{g} \binom{n-p-1}{g}$$
when $n \ne 2p$, and half of this number when $n = 2p$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Proposition 14
(`jis-2024-24.2.6-prop-14`). -/
public theorem_wanted partitionGenusCount_twoBlocks (n p g : ℕ) (hp : 2 ≤ p) (hpn : p < n) :
    (partitionGenusCount n {p, n - p} g : ℚ) =
      (if n = 2 * p then 1 / 2 else 1) *
        ((n : ℚ) / (g + 1) * ((p - 1).choose g : ℚ) * ((n - p - 1).choose g : ℚ))

end

end MetaMathlibExt
