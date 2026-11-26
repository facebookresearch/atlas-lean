/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Ore condition for group algebras of lamplighter groups (Kourovka Notebook Problem 12.47)

Kourovka Notebook, Archive of Solved Problems, Problem 12.47 (P. A. Linnell): let `k` be a field,
`p` a prime and `G = ℤₚ ≀ ℤ`. Does `kG` have a classical quotient ring, i.e. do the
non-zero-divisors of `kG` form an Ore set?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.SemidirectProduct

@[expose] public section

namespace MathlibExt.GroupTheory.LamplighterGroupAlgebraOreKourovka12Problem47Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.47 (P. A.
Linnell). UnsolvedMath record UM-00700866 (`KOU-12.47`), dataset ulamai/UnsolvedMath v1.8.0.

`ℤₚ ≀ ℤ` is the semidirect product of `⨁_{i ∈ ℤ} ℤ/p` (finitely supported functions) by `ℤ` acting
by the shift. Having a classical (right) ring of quotients is the right Ore condition for the
non-zero-divisors, as in Definition 1 of Linnell, Lück and Schick; for group algebras the left and
right conditions are equivalent. The target is stated for some field and some prime (the strongest
true form, existential when refuted, as in WantedExt/Sources/UnsolvedMath.md), so its refutation
asserts that `k[ℤₚ ≀ ℤ]` is not Ore for every field `k` and every prime `p`: stronger than the
source's negative answer, which needs one pair, and what Theorem 3 of Linnell, Lück and Schick
proves.
-/

/-- **Shift of the lamplighter base group.** For a natural number $p$, the shift is the
automorphism $f \mapsto f(\cdot - 1)$ of the base group $\bigoplus_{i \in \mathbb{Z}} \mathbb{Z}/p$,
the additive group of finitely supported functions $\mathbb{Z} \to \mathbb{Z}/p$, viewed as a
multiplicative group. -/
noncomputable def shift (p : ℕ) : MulAut (Multiplicative (ℤ →₀ ZMod p)) :=
  AddEquiv.toMultiplicative (Finsupp.domCongr (Equiv.addRight (1 : ℤ)))

/-- **Lamplighter group.** For a natural number $p$, the lamplighter group
$\mathbb{Z}/p \wr \mathbb{Z}$ is the semidirect product
$\left(\bigoplus_{i \in \mathbb{Z}} \mathbb{Z}/p\right) \rtimes \mathbb{Z}$, in which
$n \in \mathbb{Z}$ acts on the base group by the $n$-th power of the shift
$f \mapsto f(\cdot - 1)$. -/
abbrev Lamplighter (p : ℕ) : Type :=
  Multiplicative (ℤ →₀ ZMod p) ⋊[zpowersHom (MulAut (Multiplicative (ℤ →₀ ZMod p))) (shift p)]
    Multiplicative ℤ

/-- **Non-zero-divisor.** An element $s$ of a ring $R$ is a non-zero-divisor when it is neither a
left nor a right zero divisor: for every $z \in R$, $zs = 0$ implies $z = 0$ and $sz = 0$ implies
$z = 0$. -/
def IsNonZeroDivisor {R : Type*} [Ring R] (s : R) : Prop :=
  (∀ z : R, z * s = 0 → z = 0) ∧ ∀ z : R, s * z = 0 → z = 0

/-- **Right Ore ring.** A ring $R$ satisfies the right Ore condition for its non-zero-divisors, so
that it has a classical right ring of quotients, when for all $s, t \in R$ with $s$ a
non-zero-divisor there are $x, y \in R$ with $x$ a non-zero-divisor and $sy = tx$.

For group algebras the left and right conditions agree. -/
def IsOreRing (R : Type*) [Ring R] : Prop :=
  ∀ s t : R, IsNonZeroDivisor s → ∃ x y : R, IsNonZeroDivisor x ∧ s * y = t * x

/-- **Kourovka Problem 12.47: some lamplighter group algebra is Ore.** There are a field $k$ and a
prime $p$ such that the group algebra $k[\mathbb{Z}/p \wr \mathbb{Z}]$ of the lamplighter group
$\mathbb{Z}/p \wr \mathbb{Z}$ satisfies the right Ore condition for its non-zero-divisors, that
is, has a classical right ring of quotients.

Kourovka 12.47 (P. A. Linnell) asks this for a given field and prime; the existential form makes
its refutation cover every field and every prime. -/
def lamplighterGroupAlgebraOre : Prop :=
  ∃ (k : Type) (_ : Field k) (p : ℕ), p.Prime ∧ IsOreRing (MonoidAlgebra k (Lamplighter p))

/--
**Lamplighter group algebras are not Ore.** For every field $k$ and every prime $p$, the group
algebra $k[\mathbb{Z}/p \wr \mathbb{Z}]$ of the lamplighter group $\mathbb{Z}/p \wr \mathbb{Z}$
does not satisfy the right Ore condition for its non-zero-divisors: there are $s$ and $t$ in it,
with $s$ a non-zero-divisor, such that $sy = tx$ holds for no $x$ and $y$ with $x$ a
non-zero-divisor.

Resolved false: Linnell, Lück and Schick (Theorem 3, with W. Dicks's argument) prove that $kG$ is
not an Ore ring for every field $k$ and every group $G$ containing $H \wr \mathbb{Z}$ with
$H \ne 1$ finite, in particular for $G = \mathbb{Z}/p \wr \mathbb{Z}$ and every prime $p$; the
Kourovka Archive answers 12.47 "No, it does not".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.47
(P. A. Linnell); resolution: P. A. Linnell, W. Lück and T. Schick, The Ore condition, affiliated
operators, and the lamplighter group, in: High-dimensional manifold topology (Trieste, 2001), World
Scientific, 2003, 315-321, Theorem 3: kG is not an Ore ring for every field k and every group G
containing H ≀ ℤ with H ≠ 1 finite; Kourovka Archive, Problem 12.47,
http://him-lueck.uni-bonn.de/data/lamplighter.pdf.
-/
public theorem_wanted lamplighterGroupAlgebraOre_refuted : ¬ lamplighterGroupAlgebraOre

end MathlibExt.GroupTheory.LamplighterGroupAlgebraOreKourovka12Problem47Wanted
