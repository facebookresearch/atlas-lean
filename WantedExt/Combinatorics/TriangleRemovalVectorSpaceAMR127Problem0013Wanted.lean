/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynomial bounds for triangle removal in 𝔽₂ⁿ (O'Donnell, Problem 14)

R. O'Donnell, Open Problems in Analysis of Boolean Functions, Problem 14 (Triangle Removal in
`𝔽₂ⁿ`): let `A ⊆ 𝔽₂ⁿ`. Suppose that `ε 2ⁿ` elements must be removed from `A` to make it
triangle-free (no `x, y, x + y ∈ A`). Is it true that `Pr_{x,y}[x, y, x + y ∈ A] ≥ poly(ε)` for
independent uniform `x`, `y`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.TriangleRemovalVectorSpaceAMR127Problem0013Wanted

/-!
Source: R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447,
Problem 14 (Triangle Removal in 𝔽₂ⁿ). UnsolvedMath record UM-00800444 (`AMR-127-0013`), dataset
ulamai/UnsolvedMath v1.8.0.

"`ε 2ⁿ` elements must be removed" is read as: every triangle-free `B ⊆ A` misses at least `ε 2ⁿ`
elements of `A`. Triangles are ordered and may be degenerate (`x = y` gives `x + y = 0`), as in the
source and in Fox–Lovász (a triangle is an ordered triple with `x + y + z = 0`; in characteristic
`2` the triples in `A³` correspond to the pairs `(x, y)` with `x + y ∈ A`). The probability is
`triangleCount A / 4ⁿ`, and `poly(ε)` means `c ε^C` with constants `c, C > 0` independent of `n` and
`A`; `ε` ranges over `(0, 1]`.
-/

/-- **Triangle-free subsets of $\mathbb{F}_2^n$.** A set $A \subseteq \mathbb{F}_2^n$ is
triangle-free if there are no $x, y \in A$ with $x + y \in A$ (the case $x = y$ is allowed). -/
def IsTriangleFree {n : ℕ} (A : Finset (Fin n → ZMod 2)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x + y ∉ A

/-- **Number of triangles in a subset of $\mathbb{F}_2^n$.** For $A \subseteq \mathbb{F}_2^n$,
the triangle count of $A$ is the number of ordered pairs $(x, y) \in A \times A$ with
$x + y \in A$. Divided by $4^n$, it is the probability that $x, y, x + y \in A$ for independent
uniform $x, y \in \mathbb{F}_2^n$. -/
def triangleCount {n : ℕ} (A : Finset (Fin n → ZMod 2)) : ℕ :=
  ((A ×ˢ A).filter fun p => p.1 + p.2 ∈ A).card

/-- **Polynomial triangle removal in $\mathbb{F}_2^n$.** This is the statement that there are
real constants $c > 0$ and $C > 0$ such that for every $n$, every $A \subseteq \mathbb{F}_2^n$
and every real $\varepsilon$ with $0 < \varepsilon \le 1$: if every triangle-free $B \subseteq A$
misses at least $\varepsilon 2^n$ elements of $A$, then the triangle count of $A$ is at least
$c \varepsilon^C 4^n$, that is, $\Pr_{x,y}[x, y, x + y \in A] \ge c \varepsilon^C$ for
independent uniform $x, y \in \mathbb{F}_2^n$.

This is Green's question as posed by O'Donnell (Problem 14); the answer is yes. -/
def polynomialTriangleRemoval : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (A : Finset (Fin n → ZMod 2)) (ε : ℝ), 0 < ε → ε ≤ 1 →
    (∀ B ⊆ A, IsTriangleFree B → ε * 2 ^ n ≤ ((A \ B).card : ℝ)) →
      c * ε ^ C * 4 ^ n ≤ (triangleCount A : ℝ)

/-- **Polynomial triangle removal holds in $\mathbb{F}_2^n$.** There are real constants $c > 0$
and $C > 0$ such that for every natural number $n$, every finite set $A \subseteq \mathbb{F}_2^n$
and every real number $\varepsilon$ with $0 < \varepsilon \le 1$ the following holds: if every
triangle-free $B \subseteq A$ misses at least $\varepsilon 2^n$ elements of $A$, then the
triangle count of $A$ is at least $c \varepsilon^C 4^n$. Here a set $B \subseteq \mathbb{F}_2^n$
is triangle-free when there are no $x, y \in B$ with $x + y \in B$ (the case $x = y$ is allowed),
and the triangle count of $A$ is the number of ordered pairs $(x, y) \in A \times A$ with
$x + y \in A$, so that it divided by $4^n$ is the probability that $x, y, x + y \in A$ for
independent uniform $x, y \in \mathbb{F}_2^n$.

This answers O'Donnell's Problem 14 in the affirmative. Fox and Lovász proved it with the
essentially tight exponent $C = 1 + 1/(5/3 - \log_2 3) \approx 13.239$.

Source: R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447,
Problem 14 (Triangle Removal in 𝔽₂ⁿ); resolution: J. Fox and L. M. Lovász, A tight bound for Green's
arithmetic triangle removal lemma in vector spaces, Adv. Math. 321 (2017), 287-297,
arXiv:1606.01230, Theorem 1: for 0 < ε < 1 and δ = (ε/3)^{C_p}, if X, Y, Z ⊆ 𝔽_pⁿ span fewer than δ
N² triangles (N = pⁿ) then removing εN elements of X ∪ Y ∪ Z kills all triangles; C₂ = 1 + 1/(5/3 -
log₂ 3) ≈ 13.239 (applied with X = Y = Z = A and p = 2; the case ε = 1 follows from ε < 1),
https://arxiv.org/abs/1606.01230.
-/
public theorem_wanted polynomialTriangleRemoval_holds : polynomialTriangleRemoval

end MathlibExt.Combinatorics.TriangleRemovalVectorSpaceAMR127Problem0013Wanted
