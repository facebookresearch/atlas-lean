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

/-- `A ⊆ 𝔽₂ⁿ` is triangle-free: there are no `x, y` with `x, y, x + y ∈ A` (`x = y` allowed). -/
def IsTriangleFree {n : ℕ} (A : Finset (Fin n → ZMod 2)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x + y ∉ A

/-- The number of pairs `(x, y) ∈ 𝔽₂ⁿ × 𝔽₂ⁿ` with `x, y, x + y ∈ A`; divided by `4ⁿ` it is the
probability `Pr_{x,y}[x, y, x + y ∈ A]` for independent uniform `x`, `y`. -/
def triangleCount {n : ℕ} (A : Finset (Fin n → ZMod 2)) : ℕ :=
  ((A ×ˢ A).filter fun p => p.1 + p.2 ∈ A).card

/-- Green's question (O'Donnell, Problem 14), answered: there are constants `c, C > 0` such that if
`ε 2ⁿ` elements must be removed from `A ⊆ 𝔽₂ⁿ` to make it triangle-free (every triangle-free
`B ⊆ A` misses at least `ε 2ⁿ` elements of `A`), then `Pr_{x,y}[x, y, x + y ∈ A] ≥ c ε^C`. -/
def polynomialTriangleRemoval : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (A : Finset (Fin n → ZMod 2)) (ε : ℝ), 0 < ε → ε ≤ 1 →
    (∀ B ⊆ A, IsTriangleFree B → ε * 2 ^ n ≤ ((A \ B).card : ℝ)) →
      c * ε ^ C * 4 ^ n ≤ (triangleCount A : ℝ)

/--
Resolved true: Fox and Lovász proved a polynomial (and essentially tight) arithmetic triangle
removal lemma in `𝔽_pⁿ`: with `δ = (ε/3)^{C_p}`, a set needing `ε N` deletions to become
triangle-free has at least `δ N²` triangles; for `p = 2`, `C₂ ≈ 13.239`, so `c = 3^{-C₂}`, `C = C₂`
work. (The dataset record's "polynomial bounds disproved" is a record error: the answer is yes.)
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
