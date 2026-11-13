/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The monotone column permanent conjecture (Stanley, Problem 24)

R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics, Problem 24
(Haglund–Ono–Wagner): let `A` be an `n × n` real matrix for which every column is weakly increasing,
and let `J` be the `n × n` all-ones matrix. Does `per(A + xJ)` have only real zeros?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import MathlibExt.Algebra.Polynomial.RealRooted

@[expose] public section

namespace MathlibExt.Combinatorics.MonotoneColumnPermanentAMR156Problem0025Wanted

/-!
Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999),
Problem 24 (Haglund–Ono–Wagner monotone column permanent conjecture). UnsolvedMath record
UM-00801199 (`AMR-156-0025`), dataset ulamai/UnsolvedMath v1.8.0.

`per(A + xJ)` is the permanent of the matrix of polynomials `A i j + x` in `ℝ[x]`; it has degree `n`
and leading coefficient `n!`, so it is nonzero, and "only real zeros" is `Polynomial.IsRealRooted`
(MathlibExt) of its image in `ℂ[x]`: every complex root has zero imaginary part. Columns weakly
increasing means `A i j ≤ A i' j` for `i ≤ i'`. Brändén–Haglund–Visontai–Wagner state the conjecture
with weakly decreasing columns and note that the conventions are equivalent (reversing the order of
the rows does not change the permanent); the dataset record's extra word "nonnegative" is not
needed.
-/

/-- **The polynomial $\operatorname{per}(A + xJ)$.** For a real $n \times n$ matrix $A$, this is
the polynomial $\operatorname{per}(A + xJ) \in \mathbb{R}[x]$, where $J$ is the $n \times n$
all-ones matrix: the permanent of the $n \times n$ matrix of polynomials whose $(i, j)$ entry is
$A_{ij} + x$. -/
noncomputable def permanentAddXJ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Polynomial ℝ :=
  (A.map Polynomial.C + Matrix.of fun _ _ => Polynomial.X).permanent

/-- **The Haglund–Ono–Wagner monotone column permanent conjecture.** This is the statement that
for every $n \in \mathbb{N}$ and every real $n \times n$ matrix $A$ whose columns are weakly
increasing ($A_{ij} \le A_{i'j}$ whenever $i \le i'$), every complex root of the polynomial
$\operatorname{per}(A + xJ) \in \mathbb{R}[x]$ is real, where $J$ is the $n \times n$ all-ones
matrix. -/
def monotoneColumnPermanentConjecture : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), (∀ i i' j, i ≤ i' → A i j ≤ A i' j) →
    ((permanentAddXJ A).map (algebraMap ℝ ℂ)).IsRealRooted

/--
**Brändén–Haglund–Visontai–Wagner theorem (monotone column permanent conjecture).** For every
$n \in \mathbb{N}$ and every real $n \times n$ matrix $A$ whose columns are weakly increasing
($A_{ij} \le A_{i'j}$ whenever $i \le i'$), every complex root of the polynomial
$\operatorname{per}(A + xJ) \in \mathbb{R}[x]$ is real, where $J$ is the $n \times n$ all-ones
matrix.

Brändén, Haglund, Visontai and Wagner prove the stronger statement that the multivariate
polynomial $\operatorname{per}(z_j + A_{ij})$, in one variable $z_j$ for each column $j$, is real
stable.

Source: R. P.
Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999), Problem 24
(Haglund–Ono–Wagner monotone column permanent conjecture); resolution: P. Brändén, J. Haglund, M.
Visontai and D. G. Wagner, Proof of the monotone column permanent conjecture, in Notions of
Positivity and the Geometry of Polynomials, Trends Math., Birkhäuser (2011), 63-78, arXiv:1010.2565,
Section 1 and abstract: for every n × n monotone column matrix A, per(zJₙ + A) is a polynomial in z
with only real roots (the MCPC, Conjecture 2 of Haglund-Ono-Wagner), proved in full generality via
the multivariate (real stable) version, https://arxiv.org/abs/1010.2565.
-/
public theorem_wanted monotoneColumnPermanentConjecture_holds : monotoneColumnPermanentConjecture

end MathlibExt.Combinatorics.MonotoneColumnPermanentAMR156Problem0025Wanted
