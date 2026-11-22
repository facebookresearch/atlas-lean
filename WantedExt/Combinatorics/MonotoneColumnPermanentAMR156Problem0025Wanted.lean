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

/-- The polynomial `per(A + xJ) ∈ ℝ[x]`, `J` the all-ones matrix: the permanent of the matrix with
entries `A i j + x`. -/
noncomputable def permanentAddXJ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Polynomial ℝ :=
  (A.map Polynomial.C + Matrix.of fun _ _ => Polynomial.X).permanent

/-- The Haglund–Ono–Wagner monotone column permanent conjecture (Stanley, Positivity Problems,
Problem 24): if every column of the real `n × n` matrix `A` is weakly increasing, then
`per(A + xJ)` has only real zeros. -/
def monotoneColumnPermanentConjecture : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), (∀ i i' j, i ≤ i' → A i j ≤ A i' j) →
    ((permanentAddXJ A).map (algebraMap ℝ ℂ)).IsRealRooted

/--
Resolved true: Brändén, Haglund, Visontai and Wagner proved the monotone column permanent
conjecture: for every real `n × n` matrix `A` with weakly monotone columns, `per(A + xJ)` has only
real zeros (they prove the stronger statement that `per(z_j + a_ij)` is real stable). Source: R. P.
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
