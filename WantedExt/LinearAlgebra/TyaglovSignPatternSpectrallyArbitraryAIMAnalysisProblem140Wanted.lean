/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tyaglov's tridiagonal sign pattern is spectrally arbitrary (AimPL hyperbolicpoly, Problem 2.4)

AimPL: Stability and hyperbolicity, Section 2 (Matrix Theory), Problem 2.4 [M. Tyaglov]: Any real
polynomial can be written as `det(A - λI)`, where `A` has the (tridiagonal) form with rows `(+ +)`,
`(- 0 +)`, ..., `(- 0 +)`, `(- -)`: `+` on the superdiagonal and in position `(1, 1)`, `-` on the
subdiagonal and in position `(n, n)`, `0` elsewhere.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

@[expose] public section

namespace MathlibExt.LinearAlgebra.TyaglovSignPatternSpectrallyArbitraryAIMAnalysisProblem140Wanted

/-!
Source: AimPL: Stability and hyperbolicity, Section 2 (Matrix Theory), Problem 2.4 [M. Tyaglov],
American Institute of Mathematics problem lists, http://aimpl.org/hyperbolicpoly/2/. UnsolvedMath
record UM-20000608 (`AIM-ANALYSIS-0140`), dataset ulamai/UnsolvedMath v1.8.0.

Reading: `det(A - λI)` of an `n × n` real matrix has degree `n` and leading coefficient `(-1)ⁿ`, so
'any real polynomial' is read in its normalized form: for every `n ≥ 2`, every real polynomial of
degree `n` with leading coefficient `(-1)ⁿ`, equivalently every monic real polynomial `q` of degree
`n` (as `det(X • 1 - A) = (-1)ⁿ det(A - X • 1)`), is `A.charpoly` for a matrix `A` with the
displayed signs. In sign-pattern terms the pattern `S_n` is spectrally arbitrary. `n = 1` is
excluded: the single diagonal entry would have to be both positive and negative. `S_n` is the
negative transpose `-T_nᵀ` of the pattern `T_n` of Drew, Johnson, Olesky and van den Driessche (`-`
in positions `(1, 1)` and `(j + 1, j)`, `+` in positions `(n, n)` and `(j, j + 1)`).
-/

/-- Tyaglov's tridiagonal sign pattern `S_n` (AimPL, Stability and hyperbolicity, Problem 2.4), as
a matrix of signs indexed by `Fin n`: `+` on the superdiagonal and in the first diagonal position,
`-` on the subdiagonal and in the last diagonal position, `0` elsewhere. For `n ≥ 2` the two
diagonal corners `0` and `n - 1` are distinct. -/
def tyaglovPattern (n : ℕ) (i j : Fin n) : SignType :=
  if (j : ℕ) = i + 1 then 1
  else if (i : ℕ) = j + 1 then -1
  else if i = j ∧ (i : ℕ) = 0 then 1
  else if i = j ∧ (i : ℕ) + 1 = n then -1
  else 0

/-- Tyaglov's assertion (AimPL hyperbolicpoly Problem 2.4) in its normalized form: for every
`n ≥ 2` the sign pattern `S_n` is spectrally arbitrary, i.e. every monic real polynomial of degree
`n` is the characteristic polynomial `det (X • 1 - A)` of a real matrix `A` whose entries have the
signs prescribed by `S_n` (positive where `S_n` has `+`, negative where it has `-`, zero where it
has `0`). Since `det (A - λ I) = (-1)ⁿ det (λ I - A)`, this is the statement that every real
polynomial of degree `n` with leading coefficient `(-1)ⁿ` is `det (A - λ I)` for such `A`. -/
def tyaglovPatternSpectrallyArbitrary : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ q : Polynomial ℝ, q.Monic → q.natDegree = n →
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, SignType.sign (A i j) = tyaglovPattern n i j) ∧ A.charpoly = q

/--
Resolved true: Tyaglov's pattern `S_n = -T_nᵀ` is spectrally arbitrary for every `n ≥ 2`. Garnett
and Shader proved that the pattern `T_n` of Drew, Johnson, Olesky and van den Driessche is a SAP for
every `n ≥ 2`, and Drew et al. observe that the SAP property is preserved under negation and
transposition. Source: AimPL: Stability and hyperbolicity, Section 2 (Matrix Theory), Problem 2.4
[M. Tyaglov], American Institute of Mathematics problem lists, http://aimpl.org/hyperbolicpoly/2/;
resolution: C. Garnett and B. L. Shader, A proof of the T_n conjecture: Centralizers, Jacobians and
spectrally arbitrary sign patterns, Linear Algebra Appl. 436 (2012), 4451-4458,
doi:10.1016/j.laa.2011.06.051; with J. H. Drew, C. R. Johnson, D. D. Olesky and P. van den
Driessche, Spectrally arbitrary patterns, Linear Algebra Appl. 308 (2000), 121-137,
doi:10.1016/S0024-3795(00)00026-4, Garnett-Shader, abstract and Section 1: the pattern T_n with - in
positions (1, 1) and (j + 1, j), + in positions (n, n) and (j, j + 1) and 0 elsewhere is a SAP for
every n ≥ 2, where S is a SAP if every real monic polynomial of degree n is the characteristic
polynomial of some A in Q(S); Drew et al., Section 1, p. 122: 'if S is a SAP (IAP) then -S is also a
SAP (IAP). Each property is also preserved under transposition, permutation similarity and signature
similarity'. Tyaglov's pattern is -T_nᵀ, https://doi.org/10.1016/j.laa.2011.06.051.
-/
public theorem_wanted tyaglovPatternSpectrallyArbitrary_holds : tyaglovPatternSpectrallyArbitrary

end MathlibExt.LinearAlgebra.TyaglovSignPatternSpectrallyArbitraryAIMAnalysisProblem140Wanted
