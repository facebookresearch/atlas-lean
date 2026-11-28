/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three consecutive powerful numbers of middle-cube form

Statements from Tsz Ho Chan, "A Note on Three Consecutive Powerful
Numbers", *INTEGERS* 25 (2025), Paper A7, DOI 10.5281/zenodo.14679327
(<https://math.colgate.edu/~integers/z7/z7.pdf>).

All variables are integers unless positivity is stated explicitly.

Proved in `MathlibExt.NumberTheory.PowerfulNumbers`: Lemmas 1–3
(`MetaMathlibExt.int_sq_sub_int_sq_ne_two`,
`MetaMathlibExt.three_exact_dvd_sq_add_self_add_one`, and
`MetaMathlibExt.three_exact_dvd_sq_sub_self_add_one`).

The proof of Lemma 4 in `MathlibExt.NumberTheory.QuarticToCubic` constructs the cubic
point `(a * x ^ 2, a * x * y)`. Its nonzero first coordinate excludes the solution
`(0, 0)` that occurs for every choice of coefficients.

The Pell generations in Lemmas 5 and 6 use Mathlib's quadratic
integers `ℤ√3`. Lemma 5, proved in `MathlibExt.NumberTheory.PellThreeOne`,
is indexed from the first positive power of `2 + √3`.
Lemma 6, proved in `MathlibExt.NumberTheory.PellThreeNegTwo`, is indexed from the seed `(1, 1)`:
the displayed initial values are the coordinates at exponents `0`
and `1` in `(1 + √3)(2 + √3)^k`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.NumberTheory.PellThreeNegTwo
public import MathlibExt.NumberTheory.PellThreeOne
public import MathlibExt.NumberTheory.PowerfulNumbers
public import MathlibExt.NumberTheory.PrimeCubeSquareNeighbors
public import MathlibExt.NumberTheory.PrimeCubeSquareProduct
public import MathlibExt.NumberTheory.QuarticToCubic
