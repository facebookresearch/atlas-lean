/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hankel determinants of univalent functions (Hayman–Lingham Problem 6.14)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 6.14: for `f ∈ S` with
coefficients `a_n`, let `A_n^{(k)}` be the Hankel determinant `det (a_{n+i+j})_{0 ≤ i, j < k}`.
Pommerenke proved `|A_n^{(k)}|^{1/k} = O(n^{j_k})` with `j_k = -1/2 + 16/√k`; the conjecture is that
`j_k < -1/2` for large `k`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import WantedExt.Analysis.PolyaSchoenbergConvolutionAMR22Problem6009Wanted
public import WantedExt.Analysis.UnivalentClassSShared

@[expose] public section

namespace MathlibExt.Analysis.HankelDeterminantUnivalentAMR22Problem6014Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 6.14. UnsolvedMath record UM-02306014 (`AMR-022-6014`),
dataset ulamai/UnsolvedMath v1.8.0.

The class `S` is `IsNormalizedUnivalent` (`WantedExt.Analysis.UnivalentClassSShared`): holomorphic
and injective on the unit disc with `f 0 = 0` and `f' 0 = 1`; `a_n = f⁽ⁿ⁾(0)/n!` is `taylorCoeff`
from the Problem 6.9 module (`WantedExt.Analysis.PolyaSchoenbergConvolutionAMR22Problem6009Wanted`).
The target is the theorem of Pommerenke that the list's Update 6.14 records as the answer:
`A_n^{(k)} = O(n^{3/2-k/2-kβ})` for every `k ≥ 2` with one constant `β > 1/4000`, the `O`-constant
depending on `f` and `k`. Taking `k`-th roots it gives `j_k = 3/(2k) - 1/2 - β`, which is below
`-1/2` once `k > 3/(2β)`; that consequence is not stated as a separate target.
-/

open MathlibExt.Analysis.UnivalentClassSShared
open MathlibExt.Analysis.PolyaSchoenbergConvolutionAMR22Problem6009Wanted (taylorCoeff)

/-- The Hankel determinant `A_n^{(k)} = det (a_{n+i+j})_{0 ≤ i, j < k}` of the Taylor coefficients
`a_n = taylorCoeff f n = f⁽ⁿ⁾(0) / n!` of `f`. -/
noncomputable def hankelDet (f : ℂ → ℂ) (k n : ℕ) : ℂ :=
  Matrix.det (Matrix.of fun i j : Fin k => taylorCoeff f (n + i + j))

/-- Pommerenke's Hankel determinant bound (Hayman–Lingham Update 6.14): there is a constant
`β > 1/4000` such that for every `k ≥ 2` and every `f ∈ S`, `A_n^{(k)} = O(n^{3/2 - k/2 - kβ})` as
`n → ∞`. -/
def hankelDeterminantBound : Prop :=
  ∃ β : ℝ, 1 / 4000 < β ∧ ∀ k : ℕ, 2 ≤ k → ∀ f : ℂ → ℂ, IsNormalizedUnivalent f →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖hankelDet f k n‖ ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2 - k / 2 - k * β)

/--
Resolved true: Pommerenke proved that some constant `β > 1/4000` satisfies `A_n^{(k)} = O(n^{3/2 -
k/2 - kβ})` for every `k ≥ 2` and `f ∈ S` (Hayman–Lingham Update 6.14), which gives `j_k < -1/2` for
every `k > 3/(2β)`. Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory,
Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Problem 6.14; resolution: Ch. Pommerenke, On
the Hankel determinants of univalent functions, Mathematika 14 (1967), 108-112, DOI
10.1112/S002557930000807X; recorded in Hayman–Lingham, Update 6.14, Update 6.14: 'Pommerenke
[MR0215976] has proved that for k = 2, 3, …, A_n^{(k)} = O(n^{3/2 - k/2 - kβ}) as n → ∞ for some
constant β, where β > 1/4000', https://doi.org/10.1112/S002557930000807X.
-/
public theorem_wanted hankelDeterminantBound_holds : hankelDeterminantBound

end MathlibExt.Analysis.HankelDeterminantUnivalentAMR22Problem6014Wanted
