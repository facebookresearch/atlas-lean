/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Schoenberg's conjecture on Hadamard products of convex functions (Hayman–Lingham Problem 6.9)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 6.9 (Schoenberg's
conjecture): if `f = ∑ aₙ zⁿ` and `g = ∑ bₙ zⁿ` are convex functions in `S`, is the Hadamard product
`f ∗ g = ∑ aₙ bₙ zⁿ` also a convex function in `S`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import WantedExt.Analysis.UnivalentClassSShared

@[expose] public section

namespace MathlibExt.Analysis.PolyaSchoenbergConvolutionAMR22Problem6009Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 6.9 (Schoenberg's conjecture). UnsolvedMath record
UM-02306009 (`AMR-022-6009`), dataset ulamai/UnsolvedMath v1.8.0.

The class `S` is `IsNormalizedUnivalent` (`WantedExt.Analysis.UnivalentClassSShared`, shared with
Problem 6.78): `f` holomorphic and injective on the open unit disc with `f 0 = 0` and `f' 0 = 1`. A
function in `S` is convex when it maps the disc onto a convex domain. The Taylor coefficients at `0`
are `iteratedDeriv n f 0 / n!`, and `f ∗ g` is the `tsum` of `aₙ bₙ zⁿ`; for convex `f`, `g ∈ S` one
has `|aₙ|, |bₙ| ≤ 1`, so the series converges on the disc, where all conditions are evaluated.
-/

open MathlibExt.Analysis.UnivalentClassSShared

/-- A convex function in `S`: `f ∈ S` maps the unit disc onto a convex domain. -/
def IsConvexUnivalent (f : ℂ → ℂ) : Prop :=
  IsNormalizedUnivalent f ∧ Convex ℝ (f '' Metric.ball 0 1)

/-- The `n`-th Taylor coefficient of `f` at `0`. -/
noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / n.factorial

/-- The Hadamard product `f ∗ g = ∑ aₙ bₙ zⁿ` of the Taylor series of `f` and `g` at `0`. -/
noncomputable def hadamardProduct (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, taylorCoeff f n * taylorCoeff g n * z ^ n

/-- Schoenberg's conjecture (Hayman–Lingham Problem 6.9, the Pólya–Schoenberg conjecture): the
Hadamard product of two convex functions in `S` is a convex function in `S`. -/
def hadamardProductOfConvexIsConvex : Prop :=
  ∀ f g : ℂ → ℂ, IsConvexUnivalent f → IsConvexUnivalent g → IsConvexUnivalent (hadamardProduct f g)

/--
Resolved true: Ruscheweyh and Sheil-Small proved the Pólya–Schoenberg conjecture: the Hadamard
product of two convex univalent functions normalized as in `S` is again convex univalent and in `S`
(Hayman–Lingham Update 6.9). Source: W. K. Hayman and E. F. Lingham, Research Problems in Function
Theory, Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Problem 6.9 (Schoenberg's
conjecture); resolution: St. Ruscheweyh and T. Sheil-Small, Hadamard products of Schlicht functions
and the Pólya-Schoenberg conjecture, Comment. Math. Helv. 48 (1973), 119-135; recorded in
Hayman–Lingham, Update 6.9, Hayman–Lingham Update 6.9: "Ruscheweyh and Sheil-Small have proved this
result" (the Hadamard product of two convex functions in S is a convex function in S).
-/
public theorem_wanted hadamardProductOfConvexIsConvex_holds : hadamardProductOfConvexIsConvex

end MathlibExt.Analysis.PolyaSchoenbergConvolutionAMR22Problem6009Wanted
