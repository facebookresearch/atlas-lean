/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Optimal Cohn-Elkies functions in dimensions 8 and 24 (Oberwolfach Reports 1/2005)

Oberwolfach workshop Gitter und Anwendungen (2005), A. Kumar (with H. Cohn): does a function exist
that meets the criteria of the Cohn-Elkies linear programming bound exactly for `n = 24`, `r = 2`
and for `n = 8`, `r = √2`, which would prove that the Leech lattice and `E₈` give the densest sphere
packings?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform

@[expose] public section

namespace MathlibExt.Analysis.CohnElkiesMagicFunctionsOWR782Problem004Wanted

/-!
Source: A. Kumar (with H. Cohn), in Gitter und Anwendungen, Oberwolfach Reports 2 (2005), no. 1, p.
36, DOI 10.4171/OWR/2005/01. UnsolvedMath record UM-30000163 (`OWR-782-004`), dataset
ulamai/UnsolvedMath v1.8.0.

The Cohn-Elkies criteria (Theorem 4 of the source abstract): a Schwartz function `f` with `f(0) =
f̂(0) > 0`, `f(x) ≤ 0` for `|x| ≥ r` and `f̂ ≥ 0`, normalized to `f(0) = f̂(0) = 1`; `f̂(ξ) = ∫ f(x)
e^{-2πi⟨x, ξ⟩} dx` (Mathlib's `𝓕`, the papers' normalization) must be real and nonnegative. Both
constructions are radial, so radiality is included.
-/

open FourierTransform

/-- A Cohn-Elkies auxiliary function in `ℝⁿ` for radius `r`: a radial real Schwartz function `f`
with `f(0) = f̂(0) = 1`, `f(x) ≤ 0` for `‖x‖ ≥ r` and `f̂ ≥ 0`, where
`f̂(ξ) = ∫ f(x) e^{-2πi⟨x, ξ⟩} dx` is real and nonnegative everywhere. -/
def IsCohnElkiesFunction {n : ℕ} (r : ℝ) (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) : Prop :=
  (∀ x y, ‖x‖ = ‖y‖ → f x = f y) ∧ f 0 = 1 ∧ 𝓕 (fun x => (f x : ℂ)) 0 = 1 ∧
    (∀ x, r ≤ ‖x‖ → f x ≤ 0) ∧
    ∀ ξ, (𝓕 (fun x => (f x : ℂ)) ξ).im = 0 ∧ 0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re

/-- Dimension `8`, radius `√2` (Oberwolfach Report 1/2005, p. 36): a Cohn-Elkies function proving
the optimality of the `E₈` packing exists. -/
def cohnElkiesFunctionDimEight : Prop :=
  ∃ f : SchwartzMap (EuclideanSpace ℝ (Fin 8)) ℝ, IsCohnElkiesFunction (Real.sqrt 2) f

/-- Dimension `24`, radius `2`: a Cohn-Elkies function proving the optimality of the Leech lattice
packing exists. -/
def cohnElkiesFunctionDimTwentyFour : Prop :=
  ∃ f : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℝ, IsCohnElkiesFunction 2 f

/--
Resolved true: Viazovska constructed (Theorem 3) a radial Schwartz function `g` on `ℝ⁸` with `g(x) ≤
0` for `|x| ≥ √2`, `ĝ ≥ 0` and `g(0) = ĝ(0) = 1`, proving that `E₈` gives the densest sphere packing
in dimension 8. Source: A. Kumar (with H. Cohn), in Gitter und Anwendungen, Oberwolfach Reports 2
(2005), no. 1, p. 36, DOI 10.4171/OWR/2005/01; resolution: M. S. Viazovska, The sphere packing
problem in dimension 8, Ann. of Math. (2) 185 (2017), arXiv:1603.04246, Theorem 3: there is a radial
Schwartz function g : ℝ⁸ → ℝ with g(x) ≤ 0 for |x| ≥ √2, ĝ(x) ≥ 0 for all x and g(0) = ĝ(0) = 1,
https://arxiv.org/abs/1603.04246.
-/
public theorem_wanted cohnElkiesFunctionDimEight_holds : cohnElkiesFunctionDimEight

/--
Resolved true: Cohn, Kumar, Miller, Radchenko and Viazovska constructed the analogous radial
Schwartz function on `ℝ²⁴` with `f(0) = f̂(0) = 1`, `f(x) ≤ 0` for `|x| ≥ 2` and `f̂ ≥ 0`, proving
that the Leech lattice gives the densest sphere packing in dimension 24. Source: A. Kumar (with H.
Cohn), in Gitter und Anwendungen, Oberwolfach Reports 2 (2005), no. 1, p. 36, DOI
10.4171/OWR/2005/01; resolution: H. Cohn, A. Kumar, S. D. Miller, D. Radchenko and M. Viazovska, The
sphere packing problem in dimension 24, Ann. of Math. (2) 185 (2017), arXiv:1603.06518, Section 4
(proof of Theorem 1.1): the radial Schwartz function f on ℝ²⁴ constructed there has f(0) = f̂(0) = 1
and satisfies the hypotheses of the linear programming bound, Theorem 1.2, with r = 2 (f(x) ≤ 0 for
|x| ≥ 2, f̂ ≥ 0), where f̂(y) = ∫ f(x) e^{-2πi⟨x, y⟩} dx, https://arxiv.org/abs/1603.06518.
-/
public theorem_wanted cohnElkiesFunctionDimTwentyFour_holds : cohnElkiesFunctionDimTwentyFour

end MathlibExt.Analysis.CohnElkiesMagicFunctionsOWR782Problem004Wanted
