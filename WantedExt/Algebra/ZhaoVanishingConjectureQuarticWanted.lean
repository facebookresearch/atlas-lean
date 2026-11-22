/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `OWR-1452-012`
# Zhao's vanishing conjecture for quartic forms

Oberwolfach Report 01/2007 (Affine Algebraic Geometry), abstract on the Jacobian conjecture, Section
5, Conjecture 5.1 (W. Zhao).

Let `△ = ∑ᵢ ∂²/∂Xᵢ²` be the Laplacian on `ℂ[X₁, …, Xₙ]`. Vanishing Conjecture: for every homogeneous
polynomial `P` of degree `4`, if `△ᵐ(Pᵐ) = 0` for all `m ≥ 1` then `△ᵐ(Pᵐ⁺¹) = 0` for all
sufficiently large `m`. By Zhao's theorem it is equivalent (over all `n`) to the Jacobian
conjecture.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Complex.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Algebra.ZhaoVanishingConjectureQuarticWanted

open MvPolynomial

/-- The Laplacian `△ = ∑ᵢ ∂²/∂Xᵢ²` on `ℂ[X₁, …, Xₙ]`. -/
noncomputable def laplacian (n : ℕ) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
  ∑ i, (pderiv i).toLinearMap ∘ₗ (pderiv i).toLinearMap

/-- Zhao's Vanishing Conjecture for quartic forms: if `△ᵐ(Pᵐ) = 0` for all `m ≥ 1`, then
`△ᵐ(Pᵐ⁺¹) = 0` for all large `m`. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℂ), P.IsHomogeneous 4 →
    (∀ m ≥ 1, (laplacian n ^ m) (P ^ m) = 0) →
      ∃ M : ℕ, ∀ m ≥ M, (laplacian n ^ m) (P ^ (m + 1)) = 0

-- Carried source audit `OWR-1452-012` (see the Moved/ record).

/--
Resolved false: Resolved (false): Zhao proved that this vanishing conjecture, over all n, is
equivalent to the Jacobian conjecture (Trans. Amer. Math. Soc. 359 (2007), arXiv:math/0409534),
and the Jacobian conjecture is false: Alpöge's three-dimensional counterexample of July 2026,
rederived by van den Essen (arXiv:2609.17795), with further explicit counterexamples verified in
exact arithmetic by Gao (arXiv:2608.00222). The smallest n in which the quartic vanishing
conjecture fails is not known. Source: W. Zhao, Hessian nilpotent polynomials and the Jacobian
conjecture, Trans. Amer. Math. Soc. 359 (2007) 249-274, arXiv:math/0409534,
https://arxiv.org/abs/math/0409534; S. Gao, Counterexamples to the Jacobian conjecture in
dimensions greater than two, arXiv:2608.00222, https://arxiv.org/abs/2608.00222; A. van den
Essen, An elementary way to find a counterexample to the Jacobian Conjecture, arXiv:2609.17795,
https://arxiv.org/abs/2609.17795. Moved from
`OpenConjectures/Algebra/ZhaoVanishingConjectureQuartic`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Algebra.ZhaoVanishingConjectureQuarticWanted
