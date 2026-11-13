/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Bellon–Viallet Integrality Conjecture for dynamical degrees

Integrality Conjecture (Bellon–Viallet, 1999): let `f : ℙᴺ ⇢ ℙᴺ` be a dominant rational map. Then
the dynamical degree `δ_f = lim_n deg(fⁿ)^(1/n)` of `f` is an algebraic integer.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

namespace MathlibExt.Dynamics.DynamicalDegreeIntegralityAMR126Problem0026Wanted

/-!
Source: R. Benedetto, P. Ingram, R. Jones, M. Manes, J. H. Silverman, T. J. Tucker, Current trends
and open problems in arithmetic dynamics, Bull. Amer. Math. Soc. 56 (2019), 611-685,
arXiv:1806.04980, section 'Dynamical Degrees of Rational Maps', Conjecture (Integrality Conjecture),
Conjecture 13.17 of the published version. UnsolvedMath record UM-00800403 (`AMR-126-0026`), dataset
ulamai/UnsolvedMath v1.8.0.

Rational self-maps of `ℙᴺ` are given by tuples of `N + 1` forms over `ℚ` of a common degree;
dominance is algebraic independence of the forms (dominance of the cone map `𝔸ᴺ⁺¹ → 𝔸ᴺ⁺¹`). `fⁿ` is
represented by the `n`-fold substitution of the tuple, and `deg(fⁿ)` is the least degree of a
nonzero tuple of forms proportional to it (the degree after removing the common factor of the
components). The conjecture is stated for maps defined over `ℚ`; the counterexample of Bell, Diller
and Jonsson exists over every field of characteristic `≠ 2`, in particular over `ℚ`.
-/

open Filter Topology

/-- The composite `F ∘ G` of two tuples of polynomials in `N + 1` variables (substitute `G` into
each component of `F`); for homogeneous tuples this is a lift of the composite rational map. -/
noncomputable def compTuple {N : ℕ} (F G : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℚ) :
    Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℚ :=
  fun i => MvPolynomial.bind₁ G (F i)

/-- The `n`-fold composite `F ∘ ⋯ ∘ F` (the identity tuple for `n = 0`). -/
noncomputable def iterTuple {N : ℕ} (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℚ) (n : ℕ) :
    Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℚ :=
  (compTuple F)^[n] MvPolynomial.X

/-- The degree of the rational map of `ℙᴺ` represented by the tuple `G`: the least `e` such that a
nonzero tuple of degree-`e` forms is proportional to `G` (`Hᵢ Gⱼ = Hⱼ Gᵢ`), i.e. the common degree
of the components of `G` after removing their common factor. -/
noncomputable def ratDeg {N : ℕ} (G : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℚ) : ℕ :=
  sInf {e | ∃ H : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℚ, H ≠ 0 ∧
    (∀ i, (H i).IsHomogeneous e) ∧ ∀ i j, H i * G j = H j * G i}

/-- `F` defines a dominant rational self-map of `ℙᴺ` over `ℚ`: its components are forms of a
common degree and are algebraically independent (the cone map `𝔸ᴺ⁺¹ → 𝔸ᴺ⁺¹` is dominant). -/
def IsDominantRationalSelfMap {N : ℕ} (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℚ) : Prop :=
  (∃ d : ℕ, ∀ i, (F i).IsHomogeneous d) ∧ AlgebraicIndependent ℚ F

/-- Integrality Conjecture (Bellon–Viallet): the dynamical degree
`δ_f = lim_n deg(fⁿ)^(1/n)` of every dominant rational self-map `f` of `ℙᴺ` is an algebraic
integer. -/
def integralityConjecture : Prop :=
  ∀ (N : ℕ) (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℚ), IsDominantRationalSelfMap F →
    ∀ δ : ℝ, Tendsto (fun n : ℕ => (ratDeg (iterTuple F n) : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 δ) →
      IsIntegral ℤ δ

/--
Resolved false: Bell, Diller and Jonsson give a dominant rational self-map of ℙ² (over any field of
characteristic not two, in particular over ℚ) whose dynamical degree is transcendental, hence not an
algebraic integer. Source: R. Benedetto, P. Ingram, R. Jones, M. Manes, J. H. Silverman, T. J.
Tucker, Current trends and open problems in arithmetic dynamics, Bull. Amer. Math. Soc. 56 (2019),
611-685, arXiv:1806.04980, section 'Dynamical Degrees of Rational Maps', Conjecture (Integrality
Conjecture), Conjecture 13.17 of the published version; resolution: J. P. Bell, J. Diller, M.
Jonsson, A transcendental dynamical degree, Acta Math. 225 (2020), 193-225, arXiv:1907.00675, Main
Theorem: for every field k of characteristic ≠ 2 there is a dominant rational map f : ℙ²_k ⇢ ℙ²_k
whose dynamical degree is transcendental; the introduction identifies the question as [BIJMST19,
Conjecture 13.17], https://arxiv.org/abs/1907.00675.
-/
public theorem_wanted integralityConjecture_refuted : ¬ integralityConjecture

end MathlibExt.Dynamics.DynamicalDegreeIntegralityAMR126Problem0026Wanted
