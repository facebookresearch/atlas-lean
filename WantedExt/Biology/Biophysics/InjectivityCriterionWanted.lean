/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The injectivity criterion for reaction networks in a stirred-tank reactor

Consider a chemical reaction network on a finite set `S` of species, operated in a continuous-flow
stirred-tank reactor: besides its true reactions `y → y'` (indexed by `ρ`) there is an outflow
reaction `s → 0` for every species `s` and a feed reaction `0 → s` for some species. With
positive rate constants `k` on the true and outflow reactions, mass action gives the
species-formation function
`p_N(c, k) = ∑_{y → y' true} k_{y→y'} c^y (y - y') + ∑_s k_{s→0} c_s e_s`
on positive concentrations `c`, and the steady states are the positive `c` with `p_N(c, k)`
equal to the (constant) feed vector. The network is **injective** if `c ↦ p_N(c, k)` is
injective on the positive orthant for every positive `k`. An injective network does not have the
capacity for multiple positive equilibria: two positive steady states for the same rate
constants would have the same value of `p_N`.

`p_N` is a polynomial in the concentrations and rate constants, and so is the determinant of its
Jacobian matrix `∂p_N/∂c (c, k)`.

**Theorem 3.1** (Craciun–Feinberg 2005). A reaction network is injective if and only if
`det (∂p_N/∂c (c, k)) ≠ 0` for all positive `c` and all positive `k`.

**Theorem 3.3** (Craciun–Feinberg 2005). A reaction network is injective if and only if all the
coefficients in the expansion of `det (∂p_N/∂c (c, k))` (as a polynomial in `c` and `k`) are
nonnegative.

The source's networks (Definition 2.1) have no reaction from a complex to itself and at most one
reaction between two complexes; these are hypotheses here. The source allows complexes with
nonnegative real coefficients, where `p_N` is a generalized polynomial; this record states both
theorems for complexes with natural-number coefficients, where the polynomial expansion is
literal. The network structure is that of `MathlibExt.Dynamics.PolynomialNetworks.Deficiency`.

Sources: G. Craciun, M. Feinberg, "Multiple equilibria in complex chemical reaction networks:
I. The injectivity property", SIAM J. Appl. Math. 65 (2005) 1526–1546, Definitions 2.1–2.8,
Theorems 3.1 and 3.3.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

namespace WantedExt.Biology.Biophysics.InjectivityCriterionWanted

open MathlibExt.Biology.Dynamics.ComplexBalanced MvPolynomial

variable {S ρ : Type*} (N : ReactionNetwork S ρ)

/-- For finite species `S` (`[Fintype S]`) and finite reactions `ρ` (`[Fintype ρ]`), the
species-formation function of the network in a stirred-tank reactor, with rate constants
`k (Sum.inl r)` for the true reactions `r` and `k (Sum.inr s)` for the outflow reactions
`s → 0`: `p_N(c, k)_s = ∑_{r : ρ} k_r c^{src r} (src r s - prod r s) + k_{s→0} c_s`, where
`c^{src r} = ∏_{s' : S} c_{s'} ^ (src r s')`. -/
noncomputable def formationRate [Fintype S] [Fintype ρ] (k : ρ ⊕ S → ℝ) (c : S → ℝ) :
    S → ℝ :=
  fun s => (∑ r, k (.inl r) * (∏ s', c s' ^ N.src r s') * ((N.src r s : ℝ) - N.prod r s)) +
    k (.inr s) * c s

/-- The network is injective: for every choice of positive rate constants on the true and outflow
reactions, the species-formation function is injective on positive concentrations. -/
def IsInjective [Fintype S] [Fintype ρ] : Prop :=
  ∀ k : ρ ⊕ S → ℝ, (∀ i, 0 < k i) → Set.InjOn (formationRate N k) {c | ∀ s, 0 < c s}

/-- For finite species (`[Fintype S]`) and finite reactions (`[Fintype ρ]`), the
species-formation function as an integer polynomial in the concentrations `X (inl s)` and the
rate constants `X (inr i)`. -/
noncomputable def formationPoly [Fintype S] [Fintype ρ] (s : S) :
    MvPolynomial (S ⊕ (ρ ⊕ S)) ℤ :=
  (∑ r, X (.inr (.inl r)) * (∏ s', X (.inl s') ^ N.src r s') *
      C ((N.src r s : ℤ) - N.prod r s)) +
    X (.inr (.inr s)) * X (.inl s)

/-- For finite species (`[Fintype S]`) and finite reactions (`[Fintype ρ]`), the determinant of
the Jacobian matrix `∂p_N/∂c`, as an integer polynomial in the concentrations and the rate
constants. -/
noncomputable def jacobianDetPoly [Fintype S] [DecidableEq S] [Fintype ρ] :
    MvPolynomial (S ⊕ (ρ ⊕ S)) ℤ :=
  (Matrix.of fun s s' => pderiv (.inl s') (formationPoly N s)).det

/-- **Injectivity criterion for natural-number coefficients** (the case of natural-number
coefficients of Craciun–Feinberg 2005, Theorem 3.1). Let `N` be a network whose complexes have
natural-number coefficients, with finitely many species and reactions, with no reaction from a
complex to itself and at most one reaction between two complexes, operated with an outflow
reaction for every species. Then `N` is injective if and only if the Jacobian determinant
`det (∂p_N/∂c (c, k))` is nonzero for all positive concentrations `c` and all positive rate
constants `k`.

Source: G. Craciun, M. Feinberg, SIAM J. Appl. Math. 65 (2005) 1526–1546, Theorem 3.1. -/
theorem_wanted isInjective_iff_jacobianDet_ne_zero [Fintype S] [DecidableEq S] [Fintype ρ]
    (hloop : ∀ r, N.src r ≠ N.prod r)
    (hsimple : Function.Injective fun r => (N.src r, N.prod r)) :
    IsInjective N ↔ ∀ (c : S → ℝ) (k : ρ ⊕ S → ℝ), (∀ s, 0 < c s) → (∀ i, 0 < k i) →
      aeval (Sum.elim c k) (jacobianDetPoly N) ≠ 0

/-- **Coefficient criterion for natural-number coefficients** (the case of natural-number
coefficients of Craciun–Feinberg 2005, Theorem 3.3). Let `N` be a network whose complexes have
natural-number coefficients, with finitely many species and reactions, with no reaction from a
complex to itself and at most one reaction between two complexes, operated with an outflow
reaction for every species. Then `N` is injective if and only if every coefficient of the
Jacobian determinant `det (∂p_N/∂c)`, expanded as a polynomial in the concentrations and the rate
constants, is nonnegative.

Source: G. Craciun, M. Feinberg, SIAM J. Appl. Math. 65 (2005) 1526–1546, Theorem 3.3. -/
theorem_wanted isInjective_iff_coeff_jacobianDet_nonneg [Fintype S] [DecidableEq S]
    [Fintype ρ] (hloop : ∀ r, N.src r ≠ N.prod r)
    (hsimple : Function.Injective fun r => (N.src r, N.prod r)) :
    IsInjective N ↔ ∀ m, 0 ≤ (jacobianDetPoly N).coeff m

end WantedExt.Biology.Biophysics.InjectivityCriterionWanted
