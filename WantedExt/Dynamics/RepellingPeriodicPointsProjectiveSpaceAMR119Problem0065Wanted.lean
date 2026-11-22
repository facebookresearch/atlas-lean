/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Repelling periodic points of holomorphic self-maps of ℙᵏ (SCV problem list, Problem 68)

Several Complex Variables Problem List, Problem 68 (N. Sibony): does every holomorphic map `F : ℙᵏ →
ℙᵏ` of degree at least two have a repelling periodic point? Do meromorphic maps have periodic
orbits?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

namespace MathlibExt.Dynamics.RepellingPeriodicPointsProjectiveSpaceAMR119Problem0065Wanted

/-!
Source: G. Buzzard, J. E. Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several Complex Variables
Problem List, arXiv:math/9509202 (1995), Problem 68. UnsolvedMath record UM-00800269
(`AMR-119-0065`), dataset ulamai/UnsolvedMath v1.8.0.

A holomorphic self-map of `ℙᵏ` of degree `d` is given by a homogeneous lift `P` of degree `d`
without common zeros other than `0`; `[x]` is periodic when `Pⁿ(x) = c x` with `c ≠ 0`, and it is
repelling when every eigenvalue of the differential of `Fⁿ` at `[x]` has modulus `> 1`. These
eigenvalues are computed on the lift, as in the open entry `SCVProjectivePlaneRepellingFixedPoint`
for `ℙ²`: they are the roots of `charpoly(c⁻¹ D(Pⁿ)(x)) / (X - dⁿ)`. The dimension is `k ≥ 1`. Only
the first question is formalized: the second ("Do meromorphic maps have periodic orbits?") specifies
neither the maps nor how points of indeterminacy are treated.
-/

open Polynomial

/-- The polynomial map `ℂᵏ⁺¹ → ℂᵏ⁺¹` given by a tuple `P` of polynomials (the `ℙᵏ` version of
`OpenConjectures.Analysis.SCVProjectivePlaneRepellingFixedPoint.liftMap`). -/
noncomputable def liftMap {k : ℕ} (P : Fin (k + 1) → MvPolynomial (Fin (k + 1)) ℂ)
    (x : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ :=
  fun i => MvPolynomial.eval x (P i)

/-- `P` is a homogeneous lift of degree `d` of a holomorphic self-map of `ℙᵏ`: its components are
homogeneous of degree `d` and have no common zero other than `0`. -/
def IsHolomorphicSelfMapLift {k : ℕ} (P : Fin (k + 1) → MvPolynomial (Fin (k + 1)) ℂ) (d : ℕ) :
    Prop :=
  (∀ i, (P i).IsHomogeneous d) ∧ ∀ x : Fin (k + 1) → ℂ, liftMap P x = 0 → x = 0

/-- The map of `ℙᵏ` with lift `P` of degree `d` has a repelling periodic point: for some `n ≥ 1`
and `x ≠ 0`, `Pⁿ(x) = c x` with `c ≠ 0` (so `[x]` has period dividing `n`), and every eigenvalue of
the differential of the `n`-th iterate at `[x]` has modulus `> 1`. These eigenvalues are the roots
of `charpoly(c⁻¹ D(Pⁿ)(x)) / (X - dⁿ)`: by Euler's identity `c⁻¹ D(Pⁿ)(x)` has the eigenvalue `dⁿ`
on `ℂ x`, and the remaining factor is the characteristic polynomial of the induced map on
`ℂᵏ⁺¹ / ℂ x`, the tangent space of `ℙᵏ` at `[x]`. -/
def HasRepellingPeriodicPoint {k : ℕ} (P : Fin (k + 1) → MvPolynomial (Fin (k + 1)) ℂ) (d : ℕ) :
    Prop :=
  ∃ (n : ℕ) (x : Fin (k + 1) → ℂ) (c : ℂ), 1 ≤ n ∧ x ≠ 0 ∧ c ≠ 0 ∧
    (liftMap P)^[n] x = c • x ∧
      ∀ μ : ℂ, (LinearMap.charpoly ((c⁻¹ • fderiv ℂ ((liftMap P)^[n]) x :
        (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) : (Fin (k + 1) → ℂ) →ₗ[ℂ] Fin (k + 1) → ℂ) /ₘ
          (X - C ((d : ℂ) ^ n))).IsRoot μ → 1 < ‖μ‖

/-- SCV Problem List, Problem 68 (first question, N. Sibony): every holomorphic self-map of `ℙᵏ`,
`k ≥ 1`, of degree at least two has a repelling periodic point. -/
def everyEndomorphismHasRepellingPeriodicPoint : Prop :=
  ∀ (k d : ℕ) (P : Fin (k + 1) → MvPolynomial (Fin (k + 1)) ℂ), 1 ≤ k → 2 ≤ d →
    IsHolomorphicSelfMapLift P d → HasRepellingPeriodicPoint P d

/--
Resolved true: Briend and Duval proved that the repelling periodic points of period n of a
holomorphic endomorphism of ℙᵏ of degree d ≥ 2 in the support of its equilibrium measure, weighted
by d^(-kn), converge to that measure; in particular such points exist. Source: G. Buzzard, J. E.
Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several Complex Variables Problem List,
arXiv:math/9509202 (1995), Problem 68; resolution: J.-Y. Briend, J. Duval, Exposants de Liapounoff
et distribution des points périodiques d'un endomorphisme de ℂℙᵏ, Acta Math. 182 (1999), 143-157,
main theorem (the repelling periodic points of period n on the support of the equilibrium measure μ,
weighted by d^{-kn}, converge to μ), as stated in T.-C. Dinh, N. Sibony, Dynamics in several complex
variables: endomorphisms of projective spaces and polynomial-like mappings, Lecture Notes in Math.
1998 (2010), 165-294, arXiv:0810.0811, theorem 'th_periodic_pk' of the section 'Equidistribution of
points' ('The following result due to Briend-Duval shows that repelling periodic points are
equidistributed on the support of the Green measure'); in particular repelling periodic points
exist, https://arxiv.org/abs/0810.0811.
-/
public theorem_wanted everyEndomorphismHasRepellingPeriodicPoint_holds :
    everyEndomorphismHasRepellingPeriodicPoint

end MathlibExt.Dynamics.RepellingPeriodicPointsProjectiveSpaceAMR119Problem0065Wanted
