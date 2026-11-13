/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Algebra.JardenFiniteFiberClaimWanted


/-!
# Finite fibers of homogeneous polynomial maps

Source: [AIM-LOGIC-0148] Question 36 (Jarden), AIM Problem Lists,
Workshop: Extensions of Hilbert's tenth problem,
`aim-logic-notes.json` notes[147],
https://aimath.org/WWN/hilberts10th/hilberts10th.pdf

Clause list (every item appears in the formal text below):
- (C1) `m : ℕ`: number of variables `x₁, …, xₘ`; quantifier domain `Fin m → Complex`.
- (C2) `n : ℕ`: number of polynomials / equations; index domain `Fin n`.
- (C3) `d : ℕ`: common homogeneous degree.
- (C4) `f : Fin n → MvPolynomial (Fin m) Complex`: the tuple `f₁, …, fₙ ∈ ℂ[x₁, …, xₘ]`.
- (C5) homogeneity: `∀ i, (f i).IsHomogeneous d`.
- (C6) isolated common zero, exactly `{0}`:
  `∀ x, (∀ i, eval x (f i) = 0) ↔ x = 0`.
- (C7) `b : Fin n → Complex`: arbitrary values `b₁, …, bₙ ∈ ℂ`.
- (C8) fiber variety `V(f₁(x⃗) = b₁, …, fₙ(x⃗) = bₙ)`:
  `{x : Fin m → Complex | ∀ i, eval x (f i) = b i}`.
- (C9) claim: that fiber is finite for every `b`: `Set.Finite` of the fiber.
-/

/-- Finite fibers of an isolated homogeneous system ([AIM-LOGIC-0148],
Question 36 (Jarden), AIM Problem Lists, Workshop: Extensions of
Hilbert's tenth problem, `aim-logic-notes.json` notes[147]):
`f₁, …, fₙ ∈ ℂ[x₁, …, xₘ]` homogeneous of degree `d` whose only common
zero is `(0, …, 0)` have `V(f₁(x⃗) = b₁, …, fₙ(x⃗) = bₙ)` finite for all
`b₁, …, bₙ ∈ ℂ`. -/
def conjecture : Prop :=
  ∀ (m n d : ℕ) (f : Fin n → MvPolynomial (Fin m) Complex),
    (∀ i, (f i).IsHomogeneous d) →
    (∀ x : Fin m → Complex, (∀ i, MvPolynomial.eval x (f i) = 0) ↔ x = 0) →
    ∀ (b : Fin n → Complex),
      Set.Finite {x : Fin m → Complex | ∀ i, MvPolynomial.eval x (f i) = b i}

/--
Resolved true: Resolved true by the source's own solution: the AIM list (Extensions of Hilbert's
tenth problem, Question 36, Jarden) notes that an infinite fiber would make the projective
closure of the homogenized system positive-dimensional, so it would meet the hyperplane at
infinity in a nonzero common zero of the f_i. Source: AIM Problem Lists, Extensions of Hilbert's
tenth problem (hilberts10th.pdf), Question 36 (Jarden) and its Solution paragraph,
https://aimath.org/WWN/hilberts10th/hilberts10th.pdf. Moved from
`OpenConjectures/Algebra/JardenFiniteFiberClaim`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Algebra.JardenFiniteFiberClaimWanted
