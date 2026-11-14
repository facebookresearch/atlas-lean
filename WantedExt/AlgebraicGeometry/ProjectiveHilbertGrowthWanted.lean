/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.RingTheory.ProjectiveHilbertGrowth

/-!
# Macaulay growth and Gotzmann persistence

These projective embedding and Hilbert-scheme inputs control the growth of
actual standard-graded quotient pieces. The generator bound is explicit;
the persistence assertion does not apply to an arbitrary homogeneous ideal
without that bound.

References:
* F. S. Macaulay, *Some properties of enumeration in the theory of modular
  systems*, Proc. London Math. Soc. 26 (1927), 531–555.
* G. Gotzmann, *Eine Bedingung für die Flachheit und das Hilbertpolynom eines
  graduierten Ringes*, Math. Z. 158 (1978), 61–70.
* Miller–Sturmfels, *Combinatorial Commutative Algebra*, Hilbert functions,
  https://doi.org/10.1007/b138602.

Covered projective Euler-characteristic/Hilbert-polynomial source:
AxiomMath/Stacks at c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/HilbertPolynomial.lean`.
Those polynomial constructions are not requested again here.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ProjectiveHilbertGrowthWanted

open MathlibExt.RingTheory.ProjectiveHilbertGrowth

variable {k : Type*} [Field k] {n : ℕ}

/-- Every natural number has its degree-positive binomial expansion. -/
theorem_wanted exists_macaulayExpansion (d h : ℕ) (hd : 0 < d) :
    Nonempty (MacaulayExpansion d h)

/-- Macaulay's upper bound on the next homogeneous quotient dimension. -/
theorem_wanted macaulay_growth (I : Ideal (MvPolynomial (Fin n) k))
    (hI : IsHomogeneous I) (d : ℕ) (hd : 0 < d)
    (E : MacaulayExpansion d (hilbertFunction I d)) :
    hilbertFunction I (d + 1) ≤ E.successor

/-- Equality persists after the explicit generator degree bound. -/
theorem_wanted gotzmann_persistence (I : Ideal (MvPolynomial (Fin n) k))
    (hI : IsHomogeneous I) (d : ℕ) (hd : 0 < d)
    (hgen : GeneratedThrough I d)
    (E : MacaulayExpansion d (hilbertFunction I d))
    (heq : hilbertFunction I (d + 1) = E.successor) :
    ∀ t ≥ d, ∀ F : MacaulayExpansion t (hilbertFunction I t),
      hilbertFunction I (t + 1) = F.successor

end WantedExt.AlgebraicGeometry.ProjectiveHilbertGrowthWanted
