/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.Homology.DGCyclicHodgeModels

/-!
# Wanted source-normalized cyclic Hodge filtration and degeneration

These requests use the polynomial HC quotient, the actual increasing
Hodge filtration and native cone spectral sequence. Nonnegative DG
degrees and all characteristic/smoothness/properness hypotheses remain
explicit. Reference: Kaledin math/0611623v4, equation1.17, Definition5.1
and Theorem5.5. The first-page map is the completed public
`hodgeFirstPageIso`, applied to the normalized associated-graded comparison.
-/

namespace WantedExt.AlgebraicGeometry.DGCyclicHodgeModelsWanted

open CategoryTheory
open MathlibExt.Algebra.Homology.DGCyclicBarModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels
open MathlibExt.Algebra.Homology.DGCyclicHodgeModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels

universe u

/-- Assemble the actual polynomial quotient with its fixed b+uB differential. -/
def_wanted dg_polynomial_cyclic_complex (k : Type u) [CommRing k]
    (A : DGAlgebra k) (M : HochschildMixedModel A) : PolynomialCyclicModel M

/-- Assemble the actual increasing polynomial Hodge filtration on that complex. -/
def_wanted dg_cyclic_hodge_filtration (k : Type u) [CommRing k]
    (A : DGAlgebra k) (M : HochschildMixedModel A) (C : PolynomialCyclicModel M) :
  HodgeFiltrationModel C

/-- The actual associated-graded map is the fixed u^-j cone projection to Hochschild. -/
def_wanted dg_cyclic_associated_graded_comparison (k : Type u) [CommRing k]
    (A : DGAlgebra k) (M : HochschildMixedModel A)
    (C : PolynomialCyclicModel M) (H : HodgeFiltrationModel C) (j : ℕ) :
  AssociatedGradedComparison H j

/-- Source Hodge-to-de Rham degeneration, retaining A^i=0 for i<0. -/
theorem_wanted smooth_proper_nonnegative_dg_hodge_degeneration
    (k : Type u) [Field k] [CharZero k] (A : DGAlgebra k)
    (hdegree : IsNonnegativelyGraded A) (hproper : IsProperAlgebra A)
    (D : EnvelopingModuleModel (diagonal (algebraCategory A)))
    (hsmooth : IsHomologicallySmooth (algebraCategory A) D)
    (M : HochschildMixedModel A) (C : PolynomialCyclicModel M) (H : HodgeFiltrationModel C) :
  IsE1Degenerate H

/-- Eventual page objects identify with the actual graded Hodge quotient of HC.
This theorem records convergence of the graded objects; it does not choose an
abutment map or claim that a normalized comparison has been constructed. -/
theorem_wanted smooth_proper_nonnegative_dg_cyclic_hodge_convergence
    (k : Type u) [Field k] [CharZero k] (A : DGAlgebra k)
    (hdegree : IsNonnegativelyGraded A) (hproper : IsProperAlgebra A)
    (D : EnvelopingModuleModel (diagonal (algebraCategory A)))
    (hsmooth : IsHomologicallySmooth (algebraCategory A) D)
    (M : HochschildMixedModel A) (C : PolynomialCyclicModel M) (H : HodgeFiltrationModel C) :
  ∀ p q : ℤ, ∃ r : ℤ, 1 ≤ r ∧ ∀ (r' : ℤ) (hr' : 1 ≤ r'), r ≤ r' →
    Nonempty (((hodgeSpectralSequence H).page r' hr').X (p,q) ≅
      gradedCyclicHomology H (-p) (-(p + q)))

end WantedExt.AlgebraicGeometry.DGCyclicHodgeModelsWanted
