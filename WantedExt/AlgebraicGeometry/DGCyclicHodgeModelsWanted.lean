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

/-- Degeneration of the Hodge-to-de Rham spectral sequence for DG algebras (Kaledin, Theorem 5.5):
let $k$ be a field of characteristic zero and $A$ a DG algebra over $k$ that is nonnegatively graded
($A^i = 0$ for $i < 0$), proper (its cohomology is bounded and finite-dimensional in each degree)
and homologically smooth (the given model `D` of its diagonal bimodule is perfect over the
enveloping category). Then for every mixed Hochschild model `M`, polynomial cyclic model `C` and
Hodge filtration model `H`, the spectral sequence of the Hodge filtration degenerates at $E_1$: its
differentials vanish on every page $r ≥ 1$. -/
theorem_wanted smooth_proper_nonnegative_dg_hodge_degeneration
    (k : Type u) [Field k] [CharZero k] (A : DGAlgebra k)
    (hdegree : IsNonnegativelyGraded A) (hproper : IsProperAlgebra A)
    (D : EnvelopingModuleModel (diagonal (algebraCategory A)))
    (hsmooth : IsHomologicallySmooth (algebraCategory A) D)
    (M : HochschildMixedModel A) (C : PolynomialCyclicModel M) (H : HodgeFiltrationModel C) :
  IsE1Degenerate H

/-- Convergence of the Hodge-to-de Rham spectral sequence for DG algebras (Kaledin, Theorem 5.5):
let $k$ be a field of characteristic zero and $A$ a DG algebra over $k$ that is nonnegatively
graded, proper and homologically smooth (for the given model `D` of its diagonal bimodule). Then for
every mixed Hochschild model `M`, polynomial cyclic model `C` and Hodge filtration model `H`, and
all $p, q$, there is $r ≥ 1$ such that on every page $r' ≥ r$ the $(p, q)$-term of the spectral
sequence of the Hodge filtration is isomorphic to the graded piece $\mathrm{gr}_{-p} HC_{-(p+q)}$ of
the Hodge filtration on cyclic homology. Only the existence of an isomorphism is asserted, not a
particular comparison map. -/
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
