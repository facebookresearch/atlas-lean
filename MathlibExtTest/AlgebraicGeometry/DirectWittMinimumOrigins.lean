/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DirectWittQuotientTransport
import MathlibExt.AlgebraicGeometry.WittQuotientActionModels

/-!
# Direct bounded-stage and left-action source probes

The zeroth bound forces the original standard W(R) lattice on every
perfect residue-algebra test. The actual bounded-stage, ind-colimit,
quotient and positive-action maps are audited independently of the
remaining shared Wanted constructors.
-/

set_option autoImplicit false

open MathlibExt.AlgebraicGeometry.RelativeWittLoopTests
open MathlibExt.AlgebraicGeometry.RelativeWittUnramifiedNormalization
open MathlibExt.AlgebraicGeometry.DirectWittBoundedStages
open MathlibExt.LinearAlgebra

private theorem zero_bound_is_standard (p : ℕ) [Fact p.Prime]
    (k : Type) [CommRing k] (n : ℕ) (M : UnramifiedModel p k n)
    (R : PerfectAlgebra p k) (L : (boundedFunctor p k n M 0).obj R) :
    L.val.down.module = LocalizedLattices.standard
      (WittVector p R.obj) (p : WittVector p R.obj) n :=
  LocalizedLattices.boundedZero_eq _ _ _ L.val.down L.property

#print axioms zero_bound_is_standard
#print axioms functorIso
#print axioms boundedSubfunctor
#print axioms boundedIso_transition
#print axioms stagePoints_transition
#print axioms indComparison_normalized
#print axioms MathlibExt.AlgebraicGeometry.DirectWittQuotientTransport.comparison_normalized
#print axioms MathlibExt.AlgebraicGeometry.WittQuotientActionModels.groupInclusion
#print axioms MathlibExt.AlgebraicGeometry.WittQuotientActionModels.positiveAction
#print axioms MathlibExt.AlgebraicGeometry.WittQuotientActionModels.positiveAction_unit
#print axioms MathlibExt.AlgebraicGeometry.WittQuotientActionModels.positiveAction_associative
