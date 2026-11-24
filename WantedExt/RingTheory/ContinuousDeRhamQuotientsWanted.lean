/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.RingTheory.ContinuousDeRhamQuotients

/-!
# Square zero of the actual continuous quotient coefficient differential

The differential in every degree is the completed public Stacks
`extendedConnection`, with the uniquely proved quotient differential.
This request fills its remaining integrability implication.

Source: Stacks Tags 07HY and 07I0; completed Atlas PR2245
`76de3f2665f9c44b06932f9861ee9aae65e04395`, AxiomMath/Stacks
`c496df0d9beea9deaeabcea8492605f9a0a2313b`, Apache 2.0.
-/

@[expose] public noncomputable section

namespace WantedExt.RingTheory.ContinuousDeRhamQuotients

open MathlibExt.RingTheory.ContinuousDeRhamQuotients

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
  (Q : ContinuousQuotient A B) (M : Type u) [AddCommGroup M] [Module B M]
  (nabla : Q.NativeConnection M)

public theorem_wanted extendedConnectionSquareZero (h : Q.IsIntegrable M nabla) :
  Q.ExtensionSquareZero M nabla

end WantedExt.RingTheory.ContinuousDeRhamQuotients
