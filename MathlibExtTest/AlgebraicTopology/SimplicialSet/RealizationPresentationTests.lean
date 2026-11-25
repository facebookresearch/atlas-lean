/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation

/-!
# Neutral realization-presentation tests

These owners pin the universe-polymorphic quotient map without importing a
generated-topology or finite-realization specialization.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Topology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace RealizationPresentationTests

example (T : SSet.{u}) (x : SSet.toTop.obj T) :
    ∃ (n : ℕ) (s : T _⦋n⦌) (_ : s ∈ T.nonDegenerate n)
      (y : SSet.toTop.obj (Δ[n] : SSet.{u})),
      SSet.toTop.map (SSet.yonedaEquiv.symm s) y = x :=
  SSet.exists_nonDegenerate_toTop_presentation T x

example (T : SSet.{u}) :
    Topology.IsQuotientMap (SSet.sigmaToTop (T := T)) :=
  SSet.isQuotientMap_sigmaToTop T

example (T : SSet.{u}) :
    Function.Surjective (SSet.sigmaToTop (T := T)) :=
  (SSet.isQuotientMap_sigmaToTop T).surjective

example (T : SSet.{u}) :
    Topology.IsCoinducing (SSet.sigmaToTop (T := T)) :=
  (SSet.isQuotientMap_sigmaToTop T).isCoinducing

example (T : SSet.{u}) :
    Continuous (SSet.sigmaToTop (T := T)) :=
  (SSet.isQuotientMap_sigmaToTop T).continuous

example (T : SSet.{u}) {U : Set (SSet.toTop.obj T)} :
    IsOpen ((SSet.sigmaToTop (T := T)) ⁻¹' U) ↔ IsOpen U :=
  (SSet.isQuotientMap_sigmaToTop T).isCoinducing.isOpen_preimage

example (T : SSet.{1}) :
    Topology.IsQuotientMap (SSet.sigmaToTop (T := T)) :=
  SSet.isQuotientMap_sigmaToTop T

example (T : SSet.{0}) :
    Topology.IsQuotientMap (SSet.sigmaToTop (T := T)) :=
  SSet.isQuotientMap_sigmaToTop T

#guard_msgs (error, substring := true) in
#check SSet.continuous_sigmaToTop

#guard_msgs (error, substring := true) in
#synth DeltaGeneratedSpace (SSet.toTop.obj SSet.S1)

#guard_msgs (error, substring := true) in
#synth CompactSpace (SSet.toTop.obj SSet.S1)

#guard_msgs (error, substring := true) in
#synth T1Space (SSet.toTop.obj SSet.S1)

#print axioms SSet.sigmaToTop
#print axioms SSet.exists_nonDegenerate_toTop_presentation
#print axioms SSet.surjective_sigmaToTop
#print axioms SSet.isQuotientMap_sigmaToTop

end RealizationPresentationTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
