/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexFibrationTransitions
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceAddCommGrpChains
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexRelativeTotal
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence

/-!
# Actual relative coefficient transitions

The neutral cokernel-sequence module supplies evaluation/cokernel Isos and
the actual transition of the chosen functor-category cokernel, retaining its
original projection. Its existing vertical cokernel theorem derives the
relative quasi-isomorphism from the two original sides.

For two fibrations over the common base, both absolute simplex transitions
are derived weak by right properness. This gives the relative transition
isomorphisms required by the actual coefficient-groupoid/coinvariant
comparison, without a supplied relative-map or action witness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section


namespace SSet

variable {E E' B : SSet.{u}} {p : E ⟶ B} {q : E' ⟶ B}
  (v : E ⟶ E') [Mono v] (hv : v ≫ q = p) (R : AddCommGrpCat.{u})

private theorem relativeCoefficientArrow_mono :
    Mono (Functor.whiskerRight (simplexPullbackDiagramMap v hv)
      ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R)) := by
  let γ := Functor.whiskerRight (simplexPullbackDiagramMap v hv)
    ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R)
  let : ∀ s, Mono (γ.app s) := fun s => by
    let : Mono ((simplexPullbackDiagramMap v hv).app s) :=
      SSet.simplexPullbackDiagramMap_mono v hv s
    let P : SSetPair.{u} := SSetPair.of ((simplexPullbackDiagramMap v hv).app s)
    exact inferInstanceAs (Mono (SSet.chainComplexMap P.hom R))
  exact NatTrans.mono_of_mono_app γ

/-- The original relative simplex chain arrow is mono, by the same computed pointwise proof. -/
theorem relativeSimplexChainArrow_mono :
    Mono (Functor.whiskerRight (simplexPullbackDiagramMap v hv)
      ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R)) :=
  relativeCoefficientArrow_mono v hv R

/-- Every actual relative simplex transition is a quasi-isomorphism, derived from both
fibrations. -/
theorem relativeSimplexCoefficientTransition_quasiIso [Fibration p] [Fibration q]
    {s t : SimplexIndex B} (a : s ⟶ t) :
    QuasiIso
      ((cokernel (Functor.whiskerRight (simplexPullbackDiagramMap v hv)
        ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R))).map a) := by
  let α := Functor.whiskerRight (simplexPullbackDiagramMap v hv)
    ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R)
  let : Mono α := relativeCoefficientArrow_mono v hv R
  have hp := simplexPullbackTransition_mem_realizationWeakEquivalences p a
  have hq := simplexPullbackTransition_mem_realizationWeakEquivalences q a
  exact HomologicalComplex.cokernelDiagramTransition_quasiIso α a
    (hp.quasiIso_chainComplexMap_addCommGrp R) (hq.quasiIso_chainComplexMap_addCommGrp R)

/-- The actual degree-n relative homology coefficient functor inverts EVERY original simplex
arrow. -/
theorem relativeSimplexHomologyCoefficientTransition_isIso [Fibration p] [Fibration q]
    (n : ℕ) {s t : SimplexIndex B} (a : s ⟶ t) :
    IsIso
      (((cokernel (Functor.whiskerRight (simplexPullbackDiagramMap v hv)
        ((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R))) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).map a) := by
  have h := relativeSimplexCoefficientTransition_quasiIso v hv R a
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap _ n).mp (h.quasiIsoAt n)

end SSet
