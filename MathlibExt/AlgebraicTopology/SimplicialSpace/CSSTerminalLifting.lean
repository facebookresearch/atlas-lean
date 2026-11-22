/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration

/-!
# Strict terminal lifting into complete Segal spaces

The strict lifting implication in Rezk's Theorem 7.2 follows from raw inner
mapping fibrancy, the genuine all-CSS weak test, and scalar vertex lifting.
The ordinary inner-Hom bijection retains both original diagonal equations.
-/

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open CategoryTheory.MorphismProperty
open scoped SimplicialSpace.Inner Simplicial

namespace SimplicialSpace

/-- An actual complete Segal space lifts strictly against every original
monomorphism that is a Rezk weak equivalence in the same value universe. -/
theorem completeSegalSpaces_terminal_rlp (Z : SimplicialSpace.{u})
    (hZ : completeSegalSpaces Z) :
    (monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u}).rlp
      (terminal.from Z) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro A B f hf
  have hfMono : Mono f := hf.1
  have hfCof : cofibrations SimplicialSpace.{u} f :=
    (HomotopicalAlgebra.cofibration_iff f).1
      ((ReedyModel.cofibration_iff f).2 hfMono)
  let q := (innerHomFunctor.{u}.map f.op).app Z
  have hTF : trivialFibrations SSet.{u} q :=
    ⟨ReedyModel.inner_precomp_fibration f Z hfCof hZ.1, hf.2 Z hZ⟩
  have hRLP : SSet.modelCategoryQuillen.I.{u}.rlp q := by
    rw [← SSet.rlp_monomorphisms]
    change (cofibrations SSet.{u}).rlp q
    rw [cofibrations_rlp SSet.{u}]
    exact hTF
  refine ⟨?_⟩
  intro a b sq
  obtain ⟨x, hx⟩ := SSet.exists_vertex_lift_of_rlp_I hRLP (innerHomEquiv A Z a)
  let l : B ⟶ Z := (innerHomEquiv B Z).symm x
  have hl : f ≫ l = a := by
    apply (innerHomEquiv A Z).injective
    rw [← ReedyModel.inner_precomp_app_zero f Z l]
    change q.app (op ⦋0⦌) ((innerHomEquiv B Z) ((innerHomEquiv B Z).symm x)) =
      innerHomEquiv A Z a
    exact (congrArg (fun y => q.app (op ⦋0⦌) y)
      ((innerHomEquiv B Z).apply_symm_apply x)).trans hx
  exact CommSq.HasLift.mk'
    { l := l
      fac_left := hl
      fac_right := terminalIsTerminal.hom_ext _ _ }

end SimplicialSpace
