/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping

/-!
# Cobase closure of monic Rezk weak equivalences

The original monic weak leg maps into every actual CSS target as a scalar
trivial fibration. Actual adjunctions preserve the original opposite pushout
as a pullback; native RLP stability gives the desired original cobase map.
-/

set_option autoImplicit false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open CategoryTheory.MorphismProperty
open scoped SimplicialSpace.Inner
namespace SimplicialSpace

/-- The original intersection is closed under every actual cobase square. -/
theorem monomorphisms_inf_rezkWeakEquivalences_isStableUnderCobaseChange :
    (monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u}).IsStableUnderCobaseChange := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  constructor
  intro A A' B B' f g f' g' sq hf
  have hcof : cofibrations SimplicialSpace.{u} f :=
    (HomotopicalAlgebra.cofibration_iff f).mp ((ReedyModel.cofibration_iff f).mpr hf.1)
  have hcof' : cofibrations SimplicialSpace.{u} f' :=
    (cofibrations SimplicialSpace.{u}).of_isPushout sq hcof
  refine ⟨(ReedyModel.cofibration_iff f').mp
    ((HomotopicalAlgebra.cofibration_iff f').mpr hcof'), ?_⟩
  intro Z hZ
  have hZf : IsFibrant Z := hZ.1
  have hmapF : fibrations SSet.{u} ((innerHomFunctor.{u}.map f.op).app Z) :=
    ReedyModel.inner_precomp_fibration f Z hcof hZf
  have hmapTF : trivialFibrations SSet.{u}
      ((innerHomFunctor.{u}.map f.op).app Z) := ⟨hmapF, hf.2 Z hZ⟩
  have hmapRLP : (cofibrations SSet.{u}).rlp
      ((innerHomFunctor.{u}.map f.op).app Z) := by
    rw [cofibrations_rlp SSet.{u}]
    exact hmapTF
  let _ : ∀ K : SSet.{u}, PreservesColimitsOfShape WalkingCospanᵒᵖ
      (innerTensorBifunctor.{u}.flip.obj K) := fun K => by
    change PreservesColimitsOfShape WalkingCospanᵒᵖ (innerTensor K)
    let _ : (innerTensor K).IsLeftAdjoint :=
      (innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  let _ : PreservesLimitsOfShape WalkingCospan
      (innerHomFunctor.{u}.flip.obj Z) :=
    innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj WalkingCospan Z
  -- Native class convention: sq is IsPushout g f f' g', with f the monic weak leg.
  -- Use its weak-first flip, then explicitly flip the actual mapped-op pullback.
  -- The result has first H(g'), second H(f'), and first cospan H(f).
  have mapped : IsPullback
      ((innerHomFunctor.{u}.map g'.op).app Z)
      ((innerHomFunctor.{u}.map f'.op).app Z)
      ((innerHomFunctor.{u}.map f.op).app Z)
      ((innerHomFunctor.{u}.map g.op).app Z) :=
    (sq.flip.op.map (innerHomFunctor.{u}.flip.obj Z)).flip
  have resultRLP : (cofibrations SSet.{u}).rlp
      ((innerHomFunctor.{u}.map f'.op).app Z) :=
    ((cofibrations SSet.{u}).rlp).of_isPullback mapped hmapRLP
  have resultTF : trivialFibrations SSet.{u}
      ((innerHomFunctor.{u}.map f'.op).app Z) := by
    rw [← cofibrations_rlp SSet.{u}]
    exact resultRLP
  exact resultTF.2

end SimplicialSpace
