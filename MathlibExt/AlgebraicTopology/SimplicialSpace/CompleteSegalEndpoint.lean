/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.BoxProduct
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkVerticalFibration
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMonomorphisms

/-!
# Complete Segal endpoint pullback-Homs

For a Rezk fibration between complete Segal spaces, the source-left
pullback-Hom along the source vertex of the full coherent walking-isomorphism
nerve is a trivial Kan fibration. The proof uses the original pullback point
and its two projections: the first is a base change of the endpoint
restriction on the target, and the composite with that projection is the
endpoint restriction on the source.

The concrete row-lifting consequence follows from the existing two-variable
box adjunction and retains the original right row pullback-Hom.

Source: Joyal–Tierney, *Quasi-categories vs Segal spaces*, Lemma 4.2 and the
proof of Lemma 4.3, arXiv math/0607820v2, p. 22.
-/

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace.RezkModel

/-- The full coherent-endpoint source-left pullback-Hom of a Rezk fibration
between complete Segal spaces is a genuine trivial Kan fibration. -/
theorem boxLeftPullbackHom_coherentIsoEndpoint_mem_boundaryRLP
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hX : completeSegalSpaces X) (hY : completeSegalSpaces Y)
    (hf : modelCategory.{u}.categoryWithFibrations.fibrations f) :
    SSet.modelCategoryQuillen.I.rlp
      (boxLeftPullbackHom
        (SSet.yonedaEquiv.symm SSet.coherentIso.x₀) f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let u₀ : (Δ[0] : SSet.{u}) ⟶ SSet.coherentIso :=
    SSet.yonedaEquiv.symm SSet.coherentIso.x₀
  let i := discreteInnerMap u₀
  have hiMono : Mono i := by
    change Mono (ofSimplicialObject.map
      (SSet.Rezk.localizingMap.{u} (.inr PUnit.unit)).hom)
    exact SimplicialSpace.localizingMap_mono (.inr PUnit.unit)
  have hiCof : cofibrations SimplicialSpace.{u} i :=
    (HomotopicalAlgebra.cofibration_iff i).1
      ((ReedyModel.cofibration_iff i).2 hiMono)
  have hXTriv : trivialFibrations SSet.{u}
      ((boxLeftDivisionFunctor.map u₀.op).app X) := by
    refine ⟨ReedyModel.inner_precomp_fibration i X hiCof hX.1, ?_⟩
    exact hX.2 (.inr PUnit.unit)
  have hYTriv : trivialFibrations SSet.{u}
      ((boxLeftDivisionFunctor.map u₀.op).app Y) := by
    refine ⟨ReedyModel.inner_precomp_fibration i Y hiCof hY.1, ?_⟩
    exact hY.2 (.inr PUnit.unit)
  let q := boxLeftPullbackHomSquare u₀ f
  let sq : innerHomFunctor.PullbackObjObj i f :=
    { pt := q.pt
      fst := q.fst
      snd := q.snd
      isPullback := q.isPullback
      π := q.π
      π_fst := q.π_fst
      π_snd := q.π_snd }
  have hqFib : fibrations SSet.{u} q.π :=
    ReedyModel.inner_pullbackHom_fibration i f sq hiCof
      (reedyFibration_of_fibration f hf)
  have hfstTriv : trivialFibrations SSet.{u} q.fst :=
    (trivialFibrations SSet.{u}).of_isPullback q.isPullback.flip hYTriv
  have hqWeak : weakEquivalences SSet.{u} q.π := by
    apply (weakEquivalences SSet.{u}).of_postcomp q.π q.fst hfstTriv.2
    rw [q.π_fst]
    exact hXTriv.2
  rw [← SSet.rlp_monomorphisms]
  change (cofibrations SSet.{u}).rlp q.π
  rw [cofibrations_rlp]
  exact ⟨hqFib, hqWeak⟩

end SimplicialSpace.RezkModel

namespace SimplicialSpace

/-- Triviality of the original source-left coherent-endpoint pullback-Hom
gives coherent-endpoint lifting for every original right row pullback-Hom
along a monomorphism. -/
theorem rowPullbackHom_hasLiftingProperty_coherentIsoEndpoint_of_boundaryRLP
    {S T : SSet.{u}} (v : S ⟶ T) [Mono v]
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.I.rlp
      (boxLeftPullbackHom
        (SSet.yonedaEquiv.symm SSet.coherentIso.x₀) f)) :
    HasLiftingProperty (SSet.yonedaEquiv.symm SSet.coherentIso.x₀)
      (rowPullbackHom v f) := by
  apply (box_hasLiftingProperty_iff
    (SSet.yonedaEquiv.symm SSet.coherentIso.x₀) v f).2
  have hmono : (monomorphisms SSet.{u}).rlp
      (boxLeftPullbackHom
        (SSet.yonedaEquiv.symm SSet.coherentIso.x₀) f) := by
    rw [SSet.rlp_monomorphisms]
    exact hf
  exact hmono v inferInstance

end SimplicialSpace
