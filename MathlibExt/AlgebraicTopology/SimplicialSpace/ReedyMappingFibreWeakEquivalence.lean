/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyMappingFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.VertexRestriction
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCofibrant
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWProduct
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPullback

/-!
# Mapping-fibre weak equivalences for Reedy-fibrant simplicial spaces

Weak equivalences in degrees zero and one induce weak equivalences on the
canonical mapping fibres. The proof uses the endpoint fibrations and the
ordinary cospan comparison in the right-proper simplicial-set model.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SSet.modelCategoryQuillen.modelCategory
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory
namespace SimplicialSpace

private theorem reedyZeroKan (W : SimplicialSpace.{u}) (hW : IsFibrant W) :
    SSet.KanComplex (W.diagram _⦋0⦌) := by
  let X := ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[0] : SSet.{u}))
  have hK := ReedyModel.innerHom_kanComplex X W (ReedyModel.isCofibrant X) hW
  change SSet.KanComplex ((discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) at hK
  let _ : IsFibrant ((discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) := hK
  exact isFibrant_of_fibration (discreteYonedaIso W 0).inv

private theorem segalPairKan {A : SSet.{u}} (hA : SSet.KanComplex A) :
    SSet.KanComplex (A ⨯ A) := by
  let _ : IsFibrant A := hA
  have hPull : IsPullback (prod.snd : A ⨯ A ⟶ A)
      (prod.fst : A ⨯ A ⟶ A) (terminal.from A) (terminal.from A) :=
    (IsPullback.of_isLimit_binaryFan_of_isTerminal (limit.isLimit (pair A A))
      terminalIsTerminal).flip
  let _ : Fibration (prod.fst : A ⨯ A ⟶ A) :=
    (fibration_iff _).mpr ((fibrations SSet.{u}).of_isPullback hPull
      ((fibration_iff _).mp (inferInstanceAs (Fibration (terminal.from A)))))
  exact isFibrant_of_fibration (prod.fst : A ⨯ A ⟶ A)

private theorem weakLimitMapOfCospan
    (F G : WalkingCospan ⥤ SSet.{u}) (η : F ⟶ G)
    [Fibration (F.map WalkingCospan.Hom.inl)]
    [Fibration (G.map WalkingCospan.Hom.inl)]
    (hη : ∀ j, WeakEquivalence (η.app j)) :
    SSet.realizationWeakEquivalences (lim.map η) := by
  exact (weakEquivalence_iff _).mp (weakEquivalence_limitMap_of_rightProper_inl η hη)

/-- Weakness in original degrees zero and one of Reedy-fibrant spaces gives every original
mapping-fibre weak map. -/
theorem ReedyModel.mappingFibresWeak_of_zero_one_weak
    {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : IsFibrant W) (hV : IsFibrant V)
    (h0 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋0⦌)))
    (h1 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋1⦌))) :
    ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl) := by
  intro x y
  let _ : SSet.KanComplex (W.diagram _⦋0⦌) := reedyZeroKan W hW
  let _ : SSet.KanComplex (V.diagram _⦋0⦌) := reedyZeroKan V hV
  let _ : SSet.KanComplex (W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌) := segalPairKan (reedyZeroKan W hW)
  let _ : SSet.KanComplex (V.diagram _⦋0⦌ ⨯ V.diagram _⦋0⦌) := segalPairKan (reedyZeroKan V hV)
  have hb : SSet.realizationWeakEquivalences
      (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))) :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
      (((SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr h0).prodMap
        ((SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr h0))
  let F := cospan (mappingEndpoint W) (mappingPointPair W x y)
  let G := cospan (mappingEndpoint V)
    (mappingPointPair V (mappingVertexMap f x) (mappingVertexMap f y))
  let η : F ⟶ G := cospanHomMk
    (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))
    (f.hom.app (op ⦋1⦌)) (𝟙 (Δ[0] : SSet.{u}))
    (mappingEndpoint_naturality f)
    (by
      change mappingPointPair W x y ≫
        prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)) =
        𝟙 (Δ[0] : SSet.{u}) ≫ mappingPointPair V (mappingVertexMap f x) (mappingVertexMap f y)
      rw [Category.id_comp]
      exact mappingPointPair_naturality f x y)
  let _ : Fibration (F.map WalkingCospan.Hom.inl) := by
    change Fibration (mappingEndpoint W)
    exact ReedyModel.mappingEndpoint_fibration W hW
  let _ : Fibration (G.map WalkingCospan.Hom.inl) := by
    change Fibration (mappingEndpoint V)
    exact ReedyModel.mappingEndpoint_fibration V hV
  have hη : ∀ j, WeakEquivalence (η.app j) := by
    intro j
    cases j with
    | none => change WeakEquivalence (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))); exact (HomotopicalAlgebra.weakEquivalence_iff _).mpr hb
    | some j =>
      cases j with
      | left => change WeakEquivalence (f.hom.app (op ⦋1⦌)); exact (HomotopicalAlgebra.weakEquivalence_iff _).mpr h1
      | right => change WeakEquivalence (𝟙 (Δ[0] : SSet.{u})); infer_instance
  have he : lim.map η = mappingFibre.map f (x := x) (y := y) rfl rfl := by
    apply pullback.hom_ext
    · have h := limMap_π η WalkingCospan.left
      change lim.map η ≫ mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f y) =
        mappingFibre.fst W x y ≫ f.hom.app (op ⦋1⦌) at h
      exact h.trans (mappingFibre.map_fst f rfl rfl).symm
    · have h := limMap_π η WalkingCospan.right
      change lim.map η ≫ mappingFibre.snd V (mappingVertexMap f x) (mappingVertexMap f y) =
        mappingFibre.snd W x y ≫ 𝟙 (Δ[0] : SSet.{u}) at h
      rw [Category.comp_id] at h
      exact h.trans (mappingFibre.map_snd f rfl rfl).symm
  rw [← he]
  exact weakLimitMapOfCospan F G η hη

end SimplicialSpace
