/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyMappingFibre
import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Intrinsic homotopy category of a Segal space

Composition is constructed from the original degree-two and degree-three Segal
maps on the actual prescribed-vertex mapping fibres. The equivalence-arrow
subcomplex consists of the genuine moving components and supplies the object
coequalizer.

Source: Rezk (2001), Sections 5.1–5.8; Horel, Definitions 2.7–2.8.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty CategoryTheory.SimplicialObject
open scoped Simplicial SSet.modelCategoryQuillen SimplicialSpace.Inner

namespace SimplicialSpace

private def productSimplex {A B : SSet.{u}} {n : ℕ}
    (a : A _⦋n⦌) (b : B _⦋n⦌) : (A ⨯ B) _⦋n⦌ :=
  SSet.yonedaEquiv (prod.lift (SSet.yonedaEquiv.symm a) (SSet.yonedaEquiv.symm b))

private theorem productSimplex_fst {A B : SSet.{u}} {n : ℕ}
    (a : A _⦋n⦌) (b : B _⦋n⦌) :
    (prod.fst : A ⨯ B ⟶ A).app (op ⦋n⦌) (productSimplex a b) = a := by
  change SSet.yonedaEquiv
    (prod.lift (SSet.yonedaEquiv.symm a) (SSet.yonedaEquiv.symm b) ≫ prod.fst) = a
  rw [prod.lift_fst, Equiv.apply_symm_apply]

private theorem productSimplex_snd {A B : SSet.{u}} {n : ℕ}
    (a : A _⦋n⦌) (b : B _⦋n⦌) :
    (prod.snd : A ⨯ B ⟶ B).app (op ⦋n⦌) (productSimplex a b) = b := by
  change SSet.yonedaEquiv
    (prod.lift (SSet.yonedaEquiv.symm a) (SSet.yonedaEquiv.symm b) ≫ prod.snd) = b
  rw [prod.lift_snd, Equiv.apply_symm_apply]

private theorem productSimplex_ext {A B : SSet.{u}} {n : ℕ}
    {s t : (A ⨯ B) _⦋n⦌}
    (hf : (prod.fst : A ⨯ B ⟶ A).app (op ⦋n⦌) s =
      (prod.fst : A ⨯ B ⟶ A).app (op ⦋n⦌) t)
    (hs : (prod.snd : A ⨯ B ⟶ B).app (op ⦋n⦌) s =
      (prod.snd : A ⨯ B ⟶ B).app (op ⦋n⦌) t) : s = t := by
  apply SSet.yonedaEquiv.symm.injective
  apply prod.hom_ext
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hf]
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hs]

private theorem productSimplex_eta {A B : SSet.{u}} {n : ℕ} (s : (A ⨯ B) _⦋n⦌) :
    productSimplex ((prod.fst : A ⨯ B ⟶ A).app (op ⦋n⦌) s)
      ((prod.snd : A ⨯ B ⟶ B).app (op ⦋n⦌) s) = s := by
  apply productSimplex_ext
  · exact productSimplex_fst _ _
  · exact productSimplex_snd _ _

private theorem productSimplex_face_fst {A B : SSet.{u}}
    (a : A _⦋1⦌) (b : B _⦋1⦌) (i : Fin 2) :
    (prod.fst : A ⨯ B ⟶ A).app (op ⦋0⦌) ((A ⨯ B).δ i (productSimplex a b)) =
      A.δ i a := by
  have h := NatTrans.naturality_apply (prod.fst : A ⨯ B ⟶ A)
    (SimplexCategory.δ i).op (productSimplex a b)
  change (prod.fst : A ⨯ B ⟶ A).app (op ⦋0⦌) ((A ⨯ B).δ i (productSimplex a b)) =
    A.δ i ((prod.fst : A ⨯ B ⟶ A).app (op ⦋1⦌) (productSimplex a b)) at h
  rw [productSimplex_fst] at h
  exact h

private theorem productSimplex_face_snd {A B : SSet.{u}}
    (a : A _⦋1⦌) (b : B _⦋1⦌) (i : Fin 2) :
    (prod.snd : A ⨯ B ⟶ B).app (op ⦋0⦌) ((A ⨯ B).δ i (productSimplex a b)) =
      B.δ i b := by
  have h := NatTrans.naturality_apply (prod.snd : A ⨯ B ⟶ B)
    (SimplexCategory.δ i).op (productSimplex a b)
  change (prod.snd : A ⨯ B ⟶ B).app (op ⦋0⦌) ((A ⨯ B).δ i (productSimplex a b)) =
    B.δ i ((prod.snd : A ⨯ B ⟶ B).app (op ⦋1⦌) (productSimplex a b)) at h
  rw [productSimplex_snd] at h
  exact h

private def productEdge {A B : SSet.{u}} {a a' : A _⦋0⦌} {b b' : B _⦋0⦌}
    (ea : A.Edge a a') (eb : B.Edge b b') :
    (A ⨯ B).Edge (productSimplex a b) (productSimplex a' b') :=
  SSet.Edge.mk (productSimplex ea.edge eb.edge)
    (by
      apply productSimplex_ext
      · rw [productSimplex_face_fst, productSimplex_fst, SSet.Edge.src_eq]
      · rw [productSimplex_face_snd, productSimplex_snd, SSet.Edge.src_eq])
    (by
      apply productSimplex_ext
      · rw [productSimplex_face_fst, productSimplex_fst, SSet.Edge.tgt_eq]
      · rw [productSimplex_face_snd, productSimplex_snd, SSet.Edge.tgt_eq])

private def productComponentPair {A B : SSet.{u}}
    (a : SSet.π₀ A) (b : SSet.π₀ B) : SSet.π₀ (A ⨯ B) :=
  SSet.π₀.lift
    (fun x => SSet.π₀.lift (fun y => SSet.π₀.mk (productSimplex x y))
      (fun {y₀ y₁} e => SSet.π₀.sound (productEdge (SSet.Edge.id x) e)))
    (fun {x₀ x₁} e => by
      funext c
      induction c using SSet.π₀.rec with
      | mk y =>
        simp only [SSet.π₀.lift_mk]
        exact SSet.π₀.sound (productEdge e (SSet.Edge.id y))) a b

private def productComponentEquiv (A B : SSet.{u}) :
    SSet.π₀ (A ⨯ B) ≃ SSet.π₀ A × SSet.π₀ B where
  toFun c := ⟨SSet.mapπ₀ prod.fst c, SSet.mapπ₀ prod.snd c⟩
  invFun c := productComponentPair c.1 c.2
  left_inv c := by
    induction c using SSet.π₀.rec with
    | mk s =>
      simp only [SSet.mapπ₀_mk, productComponentPair, SSet.π₀.lift_mk, productSimplex_eta]
  right_inv c := by
    rcases c with ⟨a, b⟩
    induction a using SSet.π₀.rec with
    | mk x =>
      induction b using SSet.π₀.rec with
      | mk y =>
        simp only [productComponentPair, SSet.π₀.lift_mk, SSet.mapπ₀_mk,
          productSimplex_fst, productSimplex_snd]

namespace SegalHomotopy

/-- The actual chosen pullback of two original composable edges. -/
abbrev twoEdgePullback (W : SimplicialSpace.{u}) : SSet.{u} :=
  pullback (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2))

/-- The native strict Segal target comparison to the original two-edge pullback. -/
def twoEdgeTargetIso (W : SimplicialSpace.{u}) :
    limit (segalMappingCospan W 2 (by decide)) ≅ twoEdgePullback W :=
  lim.mapIso (segalTwoMappingCospanIso W)

private theorem twoEdgeTargetIso_fst (W : SimplicialSpace.{u}) :
    (twoEdgeTargetIso W).hom ≫ pullback.fst _ _ =
      limit.π (segalMappingCospan W 2 (by decide)) WalkingCospan.left ≫
        (spinePrefixFirstMappingIso W 2 (by decide)).hom := by
  change lim.map (segalTwoMappingCospanIso W).hom ≫
    limit.π _ WalkingCospan.left = _
  exact limMap_π _ _

private theorem twoEdgeTargetIso_snd (W : SimplicialSpace.{u}) :
    (twoEdgeTargetIso W).hom ≫ pullback.snd _ _ =
      limit.π (segalMappingCospan W 2 (by decide)) WalkingCospan.right ≫
        (spineEdgeMappingIso W 2 (1 : Fin 2)).hom := by
  change lim.map (segalTwoMappingCospanIso W).hom ≫
    limit.π _ WalkingCospan.right = _
  exact limMap_π _ _

@[reassoc]
private theorem prefixIso_fst (W : SimplicialSpace.{u}) :
    (spinePrefixMappingIso W 2 1 (by decide) (by decide)).hom ≫
      limit.π (spinePrefixMappingCospan W 2 1 (by decide) (by decide)) WalkingCospan.left =
      (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft 2 1 (by decide)).op :=
  (spinePrefixMapping_isPullback W 2 1 (by decide) (by decide)).isoPullback_hom_fst

@[reassoc]
private theorem prefixIso_snd (W : SimplicialSpace.{u}) :
    (spinePrefixMappingIso W 2 1 (by decide) (by decide)).hom ≫
      limit.π (spinePrefixMappingCospan W 2 1 (by decide) (by decide)) WalkingCospan.right =
      (discreteSourceMapping W).map (SSet.Rezk.spinePrefixRight 2 1 (by decide)).op :=
  (spinePrefixMapping_isPullback W 2 1 (by decide) (by decide)).isoPullback_hom_snd

private theorem firstEdgeChain :
    SSet.Rezk.spinePrefixPreviousEdge.{u} 2 1 (by decide) (by decide) ≫
        SSet.Rezk.spinePrefixLeft 2 1 (by decide) ≫
          (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 2 (by decide))).hom =
      SSet.Rezk.spineEdgeInclusion 2 (0 : Fin 2) := by
  ext m a
  rfl

private theorem secondEdgeChain :
    SSet.Subcomplex.toRange (SSet.Rezk.segalSpineEdgeMap.{u} 2 (1 : Fin 2)) ≫
        SSet.Rezk.spinePrefixRight 2 1 (by decide) ≫
          (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 2 (by decide))).hom =
      SSet.Rezk.spineEdgeInclusion 2 (1 : Fin 2) := by
  ext m a
  rfl

/-- The original degree-two Segal comparison, in increasing consecutive-edge order. -/
def twoEdgeComparison (W : SimplicialSpace.{u}) : W.diagram _⦋2⦌ ⟶ twoEdgePullback W :=
  segalStrictComparison W 2 (by decide) ≫ (twoEdgeTargetIso W).hom

/-- Its first projection is the original 01 face. -/
@[reassoc (attr := simp)]
theorem twoEdgeComparison_fst (W : SimplicialSpace.{u}) :
    twoEdgeComparison W ≫ pullback.fst _ _ = W.diagram.δ (2 : Fin 3) := by
  change twoEdgeComparison W ≫ pullback.fst _ _ = W.diagram.map (SimplexCategory.δ (2 : Fin 3)).op
  unfold twoEdgeComparison
  rw [Category.assoc, twoEdgeTargetIso_fst, ← Category.assoc]
  rw [spinePrefixFirstMappingIso_hom]
  unfold segalStrictComparison segalSpineMappingIso spinePrefixLastEdgeProjection
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [prefixIso_fst_assoc]
  have hm :
      (discreteSourceMapping W).map
          (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 2 (by decide))).op.hom ≫
        (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft 2 1 (by decide)).op ≫
          (discreteSourceMapping W).map
            (SSet.Rezk.spinePrefixPreviousEdge 2 1 (by decide) (by decide)).op =
        (discreteSourceMapping W).map (SSet.Rezk.spineEdgeInclusion 2 (0 : Fin 2)).op := by
    change (discreteSourceMapping W).map
        (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 2 (by decide))).hom.op ≫
      (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft 2 1 (by decide)).op ≫
        (discreteSourceMapping W).map
          (SSet.Rezk.spinePrefixPreviousEdge 2 1 (by decide) (by decide)).op = _
    rw [← (discreteSourceMapping W).map_comp, ← (discreteSourceMapping W).map_comp,
      ← op_comp, ← op_comp, Category.assoc, firstEdgeChain]
  have hc := congrArg (fun t => rawSegalComparison W 2 ≫ t ≫ (discreteYonedaIso W 1).hom) hm
  simp only [Category.assoc] at hc
  have hi : SimplexCategory.mkOfSucc (0 : Fin 2) = SimplexCategory.δ (2 : Fin 3) := by decide
  exact hc.trans (by simpa only [hi] using rawSegalComparison_edge W 2 (0 : Fin 2))

/-- Its second projection is the original 12 face. -/
@[reassoc (attr := simp)]
theorem twoEdgeComparison_snd (W : SimplicialSpace.{u}) :
    twoEdgeComparison W ≫ pullback.snd _ _ = W.diagram.δ (0 : Fin 3) := by
  change twoEdgeComparison W ≫ pullback.snd _ _ = W.diagram.map (SimplexCategory.δ (0 : Fin 3)).op
  unfold twoEdgeComparison
  rw [Category.assoc, twoEdgeTargetIso_snd, ← Category.assoc]
  unfold segalStrictComparison segalSpineMappingIso spineEdgeMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [prefixIso_snd_assoc]
  have hm :
      (discreteSourceMapping W).map
          (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 2 (by decide))).op.hom ≫
        (discreteSourceMapping W).map (SSet.Rezk.spinePrefixRight 2 1 (by decide)).op ≫
          (discreteSourceMapping W).map
            (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineEdgeMap 2 (1 : Fin 2))).op =
        (discreteSourceMapping W).map (SSet.Rezk.spineEdgeInclusion 2 (1 : Fin 2)).op := by
    change (discreteSourceMapping W).map
        (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 2 (by decide))).hom.op ≫
      (discreteSourceMapping W).map (SSet.Rezk.spinePrefixRight 2 1 (by decide)).op ≫
        (discreteSourceMapping W).map
          (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineEdgeMap 2 (1 : Fin 2))).op = _
    rw [← (discreteSourceMapping W).map_comp, ← (discreteSourceMapping W).map_comp,
      ← op_comp, ← op_comp, Category.assoc, secondEdgeChain]
  have hc := congrArg (fun t => rawSegalComparison W 2 ≫ t ≫ (discreteYonedaIso W 1).hom) hm
  simp only [Category.assoc] at hc
  have hi : SimplexCategory.mkOfSucc (1 : Fin 2) = SimplexCategory.δ (0 : Fin 3) := by decide
  exact hc.trans (by simpa only [hi] using rawSegalComparison_edge W 2 (1 : Fin 2))

attribute [local instance] ReedyModel.modelCategory

/-- The same original two-edge comparison is a genuine Kan trivial fibration at Segal W. -/
theorem twoEdgeComparison_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (twoEdgeComparison W) := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp
    (segalStrictComparison_trivialFibration W 2 (by decide) hW)
  let := hf
  let := hw
  exact (mem_trivialFibrations_iff _).mpr ⟨by dsimp [twoEdgeComparison]; infer_instance,
    by dsimp [twoEdgeComparison]; infer_instance⟩

/-- The original pair of prescribed-vertex mapping fibres forms a composable edge pair. -/
def twoEdgePair (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⨯ mappingFibre W y z ⟶ twoEdgePullback W :=
  pullback.lift (prod.fst ≫ mappingFibre.fst W x y)
    (prod.snd ≫ mappingFibre.fst W y z) (by
      simp only [Category.assoc, mappingFibre.target_eq, mappingFibre.source_eq]
      have h : (prod.fst : mappingFibre W x y ⨯ mappingFibre W y z ⟶ _) ≫
          mappingFibre.snd W x y = prod.snd ≫ mappingFibre.snd W y z :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ SSet.yonedaEquiv.symm y) h)

/-- The original first mapping-fibre edge is the first pair projection. -/
@[reassoc (attr := simp)]
theorem twoEdgePair_fst (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    twoEdgePair W x y z ≫ pullback.fst _ _ = prod.fst ≫ mappingFibre.fst W x y :=
  pullback.lift_fst _ _ _

/-- The original second mapping-fibre edge is the second pair projection. -/
@[reassoc (attr := simp)]
theorem twoEdgePair_snd (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    twoEdgePair W x y z ≫ pullback.snd _ _ = prod.snd ≫ mappingFibre.fst W y z :=
  pullback.lift_snd _ _ _

/-- The chosen prescribed-vertex triangle space over the original two-edge comparison. -/
abbrev triangleSpace (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (twoEdgeComparison W) (twoEdgePair W x y z)

/-- The original outer-two projection of the prescribed-vertex triangle space. -/
abbrev triangleProjection (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleSpace W x y z ⟶ W.diagram _⦋2⦌ :=
  pullback.fst _ _

/-- The original comparison from triangles to their two prescribed mapping-fibre edges. -/
abbrev triangleComparison (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleSpace W x y z ⟶ mappingFibre W x y ⨯ mappingFibre W y z :=
  pullback.snd _ _

/-- The first original face of a triangle is its first prescribed mapping-fibre edge. -/
@[reassoc (attr := simp)]
theorem triangleProjection_first (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleProjection W x y z ≫ W.diagram.δ (2 : Fin 3) =
      triangleComparison W x y z ≫ prod.fst ≫ mappingFibre.fst W x y := by
  have h := congrArg (fun t => t ≫ pullback.fst (W.diagram.δ (0 : Fin 2))
      (W.diagram.δ (1 : Fin 2))) (pullback.condition
        (f := twoEdgeComparison W) (g := twoEdgePair W x y z))
  simpa only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst] using h

/-- The last original face of a triangle is its second prescribed mapping-fibre edge. -/
@[reassoc (attr := simp)]
theorem triangleProjection_last (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleProjection W x y z ≫ W.diagram.δ (0 : Fin 3) =
      triangleComparison W x y z ≫ prod.snd ≫ mappingFibre.fst W y z := by
  have h := congrArg (fun t => t ≫ pullback.snd (W.diagram.δ (0 : Fin 2))
      (W.diagram.δ (1 : Fin 2))) (pullback.condition
        (f := twoEdgeComparison W) (g := twoEdgePair W x y z))
  simpa only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd] using h

private theorem middle_source_face (W : SimplicialSpace.{u}) :
    W.diagram.δ (1 : Fin 3) ≫ W.diagram.δ (1 : Fin 2) =
      W.diagram.δ (2 : Fin 3) ≫ W.diagram.δ (1 : Fin 2) := by
  change W.diagram.map (SimplexCategory.δ (1 : Fin 3)).op ≫
    W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op =
      W.diagram.map (SimplexCategory.δ (2 : Fin 3)).op ≫
        W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op
  have h : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3) =
      SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3) := by decide
  simpa only [Functor.map_comp, op_comp] using
    congrArg (fun t => W.diagram.map t.op) h

private theorem middle_target_face (W : SimplicialSpace.{u}) :
    W.diagram.δ (1 : Fin 3) ≫ W.diagram.δ (0 : Fin 2) =
      W.diagram.δ (0 : Fin 3) ≫ W.diagram.δ (0 : Fin 2) := by
  change W.diagram.map (SimplexCategory.δ (1 : Fin 3)).op ≫
    W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op =
      W.diagram.map (SimplexCategory.δ (0 : Fin 3)).op ≫
        W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op
  have h : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3) =
      SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) := by decide
  simpa only [Functor.map_comp, op_comp] using
    congrArg (fun t => W.diagram.map t.op) h

/-- The original middle face of a prescribed triangle lies in the original x-to-z fibre. -/
def triangleMiddle (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleSpace W x y z ⟶ mappingFibre W x z :=
  pullback.lift (triangleProjection W x y z ≫ W.diagram.δ (1 : Fin 3))
    (triangleComparison W x y z ≫ prod.fst ≫ mappingFibre.snd W x y) (by
      apply prod.hom_ext
      · simp only [Category.assoc, mappingEndpoint_fst, mappingPointPair_fst]
        rw [middle_source_face, triangleProjection_first_assoc]
        simp only [mappingFibre.source_eq]
      · simp only [Category.assoc, mappingEndpoint_snd, mappingPointPair_snd]
        rw [middle_target_face, triangleProjection_last_assoc]
        simp only [mappingFibre.target_eq]
        have h :
            (triangleComparison W x y z ≫ prod.snd ≫ mappingFibre.snd W y z) =
              triangleComparison W x y z ≫ prod.fst ≫ mappingFibre.snd W x y :=
          SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
        simpa only [Category.assoc] using
          congrArg (fun t => t ≫ SSet.yonedaEquiv.symm z) h)

/-- The edge projection of the triangle middle is literally its original d₁ face. -/
@[reassoc (attr := simp)]
theorem triangleMiddle_fst (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleMiddle W x y z ≫ mappingFibre.fst W x z =
      triangleProjection W x y z ≫ W.diagram.δ (1 : Fin 3) :=
  pullback.lift_fst _ _ _

/-- The point projection of the middle uses the original first fibre point. -/
@[reassoc (attr := simp)]
theorem triangleMiddle_snd (W : SimplicialSpace.{u}) (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    triangleMiddle W x y z ≫ mappingFibre.snd W x z =
      triangleComparison W x y z ≫ prod.fst ≫ mappingFibre.snd W x y :=
  pullback.lift_snd _ _ _

/-- The original fixed-vertex triangle comparison is a Kan trivial fibration. -/
theorem triangleComparison_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    trivialFibrations SSet.{u} (triangleComparison W x y z) := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp
    (twoEdgeComparison_trivialFibration W hW)
  let := hf
  let := hw
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

/-- The two original triangle-edge components determine its component uniquely. -/
def triangleComponentEquiv (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.π₀ (triangleSpace W x y z) ≃
      SSet.π₀ (mappingFibre W x y) × SSet.π₀ (mappingFibre W y z) := by
  have hw := (triangleComparison_trivialFibration W hW x y z).2
  refine Equiv.ofBijective
    (fun c =>
      (SSet.mapπ₀ prod.fst (SSet.mapπ₀ (triangleComparison W x y z) c),
        SSet.mapπ₀ prod.snd (SSet.mapπ₀ (triangleComparison W x y z) c))) ?_
  change Function.Bijective
    ((productComponentEquiv (mappingFibre W x y) (mappingFibre W y z)).toFun ∘
      SSet.mapπ₀ (triangleComparison W x y z))
  exact (productComponentEquiv _ _).bijective.comp
    (SSet.realizationWeakEquivalences.bijective_mapπ₀ hw)

/-- The component equivalence uses exactly the two original fibre projections. -/
theorem triangleComponentEquiv_apply (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (c : SSet.π₀ (triangleSpace W x y z)) :
    triangleComponentEquiv W hW x y z c =
      (SSet.mapπ₀ (triangleComparison W x y z ≫ prod.fst) c,
        SSet.mapπ₀ (triangleComparison W x y z ≫ prod.snd) c) := by
  simp only [triangleComponentEquiv, Equiv.ofBijective_apply, SSet.mapπ₀_comp_apply]

/-- Composition is induced by the original middle face and the proved component bijection. -/
def compose (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {x y z : (W.diagram _⦋0⦌) _⦋0⦌}
    (f : SSet.π₀ (mappingFibre W x y)) (g : SSet.π₀ (mappingFibre W y z)) :
    SSet.π₀ (mappingFibre W x z) :=
  SSet.mapπ₀ (triangleMiddle W x y z)
    ((triangleComponentEquiv W hW x y z).symm (f, g))

/-- Every original triangle computes the same composition on components. -/
theorem compose_of_triangle (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (c : SSet.π₀ (triangleSpace W x y z)) :
    compose W hW (SSet.mapπ₀ (triangleComparison W x y z ≫ prod.fst) c)
        (SSet.mapπ₀ (triangleComparison W x y z ≫ prod.snd) c) =
      SSet.mapπ₀ (triangleMiddle W x y z) c := by
  unfold compose
  rw [← triangleComponentEquiv_apply W hW x y z c, Equiv.symm_apply_apply]

private def prefixPairCospanIso (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    spinePrefixMappingCospan W n 1 hn (by decide) ≅
      cospan (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2)) :=
  cospanIsoMk (spineVertexMappingIso W n 1 (Nat.le_of_succ_le hn))
    (spinePrefixFirstMappingIso W n (Nat.le_of_succ_le hn))
    (spineEdgeMappingIso W n ⟨1, hn⟩)
    (by
      have h := spinePrefixMappingCospan_left W n 1 hn (by decide)
      rw [← spinePrefixFirstMappingIso_hom] at h
      exact h)
    (spinePrefixMappingCospan_right W n 1 hn)

private def prefixPairIso (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    (discreteSourceMapping W).obj (op (SSet.Rezk.spinePrefixSubcomplex n 2 hn : SSet.{u})) ≅
      twoEdgePullback W :=
  spinePrefixMappingIso W n 1 hn (by decide) ≪≫ lim.mapIso (prefixPairCospanIso W n hn)

@[reassoc]
private theorem prefixPairIso_fst (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    (prefixPairIso W n hn).hom ≫ pullback.fst _ _ =
      (discreteSourceMapping W).map
          (SSet.Rezk.spinePrefixPreviousEdge n 1 (Nat.le_of_succ_le hn) (by decide) ≫
            SSet.Rezk.spinePrefixLeft n 1 hn).op ≫ (discreteYonedaIso W 1).hom := by
  have hlim :
      lim.map (prefixPairCospanIso W n hn).hom ≫
        limit.π _ WalkingCospan.left =
      limit.π (spinePrefixMappingCospan W n 1 hn (by decide)) WalkingCospan.left ≫
        (spinePrefixFirstMappingIso W n (Nat.le_of_succ_le hn)).hom :=
    limMap_π _ _
  have hp : (spinePrefixMappingIso W n 1 hn (by decide)).hom ≫
      limit.π (spinePrefixMappingCospan W n 1 hn (by decide)) WalkingCospan.left =
      (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft n 1 hn).op :=
    (spinePrefixMapping_isPullback W n 1 hn (by decide)).isoPullback_hom_fst
  change (spinePrefixMappingIso W n 1 hn (by decide)).hom ≫
      lim.map (prefixPairCospanIso W n hn).hom ≫ pullback.fst _ _ = _
  rw [hlim, ← Category.assoc, hp, spinePrefixFirstMappingIso_hom]
  unfold spinePrefixLastEdgeProjection
  rw [← Category.assoc, ← (discreteSourceMapping W).map_comp, ← op_comp]

private theorem prefixPrevious_two (n : ℕ) (hn : 2 ≤ n) :
    SSet.Subcomplex.toRange (SSet.Rezk.segalSpineEdgeMap.{u} n ⟨1, hn⟩) ≫
      SSet.Rezk.spinePrefixRight n 1 hn =
        SSet.Rezk.spinePrefixPreviousEdge n 2 hn (by decide) := by
  ext m a
  rfl

@[reassoc]
private theorem prefixPairIso_snd (W : SimplicialSpace.{u}) (n : ℕ) (hn : 2 ≤ n) :
    (prefixPairIso W n hn).hom ≫ pullback.snd _ _ =
      spinePrefixLastEdgeProjection W n 2 hn (by decide) := by
  have hlim :
      lim.map (prefixPairCospanIso W n hn).hom ≫
        limit.π _ WalkingCospan.right =
      limit.π (spinePrefixMappingCospan W n 1 hn (by decide)) WalkingCospan.right ≫
        (spineEdgeMappingIso W n ⟨1, hn⟩).hom :=
    limMap_π _ _
  have hp : (spinePrefixMappingIso W n 1 hn (by decide)).hom ≫
      limit.π (spinePrefixMappingCospan W n 1 hn (by decide)) WalkingCospan.right =
      (discreteSourceMapping W).map (SSet.Rezk.spinePrefixRight n 1 hn).op :=
    (spinePrefixMapping_isPullback W n 1 hn (by decide)).isoPullback_hom_snd
  change (spinePrefixMappingIso W n 1 hn (by decide)).hom ≫
      lim.map (prefixPairCospanIso W n hn).hom ≫ pullback.snd _ _ = _
  rw [hlim, ← Category.assoc, hp]
  unfold spineEdgeMappingIso spinePrefixLastEdgeProjection
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  change (discreteSourceMapping W).map (SSet.Rezk.spinePrefixRight n 1 hn).op ≫
    (discreteSourceMapping W).map
      (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineEdgeMap n ⟨1, hn⟩)).op ≫
        (discreteYonedaIso W 1).hom = _
  rw [← Category.assoc, ← (discreteSourceMapping W).map_comp, ← op_comp, prefixPrevious_two]

/-- The actual chosen pullback of a composable pair followed by its third edge. -/
abbrev threeEdgePullback (W : SimplicialSpace.{u}) : SSet.{u} :=
  pullback (pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2)) ≫
    W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2))

private def threeEdgeCospanIso (W : SimplicialSpace.{u}) :
    segalMappingCospan W 3 (by decide) ≅
      cospan (pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2)) ≫
        W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2)) :=
  cospanIsoMk (spineVertexMappingIso W 3 2 (by decide))
    (prefixPairIso W 3 (by decide)) (spineEdgeMappingIso W 3 (2 : Fin 3))
    (by
      change (discreteSourceMapping W).map
          (SSet.Rezk.spinePrefixVertexLeft 3 2 (by decide) (by decide)).op ≫
        (spineVertexMappingIso W 3 2 (by decide)).hom =
          (prefixPairIso W 3 (by decide)).hom ≫
            (pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2)) ≫
              W.diagram.δ (0 : Fin 2))
      rw [← Category.assoc, prefixPairIso_snd]
      exact spinePrefixMappingCospan_left W 3 2 (by decide) (by decide))
    (spinePrefixMappingCospan_right W 3 2 (by decide))

private def threeEdgeTargetIso (W : SimplicialSpace.{u}) :
    limit (segalMappingCospan W 3 (by decide)) ≅ threeEdgePullback W :=
  lim.mapIso (threeEdgeCospanIso W)

/-- The original three-simplex comparison to the three consecutive composable edges. -/
def threeEdgeComparison (W : SimplicialSpace.{u}) : W.diagram _⦋3⦌ ⟶ threeEdgePullback W :=
  segalStrictComparison W 3 (by decide) ≫ (threeEdgeTargetIso W).hom

/-- The original three-edge comparison is a genuine Kan trivial fibration. -/
theorem threeEdgeComparison_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (threeEdgeComparison W) := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp
    (segalStrictComparison_trivialFibration W 3 (by decide) hW)
  let := hf
  let := hw
  exact (mem_trivialFibrations_iff _).mpr ⟨by dsimp [threeEdgeComparison]; infer_instance,
    by dsimp [threeEdgeComparison]; infer_instance⟩

@[reassoc]
private theorem threeEdgeTargetIso_fst (W : SimplicialSpace.{u}) :
    (threeEdgeTargetIso W).hom ≫ pullback.fst _ _ =
      limit.π (segalMappingCospan W 3 (by decide)) WalkingCospan.left ≫
        (prefixPairIso W 3 (by decide)).hom := by
  change lim.map (threeEdgeCospanIso W).hom ≫ limit.π _ WalkingCospan.left = _
  exact limMap_π _ _

@[reassoc]
private theorem threeEdgeTargetIso_snd (W : SimplicialSpace.{u}) :
    (threeEdgeTargetIso W).hom ≫ pullback.snd _ _ =
      limit.π (segalMappingCospan W 3 (by decide)) WalkingCospan.right ≫
        (spineEdgeMappingIso W 3 (2 : Fin 3)).hom := by
  change lim.map (threeEdgeCospanIso W).hom ≫ limit.π _ WalkingCospan.right = _
  exact limMap_π _ _

@[reassoc]
private theorem prefixThreeIso_fst (W : SimplicialSpace.{u}) :
    (spinePrefixMappingIso W 3 2 (by decide) (by decide)).hom ≫
      limit.π (segalMappingCospan W 3 (by decide)) WalkingCospan.left =
      (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft 3 2 (by decide)).op :=
  (spinePrefixMapping_isPullback W 3 2 (by decide) (by decide)).isoPullback_hom_fst

@[reassoc]
private theorem prefixThreeIso_snd (W : SimplicialSpace.{u}) :
    (spinePrefixMappingIso W 3 2 (by decide) (by decide)).hom ≫
      limit.π (segalMappingCospan W 3 (by decide)) WalkingCospan.right =
      (discreteSourceMapping W).map (SSet.Rezk.spinePrefixRight 3 2 (by decide)).op :=
  (spinePrefixMapping_isPullback W 3 2 (by decide) (by decide)).isoPullback_hom_snd

private theorem threeFirstEdgeChain :
    (SSet.Rezk.spinePrefixPreviousEdge.{u} 3 1 (by decide) (by decide) ≫
        SSet.Rezk.spinePrefixLeft 3 1 (by decide)) ≫
      SSet.Rezk.spinePrefixLeft 3 2 (by decide) ≫
        (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 3 (by decide))).hom =
      SSet.Rezk.spineEdgeInclusion 3 (0 : Fin 3) := by
  ext m a
  rfl

private theorem threeSecondEdgeChain :
    SSet.Rezk.spinePrefixPreviousEdge.{u} 3 2 (by decide) (by decide) ≫
      SSet.Rezk.spinePrefixLeft 3 2 (by decide) ≫
        (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 3 (by decide))).hom =
      SSet.Rezk.spineEdgeInclusion 3 (1 : Fin 3) := by
  ext m a
  rfl

private theorem threeThirdEdgeChain :
    SSet.Subcomplex.toRange (SSet.Rezk.segalSpineEdgeMap.{u} 3 (2 : Fin 3)) ≫
      SSet.Rezk.spinePrefixRight 3 2 (by decide) ≫
        (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 3 (by decide))).hom =
      SSet.Rezk.spineEdgeInclusion 3 (2 : Fin 3) := by
  ext m a
  rfl

/-- The first three-edge projection is the original 01 edge of W₃. -/
@[reassoc (attr := simp)]
theorem threeEdgeComparison_first (W : SimplicialSpace.{u}) :
    threeEdgeComparison W ≫ pullback.fst _ _ ≫
        pullback.fst (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2)) =
      W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin 3)).op := by
  unfold threeEdgeComparison
  simp only [Category.assoc]
  rw [threeEdgeTargetIso_fst_assoc, prefixPairIso_fst]
  unfold segalStrictComparison segalSpineMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [prefixThreeIso_fst_assoc]
  have hm :
      (discreteSourceMapping W).map
          (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 3 (by decide))).hom.op ≫
        (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft 3 2 (by decide)).op ≫
          (discreteSourceMapping W).map
            (SSet.Rezk.spinePrefixPreviousEdge 3 1 (by decide) (by decide) ≫
              SSet.Rezk.spinePrefixLeft 3 1 (by decide)).op =
        (discreteSourceMapping W).map (SSet.Rezk.spineEdgeInclusion 3 (0 : Fin 3)).op := by
    rw [← (discreteSourceMapping W).map_comp, ← (discreteSourceMapping W).map_comp,
      ← op_comp, ← op_comp, Category.assoc, threeFirstEdgeChain]
  have hc := congrArg (fun t => rawSegalComparison W 3 ≫ t ≫ (discreteYonedaIso W 1).hom) hm
  simp only [Category.assoc] at hc
  exact hc.trans (rawSegalComparison_edge W 3 (0 : Fin 3))

/-- The second three-edge projection is the original 12 edge of W₃. -/
@[reassoc (attr := simp)]
theorem threeEdgeComparison_second (W : SimplicialSpace.{u}) :
    threeEdgeComparison W ≫ pullback.fst _ _ ≫
        pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2)) =
      W.diagram.map (SimplexCategory.mkOfSucc (1 : Fin 3)).op := by
  unfold threeEdgeComparison
  simp only [Category.assoc]
  rw [threeEdgeTargetIso_fst_assoc, prefixPairIso_snd]
  unfold segalStrictComparison segalSpineMappingIso spinePrefixLastEdgeProjection
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [prefixThreeIso_fst_assoc]
  have hm :
      (discreteSourceMapping W).map
          (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 3 (by decide))).hom.op ≫
        (discreteSourceMapping W).map (SSet.Rezk.spinePrefixLeft 3 2 (by decide)).op ≫
          (discreteSourceMapping W).map
            (SSet.Rezk.spinePrefixPreviousEdge 3 2 (by decide) (by decide)).op =
        (discreteSourceMapping W).map (SSet.Rezk.spineEdgeInclusion 3 (1 : Fin 3)).op := by
    rw [← (discreteSourceMapping W).map_comp, ← (discreteSourceMapping W).map_comp,
      ← op_comp, ← op_comp, Category.assoc, threeSecondEdgeChain]
  have hc := congrArg (fun t => rawSegalComparison W 3 ≫ t ≫ (discreteYonedaIso W 1).hom) hm
  simp only [Category.assoc] at hc
  exact hc.trans (rawSegalComparison_edge W 3 (1 : Fin 3))

/-- The last three-edge projection is the original 23 edge of W₃. -/
@[reassoc (attr := simp)]
theorem threeEdgeComparison_third (W : SimplicialSpace.{u}) :
    threeEdgeComparison W ≫ pullback.snd _ _ =
      W.diagram.map (SimplexCategory.mkOfSucc (2 : Fin 3)).op := by
  unfold threeEdgeComparison
  rw [Category.assoc, threeEdgeTargetIso_snd]
  unfold segalStrictComparison segalSpineMappingIso spineEdgeMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [prefixThreeIso_snd_assoc]
  have hm :
      (discreteSourceMapping W).map
          (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_last 3 (by decide))).hom.op ≫
        (discreteSourceMapping W).map (SSet.Rezk.spinePrefixRight 3 2 (by decide)).op ≫
          (discreteSourceMapping W).map
            (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineEdgeMap 3 (2 : Fin 3))).op =
        (discreteSourceMapping W).map (SSet.Rezk.spineEdgeInclusion 3 (2 : Fin 3)).op := by
    rw [← (discreteSourceMapping W).map_comp, ← (discreteSourceMapping W).map_comp,
      ← op_comp, ← op_comp, Category.assoc, threeThirdEdgeChain]
  have hc := congrArg (fun t => rawSegalComparison W 3 ≫ t ≫ (discreteYonedaIso W 1).hom) hm
  simp only [Category.assoc] at hc
  exact hc.trans (rawSegalComparison_edge W 3 (2 : Fin 3))

private theorem point_value_zero {A : SSet.{u}} (a : A _⦋0⦌)
    (q : (Δ[0] : SSet.{u}) _⦋0⦌) :
    (SSet.yonedaEquiv.symm a).app (op ⦋0⦌) q = a := by
  have hq : q = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    have h₁ := (SSet.stdSimplex.obj₀Equiv q).isLt
    have h₂ := (SSet.stdSimplex.obj₀Equiv (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))).isLt
    omega
  rw [hq]
  change SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}) ≫ SSet.yonedaEquiv.symm a) = a
  rw [Category.id_comp, Equiv.apply_symm_apply]

private theorem fibreVertex_source (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) ((mappingFibre.fst W x y).app (op ⦋0⦌) a) = x := by
  have h := congrArg (fun f : mappingFibre W x y ⟶ W.diagram _⦋0⦌ => f.app (op ⦋0⦌) a)
    (mappingFibre.source_eq W x y)
  change (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌)
      ((mappingFibre.fst W x y).app (op ⦋0⦌) a) =
    (SSet.yonedaEquiv.symm x).app (op ⦋0⦌) ((mappingFibre.snd W x y).app (op ⦋0⦌) a) at h
  exact h.trans (point_value_zero x _)

private theorem fibreVertex_target (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌) :
    (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) ((mappingFibre.fst W x y).app (op ⦋0⦌) a) = y := by
  have h := congrArg (fun f : mappingFibre W x y ⟶ W.diagram _⦋0⦌ => f.app (op ⦋0⦌) a)
    (mappingFibre.target_eq W x y)
  change (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌)
      ((mappingFibre.fst W x y).app (op ⦋0⦌) a) =
    (SSet.yonedaEquiv.symm y).app (op ⦋0⦌) ((mappingFibre.snd W x y).app (op ⦋0⦌) a) at h
  exact h.trans (point_value_zero y _)

private def fibreVertex (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (e : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) e = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) e = y) :
    (mappingFibre W x y) _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm e) (𝟙 (Δ[0] : SSet.{u})) (by
    apply prod.hom_ext
    · rw [Category.assoc, mappingEndpoint_fst, Category.id_comp, mappingPointPair_fst,
        SSet.yonedaEquiv_symm_comp, hs]
    · rw [Category.assoc, mappingEndpoint_snd, Category.id_comp, mappingPointPair_snd,
        SSet.yonedaEquiv_symm_comp, ht]))

private theorem fibreVertex_fst (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (e : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) e = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) e = y) :
    (mappingFibre.fst W x y).app (op ⦋0⦌) (fibreVertex W x y e hs ht) = e := by
  change SSet.yonedaEquiv
    (pullback.lift (SSet.yonedaEquiv.symm e) (𝟙 (Δ[0] : SSet.{u})) _ ≫
      pullback.fst (mappingEndpoint W) (mappingPointPair W x y)) = e
  rw [pullback.lift_fst, Equiv.apply_symm_apply]

private theorem fibreVertex_ext (W : SimplicialSpace.{u}) {x y : (W.diagram _⦋0⦌) _⦋0⦌}
    {a b : (mappingFibre W x y) _⦋0⦌}
    (h : (mappingFibre.fst W x y).app (op ⦋0⦌) a =
      (mappingFibre.fst W x y).app (op ⦋0⦌) b) : a = b := by
  apply SSet.yonedaEquiv.symm.injective
  apply (ReedyModel.mappingFibre_isPullback W x y).hom_ext
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private def triangleOfVertices (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (t : (W.diagram _⦋2⦌) _⦋0⦌)
    (a : (mappingFibre W x y) _⦋0⦌) (b : (mappingFibre W y z) _⦋0⦌)
    (ha : (mappingFibre.fst W x y).app (op ⦋0⦌) a =
      (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t)
    (hb : (mappingFibre.fst W y z).app (op ⦋0⦌) b =
      (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t) :
    (triangleSpace W x y z) _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm t)
    (prod.lift (SSet.yonedaEquiv.symm a) (SSet.yonedaEquiv.symm b)) (by
      apply pullback.hom_ext
      · rw [Category.assoc, twoEdgeComparison_fst, Category.assoc, twoEdgePair_fst,
          prod.lift_fst_assoc]
        simp only [SSet.yonedaEquiv_symm_comp, ha]
      · rw [Category.assoc, twoEdgeComparison_snd, Category.assoc, twoEdgePair_snd,
          prod.lift_snd_assoc]
        simp only [SSet.yonedaEquiv_symm_comp, hb]))

private theorem triangleOfVertices_projection (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (t : (W.diagram _⦋2⦌) _⦋0⦌)
    (a : (mappingFibre W x y) _⦋0⦌) (b : (mappingFibre W y z) _⦋0⦌)
    (ha : (mappingFibre.fst W x y).app (op ⦋0⦌) a =
      (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t)
    (hb : (mappingFibre.fst W y z).app (op ⦋0⦌) b =
      (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t) :
    (triangleProjection W x y z).app (op ⦋0⦌) (triangleOfVertices W x y z t a b ha hb) = t := by
  change SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm t)
    (prod.lift (SSet.yonedaEquiv.symm a) (SSet.yonedaEquiv.symm b)) _ ≫
      pullback.fst (twoEdgeComparison W) (twoEdgePair W x y z)) = t
  rw [pullback.lift_fst, Equiv.apply_symm_apply]

private theorem triangleOfVertices_first (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (t : (W.diagram _⦋2⦌) _⦋0⦌)
    (a : (mappingFibre W x y) _⦋0⦌) (b : (mappingFibre W y z) _⦋0⦌)
    (ha : (mappingFibre.fst W x y).app (op ⦋0⦌) a =
      (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t)
    (hb : (mappingFibre.fst W y z).app (op ⦋0⦌) b =
      (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t) :
    (triangleComparison W x y z ≫ prod.fst).app (op ⦋0⦌)
        (triangleOfVertices W x y z t a b ha hb) = a := by
  change SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm t)
    (prod.lift (SSet.yonedaEquiv.symm a) (SSet.yonedaEquiv.symm b)) _ ≫
      pullback.snd (twoEdgeComparison W) (twoEdgePair W x y z) ≫ prod.fst) = a
  rw [pullback.lift_snd_assoc, prod.lift_fst, Equiv.apply_symm_apply]

private theorem triangleOfVertices_last (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (t : (W.diagram _⦋2⦌) _⦋0⦌)
    (a : (mappingFibre W x y) _⦋0⦌) (b : (mappingFibre W y z) _⦋0⦌)
    (ha : (mappingFibre.fst W x y).app (op ⦋0⦌) a =
      (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t)
    (hb : (mappingFibre.fst W y z).app (op ⦋0⦌) b =
      (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t) :
    (triangleComparison W x y z ≫ prod.snd).app (op ⦋0⦌)
        (triangleOfVertices W x y z t a b ha hb) = b := by
  change SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm t)
    (prod.lift (SSet.yonedaEquiv.symm a) (SSet.yonedaEquiv.symm b)) _ ≫
      pullback.snd (twoEdgeComparison W) (twoEdgePair W x y z) ≫ prod.snd) = b
  rw [pullback.lift_snd_assoc, prod.lift_snd, Equiv.apply_symm_apply]

/-- The middle of every original prescribed triangle computes intrinsic composition. -/
theorem compose_of_original_triangle (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {x y z : (W.diagram _⦋0⦌) _⦋0⦌} (t : (W.diagram _⦋2⦌) _⦋0⦌)
    (a : (mappingFibre W x y) _⦋0⦌) (b : (mappingFibre W y z) _⦋0⦌)
    (r : (mappingFibre W x z) _⦋0⦌)
    (ha : (mappingFibre.fst W x y).app (op ⦋0⦌) a =
      (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t)
    (hb : (mappingFibre.fst W y z).app (op ⦋0⦌) b =
      (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t)
    (hr : (mappingFibre.fst W x z).app (op ⦋0⦌) r =
      (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t) :
    compose W hW (SSet.π₀.mk a) (SSet.π₀.mk b) = SSet.π₀.mk r := by
  let q := triangleOfVertices W x y z t a b ha hb
  have h := compose_of_triangle W hW x y z (SSet.π₀.mk q)
  dsimp only [q] at h
  simp only [SSet.mapπ₀_mk] at h
  rw [triangleOfVertices_first, triangleOfVertices_last] at h
  have hm : (triangleMiddle W x y z).app (op ⦋0⦌) q = r := by
    apply fibreVertex_ext W
    change (triangleMiddle W x y z ≫ mappingFibre.fst W x z).app (op ⦋0⦌) q =
      (mappingFibre.fst W x z).app (op ⦋0⦌) r
    rw [triangleMiddle_fst]
    change (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌)
      ((triangleProjection W x y z).app (op ⦋0⦌) q) = _
    rw [triangleOfVertices_projection]
    exact hr.symm
  dsimp only [q] at hm
  rw [hm] at h
  exact h

/-- The original degenerate edge at a vertex, inside its original chosen mapping fibre. -/
def identityVertex (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingFibre W x x) _⦋0⦌ :=
  fibreVertex W x x ((W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x)
    (by
      have h := congrArg (fun f : W.diagram _⦋0⦌ ⟶ W.diagram _⦋0⦌ => f.app (op ⦋0⦌) x)
        (W.diagram.δ_comp_σ_succ (i := (0 : Fin 1)))
      simpa using h)
    (by
      have h := congrArg (fun f : W.diagram _⦋0⦌ ⟶ W.diagram _⦋0⦌ => f.app (op ⦋0⦌) x)
        (W.diagram.δ_comp_σ_self (i := (0 : Fin 1)))
      simpa using h)

/-- Its original edge projection is exactly σ₀ of the original vertex. -/
theorem identityVertex_fst (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingFibre.fst W x x).app (op ⦋0⦌) (identityVertex W x) =
      (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x :=
  fibreVertex_fst _ _ _ _ _ _

/-- The intrinsic identity hom class of an original object. -/
def identity (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.π₀ (mappingFibre W x x) :=
  SSet.π₀.mk (identityVertex W x)

/-- The original σ₀ triangle proves the left identity law on genuine mapping-fibre components. -/
theorem compose_identity_left (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} (f : SSet.π₀ (mappingFibre W x y)) :
    compose W hW (identity W x) f = f := by
  induction f using SSet.π₀.rec with
  | mk a =>
    unfold identity
    let e := (mappingFibre.fst W x y).app (op ⦋0⦌) a
    apply compose_of_original_triangle W hW
      ((W.diagram.σ (0 : Fin 2)).app (op ⦋0⦌) e) (identityVertex W x) a a
    · rw [identityVertex_fst]
      have hs : W.diagram.σ (0 : Fin 2) ≫ W.diagram.δ (2 : Fin 3) =
          W.diagram.δ (1 : Fin 2) ≫ W.diagram.σ (0 : Fin 1) :=
        W.diagram.δ_comp_σ_of_gt (n := 0) (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide)
      have h := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) e) hs
      change (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌)
          ((W.diagram.σ (0 : Fin 2)).app (op ⦋0⦌) e) =
        (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌)
          ((W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) e) at h
      dsimp only [e] at h
      rw [fibreVertex_source] at h
      exact h.symm
    · have hs := W.diagram.δ_comp_σ_self (i := (0 : Fin 2))
      have h := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) e) hs
      simpa using h.symm
    · have hs := W.diagram.δ_comp_σ_succ (i := (0 : Fin 2))
      have h := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) e) hs
      simpa using h.symm

/-- The original σ₁ triangle proves the right identity law on genuine mapping-fibre components. -/
theorem compose_identity_right (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} (f : SSet.π₀ (mappingFibre W x y)) :
    compose W hW f (identity W y) = f := by
  induction f using SSet.π₀.rec with
  | mk a =>
    unfold identity
    let e := (mappingFibre.fst W x y).app (op ⦋0⦌) a
    apply compose_of_original_triangle W hW
      ((W.diagram.σ (1 : Fin 2)).app (op ⦋0⦌) e) a (identityVertex W y) a
    · have hs := W.diagram.δ_comp_σ_succ (i := (1 : Fin 2))
      have h := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) e) hs
      simpa using h.symm
    · rw [identityVertex_fst]
      have hs : W.diagram.σ (1 : Fin 2) ≫ W.diagram.δ (0 : Fin 3) =
          W.diagram.δ (0 : Fin 2) ≫ W.diagram.σ (0 : Fin 1) :=
        W.diagram.δ_comp_σ_of_le (n := 0) (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide)
      have h := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) e) hs
      change (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌)
          ((W.diagram.σ (1 : Fin 2)).app (op ⦋0⦌) e) =
        (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌)
          ((W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) e) at h
      dsimp only [e] at h
      rw [fibreVertex_target] at h
      exact h.symm
    · have hs := W.diagram.δ_comp_σ_self (i := (1 : Fin 2))
      have h := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) e) hs
      simpa using h.symm

/-- The three original prescribed mapping-fibre edges form the original composable triple. -/
def threeEdgePair (W : SimplicialSpace.{u}) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶ threeEdgePullback W :=
  pullback.lift (prod.fst ≫ twoEdgePair W w x y)
    (prod.snd ≫ mappingFibre.fst W y z) (by
      simp only [Category.assoc, twoEdgePair_snd_assoc, mappingFibre.target_eq,
          mappingFibre.source_eq]
      have h :
          (prod.fst : (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶ _) ≫
              prod.snd ≫ mappingFibre.snd W x y =
            prod.snd ≫ mappingFibre.snd W y z :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      simpa only [Category.assoc] using congrArg (fun t => t ≫ SSet.yonedaEquiv.symm y) h)

/-- The first prescribed edge retains both original first product projections. -/
@[reassoc (attr := simp)]
theorem threeEdgePair_first (W : SimplicialSpace.{u}) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    threeEdgePair W w x y z ≫ pullback.fst _ _ ≫
        pullback.fst (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2)) =
      prod.fst ≫ prod.fst ≫ mappingFibre.fst W w x := by
  unfold threeEdgePair
  rw [pullback.lift_fst_assoc, Category.assoc, twoEdgePair_fst]

/-- The second prescribed edge retains its original inner second product projection. -/
@[reassoc (attr := simp)]
theorem threeEdgePair_second (W : SimplicialSpace.{u}) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    threeEdgePair W w x y z ≫ pullback.fst _ _ ≫
        pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2)) =
      prod.fst ≫ prod.snd ≫ mappingFibre.fst W x y := by
  unfold threeEdgePair
  rw [pullback.lift_fst_assoc, Category.assoc, twoEdgePair_snd]

/-- The third prescribed edge retains its original outer second product projection. -/
@[reassoc (attr := simp)]
theorem threeEdgePair_third (W : SimplicialSpace.{u}) (w x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    threeEdgePair W w x y z ≫ pullback.snd _ _ = prod.snd ≫ mappingFibre.fst W y z :=
  pullback.lift_snd _ _ _

private theorem vertex_surjective_of_trivialFibration {A B : SSet.{u}} (p : A ⟶ B)
    (hp : trivialFibrations SSet.{u} p) : Function.Surjective (p.app (op ⦋0⦌)) := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff p).mp hp
  let := hf
  let := hw
  let : Cofibration (initial.to (Δ[0] : SSet.{u})) :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  intro b
  have sq : CommSq (initial.to A) (initial.to (Δ[0] : SSet.{u})) p
      (SSet.yonedaEquiv.symm b) := ⟨Subsingleton.elim _ _⟩
  refine ⟨SSet.yonedaEquiv sq.lift, ?_⟩
  have h := congrArg SSet.yonedaEquiv sq.fac_right
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h

/-- Every original three prescribed mapping-fibre edges admit one original three-simplex. -/
theorem exists_threeSimplex (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (w x y z : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (mappingFibre W w x) _⦋0⦌) (b : (mappingFibre W x y) _⦋0⦌)
    (c : (mappingFibre W y z) _⦋0⦌) :
    ∃ t : (W.diagram _⦋3⦌) _⦋0⦌,
      (W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin 3)).op).app (op ⦋0⦌) t =
          (mappingFibre.fst W w x).app (op ⦋0⦌) a ∧
        (W.diagram.map (SimplexCategory.mkOfSucc (1 : Fin 3)).op).app (op ⦋0⦌) t =
          (mappingFibre.fst W x y).app (op ⦋0⦌) b ∧
        (W.diagram.map (SimplexCategory.mkOfSucc (2 : Fin 3)).op).app (op ⦋0⦌) t =
          (mappingFibre.fst W y z).app (op ⦋0⦌) c := by
  let q := productSimplex (productSimplex a b) c
  obtain ⟨t, ht⟩ := vertex_surjective_of_trivialFibration (threeEdgeComparison W)
    (threeEdgeComparison_trivialFibration W hW) ((threeEdgePair W w x y z).app (op ⦋0⦌) q)
  refine ⟨t, ?_, ?_, ?_⟩
  · have h := congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ =>
      f.app (op ⦋0⦌) t) (threeEdgeComparison_first W)
    change (pullback.fst (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2))).app (op ⦋0⦌)
      ((pullback.fst _ _ : threeEdgePullback W ⟶ twoEdgePullback W).app (op ⦋0⦌)
          ((threeEdgeComparison W).app (op ⦋0⦌) t)) = _ at h
    rw [ht] at h
    have hq := congrArg (fun f :
        (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶ W.diagram _⦋1⦌ =>
      f.app (op ⦋0⦌) q) (threeEdgePair_first W w x y z)
    change (pullback.fst (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2))).app (op ⦋0⦌)
      ((pullback.fst _ _ : threeEdgePullback W ⟶ twoEdgePullback W).app (op ⦋0⦌)
          ((threeEdgePair W w x y z).app (op ⦋0⦌) q)) =
        (mappingFibre.fst W w x).app (op ⦋0⦌)
          ((prod.fst : mappingFibre W w x ⨯ mappingFibre W x y ⟶ _).app (op ⦋0⦌)
            ((prod.fst : (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶ _).app
              (op ⦋0⦌) q)) at hq
    dsimp only [q] at hq
    rw [productSimplex_fst, productSimplex_fst] at hq
    exact h.symm.trans hq
  · have h := congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ =>
      f.app (op ⦋0⦌) t) (threeEdgeComparison_second W)
    change (pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2))).app (op ⦋0⦌)
      ((pullback.fst _ _ : threeEdgePullback W ⟶ twoEdgePullback W).app (op ⦋0⦌)
          ((threeEdgeComparison W).app (op ⦋0⦌) t)) = _ at h
    rw [ht] at h
    have hq := congrArg (fun f :
        (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶ W.diagram _⦋1⦌ =>
      f.app (op ⦋0⦌) q) (threeEdgePair_second W w x y z)
    change (pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (1 : Fin 2))).app (op ⦋0⦌)
      ((pullback.fst _ _ : threeEdgePullback W ⟶ twoEdgePullback W).app (op ⦋0⦌)
          ((threeEdgePair W w x y z).app (op ⦋0⦌) q)) =
        (mappingFibre.fst W x y).app (op ⦋0⦌)
          ((prod.snd : mappingFibre W w x ⨯ mappingFibre W x y ⟶ _).app (op ⦋0⦌)
            ((prod.fst : (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶ _).app
              (op ⦋0⦌) q)) at hq
    dsimp only [q] at hq
    rw [productSimplex_fst, productSimplex_snd] at hq
    exact h.symm.trans hq
  · have h := congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ =>
      f.app (op ⦋0⦌) t) (threeEdgeComparison_third W)
    change (pullback.snd _ _ : threeEdgePullback W ⟶ W.diagram _⦋1⦌).app (op ⦋0⦌)
        ((threeEdgeComparison W).app (op ⦋0⦌) t) = _ at h
    rw [ht] at h
    have hq := congrArg (fun f :
        (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶ W.diagram _⦋1⦌ =>
      f.app (op ⦋0⦌) q) (threeEdgePair_third W w x y z)
    change (pullback.snd _ _ : threeEdgePullback W ⟶ W.diagram _⦋1⦌).app (op ⦋0⦌)
        ((threeEdgePair W w x y z).app (op ⦋0⦌) q) =
      (mappingFibre.fst W y z).app (op ⦋0⦌)
        ((prod.snd : (mappingFibre W w x ⨯ mappingFibre W x y) ⨯ mappingFibre W y z ⟶ _).app
          (op ⦋0⦌) q) at hq
    dsimp only [q] at hq
    rw [productSimplex_snd] at hq
    exact h.symm.trans hq

private theorem triangle_middle_vertex (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (t : (W.diagram _⦋2⦌) _⦋0⦌)
    (a : (mappingFibre W x y) _⦋0⦌) (b : (mappingFibre W y z) _⦋0⦌)
    (ha : (mappingFibre.fst W x y).app (op ⦋0⦌) a =
      (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t)
    (hb : (mappingFibre.fst W y z).app (op ⦋0⦌) b =
      (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t) :
    (mappingFibre.fst W x z).app (op ⦋0⦌)
        ((triangleMiddle W x y z).app (op ⦋0⦌) (triangleOfVertices W x y z t a b ha hb)) =
      (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t := by
  change (triangleMiddle W x y z ≫ mappingFibre.fst W x z).app (op ⦋0⦌)
    (triangleOfVertices W x y z t a b ha hb) = _
  rw [triangleMiddle_fst]
  change (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌)
    ((triangleProjection W x y z).app (op ⦋0⦌) (triangleOfVertices W x y z t a b ha hb)) = _
  rw [triangleOfVertices_projection]

private theorem compose_mk_triangle (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) (t : (W.diagram _⦋2⦌) _⦋0⦌)
    (a : (mappingFibre W x y) _⦋0⦌) (b : (mappingFibre W y z) _⦋0⦌)
    (ha : (mappingFibre.fst W x y).app (op ⦋0⦌) a =
      (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t)
    (hb : (mappingFibre.fst W y z).app (op ⦋0⦌) b =
      (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t) :
    compose W hW (SSet.π₀.mk a) (SSet.π₀.mk b) =
      SSet.π₀.mk ((triangleMiddle W x y z).app (op ⦋0⦌)
        (triangleOfVertices W x y z t a b ha hb)) :=
  compose_of_original_triangle W hW t a b _ ha hb
    (triangle_middle_vertex W x y z t a b ha hb)

private theorem face3_edge (W : SimplicialSpace.{u}) (i : Fin 4) (j : Fin 3) (k : Fin 3)
    (h : SimplexCategory.δ j ≫ SimplexCategory.δ i = SimplexCategory.mkOfSucc k) :
    W.diagram.δ i ≫ W.diagram.δ j = W.diagram.map (SimplexCategory.mkOfSucc k).op := by
  change W.diagram.map (SimplexCategory.δ i).op ≫
    W.diagram.map (SimplexCategory.δ j).op = _
  simpa only [Functor.map_comp, op_comp] using
    congrArg (fun f => W.diagram.map f.op) h

private theorem face3_edge_apply (W : SimplicialSpace.{u}) (i : Fin 4) (j : Fin 3) (k : Fin 3)
    (h : SimplexCategory.δ j ≫ SimplexCategory.δ i = SimplexCategory.mkOfSucc k)
    (t : (W.diagram _⦋3⦌) _⦋0⦌) :
    (W.diagram.δ j).app (op ⦋0⦌) ((W.diagram.δ i).app (op ⦋0⦌) t) =
      (W.diagram.map (SimplexCategory.mkOfSucc k).op).app (op ⦋0⦌) t := by
  have hm := congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) t)
    (face3_edge W i j k h)
  exact hm

/-- The original three-simplex proves associativity on the genuine mapping-fibre components. -/
theorem compose_assoc (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {w x y z : (W.diagram _⦋0⦌) _⦋0⦌}
    (f : SSet.π₀ (mappingFibre W w x)) (g : SSet.π₀ (mappingFibre W x y))
    (h : SSet.π₀ (mappingFibre W y z)) :
    compose W hW (compose W hW f g) h = compose W hW f (compose W hW g h) := by
  induction f using SSet.π₀.rec with
  | mk a =>
    induction g using SSet.π₀.rec with
    | mk b =>
      induction h using SSet.π₀.rec with
      | mk c =>
        obtain ⟨t, ht₀, ht₁, ht₂⟩ := exists_threeSimplex W hW w x y z a b c
        let t012 := (W.diagram.δ (3 : Fin 4)).app (op ⦋0⦌) t
        let t123 := (W.diagram.δ (0 : Fin 4)).app (op ⦋0⦌) t
        let t023 := (W.diagram.δ (1 : Fin 4)).app (op ⦋0⦌) t
        let t013 := (W.diagram.δ (2 : Fin 4)).app (op ⦋0⦌) t
        have ha012 : (mappingFibre.fst W w x).app (op ⦋0⦌) a =
            (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t012 :=
          ht₀.symm.trans (face3_edge_apply W 3 2 0 (by decide) t).symm
        have hb012 : (mappingFibre.fst W x y).app (op ⦋0⦌) b =
            (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t012 :=
          ht₁.symm.trans (face3_edge_apply W 3 0 1 (by decide) t).symm
        have hb123 : (mappingFibre.fst W x y).app (op ⦋0⦌) b =
            (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t123 :=
          ht₁.symm.trans (face3_edge_apply W 0 2 1 (by decide) t).symm
        have hc123 : (mappingFibre.fst W y z).app (op ⦋0⦌) c =
            (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t123 :=
          ht₂.symm.trans (face3_edge_apply W 0 0 2 (by decide) t).symm
        let r02 := (triangleMiddle W w x y).app (op ⦋0⦌)
          (triangleOfVertices W w x y t012 a b ha012 hb012)
        let r13 := (triangleMiddle W x y z).app (op ⦋0⦌)
          (triangleOfVertices W x y z t123 b c hb123 hc123)
        have hr02 : (mappingFibre.fst W w y).app (op ⦋0⦌) r02 =
            (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t012 :=
          triangle_middle_vertex W w x y t012 a b ha012 hb012
        have hr13 : (mappingFibre.fst W x z).app (op ⦋0⦌) r13 =
            (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t123 :=
          triangle_middle_vertex W x y z t123 b c hb123 hc123
        have hr023 : (mappingFibre.fst W w y).app (op ⦋0⦌) r02 =
            (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t023 := by
          have hd := congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) t)
            (W.diagram.δ_comp_δ (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide))
          change (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t012 =
            (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t023 at hd
          exact hr02.trans hd
        have hc023 : (mappingFibre.fst W y z).app (op ⦋0⦌) c =
            (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t023 :=
          ht₂.symm.trans (face3_edge_apply W 1 0 2 (by decide) t).symm
        have ha013 : (mappingFibre.fst W w x).app (op ⦋0⦌) a =
            (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t013 :=
          ht₀.symm.trans (face3_edge_apply W 2 2 0 (by decide) t).symm
        have hr013 : (mappingFibre.fst W x z).app (op ⦋0⦌) r13 =
            (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t013 := by
          have hd := congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) t)
            (W.diagram.δ_comp_δ (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide))
          change (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t013 =
            (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t123 at hd
          exact hr13.trans hd.symm
        let r03L := (triangleMiddle W w y z).app (op ⦋0⦌)
          (triangleOfVertices W w y z t023 r02 c hr023 hc023)
        let r03R := (triangleMiddle W w x z).app (op ⦋0⦌)
          (triangleOfVertices W w x z t013 a r13 ha013 hr013)
        have heq : r03L = r03R := by
          apply fibreVertex_ext W
          have hL := triangle_middle_vertex W w y z t023 r02 c hr023 hc023
          have hR := triangle_middle_vertex W w x z t013 a r13 ha013 hr013
          have hd := congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) t)
            (W.diagram.δ_comp_δ_self (i := (1 : Fin 3)))
          change (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t023 =
            (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t013 at hd
          exact hL.trans (hd.trans hR.symm)
        have h012 := compose_mk_triangle W hW w x y t012 a b ha012 hb012
        have h123 := compose_mk_triangle W hW x y z t123 b c hb123 hc123
        have h023 := compose_mk_triangle W hW w y z t023 r02 c hr023 hc023
        have h013 := compose_mk_triangle W hW w x z t013 a r13 ha013 hr013
        change compose W hW (compose W hW (SSet.π₀.mk a) (SSet.π₀.mk b)) (SSet.π₀.mk c) =
          compose W hW (SSet.π₀.mk a) (compose W hW (SSet.π₀.mk b) (SSet.π₀.mk c))
        rw [h012, h123]
        change compose W hW (SSet.π₀.mk r02) (SSet.π₀.mk c) =
          compose W hW (SSet.π₀.mk a) (SSet.π₀.mk r13)
        rw [h023, h013]
        exact congrArg SSet.π₀.mk heq

private theorem exists_triangle (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌)
    (a : (mappingFibre W x y) _⦋0⦌) (b : (mappingFibre W y z) _⦋0⦌) :
    ∃ t : (W.diagram _⦋2⦌) _⦋0⦌, ∃ r : (mappingFibre W x z) _⦋0⦌,
      (mappingFibre.fst W x y).app (op ⦋0⦌) a = (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t ∧
      (mappingFibre.fst W y z).app (op ⦋0⦌) b = (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t ∧
      (mappingFibre.fst W x z).app (op ⦋0⦌) r = (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t ∧
      compose W hW (SSet.π₀.mk a) (SSet.π₀.mk b) = SSet.π₀.mk r := by
  obtain ⟨q, hq⟩ := vertex_surjective_of_trivialFibration (triangleComparison W x y z)
    (triangleComparison_trivialFibration W hW x y z) (productSimplex a b)
  let t := (triangleProjection W x y z).app (op ⦋0⦌) q
  let r := (triangleMiddle W x y z).app (op ⦋0⦌) q
  have ha := congrArg (fun f : triangleSpace W x y z ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) q)
    (triangleProjection_first W x y z)
  change (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t =
    (mappingFibre.fst W x y).app (op ⦋0⦌)
      ((prod.fst : mappingFibre W x y ⨯ mappingFibre W y z ⟶ _).app (op ⦋0⦌)
        ((triangleComparison W x y z).app (op ⦋0⦌) q)) at ha
  rw [hq, productSimplex_fst] at ha
  have hb := congrArg (fun f : triangleSpace W x y z ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) q)
    (triangleProjection_last W x y z)
  change (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t =
    (mappingFibre.fst W y z).app (op ⦋0⦌)
      ((prod.snd : mappingFibre W x y ⨯ mappingFibre W y z ⟶ _).app (op ⦋0⦌)
        ((triangleComparison W x y z).app (op ⦋0⦌) q)) at hb
  rw [hq, productSimplex_snd] at hb
  have hr := congrArg (fun f : triangleSpace W x y z ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) q)
    (triangleMiddle_fst W x y z)
  change (mappingFibre.fst W x z).app (op ⦋0⦌) r =
    (W.diagram.δ (1 : Fin 3)).app (op ⦋0⦌) t at hr
  exact ⟨t, r, ha.symm, hb.symm, hr,
    compose_of_original_triangle W hW t a b r ha.symm hb.symm hr⟩

private theorem map_fibreVertex_fst {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} (a : (mappingFibre W x y) _⦋0⦌) :
    (mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f y)).app (op ⦋0⦌)
      ((mappingFibre.map f (x := x) (y := y) rfl rfl).app (op ⦋0⦌) a) =
      (f.hom.app (op ⦋1⦌)).app (op ⦋0⦌) ((mappingFibre.fst W x y).app (op ⦋0⦌) a) := by
  have h := congrArg (fun g : mappingFibre W x y ⟶ V.diagram _⦋1⦌ => g.app (op ⦋0⦌) a)
    (mappingFibre.map_fst f (x := x) (y := y) rfl rfl)
  exact h

private theorem map_triangle_face {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (i : Fin 3) (t : (W.diagram _⦋2⦌) _⦋0⦌) :
    (V.diagram.δ i).app (op ⦋0⦌) ((f.hom.app (op ⦋2⦌)).app (op ⦋0⦌) t) =
      (f.hom.app (op ⦋1⦌)).app (op ⦋0⦌) ((W.diagram.δ i).app (op ⦋0⦌) t) := by
  have h := congrArg (fun g : W.diagram _⦋2⦌ ⟶ V.diagram _⦋1⦌ => g.app (op ⦋0⦌) t)
    (SimplicialObject.δ_naturality f.hom i)
  exact h.symm

/-- Every original simplicial-space map preserves the constructed intrinsic composition. -/
theorem compose_map {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    {x y z : (W.diagram _⦋0⦌) _⦋0⦌}
    (a : SSet.π₀ (mappingFibre W x y)) (b : SSet.π₀ (mappingFibre W y z)) :
    SSet.mapπ₀ (mappingFibre.map f (x := x) (y := z) rfl rfl) (compose W hW a b) =
      compose V hV (SSet.mapπ₀ (mappingFibre.map f (x := x) (y := y) rfl rfl) a)
        (SSet.mapπ₀ (mappingFibre.map f (x := y) (y := z) rfl rfl) b) := by
  induction a using SSet.π₀.rec with
  | mk a =>
    induction b using SSet.π₀.rec with
    | mk b =>
      obtain ⟨t, r, ha, hb, hr, hc⟩ := exists_triangle W hW x y z a b
      rw [hc, SSet.mapπ₀_mk, SSet.mapπ₀_mk, SSet.mapπ₀_mk]
      symm
      apply compose_of_original_triangle V hV
        ((f.hom.app (op ⦋2⦌)).app (op ⦋0⦌) t)
        ((mappingFibre.map f (x := x) (y := y) rfl rfl).app (op ⦋0⦌) a)
        ((mappingFibre.map f (x := y) (y := z) rfl rfl).app (op ⦋0⦌) b)
        ((mappingFibre.map f (x := x) (y := z) rfl rfl).app (op ⦋0⦌) r)
      · exact (map_fibreVertex_fst f a).trans
          ((congrArg (fun e => (f.hom.app (op ⦋1⦌)).app (op ⦋0⦌) e) ha).trans
            (map_triangle_face f 2 t).symm)
      · exact (map_fibreVertex_fst f b).trans
          ((congrArg (fun e => (f.hom.app (op ⦋1⦌)).app (op ⦋0⦌) e) hb).trans
            (map_triangle_face f 0 t).symm)
      · exact (map_fibreVertex_fst f r).trans
          ((congrArg (fun e => (f.hom.app (op ⦋1⦌)).app (op ⦋0⦌) e) hr).trans
            (map_triangle_face f 1 t).symm)

private theorem identityVertex_map {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingFibre.map f (x := x) (y := x) rfl rfl).app (op ⦋0⦌) (identityVertex W x) =
      identityVertex V (mappingVertexMap f x) := by
  apply fibreVertex_ext V
  rw [map_fibreVertex_fst, identityVertex_fst, identityVertex_fst]
  have h := congrArg (fun g : W.diagram _⦋0⦌ ⟶ V.diagram _⦋1⦌ => g.app (op ⦋0⦌) x)
    (SimplicialObject.σ_naturality f.hom (0 : Fin 1))
  exact h

/-- Every original simplicial-space map preserves the original intrinsic identity class. -/
theorem identity_map {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.mapπ₀ (mappingFibre.map f (x := x) (y := x) rfl rfl) (identity W x) =
      identity V (mappingVertexMap f x) := by
  unfold identity
  rw [SSet.mapπ₀_mk, identityVertex_map]

/-- Objects of the intrinsic homotopy category are the original outer-zero vertices. -/
structure Object (W : SimplicialSpace.{u}) (hW : segalSpaces W) where
  /-- The original vertex of W₀. -/
  vertex : (W.diagram _⦋0⦌) _⦋0⦌

/-- The constructed category has exactly π₀ of the original mapping fibres as its homs. -/
instance objectCategory (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Category.{u} (Object W hW) where
  Hom a b := SSet.π₀ (mappingFibre W a.vertex b.vertex)
  id a := identity W a.vertex
  comp f g := compose W hW f g
  id_comp f := compose_identity_left W hW f
  comp_id f := compose_identity_right W hW f
  assoc f g h := compose_assoc W hW f g h

/-- The original map on vertices and mapping fibres is the intrinsic homotopy-category functor. -/
@[implicit_reducible]
def map {W V : SimplicialSpace.{u}} (f : W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V) :
    Object W hW ⥤ Object V hV where
  obj a := ⟨mappingVertexMap f a.vertex⟩
  map a := SSet.mapπ₀ (mappingFibre.map f rfl rfl) a
  map_id a := identity_map f a.vertex
  map_comp a b := compose_map f hW hV a b

/-- The original identity map induces the actual identity intrinsic functor. -/
theorem map_id (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    map (𝟙 W) hW hW = 𝟭 (Object W hW) := by
  refine CategoryTheory.Functor.ext (F := map (𝟙 W) hW hW) (G := 𝟭 (Object W hW))
    (fun _ => rfl) ?_
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change SSet.mapπ₀ (mappingFibre.map (𝟙 W) (x := a.vertex) (y := b.vertex) rfl rfl) f = f
  rw [mappingFibre.map_id, SSet.mapπ₀_id_apply]

/-- Original composition of simplicial-space maps induces actual composition of intrinsic
functors. -/
theorem map_comp {W V U : SimplicialSpace.{u}} (f : W ⟶ V) (g : V ⟶ U)
    (hW : segalSpaces W) (hV : segalSpaces V) (hU : segalSpaces U) :
    map (f ≫ g) hW hU = map f hW hV ⋙ map g hV hU := by
  refine CategoryTheory.Functor.ext (F := map (f ≫ g) hW hU)
    (G := map f hW hV ⋙ map g hV hU) (fun _ => rfl) ?_
  intro a b k
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change SSet.mapπ₀ (mappingFibre.map (f ≫ g) (x := a.vertex) (y := b.vertex) rfl rfl) k =
    SSet.mapπ₀ (mappingFibre.map g rfl rfl)
      (SSet.mapπ₀ (mappingFibre.map f (x := a.vertex) (y := b.vertex) rfl rfl) k)
  rw [← mappingFibre.map_comp f g rfl rfl rfl rfl, SSet.mapπ₀_comp_apply]

private theorem lift_edge {A B : SSet.{u}} (p : A ⟶ B) [Fibration p]
    {b₀ b₁ : B _⦋0⦌} (e : B.Edge b₀ b₁) (a : A _⦋0⦌)
    (ha : p.app (op ⦋0⦌) a = b₀) :
    ∃ a₁ : A _⦋0⦌, ∃ l : A.Edge a a₁,
      p.app (op ⦋0⦌) a₁ = b₁ ∧ p.app (op ⦋1⦌) l.edge = e.edge := by
  let faces : ∀ (j : Fin 2) (_ : j ≠ (0 : Fin 2)), (Δ[0] : SSet.{u}) ⟶ A :=
    fun _ _ => SSet.yonedaEquiv.symm a
  have hc : SSet.horn.IsCompatible (i := (0 : Fin 2)) faces := True.intro
  have hcomm : ∀ (j : Fin 2) (hj : j ≠ (0 : Fin 2)),
      faces j hj ≫ p = SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm e.edge := by
    intro j hj
    have hj₁ : j = (1 : Fin 2) := by fin_cases j <;> simp_all
    subst j
    dsimp only [faces]
    rw [SSet.yonedaEquiv_symm_comp, ha, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.Edge.src_eq]
  obtain ⟨L, hfaces, hL⟩ := hc.exists_lift p (SSet.yonedaEquiv.symm e.edge) hcomm
  let a₁ := SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2) ≫ L)
  have hs : A.δ (1 : Fin 2) (SSet.yonedaEquiv L) = a := by
    have h := congrArg SSet.yonedaEquiv (hfaces (1 : Fin 2) (by decide))
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] at h
    exact h
  have ht : A.δ (0 : Fin 2) (SSet.yonedaEquiv L) = a₁ :=
    (SSet.stdSimplex.yonedaEquiv_δ_comp L (0 : Fin 2)).symm
  let l := SSet.Edge.mk (SSet.yonedaEquiv L) hs ht
  have him : p.app (op ⦋1⦌) l.edge = e.edge := by
    change p.app (op ⦋1⦌) (SSet.yonedaEquiv L) = e.edge
    have h := congrArg SSet.yonedaEquiv hL
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  have h₁ : p.app (op ⦋0⦌) a₁ = b₁ :=
    (l.map p).tgt_eq.symm.trans ((congrArg (fun s => B.δ (0 : Fin 2) s) him).trans e.tgt_eq)
  exact ⟨a₁, l, h₁, him⟩

/-- The original edge vertex defines its actual hom class between its source and target. -/
def edgeClass (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (g : (W.diagram _⦋1⦌) _⦋0⦌) :
    (⟨(W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g⟩ : Object W hW) ⟶
      (⟨(W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g⟩ : Object W hW) :=
  SSet.π₀.mk (fibreVertex W
    ((W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g)
    ((W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g) g rfl rfl)

/-- An original edge is an intrinsic equivalence when its constructed hom class is invertible. -/
def IsEquivalenceEdge (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (g : (W.diagram _⦋1⦌) _⦋0⦌) : Prop :=
  IsIso (edgeClass W hW g)

/-- Equivalence recognition on a genuine prescribed fibre uses its exact original edge
projection. -/
theorem isEquivalenceEdge_iff_of_fibre (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (a : (mappingFibre W x y) _⦋0⦌)
    (ha : (mappingFibre.fst W x y).app (op ⦋0⦌) a = g) :
    IsEquivalenceEdge W hW g ↔
      IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk a) := by
  have hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x := by
    rw [← ha]
    exact fibreVertex_source W x y a
  have ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y := by
    rw [← ha]
    exact fibreVertex_target W x y a
  subst x
  subst y
  unfold IsEquivalenceEdge edgeClass
  have hpoint : fibreVertex W
      ((W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g)
      ((W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g) g rfl rfl = a := by
    apply fibreVertex_ext W
    rw [fibreVertex_fst, ha]
  rw [hpoint]

/-- Every original degenerate identity edge is intrinsically invertible. -/
theorem identity_isEquivalenceEdge (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    IsEquivalenceEdge W hW ((W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x) := by
  apply (isEquivalenceEdge_iff_of_fibre W hW _ (identityVertex W x)
    (identityVertex_fst W x)).mpr
  change IsIso (𝟙 (⟨x⟩ : Object W hW))
  infer_instance

/-- Every original simplicial-space map carries intrinsic equivalence edges to equivalence edges. -/
theorem isEquivalenceEdge_map {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (g : (W.diagram _⦋1⦌) _⦋0⦌) (hg : IsEquivalenceEdge W hW g) :
    IsEquivalenceEdge V hV ((f.hom.app (op ⦋1⦌)).app (op ⦋0⦌) g) := by
  let x := (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g
  let y := (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g
  let a := fibreVertex W x y g rfl rfl
  let b := (mappingFibre.map f (x := x) (y := y) rfl rfl).app (op ⦋0⦌) a
  have ha : (mappingFibre.fst W x y).app (op ⦋0⦌) a = g := fibreVertex_fst _ _ _ _ _ _
  have hb : (mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f y)).app (op ⦋0⦌) b =
      (f.hom.app (op ⦋1⦌)).app (op ⦋0⦌) g := by
    rw [map_fibreVertex_fst, ha]
  apply (isEquivalenceEdge_iff_of_fibre V hV _ b hb).mpr
  let : IsIso (edgeClass W hW g) := hg
  have hmap : IsIso ((map f hW hV).map (edgeClass W hW g)) := inferInstance
  change IsIso (C := Object V hV) (X := ⟨mappingVertexMap f x⟩) (Y := ⟨mappingVertexMap f y⟩)
    (SSet.mapπ₀ (mappingFibre.map f (x := x) (y := y) rfl rfl) (SSet.π₀.mk a)) at hmap
  rw [SSet.mapπ₀_mk] at hmap
  exact hmap

private abbrev zFirst : (Δ[3] : SSet.{u}).Subcomplex := SSet.stdSimplex.face {0, 2}
private abbrev zMiddle : (Δ[3] : SSet.{u}).Subcomplex := SSet.stdSimplex.face {1, 2}
private abbrev zLast : (Δ[3] : SSet.{u}).Subcomplex := SSet.stdSimplex.face {1, 3}
private abbrev zPair : (Δ[3] : SSet.{u}).Subcomplex := zFirst ⊔ zMiddle

/-- The actual zig-zag Z(3), with original edges 02, 12 and 13. -/
def zigzagSubcomplex : (Δ[3] : SSet.{u}).Subcomplex := zPair ⊔ zLast

private theorem zFirstSquare :
    SSet.Subcomplex.BicartSq (SSet.stdSimplex.face {2}) zFirst.{u} zMiddle zPair where
  sup_eq := rfl
  inf_eq := by
    rw [SSet.stdSimplex.face_inter_face]
    rfl

private theorem zLastSquare :
    SSet.Subcomplex.BicartSq (SSet.stdSimplex.face {1}) zPair.{u} zLast zigzagSubcomplex where
  sup_eq := rfl
  inf_eq := by
    change (zFirst ⊔ zMiddle) ⊓ zLast = SSet.stdSimplex.face {1}
    have hd : (zFirst.{u} ⊔ zMiddle) ⊓ zLast =
        (zFirst ⊓ zLast) ⊔ (zMiddle ⊓ zLast) := by
      ext n t
      change ((t ∈ zFirst.obj n ∨ t ∈ zMiddle.obj n) ∧ t ∈ zLast.obj n) ↔
        ((t ∈ zFirst.obj n ∧ t ∈ zLast.obj n) ∨ (t ∈ zMiddle.obj n ∧ t ∈ zLast.obj n))
      tauto
    rw [hd, SSet.stdSimplex.face_inter_face, SSet.stdSimplex.face_inter_face]
    have h₀ : ({0, 2} : Finset (Fin 4)) ⊓ {1, 3} = ∅ := by decide
    have h₁ : ({1, 2} : Finset (Fin 4)) ⊓ {1, 3} = {1} := by decide
    rw [h₀, h₁, SSet.stdSimplex.face_empty]
    simp

private theorem stdPair_hom_ι (i j : Fin 4) (hij : i < j) :
    (SSet.stdSimplex.facePairIso.{u} i j hij).hom ≫ (SSet.stdSimplex.face {i, j}).ι =
      SSet.stdSimplex.map (SimplexCategory.mkOfLe i j hij.le) := by
  apply SSet.yonedaEquiv.injective
  ext k
  fin_cases k <;> rfl

private theorem stdVertex_hom_ι (i : Fin 4) :
    (SSet.stdSimplex.faceSingletonIso.{u} i).hom ≫ (SSet.stdSimplex.face {i}).ι =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ i) := by
  ext d t
  rfl

private theorem discrete_preservesPushouts :
    PreservesColimitsOfShape WalkingSpan SSet.simplicialSpaceDiscrete.{u} := by
  change PreservesColimitsOfShape WalkingSpan
    ((CategoryTheory.Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) SSet.{u}).obj
      (SimplicialObject.const (Type u)))
  infer_instance

private theorem mapping_preservesPullbacks (W : SimplicialSpace.{u}) :
    PreservesLimitsOfShape WalkingCospan (innerHomFunctor.flip.obj W) := by
  let : ∀ K : SSet.{u}, PreservesColimitsOfShape WalkingCospanᵒᵖ
      (innerTensorBifunctor.flip.obj K) := fun K => by
    change PreservesColimitsOfShape WalkingCospanᵒᵖ (innerTensor K)
    let : (innerTensor K).IsLeftAdjoint := (innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  exact innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj WalkingCospan W

private theorem mapping_firstSquare (W : SimplicialSpace.{u}) :
    IsPullback
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₂₄).op)
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₃₄).op)
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₂).op)
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₃).op) := by
  let := discrete_preservesPushouts.{u}
  let := mapping_preservesPullbacks W
  have hp := (zFirstSquare.{u}.isPushout.map SSet.simplicialSpaceDiscrete).map ofSimplicialObject
  exact (hp.op.map (innerHomFunctor.flip.obj W)).flip

private theorem mapping_lastSquare (W : SimplicialSpace.{u}) :
    IsPullback
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₂₄).op)
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₃₄).op)
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₂).op)
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₃).op) := by
  let := discrete_preservesPushouts.{u}
  let := mapping_preservesPullbacks W
  have hp := (zLastSquare.{u}.isPushout.map SSet.simplicialSpaceDiscrete).map ofSimplicialObject
  exact (hp.op.map (innerHomFunctor.flip.obj W)).flip

private def sourceVertexInEdge (i j : Fin 4) :
    (SSet.stdSimplex.face {i} : SSet.{u}) ⟶ (SSet.stdSimplex.face {i, j} : SSet.{u}) :=
  SSet.Subcomplex.homOfLE ((SSet.stdSimplex.face_le_face_iff _ _).mpr (by simp))

private def targetVertexInEdge (i j : Fin 4) :
    (SSet.stdSimplex.face {j} : SSet.{u}) ⟶ (SSet.stdSimplex.face {i, j} : SSet.{u}) :=
  SSet.Subcomplex.homOfLE ((SSet.stdSimplex.face_le_face_iff _ _).mpr (by simp))

private theorem sourceVertexInEdge_eq (i j : Fin 4) (hij : i < j) :
    (SSet.stdSimplex.faceSingletonIso.{u} i).hom ≫ sourceVertexInEdge i j =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ (SSet.stdSimplex.facePairIso i j hij).hom := by
  unfold sourceVertexInEdge
  apply (cancel_mono (SSet.stdSimplex.face {i, j}).ι).mp
  rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, stdVertex_hom_ι,
    Category.assoc, stdPair_hom_ι]
  change SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ i) =
    SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
      SSet.stdSimplex.map (SimplexCategory.mkOfLe i j hij.le)
  rw [← SSet.stdSimplex.map_comp]
  congr 1
  ext k
  fin_cases k
  rfl

private theorem targetVertexInEdge_eq (i j : Fin 4) (hij : i < j) :
    (SSet.stdSimplex.faceSingletonIso.{u} j).hom ≫ targetVertexInEdge i j =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ (SSet.stdSimplex.facePairIso i j hij).hom := by
  unfold targetVertexInEdge
  apply (cancel_mono (SSet.stdSimplex.face {i, j}).ι).mp
  rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, stdVertex_hom_ι,
    Category.assoc, stdPair_hom_ι]
  change SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ j) =
    SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
      SSet.stdSimplex.map (SimplexCategory.mkOfLe i j hij.le)
  rw [← SSet.stdSimplex.map_comp]
  congr 1
  ext k
  fin_cases k
  rfl

private def edgeFaceMappingIso (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i < j) :
    (discreteSourceMapping W).obj (op (SSet.stdSimplex.face {i, j} : SSet.{u})) ≅
      W.diagram _⦋1⦌ :=
  (discreteSourceMapping W).mapIso (SSet.stdSimplex.facePairIso i j hij).op ≪≫
    discreteYonedaIso W 1

private def vertexFaceMappingIso (W : SimplicialSpace.{u}) (i : Fin 4) :
    (discreteSourceMapping W).obj (op (SSet.stdSimplex.face {i} : SSet.{u})) ≅
      W.diagram _⦋0⦌ :=
  (discreteSourceMapping W).mapIso (SSet.stdSimplex.faceSingletonIso i).op ≪≫
    discreteYonedaIso W 0

private theorem mappedSourceVertex (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i < j) :
    (discreteSourceMapping W).map (sourceVertexInEdge i j).op ≫
        (vertexFaceMappingIso W i).hom =
      (edgeFaceMappingIso W i j hij).hom ≫ W.diagram.δ (1 : Fin 2) := by
  unfold vertexFaceMappingIso edgeFaceMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change (discreteSourceMapping W).map (sourceVertexInEdge i j).op ≫
      (discreteSourceMapping W).map (SSet.stdSimplex.faceSingletonIso i).hom.op ≫
        (discreteYonedaIso W 0).hom =
    (discreteSourceMapping W).map (SSet.stdSimplex.facePairIso i j hij).hom.op ≫
      (discreteYonedaIso W 1).hom ≫ W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op
  have h := congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ (SSet.stdSimplex.face {i, j} : SSet.{u}) =>
      (discreteSourceMapping W).map f.op) (sourceVertexInEdge_eq.{u} i j hij)
  simp only [op_comp, Functor.map_comp] at h
  calc
    _ = (discreteSourceMapping W).map (SSet.stdSimplex.facePairIso i j hij).hom.op ≫
        (discreteSourceMapping W).map (SSet.stdSimplex.δ (1 : Fin 2)).op ≫
          (discreteYonedaIso W 0).hom := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ (discreteYonedaIso W 0).hom) h
    _ = _ := by
      change (discreteSourceMapping W).map (SSet.stdSimplex.facePairIso i j hij).hom.op ≫
        (discreteSourceMapping W).map (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))).op ≫
          (discreteYonedaIso W 0).hom = _
      rw [discreteYonedaIso_naturality_index W (SimplexCategory.δ (1 : Fin 2))]

private theorem mappedTargetVertex (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i < j) :
    (discreteSourceMapping W).map (targetVertexInEdge i j).op ≫
        (vertexFaceMappingIso W j).hom =
      (edgeFaceMappingIso W i j hij).hom ≫ W.diagram.δ (0 : Fin 2) := by
  unfold vertexFaceMappingIso edgeFaceMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change (discreteSourceMapping W).map (targetVertexInEdge i j).op ≫
      (discreteSourceMapping W).map (SSet.stdSimplex.faceSingletonIso j).hom.op ≫
        (discreteYonedaIso W 0).hom =
    (discreteSourceMapping W).map (SSet.stdSimplex.facePairIso i j hij).hom.op ≫
      (discreteYonedaIso W 1).hom ≫ W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op
  have h := congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ (SSet.stdSimplex.face {i, j} : SSet.{u}) =>
      (discreteSourceMapping W).map f.op) (targetVertexInEdge_eq.{u} i j hij)
  simp only [op_comp, Functor.map_comp] at h
  calc
    _ = (discreteSourceMapping W).map (SSet.stdSimplex.facePairIso i j hij).hom.op ≫
        (discreteSourceMapping W).map (SSet.stdSimplex.δ (0 : Fin 2)).op ≫
          (discreteYonedaIso W 0).hom := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ (discreteYonedaIso W 0).hom) h
    _ = _ := by
      change (discreteSourceMapping W).map (SSet.stdSimplex.facePairIso i j hij).hom.op ≫
        (discreteSourceMapping W).map (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))).op ≫
          (discreteYonedaIso W 0).hom = _
      rw [discreteYonedaIso_naturality_index W (SimplexCategory.δ (0 : Fin 2))]

/-- The chosen limit of the original 02 and 12 edges, sharing their target. -/
abbrev inversePairLimit (W : SimplicialSpace.{u}) : SSet.{u} :=
  pullback (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2))

private def zPairDiagramIso (W : SimplicialSpace.{u}) :
    cospan
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₂).op)
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₃).op) ≅
      cospan (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2)) :=
  cospanIsoMk (vertexFaceMappingIso W 2) (edgeFaceMappingIso W 0 2 (by decide))
    (edgeFaceMappingIso W 1 2 (by decide))
    (by exact mappedTargetVertex W 0 2 (by decide))
    (by exact mappedTargetVertex W 1 2 (by decide))

private def zPairMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (zPair : SSet.{u})) ≅ inversePairLimit W :=
  (mapping_firstSquare W).isoPullback ≪≫ lim.mapIso (zPairDiagramIso W)

@[reassoc]
private theorem zPairMappingIso_fst (W : SimplicialSpace.{u}) :
    (zPairMappingIso W).hom ≫ pullback.fst _ _ =
      (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₂₄).op ≫
        (edgeFaceMappingIso W 0 2 (by decide)).hom := by
  have hlim : lim.map (zPairDiagramIso W).hom ≫ limit.π _ WalkingCospan.left =
      limit.π (cospan
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₂).op)
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₃).op))
          WalkingCospan.left ≫ (edgeFaceMappingIso W 0 2 (by decide)).hom :=
    limMap_π _ _
  have hp : (mapping_firstSquare W).isoPullback.hom ≫ limit.π (cospan
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₂).op)
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₃).op))
        WalkingCospan.left =
      (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₂₄).op :=
    (mapping_firstSquare W).isoPullback_hom_fst
  unfold zPairMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [hlim, ← Category.assoc, hp]

@[reassoc]
private theorem zPairMappingIso_snd (W : SimplicialSpace.{u}) :
    (zPairMappingIso W).hom ≫ pullback.snd _ _ =
      (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₃₄).op ≫
        (edgeFaceMappingIso W 1 2 (by decide)).hom := by
  have hlim : lim.map (zPairDiagramIso W).hom ≫ limit.π _ WalkingCospan.right =
      limit.π (cospan
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₂).op)
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₃).op))
          WalkingCospan.right ≫ (edgeFaceMappingIso W 1 2 (by decide)).hom :=
    limMap_π _ _
  have hp : (mapping_firstSquare W).isoPullback.hom ≫ limit.π (cospan
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₂).op)
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₁₃).op))
        WalkingCospan.right =
      (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₃₄).op :=
    (mapping_firstSquare W).isoPullback_hom_snd
  unfold zPairMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [hlim, ← Category.assoc, hp]

private theorem zVertexToPair_eq :
    (SSet.Subcomplex.homOfLE zLastSquare.{u}.le₁₂) =
      sourceVertexInEdge.{u} 1 2 ≫ SSet.Subcomplex.homOfLE zFirstSquare.le₃₄ := by
  ext d t
  rfl

private theorem mappedPairVertex (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₂).op ≫
      (vertexFaceMappingIso W 1).hom =
        (zPairMappingIso W).hom ≫ pullback.snd _ _ ≫ W.diagram.δ (1 : Fin 2) := by
  rw [zVertexToPair_eq]
  simp only [op_comp, Functor.map_comp, Category.assoc]
  rw [mappedSourceVertex W 1 2 (by decide), ← zPairMappingIso_snd_assoc]

/-- The actual finite zig-zag edge limit, ordered 02, 12, 13. -/
abbrev inverseEdgeLimit (W : SimplicialSpace.{u}) : SSet.{u} :=
  pullback (pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2)) ≫
    W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2))

private def zLastDiagramIso (W : SimplicialSpace.{u}) :
    cospan
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₂).op)
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₃).op) ≅
      cospan (pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2)) ≫
        W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2)) :=
  cospanIsoMk (vertexFaceMappingIso W 1) (zPairMappingIso W)
    (edgeFaceMappingIso W 1 3 (by decide)) (mappedPairVertex W)
    (by exact mappedSourceVertex W 1 3 (by decide))

/-- The actual inner mapping object of Z(3) is its original labelled three-edge limit. -/
def zigzagMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (zigzagSubcomplex : SSet.{u})) ≅ inverseEdgeLimit W :=
  (mapping_lastSquare W).isoPullback ≪≫ lim.mapIso (zLastDiagramIso W)

@[reassoc]
private theorem zigzagMappingIso_fst (W : SimplicialSpace.{u}) :
    (zigzagMappingIso W).hom ≫ pullback.fst _ _ =
      (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₂₄).op ≫
        (zPairMappingIso W).hom := by
  have hlim : lim.map (zLastDiagramIso W).hom ≫ limit.π _ WalkingCospan.left =
      limit.π (cospan
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₂).op)
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₃).op))
          WalkingCospan.left ≫ (zPairMappingIso W).hom := limMap_π _ _
  have hp : (mapping_lastSquare W).isoPullback.hom ≫ limit.π (cospan
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₂).op)
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₃).op))
        WalkingCospan.left =
      (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₂₄).op :=
    (mapping_lastSquare W).isoPullback_hom_fst
  unfold zigzagMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [hlim, ← Category.assoc, hp]

@[reassoc]
private theorem zigzagMappingIso_snd (W : SimplicialSpace.{u}) :
    (zigzagMappingIso W).hom ≫ pullback.snd _ _ =
      (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₃₄).op ≫
        (edgeFaceMappingIso W 1 3 (by decide)).hom := by
  have hlim : lim.map (zLastDiagramIso W).hom ≫ limit.π _ WalkingCospan.right =
      limit.π (cospan
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₂).op)
        ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₃).op))
          WalkingCospan.right ≫ (edgeFaceMappingIso W 1 3 (by decide)).hom := limMap_π _ _
  have hp : (mapping_lastSquare W).isoPullback.hom ≫ limit.π (cospan
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₂).op)
      ((discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₁₃).op))
        WalkingCospan.right =
      (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₃₄).op :=
    (mapping_lastSquare W).isoPullback_hom_snd
  unfold zigzagMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [hlim, ← Category.assoc, hp]

/-- The original 02 edge projection of the zig-zag limit. -/
abbrev inverseFirst (W : SimplicialSpace.{u}) : inverseEdgeLimit W ⟶ W.diagram _⦋1⦌ :=
  pullback.fst _ _ ≫ pullback.fst _ _

/-- The original 12 edge projection of the zig-zag limit. -/
abbrev inverseMiddle (W : SimplicialSpace.{u}) : inverseEdgeLimit W ⟶ W.diagram _⦋1⦌ :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- The original 13 edge projection of the zig-zag limit. -/
abbrev inverseLast (W : SimplicialSpace.{u}) : inverseEdgeLimit W ⟶ W.diagram _⦋1⦌ :=
  pullback.snd _ _

/-- The original three-simplex restriction to the exact Z(3) edge limit. -/
def inverseRestriction (W : SimplicialSpace.{u}) : W.diagram _⦋3⦌ ⟶ inverseEdgeLimit W :=
  (discreteYonedaIso W 3).inv ≫
    (discreteSourceMapping W).map zigzagSubcomplex.ι.op ≫ (zigzagMappingIso W).hom

private theorem discrete_precomp_fibration {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (W : SimplicialSpace.{u}) (hW : IsFibrant W) :
    Fibration ((discreteSourceMapping W).map i.op) := by
  have hm : Mono (SSet.simplicialSpaceDiscrete.map i) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [NatTrans.mono_iff_mono_app]
    intro k
    change Mono (i.app n)
    infer_instance
  let f := ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map i)
  have hc : cofibrations SimplicialSpace.{u} f :=
    (HomotopicalAlgebra.cofibration_iff f).mp
      ((ReedyModel.cofibration_iff f).mpr (by infer_instance))
  exact (HomotopicalAlgebra.fibration_iff _).mpr (ReedyModel.inner_precomp_fibration f W hc hW)

/-- Actual Reedy fibrancy supplies the full original Z(3) restriction Kan fibration. -/
theorem inverseRestriction_fibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Fibration (inverseRestriction W) := by
  let := discrete_precomp_fibration zigzagSubcomplex.ι W hW.1
  unfold inverseRestriction
  infer_instance

private theorem mappedFaceRestriction (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i < j) :
    (discreteYonedaIso W 3).inv ≫
        (discreteSourceMapping W).map (SSet.stdSimplex.face {i, j}).ι.op ≫
          (edgeFaceMappingIso W i j hij).hom =
      W.diagram.map (SimplexCategory.mkOfLe i j hij.le).op := by
  unfold edgeFaceMappingIso
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  change (discreteYonedaIso W 3).inv ≫
      (discreteSourceMapping W).map (SSet.stdSimplex.face {i, j}).ι.op ≫
        (discreteSourceMapping W).map (SSet.stdSimplex.facePairIso i j hij).hom.op ≫
          (discreteYonedaIso W 1).hom = _
  have hm :
      (discreteSourceMapping W).map (SSet.stdSimplex.face {i, j}).ι.op ≫
        (discreteSourceMapping W).map (SSet.stdSimplex.facePairIso i j hij).hom.op =
      (discreteSourceMapping W).map
        (SSet.stdSimplex.map (SimplexCategory.mkOfLe i j hij.le)).op := by
    rw [← (discreteSourceMapping W).map_comp, ← op_comp, stdPair_hom_ι]
  have h := congrArg (fun f => (discreteYonedaIso W 3).inv ≫ f ≫
    (discreteYonedaIso W 1).hom) hm
  simp only [Category.assoc] at h
  rw [discreteYonedaIso_naturality_index, Iso.inv_hom_id_assoc] at h
  exact h

private theorem zFirstChain :
    SSet.Subcomplex.homOfLE zFirstSquare.{u}.le₂₄ ≫
      SSet.Subcomplex.homOfLE zLastSquare.le₂₄ ≫ zigzagSubcomplex.ι = zFirst.ι := by
  ext n x
  rfl

private theorem zMiddleChain :
    SSet.Subcomplex.homOfLE zFirstSquare.{u}.le₃₄ ≫
      SSet.Subcomplex.homOfLE zLastSquare.le₂₄ ≫ zigzagSubcomplex.ι = zMiddle.ι := by
  ext n x
  rfl

private theorem zLastChain :
    SSet.Subcomplex.homOfLE zLastSquare.{u}.le₃₄ ≫ zigzagSubcomplex.ι = zLast.ι := by
  ext n x
  rfl

/-- The first restriction projection is the literal original 02 edge. -/
@[reassoc (attr := simp)]
theorem inverseRestriction_first (W : SimplicialSpace.{u}) :
    inverseRestriction W ≫ inverseFirst W =
      W.diagram.map (SimplexCategory.mkOfLe (0 : Fin 4) 2 (by decide)).op := by
  unfold inverseRestriction inverseFirst
  simp only [Category.assoc]
  rw [zigzagMappingIso_fst_assoc, zPairMappingIso_fst]
  have hm :
      (discreteSourceMapping W).map zigzagSubcomplex.ι.op ≫
        (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₂₄).op ≫
          (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₂₄).op =
      (discreteSourceMapping W).map zFirst.ι.op := by
    rw [← (discreteSourceMapping W).map_comp, ← (discreteSourceMapping W).map_comp,
      ← op_comp, ← op_comp, Category.assoc, zFirstChain]
  have h := congrArg (fun f => (discreteYonedaIso W 3).inv ≫ f ≫
    (edgeFaceMappingIso W 0 2 (by decide)).hom) hm
  simp only [Category.assoc] at h
  exact h.trans (mappedFaceRestriction W 0 2 (by decide))

/-- The middle restriction projection is the literal original 12 edge. -/
@[reassoc (attr := simp)]
theorem inverseRestriction_middle (W : SimplicialSpace.{u}) :
    inverseRestriction W ≫ inverseMiddle W =
      W.diagram.map (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)).op := by
  unfold inverseRestriction inverseMiddle
  simp only [Category.assoc]
  rw [zigzagMappingIso_fst_assoc, zPairMappingIso_snd]
  have hm :
      (discreteSourceMapping W).map zigzagSubcomplex.ι.op ≫
        (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₂₄).op ≫
          (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zFirstSquare.le₃₄).op =
      (discreteSourceMapping W).map zMiddle.ι.op := by
    rw [← (discreteSourceMapping W).map_comp, ← (discreteSourceMapping W).map_comp,
      ← op_comp, ← op_comp, Category.assoc, zMiddleChain]
  have h := congrArg (fun f => (discreteYonedaIso W 3).inv ≫ f ≫
    (edgeFaceMappingIso W 1 2 (by decide)).hom) hm
  simp only [Category.assoc] at h
  exact h.trans (mappedFaceRestriction W 1 2 (by decide))

/-- The last restriction projection is the literal original 13 edge. -/
@[reassoc (attr := simp)]
theorem inverseRestriction_last (W : SimplicialSpace.{u}) :
    inverseRestriction W ≫ inverseLast W =
      W.diagram.map (SimplexCategory.mkOfLe (1 : Fin 4) 3 (by decide)).op := by
  unfold inverseRestriction inverseLast
  simp only [Category.assoc]
  rw [zigzagMappingIso_snd]
  have hm :
      (discreteSourceMapping W).map zigzagSubcomplex.ι.op ≫
        (discreteSourceMapping W).map (SSet.Subcomplex.homOfLE zLastSquare.le₃₄).op =
      (discreteSourceMapping W).map zLast.ι.op := by
    rw [← (discreteSourceMapping W).map_comp, ← op_comp, zLastChain]
  have h := congrArg (fun f => (discreteYonedaIso W 3).inv ≫ f ≫
    (edgeFaceMappingIso W 1 3 (by decide)).hom) hm
  simp only [Category.assoc] at h
  exact h.trans (mappedFaceRestriction W 1 3 (by decide))

private def identityPair (W : SimplicialSpace.{u}) : W.diagram _⦋1⦌ ⟶ inversePairLimit W :=
  pullback.lift (W.diagram.δ (0 : Fin 2) ≫ W.diagram.σ (0 : Fin 1)) (𝟙 _) (by
    have h : W.diagram.σ (0 : Fin 1) ≫ W.diagram.δ (0 : Fin 2) = 𝟙 (W.diagram _⦋0⦌) :=
      W.diagram.δ_comp_σ_self (i := (0 : Fin 1))
    rw [Category.assoc, h, Category.comp_id, Category.id_comp])

private theorem identityPair_snd (W : SimplicialSpace.{u}) :
    identityPair W ≫ pullback.snd (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2)) =
      𝟙 (W.diagram _⦋1⦌) :=
  pullback.lift_snd _ _ _

/-- The canonical inverse-test triple keeps g on edge12, with target/source identities on 02/13. -/
def identityTriple (W : SimplicialSpace.{u}) : W.diagram _⦋1⦌ ⟶ inverseEdgeLimit W :=
  pullback.lift (identityPair W) (W.diagram.δ (1 : Fin 2) ≫ W.diagram.σ (0 : Fin 1)) (by
    have h : W.diagram.σ (0 : Fin 1) ≫ W.diagram.δ (1 : Fin 2) = 𝟙 (W.diagram _⦋0⦌) :=
      W.diagram.δ_comp_σ_succ (i := (0 : Fin 1))
    rw [← Category.assoc, identityPair_snd, Category.id_comp, Category.assoc,
      h, Category.comp_id])

/-- In increasing 02/12/13 order, the first edge is the original target identity. -/
@[reassoc (attr := simp)]
theorem identityTriple_first (W : SimplicialSpace.{u}) :
    identityTriple W ≫ inverseFirst W = W.diagram.δ (0 : Fin 2) ≫ W.diagram.σ (0 : Fin 1) := by
  unfold identityTriple inverseFirst
  rw [pullback.lift_fst_assoc]
  unfold identityPair
  rw [pullback.lift_fst]

/-- The inverse-test triple retains the same original middle edge. -/
@[reassoc (attr := simp)]
theorem identityTriple_middle (W : SimplicialSpace.{u}) :
    identityTriple W ≫ inverseMiddle W = 𝟙 (W.diagram _⦋1⦌) := by
  unfold identityTriple inverseMiddle
  rw [pullback.lift_fst_assoc]
  unfold identityPair
  rw [pullback.lift_snd]

/-- In increasing 02/12/13 order, the last edge is the original source identity. -/
@[reassoc (attr := simp)]
theorem identityTriple_last (W : SimplicialSpace.{u}) :
    identityTriple W ≫ inverseLast W = W.diagram.δ (1 : Fin 2) ≫ W.diagram.σ (0 : Fin 1) :=
  pullback.lift_snd _ _ _

private theorem fill_interval {A B : SSet.{u}} (p : A ⟶ B) [Fibration p]
    (i : Fin 2) (a : (Δ[0] : SSet.{u}) ⟶ A) (b : (Δ[1] : SSet.{u}) ⟶ B)
    (ha : a ≫ p = SSet.stdSimplex.δ i ≫ b) :
    ∃ L : (Δ[1] : SSet.{u}) ⟶ A, SSet.stdSimplex.δ i ≫ L = a ∧ L ≫ p = b := by
  let faces : ∀ (j : Fin 2) (_ : j ≠ i.rev), (Δ[0] : SSet.{u}) ⟶ A := fun _ _ => a
  have hc : SSet.horn.IsCompatible (i := i.rev) faces := True.intro
  have hcomm : ∀ (j : Fin 2) (hj : j ≠ i.rev), faces j hj ≫ p = SSet.stdSimplex.δ j ≫ b := by
    intro j hj
    have hji : j = i := by fin_cases i <;> fin_cases j <;> simp_all
    subst j
    exact ha
  obtain ⟨L, hfaces, hL⟩ := hc.exists_lift p b hcomm
  have hi : i ≠ i.rev := by fin_cases i <;> decide
  exact ⟨L, hfaces i hi, hL⟩

private theorem exists_over_target {A B : SSet.{u}} (p : A ⟶ B) [Fibration p]
    {b₀ b₁ : B _⦋0⦌} (e : B.Edge b₀ b₁) (h : ∃ a₁ : A _⦋0⦌, p.app (op ⦋0⦌) a₁ = b₁) :
    ∃ a₀ : A _⦋0⦌, p.app (op ⦋0⦌) a₀ = b₀ := by
  rcases h with ⟨a₁, ha₁⟩
  have hs : SSet.yonedaEquiv.symm a₁ ≫ p =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge := by
    rw [SSet.yonedaEquiv_symm_comp, ha₁, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.Edge.tgt_eq]
  obtain ⟨L, _,
      hL⟩ := fill_interval p 0 (SSet.yonedaEquiv.symm a₁) (SSet.yonedaEquiv.symm e.edge) hs
  let a₀ := SSet.yonedaEquiv (SSet.stdSimplex.δ (1 : Fin 2) ≫ L)
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ B =>
    SSet.yonedaEquiv (SSet.stdSimplex.δ (1 : Fin 2) ≫ f)) hL
  rw [← Category.assoc, SSet.yonedaEquiv_comp] at h
  have he : SSet.yonedaEquiv (SSet.stdSimplex.δ (1 : Fin 2) ≫
      SSet.yonedaEquiv.symm e.edge) = b₀ := by
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, SSet.Edge.src_eq]
  exact ⟨a₀, h.trans he⟩

private theorem image_iff_of_edge {A B : SSet.{u}} (p : A ⟶ B) [Fibration p]
    {b₀ b₁ : B _⦋0⦌} (e : B.Edge b₀ b₁) :
    (∃ a₀ : A _⦋0⦌, p.app (op ⦋0⦌) a₀ = b₀) ↔
      (∃ a₁ : A _⦋0⦌, p.app (op ⦋0⦌) a₁ = b₁) := by
  constructor
  · rintro ⟨a₀, ha₀⟩
    obtain ⟨a₁, _, ha₁, _⟩ := lift_edge p e a₀ ha₀
    exact ⟨a₁, ha₁⟩
  · exact exists_over_target p e

private theorem image_iff_of_component {A B : SSet.{u}} (p : A ⟶ B) [Fibration p]
    {b₀ b₁ : B _⦋0⦌} (h : SSet.π₀.mk b₀ = SSet.π₀.mk b₁) :
    (∃ a₀ : A _⦋0⦌, p.app (op ⦋0⦌) a₀ = b₀) ↔
      (∃ a₁ : A _⦋0⦌, p.app (op ⦋0⦌) a₁ = b₁) := by
  have he := (SSet.π₀.mk_eq_mk_iff b₀ b₁).mp h
  clear h
  induction he with
  | rel x y h => rcases h with ⟨e⟩; exact image_iff_of_edge p e
  | refl => exact Iff.rfl
  | symm x y h ih => exact ih.symm
  | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private def longPair (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    mappingFibre W y y ⨯ mappingFibre W x x ⟶ inversePairLimit W :=
  pullback.lift (prod.fst ≫ mappingFibre.fst W y y)
    (prod.fst ≫ mappingFibre.snd W y y ≫ SSet.yonedaEquiv.symm g) (by
      simp only [Category.assoc, mappingFibre.target_eq, SSet.yonedaEquiv_symm_comp, ht])

private theorem longPair_snd (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    longPair W x y g ht ≫ pullback.snd _ _ =
      prod.fst ≫ mappingFibre.snd W y y ≫ SSet.yonedaEquiv.symm g :=
  pullback.lift_snd _ _ _

private def longLoopPair (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    mappingFibre W y y ⨯ mappingFibre W x x ⟶ inverseEdgeLimit W :=
  pullback.lift (longPair W x y g ht) (prod.snd ≫ mappingFibre.fst W x x) (by
    rw [← Category.assoc, longPair_snd]
    simp only [Category.assoc, mappingFibre.source_eq, SSet.yonedaEquiv_symm_comp, hs]
    have h : (prod.fst : mappingFibre W y y ⨯ mappingFibre W x x ⟶ _) ≫ mappingFibre.snd W y y =
        prod.snd ≫ mappingFibre.snd W x x := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    simpa only [Category.assoc] using congrArg (fun f => f ≫ SSet.yonedaEquiv.symm x) h)

@[reassoc]
private theorem longLoopPair_first (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    longLoopPair W x y g hs ht ≫ inverseFirst W = prod.fst ≫ mappingFibre.fst W y y := by
  unfold longLoopPair inverseFirst
  rw [pullback.lift_fst_assoc]
  unfold longPair
  rw [pullback.lift_fst]

@[reassoc]
private theorem longLoopPair_middle (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    longLoopPair W x y g hs ht ≫ inverseMiddle W =
      prod.fst ≫ mappingFibre.snd W y y ≫ SSet.yonedaEquiv.symm g := by
  unfold longLoopPair inverseMiddle
  rw [pullback.lift_fst_assoc, longPair_snd]

@[reassoc]
private theorem longLoopPair_last (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    longLoopPair W x y g hs ht ≫ inverseLast W = prod.snd ≫ mappingFibre.fst W x x :=
  pullback.lift_snd _ _ _

private theorem inverseVertex_ext (W : SimplicialSpace.{u}) {a b : (inverseEdgeLimit W) _⦋0⦌}
    (h₀ : (inverseFirst W).app (op ⦋0⦌) a = (inverseFirst W).app (op ⦋0⦌) b)
    (h₁ : (inverseMiddle W).app (op ⦋0⦌) a = (inverseMiddle W).app (op ⦋0⦌) b)
    (h₂ : (inverseLast W).app (op ⦋0⦌) a = (inverseLast W).app (op ⦋0⦌) b) : a = b := by
  apply SSet.yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · change SSet.yonedaEquiv.symm a ≫ inverseFirst W = SSet.yonedaEquiv.symm b ≫ inverseFirst W
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h₀]
    · change SSet.yonedaEquiv.symm a ≫ inverseMiddle W = SSet.yonedaEquiv.symm b ≫ inverseMiddle W
      rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h₁]
  · change SSet.yonedaEquiv.symm a ≫ inverseLast W = SSet.yonedaEquiv.symm b ≫ inverseLast W
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h₂]

private theorem longLoopPair_vertex_first (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y)
    (a : (mappingFibre W y y) _⦋0⦌) (b : (mappingFibre W x x) _⦋0⦌) :
    (inverseFirst W).app (op ⦋0⦌) ((longLoopPair W x y g hs ht).app (op ⦋0⦌) (productSimplex a b)) =
      (mappingFibre.fst W y y).app (op ⦋0⦌) a := by
  have h := congrArg (fun f : mappingFibre W y y ⨯ mappingFibre W x x ⟶ W.diagram _⦋1⦌ =>
    f.app (op ⦋0⦌) (productSimplex a b)) (longLoopPair_first W x y g hs ht)
  change _ = (mappingFibre.fst W y y).app (op ⦋0⦌)
    ((prod.fst : mappingFibre W y y ⨯ mappingFibre W x x ⟶ _).app (op ⦋0⦌)
        (productSimplex a b)) at h
  rw [productSimplex_fst] at h
  exact h

private theorem longLoopPair_vertex_middle (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y)
    (a : (mappingFibre W y y) _⦋0⦌) (b : (mappingFibre W x x) _⦋0⦌) :
    (inverseMiddle W).app (op ⦋0⦌) ((longLoopPair W x y g hs ht).app (op ⦋0⦌)
        (productSimplex a b)) = g := by
  have h := congrArg (fun f : mappingFibre W y y ⨯ mappingFibre W x x ⟶ W.diagram _⦋1⦌ =>
    f.app (op ⦋0⦌) (productSimplex a b)) (longLoopPair_middle W x y g hs ht)
  change _ = (SSet.yonedaEquiv.symm g).app (op ⦋0⦌) _ at h
  exact h.trans (point_value_zero g _)

private theorem longLoopPair_vertex_last (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y)
    (a : (mappingFibre W y y) _⦋0⦌) (b : (mappingFibre W x x) _⦋0⦌) :
    (inverseLast W).app (op ⦋0⦌) ((longLoopPair W x y g hs ht).app (op ⦋0⦌) (productSimplex a b)) =
      (mappingFibre.fst W x x).app (op ⦋0⦌) b := by
  have h := congrArg (fun f : mappingFibre W y y ⨯ mappingFibre W x x ⟶ W.diagram _⦋1⦌ =>
    f.app (op ⦋0⦌) (productSimplex a b)) (longLoopPair_last W x y g hs ht)
  change _ = (mappingFibre.fst W x x).app (op ⦋0⦌)
    ((prod.snd : mappingFibre W y y ⨯ mappingFibre W x x ⟶ _).app (op ⦋0⦌)
        (productSimplex a b)) at h
  rw [productSimplex_snd] at h
  exact h

private theorem longLoopPair_identity (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x)
    (ht : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y) :
    (longLoopPair W x y g hs ht).app (op ⦋0⦌)
        (productSimplex (identityVertex W y) (identityVertex W x)) =
      (identityTriple W).app (op ⦋0⦌) g := by
  apply inverseVertex_ext W
  · rw [longLoopPair_vertex_first, identityVertex_fst]
    have h := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) g)
      (identityTriple_first W)
    change (inverseFirst W).app (op ⦋0⦌) ((identityTriple W).app (op ⦋0⦌) g) =
      (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) ((W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g) at h
    rw [ht] at h
    exact h.symm
  · rw [longLoopPair_vertex_middle]
    have h := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) g)
      (identityTriple_middle W)
    exact h.symm
  · rw [longLoopPair_vertex_last, identityVertex_fst]
    have h := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) g)
      (identityTriple_last W)
    change (inverseLast W).app (op ⦋0⦌) ((identityTriple W).app (op ⦋0⦌) g) =
      (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) ((W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g) at h
    rw [hs] at h
    exact h.symm

private def vertex3 (W : SimplicialSpace.{u}) (i : Fin 4) : W.diagram _⦋3⦌ ⟶ W.diagram _⦋0⦌ :=
  W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ i).op

private def interval3 (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i ≤ j) :
    W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ :=
  W.diagram.map (SimplexCategory.mkOfLe i j hij).op

private theorem interval3_source (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i ≤ j) :
    interval3 W i j hij ≫ W.diagram.δ (1 : Fin 2) = vertex3 W i := by
  change W.diagram.map (SimplexCategory.mkOfLe i j hij).op ≫
    W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op =
      W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ i).op
  have h : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.mkOfLe i j hij =
      SimplexCategory.const ⦋0⦌ ⦋3⦌ i := by ext k; fin_cases k; rfl
  simpa only [Functor.map_comp, op_comp] using congrArg (fun f => W.diagram.map f.op) h

private theorem interval3_target (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i ≤ j) :
    interval3 W i j hij ≫ W.diagram.δ (0 : Fin 2) = vertex3 W j := by
  change W.diagram.map (SimplexCategory.mkOfLe i j hij).op ≫
    W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op =
      W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ j).op
  have h : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.mkOfLe i j hij =
      SimplexCategory.const ⦋0⦌ ⦋3⦌ j := by ext k; fin_cases k; rfl
  simpa only [Functor.map_comp, op_comp] using congrArg (fun f => W.diagram.map f.op) h

private theorem interval3_source_apply (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i ≤ j)
    (t : (W.diagram _⦋3⦌) _⦋0⦌) :
    (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) ((interval3 W i j hij).app (op ⦋0⦌) t) =
      (vertex3 W i).app (op ⦋0⦌) t :=
  congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋0⦌ => f.app (op ⦋0⦌) t)
    (interval3_source W i j hij)

private theorem interval3_target_apply (W : SimplicialSpace.{u}) (i j : Fin 4) (hij : i ≤ j)
    (t : (W.diagram _⦋3⦌) _⦋0⦌) :
    (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) ((interval3 W i j hij).app (op ⦋0⦌) t) =
      (vertex3 W j).app (op ⦋0⦌) t :=
  congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋0⦌ => f.app (op ⦋0⦌) t)
    (interval3_target W i j hij)

private theorem face3_interval (W : SimplicialSpace.{u}) (i : Fin 4) (j : Fin 3)
    (a b : Fin 4) (hab : a ≤ b)
    (h : SimplexCategory.δ j ≫ SimplexCategory.δ i = SimplexCategory.mkOfLe a b hab) :
    W.diagram.δ i ≫ W.diagram.δ j = interval3 W a b hab := by
  change W.diagram.map (SimplexCategory.δ i).op ≫ W.diagram.map (SimplexCategory.δ j).op =
    W.diagram.map (SimplexCategory.mkOfLe a b hab).op
  simpa only [Functor.map_comp, op_comp] using congrArg (fun f => W.diagram.map f.op) h

private theorem face3_interval_apply (W : SimplicialSpace.{u}) (i : Fin 4) (j : Fin 3)
    (a b : Fin 4) (hab : a ≤ b)
    (h : SimplexCategory.δ j ≫ SimplexCategory.δ i = SimplexCategory.mkOfLe a b hab)
    (t : (W.diagram _⦋3⦌) _⦋0⦌) :
    (W.diagram.δ j).app (op ⦋0⦌) ((W.diagram.δ i).app (op ⦋0⦌) t) =
      (interval3 W a b hab).app (op ⦋0⦌) t :=
  congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) t)
    (face3_interval W i j a b hab h)

/-- The actual original Z(3) test: a three-simplex over the source/target identity triple. -/
def HasInverseData (W : SimplicialSpace.{u}) (g : (W.diagram _⦋1⦌) _⦋0⦌) : Prop :=
  ∃ t : (W.diagram _⦋3⦌) _⦋0⦌,
    (inverseRestriction W).app (op ⦋0⦌) t = (identityTriple W).app (op ⦋0⦌) g

private theorem inverseRestriction_first_apply (W : SimplicialSpace.{u})
    (t : (W.diagram _⦋3⦌) _⦋0⦌) :
    (inverseFirst W).app (op ⦋0⦌) ((inverseRestriction W).app (op ⦋0⦌) t) =
      (interval3 W 0 2 (by decide)).app (op ⦋0⦌) t :=
  congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) t)
    (inverseRestriction_first W)

private theorem inverseRestriction_middle_apply (W : SimplicialSpace.{u})
    (t : (W.diagram _⦋3⦌) _⦋0⦌) :
    (inverseMiddle W).app (op ⦋0⦌) ((inverseRestriction W).app (op ⦋0⦌) t) =
      (interval3 W 1 2 (by decide)).app (op ⦋0⦌) t :=
  congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) t)
    (inverseRestriction_middle W)

private theorem inverseRestriction_last_apply (W : SimplicialSpace.{u})
    (t : (W.diagram _⦋3⦌) _⦋0⦌) :
    (inverseLast W).app (op ⦋0⦌) ((inverseRestriction W).app (op ⦋0⦌) t) =
      (interval3 W 1 3 (by decide)).app (op ⦋0⦌) t :=
  congrArg (fun f : W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) t)
    (inverseRestriction_last W)

private theorem interval3_consecutive (W : SimplicialSpace.{u}) (k : Fin 3) :
    interval3 W k.castSucc k.succ k.castSucc_lt_succ.le =
      W.diagram.map (SimplexCategory.mkOfSucc k).op := rfl

/-- Intrinsic invertibility supplies the original inverse-test three-simplex.
The initial long edges have identity components; actual Kan lifting corrects them to identities. -/
theorem hasInverseData_of_isEquivalenceEdge (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (g : (W.diagram _⦋1⦌) _⦋0⦌) (hg : IsEquivalenceEdge W hW g) : HasInverseData W g := by
  let x := (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g
  let y := (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g
  let a := fibreVertex W x y g rfl rfl
  let f : (⟨x⟩ : Object W hW) ⟶ (⟨y⟩ : Object W hW) := edgeClass W hW g
  let : IsIso f := hg
  obtain ⟨b, hb⟩ := SSet.π₀.mk_surjective (X := mappingFibre W y x) (inv f)
  obtain ⟨t, ht₀, ht₁, ht₂⟩ := exists_threeSimplex W hW y x y x b a b
  let t012 := (W.diagram.δ (3 : Fin 4)).app (op ⦋0⦌) t
  let t123 := (W.diagram.δ (0 : Fin 4)).app (op ⦋0⦌) t
  have hb012 : (mappingFibre.fst W y x).app (op ⦋0⦌) b =
      (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t012 :=
    ht₀.symm.trans (face3_edge_apply W 3 2 0 (by decide) t).symm
  have ha012 : (mappingFibre.fst W x y).app (op ⦋0⦌) a =
      (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t012 :=
    ht₁.symm.trans (face3_edge_apply W 3 0 1 (by decide) t).symm
  have ha123 : (mappingFibre.fst W x y).app (op ⦋0⦌) a =
      (W.diagram.δ (2 : Fin 3)).app (op ⦋0⦌) t123 :=
    ht₁.symm.trans (face3_edge_apply W 0 2 1 (by decide) t).symm
  have hb123 : (mappingFibre.fst W y x).app (op ⦋0⦌) b =
      (W.diagram.δ (0 : Fin 3)).app (op ⦋0⦌) t123 :=
    ht₂.symm.trans (face3_edge_apply W 0 0 2 (by decide) t).symm
  let L := (triangleMiddle W y x y).app (op ⦋0⦌)
    (triangleOfVertices W y x y t012 b a hb012 ha012)
  let R := (triangleMiddle W x y x).app (op ⦋0⦌)
    (triangleOfVertices W x y x t123 a b ha123 hb123)
  have hL : (mappingFibre.fst W y y).app (op ⦋0⦌) L =
      (interval3 W 0 2 (by decide)).app (op ⦋0⦌) t :=
    (triangle_middle_vertex W y x y t012 b a hb012 ha012).trans
      (face3_interval_apply W 3 1 0 2 (by decide) (by decide) t)
  have hR : (mappingFibre.fst W x x).app (op ⦋0⦌) R =
      (interval3 W 1 3 (by decide)).app (op ⦋0⦌) t :=
    (triangle_middle_vertex W x y x t123 a b ha123 hb123).trans
      (face3_interval_apply W 0 1 1 3 (by decide) (by decide) t)
  have hcL : SSet.π₀.mk L = SSet.π₀.mk (identityVertex W y) := by
    have hc := compose_mk_triangle W hW y x y t012 b a hb012 ha012
    change compose W hW (SSet.π₀.mk b) (SSet.π₀.mk a) = SSet.π₀.mk L at hc
    rw [hb] at hc
    have hi : compose W hW (inv f) (SSet.π₀.mk a) = identity W y :=
      IsIso.inv_hom_id f
    exact hc.symm.trans hi
  have hcR : SSet.π₀.mk R = SSet.π₀.mk (identityVertex W x) := by
    have hc := compose_mk_triangle W hW x y x t123 a b ha123 hb123
    change compose W hW (SSet.π₀.mk a) (SSet.π₀.mk b) = SSet.π₀.mk R at hc
    rw [hb] at hc
    have hi : compose W hW (SSet.π₀.mk a) (inv f) = identity W x :=
      IsIso.hom_inv_id f
    exact hc.symm.trans hi
  have hmid : (interval3 W 1 2 (by decide)).app (op ⦋0⦌) t = g := by
    change (interval3 W (1 : Fin 3).castSucc (1 : Fin 3).succ (by decide)).app (op ⦋0⦌) t = g
    rw [interval3_consecutive, ht₁]
    exact fibreVertex_fst _ _ _ _ _ _
  have hbase : (inverseRestriction W).app (op ⦋0⦌) t =
      (longLoopPair W x y g rfl rfl).app (op ⦋0⦌) (productSimplex L R) := by
    apply inverseVertex_ext W
    · rw [inverseRestriction_first_apply, longLoopPair_vertex_first, hL]
    · rw [inverseRestriction_middle_apply, longLoopPair_vertex_middle, hmid]
    · rw [inverseRestriction_last_apply, longLoopPair_vertex_last, hR]
  have hp : SSet.π₀.mk (productSimplex L R) =
      SSet.π₀.mk (productSimplex (identityVertex W y) (identityVertex W x)) := by
    apply (productComponentEquiv (mappingFibre W y y) (mappingFibre W x x)).injective
    change (SSet.mapπ₀ prod.fst (SSet.π₀.mk (productSimplex L R)),
        SSet.mapπ₀ prod.snd (SSet.π₀.mk (productSimplex L R))) =
      (SSet.mapπ₀ prod.fst (SSet.π₀.mk (productSimplex (identityVertex W y) (identityVertex W x))),
        SSet.mapπ₀ prod.snd (SSet.π₀.mk (productSimplex (identityVertex W y) (identityVertex W x))))
    simp only [SSet.mapπ₀_mk, productSimplex_fst, productSimplex_snd, hcL, hcR]
  have hπ : SSet.π₀.mk ((inverseRestriction W).app (op ⦋0⦌) t) =
      SSet.π₀.mk ((identityTriple W).app (op ⦋0⦌) g) := by
    rw [hbase]
    have h := congrArg (SSet.mapπ₀ (longLoopPair W x y g rfl rfl)) hp
    rw [SSet.mapπ₀_mk, SSet.mapπ₀_mk, longLoopPair_identity] at h
    exact h
  let : Fibration (inverseRestriction W) := inverseRestriction_fibration W hW
  exact (image_iff_of_component (inverseRestriction W) hπ).mp ⟨t, rfl⟩

private theorem identity_edge_source (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) ((W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x) = x := by
  rw [← identityVertex_fst]
  exact fibreVertex_source W x x (identityVertex W x)

private theorem identity_edge_target (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) ((W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x) = x := by
  rw [← identityVertex_fst]
  exact fibreVertex_target W x x (identityVertex W x)

/-- The two original faces of an inverse-test three-simplex give genuine left and right inverses. -/
theorem isEquivalenceEdge_of_hasInverseData (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (g : (W.diagram _⦋1⦌) _⦋0⦌) (hg : HasInverseData W g) : IsEquivalenceEdge W hW g := by
  obtain ⟨t, ht⟩ := hg
  let x := (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g
  let y := (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g
  have h02 : (interval3 W 0 2 (by decide)).app (op ⦋0⦌) t =
      (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) y := by
    have h := congrArg ((inverseFirst W).app (op ⦋0⦌)) ht
    rw [inverseRestriction_first_apply] at h
    have hi := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) g)
      (identityTriple_first W)
    exact h.trans hi
  have h12 : (interval3 W 1 2 (by decide)).app (op ⦋0⦌) t = g := by
    have h := congrArg ((inverseMiddle W).app (op ⦋0⦌)) ht
    rw [inverseRestriction_middle_apply] at h
    have hi := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) g)
      (identityTriple_middle W)
    exact h.trans hi
  have h13 : (interval3 W 1 3 (by decide)).app (op ⦋0⦌) t =
      (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x := by
    have h := congrArg ((inverseLast W).app (op ⦋0⦌)) ht
    rw [inverseRestriction_last_apply] at h
    have hi := congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋1⦌ => f.app (op ⦋0⦌) g)
      (identityTriple_last W)
    exact h.trans hi
  have hv0 : (vertex3 W 0).app (op ⦋0⦌) t = y :=
    (interval3_source_apply W 0 2 (by decide) t).symm.trans
      ((congrArg ((W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌)) h02).trans (identity_edge_source W y))
  have hv1 : (vertex3 W 1).app (op ⦋0⦌) t = x :=
    (interval3_source_apply W 1 2 (by decide) t).symm.trans
      (congrArg ((W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌)) h12)
  have hv2 : (vertex3 W 2).app (op ⦋0⦌) t = y :=
    (interval3_target_apply W 1 2 (by decide) t).symm.trans
      (congrArg ((W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌)) h12)
  have hv3 : (vertex3 W 3).app (op ⦋0⦌) t = x :=
    (interval3_target_apply W 1 3 (by decide) t).symm.trans
      ((congrArg ((W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌)) h13).trans (identity_edge_target W x))
  let a := fibreVertex W x y g rfl rfl
  let b := fibreVertex W y x ((interval3 W 0 1 (by decide)).app (op ⦋0⦌) t)
    ((interval3_source_apply W 0 1 (by decide) t).trans hv0)
    ((interval3_target_apply W 0 1 (by decide) t).trans hv1)
  let c := fibreVertex W y x ((interval3 W 2 3 (by decide)).app (op ⦋0⦌) t)
    ((interval3_source_apply W 2 3 (by decide) t).trans hv2)
    ((interval3_target_apply W 2 3 (by decide) t).trans hv3)
  have hleft : compose W hW (SSet.π₀.mk b) (SSet.π₀.mk a) = identity W y := by
    apply compose_of_original_triangle W hW ((W.diagram.δ (3 : Fin 4)).app (op ⦋0⦌) t)
      b a (identityVertex W y)
    · exact (fibreVertex_fst _ _ _ _ _ _).trans
        (face3_interval_apply W 3 2 0 1 (by decide) (by decide) t).symm
    · exact (fibreVertex_fst _ _ _ _ _ _).trans
        (h12.symm.trans (face3_interval_apply W 3 0 1 2 (by decide) (by decide) t).symm)
    · exact (identityVertex_fst W y).trans
        (h02.symm.trans (face3_interval_apply W 3 1 0 2 (by decide) (by decide) t).symm)
  have hright : compose W hW (SSet.π₀.mk a) (SSet.π₀.mk c) = identity W x := by
    apply compose_of_original_triangle W hW ((W.diagram.δ (0 : Fin 4)).app (op ⦋0⦌) t)
      a c (identityVertex W x)
    · exact (fibreVertex_fst _ _ _ _ _ _).trans
        (h12.symm.trans (face3_interval_apply W 0 2 1 2 (by decide) (by decide) t).symm)
    · exact (fibreVertex_fst _ _ _ _ _ _).trans
        (face3_interval_apply W 0 0 2 3 (by decide) (by decide) t).symm
    · exact (identityVertex_fst W x).trans
        (h13.symm.trans (face3_interval_apply W 0 1 1 3 (by decide) (by decide) t).symm)
  let f : (⟨x⟩ : Object W hW) ⟶ (⟨y⟩ : Object W hW) := edgeClass W hW g
  let l : (⟨y⟩ : Object W hW) ⟶ (⟨x⟩ : Object W hW) := SSet.π₀.mk b
  let r : (⟨y⟩ : Object W hW) ⟶ (⟨x⟩ : Object W hW) := SSet.π₀.mk c
  have hl : l ≫ f = 𝟙 (⟨y⟩ : Object W hW) := hleft
  have hr : f ≫ r = 𝟙 (⟨x⟩ : Object W hW) := hright
  have he : l = r := by
    calc
      l = l ≫ 𝟙 (⟨x⟩ : Object W hW) := (Category.comp_id l).symm
      _ = l ≫ (f ≫ r) := by rw [hr]
      _ = (l ≫ f) ≫ r := (Category.assoc l f r).symm
      _ = r := by rw [hl, Category.id_comp]
  exact ⟨⟨l, he.symm ▸ hr, hl⟩⟩

/-- Intrinsic equivalences are exactly the original three-simplex inverse test. -/
theorem isEquivalenceEdge_iff_hasInverseData (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (g : (W.diagram _⦋1⦌) _⦋0⦌) : IsEquivalenceEdge W hW g ↔ HasInverseData W g :=
  ⟨hasInverseData_of_isEquivalenceEdge W hW g, isEquivalenceEdge_of_hasInverseData W hW g⟩

/-- Intrinsic equivalence is stable along every original W₁ edge, including moving endpoints. -/
theorem isEquivalenceEdge_iff_of_edge (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {g g' : (W.diagram _⦋1⦌) _⦋0⦌} (e : (W.diagram _⦋1⦌).Edge g g') :
    IsEquivalenceEdge W hW g ↔ IsEquivalenceEdge W hW g' := by
  rw [isEquivalenceEdge_iff_hasInverseData, isEquivalenceEdge_iff_hasInverseData]
  let : Fibration (inverseRestriction W) := inverseRestriction_fibration W hW
  exact image_iff_of_edge (inverseRestriction W) (e.map (identityTriple W))

/-- Intrinsic equivalence depends only on the actual W₁ component, with no fixed endpoint
premise. -/
theorem isEquivalenceEdge_iff_of_component (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {g g' : (W.diagram _⦋1⦌) _⦋0⦌} (h : SSet.π₀.mk g = SSet.π₀.mk g') :
    IsEquivalenceEdge W hW g ↔ IsEquivalenceEdge W hW g' := by
  rw [isEquivalenceEdge_iff_hasInverseData, isEquivalenceEdge_iff_hasInverseData]
  let : Fibration (inverseRestriction W) := inverseRestriction_fibration W hW
  have hi := congrArg (SSet.mapπ₀ (identityTriple W)) h
  rw [SSet.mapπ₀_mk, SSet.mapπ₀_mk] at hi
  exact image_iff_of_component (inverseRestriction W) hi

/-- The actual W₁ components containing intrinsic equivalence arrows. -/
def equivalenceComponents (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Set (SSet.π₀ (W.diagram _⦋1⦌)) :=
  {c | ∃ g : (W.diagram _⦋1⦌) _⦋0⦌, SSet.π₀.mk g = c ∧ IsEquivalenceEdge W hW g}

/-- The equivalence-arrow subcomplex is the actual union of those original W₁ components. -/
def equivalenceSubcomplex (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (W.diagram _⦋1⦌).Subcomplex :=
  ⨆ c : {c // c ∈ equivalenceComponents W hW}, SSet.π₀.component c.val

/-- All-degree membership is tested by the literal original zeroth vertex. -/
theorem mem_equivalenceSubcomplex (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (n : SimplexCategoryᵒᵖ) (q : (W.diagram _⦋1⦌).obj n) :
    q ∈ (equivalenceSubcomplex W hW).obj n ↔
      IsEquivalenceEdge W hW ((W.diagram _⦋1⦌).map (SimplexCategory.const ⦋0⦌ n.unop 0).op q) := by
  rw [equivalenceSubcomplex, Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨c, g, hg, hP⟩, hq⟩
    change SSet.π₀.mk ((W.diagram _⦋1⦌).map (SimplexCategory.const ⦋0⦌ n.unop 0).op q) = c at hq
    exact (isEquivalenceEdge_iff_of_component W hW (hq.trans hg.symm)).mpr hP
  · intro hq
    let g := (W.diagram _⦋1⦌).map (SimplexCategory.const ⦋0⦌ n.unop 0).op q
    exact ⟨⟨SSet.π₀.mk g, g, rfl, hq⟩, rfl⟩

/-- Its original vertices are exactly the intrinsically invertible edges. -/
theorem mem_equivalenceSubcomplex_zero (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (g : (W.diagram _⦋1⦌) _⦋0⦌) :
    g ∈ (equivalenceSubcomplex W hW).obj (op ⦋0⦌) ↔ IsEquivalenceEdge W hW g := by
  simpa using mem_equivalenceSubcomplex W hW (op ⦋0⦌) g

/-- Every original vertex of an equivalence simplex recognizes the same membership. -/
theorem mem_equivalenceSubcomplex_iff_vertex (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (n : SimplexCategoryᵒᵖ) (q : (W.diagram _⦋1⦌).obj n) (α : ⦋0⦌ ⟶ n.unop) :
    q ∈ (equivalenceSubcomplex W hW).obj n ↔
      IsEquivalenceEdge W hW ((W.diagram _⦋1⦌).map α.op q) := by
  rw [mem_equivalenceSubcomplex]
  let c := SSet.π₀.mk ((W.diagram _⦋1⦌).map (SimplexCategory.const ⦋0⦌ n.unop 0).op q)
  have hq : q ∈ (SSet.π₀.component c).obj n := rfl
  have ha := (SSet.π₀.component c).map α.op hq
  have h : SSet.π₀.mk ((W.diagram _⦋1⦌).map α.op q) = c := by simpa using ha
  exact isEquivalenceEdge_iff_of_component W hW h.symm

/-- Every original simplicial-space map restricts to the constructed equivalence subcomplexes. -/
def equivalenceMap {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    (equivalenceSubcomplex W hW : SSet) ⟶ (equivalenceSubcomplex V hV : SSet) :=
  SSet.Subcomplex.lift ((equivalenceSubcomplex W hW).ι ≫ f.hom.app (op ⦋1⦌)) (by
    intro n q hq
    rcases hq with ⟨a, rfl⟩
    rw [mem_equivalenceSubcomplex]
    change IsEquivalenceEdge V hV
      ((V.diagram _⦋1⦌).map (SimplexCategory.const ⦋0⦌ n.unop 0).op
        ((f.hom.app (op ⦋1⦌)).app n a.val))
    rw [← (f.hom.app (op ⦋1⦌)).naturality_apply]
    exact isEquivalenceEdge_map f hW hV _
      ((mem_equivalenceSubcomplex W hW n a.val).mp a.property))

/-- The restriction retains the original W₁ map and its original inclusion. -/
@[reassoc (attr := simp)]
theorem equivalenceMap_ι {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    equivalenceMap f hW hV ≫ (equivalenceSubcomplex V hV).ι =
      (equivalenceSubcomplex W hW).ι ≫ f.hom.app (op ⦋1⦌) :=
  SSet.Subcomplex.lift_ι _ _

/-- Original identity maps induce identity maps of the equivalence subcomplex. -/
theorem equivalenceMap_id (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    equivalenceMap (𝟙 W) hW hW = 𝟙 (equivalenceSubcomplex W hW : SSet) := by
  apply (cancel_mono (equivalenceSubcomplex W hW).ι).mp
  rw [equivalenceMap_ι, Category.id_comp]
  rfl

/-- Original composites induce actual composites on the equivalence subcomplexes. -/
theorem equivalenceMap_comp {W V U : SimplicialSpace.{u}} (f : W ⟶ V) (g : V ⟶ U)
    (hW : segalSpaces W) (hV : segalSpaces V) (hU : segalSpaces U) :
    equivalenceMap (f ≫ g) hW hU = equivalenceMap f hW hV ≫ equivalenceMap g hV hU := by
  apply (cancel_mono (equivalenceSubcomplex U hU).ι).mp
  rw [equivalenceMap_ι, Category.assoc, equivalenceMap_ι, equivalenceMap_ι_assoc]
  rfl

/-- The literal original identity degeneracy factors through the equivalence subcomplex. -/
def equivalenceIdentity (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    W.diagram _⦋0⦌ ⟶ (equivalenceSubcomplex W hW : SSet) :=
  SSet.Subcomplex.lift (W.diagram.σ (0 : Fin 1)) (by
    intro n q hq
    rcases hq with ⟨a, rfl⟩
    rw [mem_equivalenceSubcomplex, ← (W.diagram.σ (0 : Fin 1)).naturality_apply]
    exact identity_isEquivalenceEdge W hW _)

/-- The constructed factor is exactly the original σ₀ after the original inclusion. -/
@[reassoc (attr := simp)]
theorem equivalenceIdentity_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    equivalenceIdentity W hW ≫ (equivalenceSubcomplex W hW).ι = W.diagram.σ (0 : Fin 1) :=
  SSet.Subcomplex.lift_ι _ _

/-- The original source d₁ on the equivalence-arrow subcomplex. -/
def equivalenceSource (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (equivalenceSubcomplex W hW : SSet) ⟶ W.diagram _⦋0⦌ :=
  (equivalenceSubcomplex W hW).ι ≫ W.diagram.δ (1 : Fin 2)

/-- The original target d₀ on the equivalence-arrow subcomplex. -/
def equivalenceTarget (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (equivalenceSubcomplex W hW : SSet) ⟶ W.diagram _⦋0⦌ :=
  (equivalenceSubcomplex W hW).ι ≫ W.diagram.δ (0 : Fin 2)

/-- Intrinsic object equivalence classes are actual isomorphism classes of the constructed
category. -/
abbrev ObjectQuotient (W : SimplicialSpace.{u}) (hW : segalSpaces W) : Type u :=
  Quotient (CategoryTheory.isIsomorphicSetoid (Object W hW))

/-- The quotient map is defined on the original W₀ vertices. -/
def objectClass (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) : ObjectQuotient W hW := Quotient.mk _ ⟨x⟩

/-- Equality of object classes is precisely intrinsic isomorphism, without a completeness
premise. -/
theorem objectClass_eq_iff (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    objectClass W hW x = objectClass W hW y ↔
      Nonempty ((⟨x⟩ : Object W hW) ≅ (⟨y⟩ : Object W hW)) :=
  Quotient.eq

/-- The actual equivalence-arrow vertices and original object map form a cofork. -/
def objectVertexCofork (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Cofork ((equivalenceSource W hW).app (op ⦋0⦌)) ((equivalenceTarget W hW).app (op ⦋0⦌)) :=
  Cofork.ofπ (↾(objectClass W hW)) (by
    ext a
    change objectClass W hW ((W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) a.val) =
      objectClass W hW ((W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) a.val)
    apply (objectClass_eq_iff W hW _ _).mpr
    let : IsIso (edgeClass W hW a.val) :=
      (mem_equivalenceSubcomplex_zero W hW a.val).mp a.property
    exact ⟨asIso (edgeClass W hW a.val)⟩)

private theorem vertexCofork_identifies_iso (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (s : Cofork ((equivalenceSource W hW).app (op ⦋0⦌)) ((equivalenceTarget W hW).app (op ⦋0⦌)))
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} (e : (⟨x⟩ : Object W hW) ≅ (⟨y⟩ : Object W hW)) :
    s.π x = s.π y := by
  obtain ⟨a, ha⟩ := SSet.π₀.mk_surjective (X := mappingFibre W x y) e.hom
  have hi : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk a) := by
    rw [ha]
    infer_instance
  let g := (mappingFibre.fst W x y).app (op ⦋0⦌) a
  have hg : IsEquivalenceEdge W hW g := (isEquivalenceEdge_iff_of_fibre W hW g a rfl).mpr hi
  let b : (equivalenceSubcomplex W hW : SSet) _⦋0⦌ :=
    ⟨g, (mem_equivalenceSubcomplex_zero W hW g).mpr hg⟩
  have h := congrArg (fun f : (equivalenceSubcomplex W hW : SSet) _⦋0⦌ ⟶ s.pt => f b) s.condition
  change s.π ((W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g) =
    s.π ((W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g) at h
  dsimp only [g] at h
  rw [fibreVertex_source, fibreVertex_target] at h
  exact h

/-- The quotient is the coequalizer of the actual source and target on equivalence-arrow
vertices. -/
def isColimitObjectVertexCofork (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IsColimit (objectVertexCofork W hW) :=
  Cofork.IsColimit.mk _
    (fun s => ↾(Quotient.lift (fun a : Object W hW => s.π a.vertex)
      (by rintro a b ⟨e⟩; exact vertexCofork_identifies_iso W hW s e)))
    (fun _ => rfl)
    (fun s m hm => by
      ext q
      refine Quotient.inductionOn q ?_
      intro a
      exact congrArg (fun f : (W.diagram _⦋0⦌) _⦋0⦌ ⟶ s.pt => f a.vertex) hm)

/-- An original equivalence arrow identifies its actual source and target object classes. -/
theorem objectClass_eq_of_equivalence (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (g : (W.diagram _⦋1⦌) _⦋0⦌) (hg : IsEquivalenceEdge W hW g) :
    objectClass W hW ((W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g) =
      objectClass W hW ((W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g) := by
  apply (objectClass_eq_iff W hW _ _).mpr
  let : IsIso (edgeClass W hW g) := hg
  exact ⟨asIso (edgeClass W hW g)⟩

private theorem endpoint_vertex_fst (W : SimplicialSpace.{u})
    (g : (W.diagram _⦋1⦌) _⦋0⦌) :
    (prod.fst : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ _).app (op ⦋0⦌)
        ((mappingEndpoint W).app (op ⦋0⦌) g) =
      (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g :=
  congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋0⦌ => f.app (op ⦋0⦌) g)
    (mappingEndpoint_fst W)

private theorem endpoint_vertex_snd (W : SimplicialSpace.{u})
    (g : (W.diagram _⦋1⦌) _⦋0⦌) :
    (prod.snd : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ _).app (op ⦋0⦌)
        ((mappingEndpoint W).app (op ⦋0⦌) g) =
      (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g :=
  congrArg (fun f : W.diagram _⦋1⦌ ⟶ W.diagram _⦋0⦌ => f.app (op ⦋0⦌) g)
    (mappingEndpoint_snd W)

/-- Every original W₀ path identifies intrinsic object classes.
Its actual endpoint lift starts at the identity and stays in the equivalence component. -/
theorem objectClass_eq_of_edge (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} (e : (W.diagram _⦋0⦌).Edge x y) :
    objectClass W hW x = objectClass W hW y := by
  let a := (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x
  have ha : (mappingEndpoint W).app (op ⦋0⦌) a = productSimplex x x := by
    apply productSimplex_ext
    · rw [endpoint_vertex_fst, productSimplex_fst]
      exact identity_edge_source W x
    · rw [endpoint_vertex_snd, productSimplex_snd]
      exact identity_edge_target W x
  let : Fibration (mappingEndpoint W) := ReedyModel.mappingEndpoint_fibration W hW.1
  obtain ⟨g, l, hg, _⟩ := lift_edge (mappingEndpoint W) (productEdge (SSet.Edge.id x) e) a ha
  have hx : (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g = x := by
    have h := congrArg ((prod.fst : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ _).app (op ⦋0⦌)) hg
    rw [endpoint_vertex_fst, productSimplex_fst] at h
    exact h
  have hy : (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g = y := by
    have h := congrArg ((prod.snd : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ _).app (op ⦋0⦌)) hg
    rw [endpoint_vertex_snd, productSimplex_snd] at h
    exact h
  have hP : IsEquivalenceEdge W hW g :=
    (isEquivalenceEdge_iff_of_edge W hW l).mp (identity_isEquivalenceEdge W hW x)
  simpa only [hx, hy] using objectClass_eq_of_equivalence W hW g hP

/-- The intrinsic object quotient receives the original W₀ component map. -/
def objectComponentClass (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.π₀ (W.diagram _⦋0⦌) → ObjectQuotient W hW :=
  SSet.π₀.lift (objectClass W hW) (fun {_ _} e => objectClass_eq_of_edge W hW e)

/-- The component quotient retains the same original object class on every vertex. -/
@[simp]
theorem objectComponentClass_mk (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    objectComponentClass W hW (SSet.π₀.mk x) = objectClass W hW x := rfl

/-- The original component source and target maps form the intrinsic object cofork. -/
def objectComponentCofork (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Cofork (↾(SSet.mapπ₀ (equivalenceSource W hW))) (↾(SSet.mapπ₀ (equivalenceTarget W hW))) :=
  Cofork.ofπ (↾(objectComponentClass W hW)) (by
    ext c
    change objectComponentClass W hW (SSet.mapπ₀ (equivalenceSource W hW) c) =
      objectComponentClass W hW (SSet.mapπ₀ (equivalenceTarget W hW) c)
    induction c using SSet.π₀.rec with
    | mk a =>
      rw [SSet.mapπ₀_mk, SSet.mapπ₀_mk, objectComponentClass_mk, objectComponentClass_mk]
      exact objectClass_eq_of_equivalence W hW a.val
        ((mem_equivalenceSubcomplex_zero W hW a.val).mp a.property))

private def vertexCoforkOfComponent (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (s : Cofork (↾(SSet.mapπ₀ (equivalenceSource W hW))) (↾(SSet.mapπ₀ (equivalenceTarget W hW)))) :
    Cofork ((equivalenceSource W hW).app (op ⦋0⦌)) ((equivalenceTarget W hW).app (op ⦋0⦌)) :=
  Cofork.ofπ (↾(fun x => s.π (SSet.π₀.mk x))) (by
    ext a
    change s.π (SSet.π₀.mk ((equivalenceSource W hW).app (op ⦋0⦌) a)) =
      s.π (SSet.π₀.mk ((equivalenceTarget W hW).app (op ⦋0⦌) a))
    have h := congrArg
      (fun f : SSet.π₀ (equivalenceSubcomplex W hW : SSet) ⟶ s.pt => f (SSet.π₀.mk a)) s.condition
    change s.π (SSet.mapπ₀ (equivalenceSource W hW) (SSet.π₀.mk a)) =
      s.π (SSet.mapπ₀ (equivalenceTarget W hW) (SSet.π₀.mk a)) at h
    rw [SSet.mapπ₀_mk, SSet.mapπ₀_mk] at h
    exact h)

/-- The object equivalence quotient is the genuine coequalizer π₀(W_equiv) ⇉ π₀(W₀). -/
def isColimitObjectComponentCofork (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IsColimit (objectComponentCofork W hW) :=
  Cofork.IsColimit.mk _
    (fun s => (isColimitObjectVertexCofork W hW).desc (vertexCoforkOfComponent W hW s))
    (fun s => by
      ext c
      induction c using SSet.π₀.rec with
      | mk x =>
        exact congrArg (fun f : (W.diagram _⦋0⦌) _⦋0⦌ ⟶ s.pt => f x)
          (Cofork.IsColimit.π_desc (t := vertexCoforkOfComponent W hW s)
              (isColimitObjectVertexCofork W hW)))
    (fun s m hm => by
      apply Cofork.IsColimit.hom_ext (isColimitObjectVertexCofork W hW)
      ext x
      exact congrArg (fun f : SSet.π₀ (W.diagram _⦋0⦌) ⟶ s.pt => f (SSet.π₀.mk x)) hm)

/-- The actual intrinsic functor induces the original map of object equivalence quotients. -/
def objectQuotientMap {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) : ObjectQuotient W hW → ObjectQuotient V hV :=
  Quotient.map (map f hW hV).obj (by rintro a b ⟨e⟩; exact ⟨(map f hW hV).mapIso e⟩)

/-- The quotient functor uses the literal original map on W₀ vertices. -/
@[simp]
theorem objectQuotientMap_class {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    objectQuotientMap f hW hV (objectClass W hW x) = objectClass V hV (mappingVertexMap f x) := rfl

/-- Original identity maps induce identity maps on the actual object quotient. -/
theorem objectQuotientMap_id (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    objectQuotientMap (𝟙 W) hW hW = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  rfl

/-- Original composites induce composites on the actual object quotient. -/
theorem objectQuotientMap_comp {W V U : SimplicialSpace.{u}} (f : W ⟶ V) (g : V ⟶ U)
    (hW : segalSpaces W) (hV : segalSpaces V) (hU : segalSpaces U) :
    objectQuotientMap (f ≫ g) hW hU = objectQuotientMap g hV hU ∘ objectQuotientMap f hW hV := by
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  rfl

/-- The original W₀ component map commutes with the actual intrinsic object quotient map. -/
theorem objectComponentClass_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) (c : SSet.π₀ (W.diagram _⦋0⦌)) :
    objectQuotientMap f hW hV (objectComponentClass W hW c) =
      objectComponentClass V hV (SSet.mapπ₀ (f.hom.app (op ⦋0⦌)) c) := by
  induction c using SSet.π₀.rec with
  | mk x => rfl

/-- Equivalence-subcomplex source naturality retains the literal original d₁ and f₀. -/
@[reassoc]
theorem equivalenceSource_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    equivalenceMap f hW hV ≫ equivalenceSource V hV =
      equivalenceSource W hW ≫ f.hom.app (op ⦋0⦌) := by
  unfold equivalenceSource
  rw [← Category.assoc, equivalenceMap_ι, Category.assoc]
  rw [← SimplicialObject.δ_naturality f.hom (1 : Fin 2), ← Category.assoc]

/-- Equivalence-subcomplex target naturality retains the literal original d₀ and f₀. -/
@[reassoc]
theorem equivalenceTarget_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    equivalenceMap f hW hV ≫ equivalenceTarget V hV =
      equivalenceTarget W hW ≫ f.hom.app (op ⦋0⦌) := by
  unfold equivalenceTarget
  rw [← Category.assoc, equivalenceMap_ι, Category.assoc]
  rw [← SimplicialObject.δ_naturality f.hom (0 : Fin 2), ← Category.assoc]

/-- The factored original degeneracy is natural for every original simplicial-space map. -/
@[reassoc]
theorem equivalenceIdentity_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    equivalenceIdentity W hW ≫ equivalenceMap f hW hV =
      f.hom.app (op ⦋0⦌) ≫ equivalenceIdentity V hV := by
  apply (cancel_mono (equivalenceSubcomplex V hV).ι).mp
  rw [Category.assoc, equivalenceMap_ι, equivalenceIdentity_ι_assoc, Category.assoc,
    equivalenceIdentity_ι]
  exact SimplicialObject.σ_naturality f.hom (0 : Fin 1)

end SegalHomotopy

end SimplicialSpace
