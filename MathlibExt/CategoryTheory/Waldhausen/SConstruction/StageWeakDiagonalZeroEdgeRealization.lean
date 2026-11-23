/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalEdgeNormalization
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0WeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoid

/-!
# Realized normalization of zero-valued weak-stage edges

An arbitrary edge in the weak-stage diagonal is normalized in the simplicial
fundamental groupoid by its coherent zero-to-vertex connectors and the
canonical object edge of its Stage-one off-diagonal value.  When that value
is a zero object, the canonical object edge becomes the identity.  Realizing
the resulting equation gives a homotopy from the realized edge followed by
the inverse target connector to the inverse source connector.

This is only a reusable path-homotopy adapter.  It asserts no equality of
paths, pointed-map naturality, loop-map statement, weak equivalence,
additivity theorem, spectrum result, or Q/S comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial ZeroObject
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C]
  [WaldhausenCategory C]

private theorem objectEdge_homMk_eq_id_of_isZero
    (X : C) (hX : IsZero X) :
    SSet.FundamentalGroupoid.homMk (stageWeakDiagonalObjectEdge C X) =
      𝟙 (SSet.FundamentalGroupoid.mk (stageWeakDiagonalZeroVertex C)) := by
  let z := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalObjectEdge C (0 : C))
  have hCof : IsCofibration (C := C) (𝟙 (0 : C)) :=
    WaldhausenCategory.zero_isCofibration _ _
  have hSeq : IsCofibrationSequence (C := C) (𝟙 (0 : C)) (𝟙 (0 : C)) :=
    ⟨hCof, 𝟙 (0 : C), 𝟙 (0 : C), IsPushout.of_id_fst⟩
  have hmul :=
    (stageWeakDiagonalCofiberCompStruct C
      (𝟙 (0 : C)) (𝟙 (0 : C)) hSeq).homMk_comp
  have hz : z = 𝟙 _ := by
    rw [← cancel_epi z]
    simpa only [Category.comp_id, z] using hmul
  let e := hX.isoZero
  have he : IsWeakEquivalence e.hom :=
    (WaldhausenCategory.weakEquivalences (C := C)).of_isIso e.hom
  exact (stageWeakDiagonalObjectEdge_homMk_eq_of_weakEquivalence
    C e.hom he).trans hz

/-- If the Stage-one off-diagonal value of an edge is zero, then the realized
edge followed by the inverse zero connector at its target is homotopic to the
inverse zero connector at its source. -/
theorem stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
    {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
    (e : (stageWeakDiagonal C).Edge x y)
    (hzero : IsZero
      ((stageOneEval C).obj (ComposableArrows.left e.edge).obj)) :
    ((TopCat.pathEquiv (SSet.realizedEdgePath e)).trans
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalZeroToVertexEdge C y))).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalZeroToVertexEdge C x))).symm := by
  let R := SSet.realizationFundamentalGroupoidFunctor (stageWeakDiagonal C)
  have hnorm := stageWeakDiagonalEdge_normalization C e
  have hzeroEdge := objectEdge_homMk_eq_id_of_isZero C _ hzero
  rw [hzeroEdge] at hnorm
  have hmap := congrArg (fun q => R.map q) hnorm
  simp only [Functor.map_comp] at hmap
  rw [Functor.map_inv] at hmap
  rw [R.map_id] at hmap
  have hcx := SSet.realizationFundamentalGroupoidFunctor_map_homMk
    (stageWeakDiagonal C) (stageWeakDiagonalZeroToVertexEdge C x)
  have hcy := SSet.realizationFundamentalGroupoidFunctor_map_homMk
    (stageWeakDiagonal C) (stageWeakDiagonalZeroToVertexEdge C y)
  have he := SSet.realizationFundamentalGroupoidFunctor_map_homMk
    (stageWeakDiagonal C) e
  let qx : _root_.FundamentalGroupoid.mk
        (SSet.realizedVertex (stageWeakDiagonalZeroVertex C)) ⟶
      _root_.FundamentalGroupoid.mk (SSet.realizedVertex x) :=
    Path.Homotopic.Quotient.mk
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalZeroToVertexEdge C x)))
  let qe : _root_.FundamentalGroupoid.mk (SSet.realizedVertex x) ⟶
      _root_.FundamentalGroupoid.mk (SSet.realizedVertex y) :=
    Path.Homotopic.Quotient.mk
      (TopCat.pathEquiv (SSet.realizedEdgePath e))
  let qy : _root_.FundamentalGroupoid.mk
        (SSet.realizedVertex (stageWeakDiagonalZeroVertex C)) ⟶
      _root_.FundamentalGroupoid.mk (SSet.realizedVertex y) :=
    Path.Homotopic.Quotient.mk
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalZeroToVertexEdge C y)))
  have hmap' : (qx ≫ qe) ≫ inv qy = 𝟙 _ := by
    dsimp only [R] at hmap
    simpa only [hcx, hcy, he, qx, qe, qy,
      SSet.realizationFundamentalGroupoidFunctor_obj_mk] using hmap
  apply Path.Homotopic.Quotient.eq.mp
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  have hcat : qe ≫ inv qy = inv qx := by
    rw [← cancel_epi qx]
    simpa only [Category.assoc, IsIso.hom_inv_id,
      Category.comp_id] using hmap'
  have hInvY : inv qy = Path.Homotopic.Quotient.symm qy := by
    rw [← Groupoid.inv_eq_inv]
    rfl
  have hInvX : inv qx = Path.Homotopic.Quotient.symm qx := by
    rw [← Groupoid.inv_eq_inv]
    rfl
  rw [hInvY, hInvX] at hcat
  simpa only [qx, qe, qy, _root_.FundamentalGroupoid.comp_eq] using hcat

end CategoryTheory.Waldhausen.SConstruction
