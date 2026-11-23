/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidEquivalence
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Equivalence
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpace
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealizationMap
public import MathlibExt.Topology.Homotopy.LoopComponents
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.CategoryTheory.Conj

set_option linter.style.longLine false

/-!
# Realized weak-diagonal fundamental group and Waldhausen K-zero

Direct geometric realization identifies the based combinatorial fundamental
group of the weak-stage diagonal with the topological fundamental group at
the selected realized basepoint.  Composing its inverse with the landed
combinatorial equivalence gives the one-fold comparison
`π₀ Ω|diag NwS(C)| ≃ K₀(C)` in every universe.

The basepoint change is explicit conjugation by an equality isomorphism.  No
global group, realization-equivalence, or model-category instance is
installed.  No additivity, spectrum, or Q/S statement is made here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategory C]

/-- Equality transport from the directly realized zero vertex to the
selected basepoint of the one-fold K-space. -/
noncomputable def stageWeakDiagonalRealizedVertexBasepointIso :
    _root_.FundamentalGroupoid.mk
        (SSet.realizedVertex (stageWeakDiagonalZeroVertex C)) ≅
      _root_.FundamentalGroupoid.mk
        (stageWeakDiagonalReal.basepoint C) :=
  eqToIso (congrArg _
    (stageWeakDiagonalReal.basepoint_eq_realizedVertex C).symm)

/-- Direct realization, followed by explicit basepoint conjugation, gives an
equivalence from the combinatorial based fundamental group to the
topological fundamental group at the selected basepoint. -/
noncomputable def stageWeakDiagonalRealizationFundamentalMulEquiv :
    stageWeakDiagonalFundamentalGroup C ≃*
      FundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) :=
  (SSet.realizationFundamentalGroupoidFunctorEndMulEquiv
      (stageWeakDiagonal C) (stageWeakDiagonalZeroVertex C)).trans
    (stageWeakDiagonalRealizedVertexBasepointIso C).conj

/-- The topological fundamental group of the realized weak-stage diagonal is
multiplicatively equivalent to Waldhausen K-zero. -/
noncomputable def stageWeakDiagonalRealizedFundamentalK0MulEquiv :
    FundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) ≃*
      Multiplicative (WaldhausenKTheory.K0 C) :=
  (stageWeakDiagonalRealizationFundamentalMulEquiv C).symm.trans
    (stageWeakDiagonalFundamentalK0MulEquiv C)

/-- Additive tagged form of the realized fundamental-group/K-zero
equivalence. -/
noncomputable def stageWeakDiagonalRealizedFundamentalK0AddEquiv :
    Additive (FundamentalGroup (stageWeakDiagonalReal C)
      (stageWeakDiagonalReal.basepoint C)) ≃+
      WaldhausenKTheory.K0 C :=
  MulEquiv.toAdditiveLeft
    (stageWeakDiagonalRealizedFundamentalK0MulEquiv C)

/-- Literal path-component comparison for the one-fold Waldhausen K-space. -/
noncomputable def stageWeakDiagonalKSpacePiZeroEquivK0 :
    ZerothHomotopy
        (LoopSpace (stageWeakDiagonalReal C)
          (stageWeakDiagonalReal.basepoint C)) ≃
      WaldhausenKTheory.K0 C :=
  (loopComponentsEquivFundamentalGroup
      (stageWeakDiagonalReal C) (stageWeakDiagonalReal.basepoint C)).trans
    ((stageWeakDiagonalRealizedFundamentalK0MulEquiv C).toEquiv.trans
      Multiplicative.toAdd)

/-- Canonical loop at the selected basepoint represented by the object edge
of `X`. -/
noncomputable def stageWeakDiagonalObjectLoop (X : C) :
    LoopSpace (stageWeakDiagonalReal C)
      (stageWeakDiagonalReal.basepoint C) :=
  (TopCat.pathEquiv
      (SSet.realizedEdgePath (stageWeakDiagonalObjectEdge C X))).cast
    (stageWeakDiagonalReal.basepoint_eq_realizedVertex C)
    (stageWeakDiagonalReal.basepoint_eq_realizedVertex C)

/-- Direct realization and explicit basepoint conjugation send the
combinatorial object generator to the component of its realized loop. -/
@[simp]
theorem stageWeakDiagonalRealizationFundamentalMulEquiv_objectGenerator
    (X : C) :
    stageWeakDiagonalRealizationFundamentalMulEquiv C
        (stageWeakDiagonalObjectGenerator C X) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (stageWeakDiagonalObjectLoop C X)) := by
  apply CategoryTheory.End.ext
  let e := stageWeakDiagonalRealizedVertexBasepointIso C
  have hMap := congrArg
    (fun f : (SSet.realizationFundamentalGroupoidFunctor (stageWeakDiagonal C)).obj
        (SSet.FundamentalGroupoid.mk (stageWeakDiagonalZeroVertex C)) ⟶
      (SSet.realizationFundamentalGroupoidFunctor (stageWeakDiagonal C)).obj
        (SSet.FundamentalGroupoid.mk (stageWeakDiagonalZeroVertex C)) =>
      e.inv ≫ f ≫ e.hom)
    (SSet.realizationFundamentalGroupoidFunctor_map_homMk
      (stageWeakDiagonal C) (stageWeakDiagonalObjectEdge C X))
  change (e.conj
      (CategoryTheory.End.of
        ((SSet.realizationFundamentalGroupoidFunctor (stageWeakDiagonal C)).map
          (SSet.FundamentalGroupoid.homMk (stageWeakDiagonalObjectEdge C X))))).asHom =
    Path.Homotopic.Quotient.mk (stageWeakDiagonalObjectLoop C X)
  exact (CategoryTheory.Iso.conj_apply_asHom e _).trans
    (hMap.trans ((_root_.FundamentalGroupoid.conj_eqToHom
      (stageWeakDiagonalReal.basepoint_eq_realizedVertex C)
      (stageWeakDiagonalReal.basepoint_eq_realizedVertex C)).trans
        (Path.Homotopic.Quotient.mk_cast _ _ _).symm))

/-- The realized object loop represents the canonical K-zero generator. -/
@[simp]
theorem stageWeakDiagonalKSpacePiZeroEquivK0_objectLoop (X : C) :
    stageWeakDiagonalKSpacePiZeroEquivK0 C
        (ZerothHomotopy.mk (stageWeakDiagonalObjectLoop C X)) =
      WaldhausenKTheory.K0.mk X := by
  change Multiplicative.toAdd
      (stageWeakDiagonalFundamentalK0MulEquiv C
        ((stageWeakDiagonalRealizationFundamentalMulEquiv C).symm
          (loopComponentsEquivFundamentalGroup
            (stageWeakDiagonalReal C)
            (stageWeakDiagonalReal.basepoint C)
            (ZerothHomotopy.mk
              (stageWeakDiagonalObjectLoop C X))))) = _
  rw [
    loopComponentsEquivFundamentalGroup_mk,
    ← stageWeakDiagonalRealizationFundamentalMulEquiv_objectGenerator,
    MulEquiv.symm_apply_apply,
    stageWeakDiagonalFundamentalK0MulEquiv_objectGenerator]
  rfl

end CategoryTheory.Waldhausen.SConstruction

end


public section

noncomputable section

open CategoryTheory Limits

universe uK vK

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type uK) [Category.{vK} C] [HasZeroObject C] [WaldhausenCategory C]

/-- The original realization equivalence uses the direct realization functor
and the selected basepoint equality isomorphism. -/
theorem stageWeakDiagonalRealizationFundamentalMulEquiv_apply
    (g : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalRealizationFundamentalMulEquiv C g =
      (stageWeakDiagonalRealizedVertexBasepointIso C).conj
        ((SSet.realizationFundamentalGroupoidFunctor (stageWeakDiagonal C)).mapEnd
          (SSet.FundamentalGroupoid.mk (stageWeakDiagonalZeroVertex C)) g) := by
  change (stageWeakDiagonalRealizedVertexBasepointIso C).conj
      (SSet.realizationFundamentalGroupoidFunctorEndMulEquiv
        (stageWeakDiagonal C) (stageWeakDiagonalZeroVertex C) g) = _
  rw [SSet.realizationFundamentalGroupoidFunctor_endMulEquiv_apply]

/-- Decoding a directly realized endomorphism keeps the original combinatorial decode. -/
theorem stageWeakDiagonalRealizedFundamentalK0MulEquiv_realization
    (g : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalRealizedFundamentalK0MulEquiv C
        (stageWeakDiagonalRealizationFundamentalMulEquiv C g) =
      stageWeakDiagonalFundamentalK0MulEquiv C g := by
  change stageWeakDiagonalFundamentalK0MulEquiv C
      ((stageWeakDiagonalRealizationFundamentalMulEquiv C).symm
        (stageWeakDiagonalRealizationFundamentalMulEquiv C g)) = _
  rw [MulEquiv.symm_apply_apply]

/-- The original component comparison decodes the represented fundamental-group class. -/
theorem stageWeakDiagonalKSpacePiZeroEquivK0_apply
    (a : ZerothHomotopy (stageWeakDiagonalKSpace C)) :
    stageWeakDiagonalKSpacePiZeroEquivK0 C a =
      Multiplicative.toAdd
        (stageWeakDiagonalRealizedFundamentalK0MulEquiv C
          (loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
            (stageWeakDiagonalReal.basepoint C) a)) := rfl

end CategoryTheory.Waldhausen.SConstruction

end
