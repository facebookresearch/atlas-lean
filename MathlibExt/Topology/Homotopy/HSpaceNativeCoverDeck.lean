/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HSpaceHomotopyAction
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverTraceCoordinate
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Every actual H-space deck map is homotopic to identity

The two ordinary unit homotopies construct the required identity self-homotopy
of the original space. Its trace is prescribed at any actual point by the
ordinary path square. The native fibration lifts this homotopy from identity;
the original root-coordinate calculation identifies its whole endpoint map
with the saved inverse-precomposition deck map.

This derives trivial deck action on every ordinary homology degree of the
actual native cover. It does not assume that an arbitrary homology-isomorphism
map induces a cover homology isomorphism, and it does not assert the full
H-space homology Whitehead theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial Topology Topology.Homotopy

universe u uC vC

public section

namespace TopCat.HSpaceHomotopyAction

private theorem exists_selfHomotopy_with_trace_at_point
    (X : TopCat.{u}) [PathConnectedSpace X] (mu : C(X × X, X)) (e : X)
    (HL : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))) (ContinuousMap.id X))
    (HR : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X e))) (ContinuousMap.id X))
    (x : X) (p : _root_.Path x x) :
    ∃ H : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.id X),
      (H.evalAt x).Homotopic p := by
  let q : _root_.Path e x := PathConnectedSpace.somePath e x
  let beta : _root_.Path e e := q.trans (p.trans q.symm)
  obtain ⟨H, hH⟩ := exists_selfHomotopy_with_trace_of_unit_homotopies X mu e HL HR beta
  refine ⟨H, ?_⟩
  let Q : _root_.Path.Homotopic.Quotient e x := _root_.Path.Homotopic.Quotient.mk q
  let P : _root_.Path.Homotopic.Quotient x x := _root_.Path.Homotopic.Quotient.mk p
  let T₀ : _root_.Path.Homotopic.Quotient e e :=
    _root_.Path.Homotopic.Quotient.mk (H.evalAt e)
  let T₁ : _root_.Path.Homotopic.Quotient x x :=
    _root_.Path.Homotopic.Quotient.mk (H.evalAt x)
  have hLeft : (q.map (ContinuousMap.id X).continuous).trans (H.evalAt x) =
      q.trans (H.evalAt x) := by
    apply _root_.Path.ext
    rfl
  have hRight : (H.evalAt e).trans (q.map (ContinuousMap.id X).continuous) =
      (H.evalAt e).trans q := by
    apply _root_.Path.ext
    rfl
  have hSquare : Q.trans T₁ = T₀.trans Q :=
    _root_.Path.Homotopic.Quotient.eq.mpr
      (Nonempty.map (fun F => _root_.Path.Homotopy.cast F hLeft hRight)
        (_root_.Path.Homotopic.map_trans_evalAt H q))
  have hUnit : T₀ = Q.trans (P.trans Q.symm) :=
    _root_.Path.Homotopic.Quotient.eq.mpr hH
  have h₁ : (Q.trans (P.trans Q.symm)).trans Q =
      Q.trans ((P.trans Q.symm).trans Q) :=
    _root_.Path.Homotopic.Quotient.trans_assoc Q (P.trans Q.symm) Q
  have h₂ : Q.trans ((P.trans Q.symm).trans Q) =
      Q.trans (P.trans (Q.symm.trans Q)) :=
    congrArg (fun k : _root_.Path.Homotopic.Quotient x x => Q.trans k)
      (_root_.Path.Homotopic.Quotient.trans_assoc P Q.symm Q)
  have h₃ : Q.trans (P.trans (Q.symm.trans Q)) =
      Q.trans (P.trans (_root_.Path.Homotopic.Quotient.refl x)) :=
    congrArg (fun k : _root_.Path.Homotopic.Quotient x x => Q.trans (P.trans k))
      (_root_.Path.Homotopic.Quotient.symm_trans Q)
  have h₄ : Q.trans (P.trans (_root_.Path.Homotopic.Quotient.refl x)) = Q.trans P :=
    congrArg (fun k : _root_.Path.Homotopic.Quotient x x => Q.trans k)
      (_root_.Path.Homotopic.Quotient.trans_refl P)
  have hEnd : Q.trans T₁ = Q.trans P :=
    hSquare.trans
      ((congrArg (fun k : _root_.Path.Homotopic.Quotient e e => k.trans Q) hUnit).trans
        (h₁.trans (h₂.trans (h₃.trans h₄))))
  have hCancel : Q.symm.trans (Q.trans T₁) = Q.symm.trans (Q.trans P) := congrArg
    (fun k : _root_.Path.Homotopic.Quotient e x => Q.symm.trans k) hEnd
  have hLeftCancel : Q.symm.trans (Q.trans T₁) = T₁ :=
    (_root_.Path.Homotopic.Quotient.trans_assoc Q.symm Q T₁).symm.trans
      ((congrArg (fun k : _root_.Path.Homotopic.Quotient x x => k.trans T₁)
        (_root_.Path.Homotopic.Quotient.symm_trans Q)).trans
        (_root_.Path.Homotopic.Quotient.refl_trans T₁))
  have hRightCancel : Q.symm.trans (Q.trans P) = P :=
    (_root_.Path.Homotopic.Quotient.trans_assoc Q.symm Q P).symm.trans
      ((congrArg (fun k : _root_.Path.Homotopic.Quotient x x => k.trans P)
        (_root_.Path.Homotopic.Quotient.symm_trans Q)).trans
        (_root_.Path.Homotopic.Quotient.refl_trans P))
  have hTrace : T₁ = P := hLeftCancel.symm.trans (hCancel.trans hRightCancel)
  exact _root_.Path.Homotopic.Quotient.eq.mp hTrace

private theorem singularPathHom_end_equiv (X : TopCat.{u}) (x : X)
    (p : _root_.Path x x) :
    TopCat.singularFundamentalGroupoidEndMulEquiv X x
      (End.of (TopCat.singularPathHom X p)) =
        End.of (_root_.Path.Homotopic.Quotient.mk p) := by
  let E := TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)
  let P := TopCat.pathEquiv (X := X) (x := x) (y := x)
  let ep : (TopCat.toSSet.obj X).Edge
      (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm x) :=
    E.symm (P.symm p)
  have hp : P (E ep) = p :=
    (congrArg P (E.apply_symm_apply (P.symm p))).trans (P.apply_symm_apply p)
  have hpClass : _root_.Path.Homotopic.Quotient.mk (P (E ep)) =
      _root_.Path.Homotopic.Quotient.mk p :=
    congrArg (_root_.Path.Homotopic.Quotient.mk :
      _root_.Path x x → _root_.Path.Homotopic.Quotient x x) hp
  have hEnd : (End.of (_root_.Path.Homotopic.Quotient.mk (P (E ep))) :
      End (_root_.FundamentalGroupoid.mk x)) =
        End.of (_root_.Path.Homotopic.Quotient.mk p) := by
    apply End.ext
    exact hpClass
  have hMk : TopCat.singularFundamentalGroupoidEndMulEquiv X x
      (End.of (SSet.FundamentalGroupoid.homMk ep)) =
        End.of (_root_.Path.Homotopic.Quotient.mk (P (E ep))) :=
    TopCat.singularFundamentalGroupoidEndMulEquiv_homMk X x ep
  change TopCat.singularFundamentalGroupoidEndMulEquiv X x
      (End.of (SSet.FundamentalGroupoid.homMk ep)) =
    End.of (_root_.Path.Homotopic.Quotient.mk p)
  exact hMk.trans hEnd

private theorem singularPathHom_surjective (X : TopCat.{u}) (x : X) :
    Function.Surjective (TopCat.singularPathHom X (x := x) (y := x)) := by
  intro h
  let E := TopCat.singularFundamentalGroupoidEndMulEquiv X x
  let g := End.of h
  obtain ⟨p, hp⟩ := _root_.Path.Homotopic.Quotient.mk_surjective (E g).asHom
  have hE : E (End.of (TopCat.singularPathHom X p)) = E g :=
    (singularPathHom_end_equiv X x p).trans
      ((congrArg End.of hp).trans (by apply End.ext; rfl))
  refine ⟨p, ?_⟩
  exact congrArg End.asHom (E.injective hE)

private def strictSingularSelfHomotopy (X : TopCat.{u})
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.id X)) :
    SSet.Homotopy (𝟙 (TopCat.toSSet.obj X)) (𝟙 (TopCat.toSSet.obj X)) := by
  let T : TopCat.Homotopy (𝟙 X) (𝟙 X) := H
  exact SSet.Homotopy.mkOfH T.toSSet.h
    (T.toSSet.h₀.trans (TopCat.toSSet.map_id X))
    (T.toSSet.h₁.trans (TopCat.toSSet.map_id X))

private theorem strictSingularSelfHomotopy_h (X : TopCat.{u})
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.id X)) :
    (strictSingularSelfHomotopy X H).h =
      (show TopCat.Homotopy (𝟙 X) (𝟙 X) from H).toSSet.h := by
  rfl

private theorem strictSingularSelfHomotopy_trace (X : TopCat.{u})
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.id X)) (x : X) :
    SSet.FundamentalGroupoid.homMk
      (SSet.Edge.ofSimplicialObjectHomotopy
        (strictSingularSelfHomotopy X H).toSimplicialObjectHomotopy
          (TopCat.toSSetObj₀Equiv.symm x)) = TopCat.singularPathHom X (H.evalAt x) := by
  let SX := TopCat.toSSet.obj X
  let G := SSet.FundamentalGroupoid SX
  let T : TopCat.Homotopy (𝟙 X) (𝟙 X) := H
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let e : SX.Edge sx sx := SSet.Edge.ofSimplicialObjectHomotopy
    (strictSingularSelfHomotopy X H).toSimplicialObjectHomotopy sx
  let eo := SSet.Edge.ofSimplicialObjectHomotopy T.toSSet.toSimplicialObjectHomotopy sx
  have hRaw : e.edge = eo.edge := by
    dsimp only [e, eo]
    rw [SSet.Edge.ofSimplicialObjectHomotopy_edge,
      SSet.Edge.ofSimplicialObjectHomotopy_edge]
    dsimp only [SSet.Homotopy.toSimplicialObjectHomotopy]
    rw [strictSingularSelfHomotopy_h]
  have hOriginal : SSet.FundamentalGroupoid.homMk eo =
      TopCat.singularPathHom X (H.evalAt x) := TopCat.singularHomotopy_trace T x
  have hChain : (ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e) :
      (CategoryTheory.nerve G) _⦋1⦌) =
          ComposableArrows.mk₁ (TopCat.singularPathHom X (H.evalAt x)) :=
    (SSet.fundamentalGroupoidNerveEquiv_app_edge SX G (𝟭 G) e).symm.trans
      ((congrArg ((SSet.KanComplex.nativeCoverUnit SX).app (op ⦋1⦌)) hRaw).trans
        ((SSet.fundamentalGroupoidNerveEquiv_app_edge SX G (𝟭 G) eo).trans
          (congrArg (fun h => ComposableArrows.mk₁ h) hOriginal)))
  exact CategoryTheory.Arrow.mk_injective _ _ (congrArg ComposableArrows.arrowEquiv hChain)

/-- The two bare ordinary unit homotopies derive an actual identity-to-deck
homotopy at every point of the original connected H-space. -/
theorem exists_nativeCover_deckHomotopy_of_unit_homotopies
    (X : TopCat.{u}) [PathConnectedSpace X] (mu : C(X × X, X)) (e : X)
    (HL : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))) (ContinuousMap.id X))
    (HR : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X e))) (ContinuousMap.id X))
    (x : X)
    (g : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))) :
    Nonempty (SSet.Homotopy
      (𝟙 (SSet.KanComplex.nativeCover (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x)))
      (SSet.KanComplex.nativeCoverDeckMap g)) := by
  let SX := TopCat.toSSet.obj X
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let : SSet.KanComplex SX := TopCat.toSSet_obj_kanComplex X
  obtain ⟨p, hp⟩ := singularPathHom_surjective X x (g⁻¹).asHom
  obtain ⟨H, hH⟩ := exists_selfHomotopy_with_trace_at_point X mu e HL HR x p
  let h := strictSingularSelfHomotopy X H
  have hTrace : SSet.FundamentalGroupoid.homMk
      (SSet.Edge.ofSimplicialObjectHomotopy h.toSimplicialObjectHomotopy sx) = (g⁻¹).asHom :=
    (strictSingularSelfHomotopy_trace X H x).trans
      ((TopCat.singularPathHom_eq_of_homotopic X hH).trans hp)
  obtain ⟨K, _⟩ := SSet.KanComplex.exists_nativeCover_deckHomotopy_of_selfTrace sx h g hTrace
  exact ⟨K⟩

/-- The standard H-space structure supplies all the unit homotopies; every
original native deck element has an actual homotopy from identity. -/
theorem exists_nativeCover_deckHomotopy (X : TopCat.{u}) [HSpace X] [PathConnectedSpace X]
    (x : X)
    (g : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))) :
    Nonempty (SSet.Homotopy
      (𝟙 (SSet.KanComplex.nativeCover (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x)))
      (SSet.KanComplex.nativeCoverDeckMap g)) :=
  exists_nativeCover_deckHomotopy_of_unit_homotopies X HSpace.hmul HSpace.e
    HSpace.eHmul.toHomotopy HSpace.hmulE.toHomotopy x g

/-- Realization gives a homotopy from the SAME original deck map to identity. -/
theorem exists_realizedNativeCover_deckHomotopy (X : TopCat.{u}) [HSpace X]
    [PathConnectedSpace X] (x : X)
    (g : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))) :
    Nonempty (ContinuousMap.Homotopy
      (SSet.toTop.map (SSet.KanComplex.nativeCoverDeckMap g)).hom
      (ContinuousMap.id (SSet.toTop.obj
        (SSet.KanComplex.nativeCover (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x))))) := by
  obtain ⟨K⟩ := exists_nativeCover_deckHomotopy X x g
  let P := SSet.KanComplex.nativeCover (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x)
  let H := SSet.realizeHomotopy P P (𝟙 P) (SSet.KanComplex.nativeCoverDeckMap g) K
  have hId : (SSet.toTop.map (𝟙 P)).hom = ContinuousMap.id (SSet.toTop.obj P) :=
    congrArg (fun f : SSet.toTop.obj P ⟶ SSet.toTop.obj P => f.hom) (SSet.toTop.map_id P)
  exact ⟨H.symm.cast rfl hId⟩

/-- Every actual native deck map induces identity on every homology degree,
with independently sized coefficient category and arbitrary constant coefficient. -/
theorem nativeCoverDeckMap_homologyMap_eq_id
    (X : TopCat.{u}) [HSpace X] [PathConnectedSpace X] (x : X)
    (g : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x)))
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    SSet.homologyMap (SSet.KanComplex.nativeCoverDeckMap g) R n = 𝟙 _ := by
  obtain ⟨K⟩ := exists_nativeCover_deckHomotopy X x g
  exact (K.congr_homologyMap R n).symm.trans
    (SSet.homologyMap_id
      (SSet.KanComplex.nativeCover (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x)) R n)

end TopCat.HSpaceHomotopyAction
