/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.TopCat.HomotopyTraceAction
public import Mathlib.Topology.Homotopy.HSpaces
public import Mathlib.Topology.Connected.PathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Trivial positive homotopy action from the actual H-space unit homotopies

Multiplication and the two ordinary unit homotopies suffice. The product
unit may be shifted, and the unit homotopies need not be relative to the
chosen point. Every path used in the proof is the computed trace of a unit
homotopy. No trivial-action or root-calibration witness is supplied.

This is a simplicity prerequisite for integral homology Whitehead. It does
not assert the full comparison theorem or assume a comparison map is an
H-map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy

universe u

public section

namespace TopCat.HSpaceHomotopyAction

private def leftMap (X : TopCat.{u}) (mu : C(X × X, X)) (e : X) : C(X, X) :=
  mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))

private def rightMap (X : TopCat.{u}) (mu : C(X × X, X)) (e : X) : C(X, X) :=
  mu.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X e))

private def productPoint (X : TopCat.{u}) (mu : C(X × X, X)) (e : X) : X := mu (e, e)

private def leftTrace (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (H : ContinuousMap.Homotopy (leftMap X mu e) (ContinuousMap.id X)) :
    _root_.Path (productPoint X mu e) e :=
  H.evalAt e

private def rightTrace (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (H : ContinuousMap.Homotopy (rightMap X mu e) (ContinuousMap.id X)) :
    _root_.Path (productPoint X mu e) e :=
  H.evalAt e

private theorem homotopy_evalAt_symm (X : TopCat.{u}) {f g : C(X, X)}
    (H : ContinuousMap.Homotopy f g) (x : X) :
    (H.symm.evalAt x) = (H.evalAt x).symm := by
  ext t
  simp only [ContinuousMap.Homotopy.evalAt_apply, ContinuousMap.Homotopy.symm_apply,
    _root_.Path.symm_apply, Function.comp_apply]

private theorem homotopy_evalAt_trans (X : TopCat.{u}) {f g h : C(X, X)}
    (H : ContinuousMap.Homotopy f g) (K : ContinuousMap.Homotopy g h) (x : X) :
    ((H.trans K).evalAt x) = (H.evalAt x).trans (K.evalAt x) := by
  ext t
  simp only [ContinuousMap.Homotopy.evalAt_apply, ContinuousMap.Homotopy.trans_apply,
    _root_.Path.trans_apply]

private def leftGroupMap (X : TopCat.{u}) (mu : C(X × X, X)) (e : X) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) X e → HomotopyGroup.Pi (n + 1) X (productPoint X mu e) :=
  HomotopyGroup.mapHomOfEq (leftMap X mu e) rfl n

private theorem basepointChange_trans_apply (n : ℕ) (X : TopCat.{u})
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X q
      (TopCat.homotopyGroupBasepointChangeMulEquiv n X p a) =
        TopCat.homotopyGroupBasepointChangeMulEquiv n X (p.trans q) a :=
  (congrArg (fun E : HomotopyGroup.Pi (n + 1) X x ≃*
    HomotopyGroup.Pi (n + 1) X z => E a)
      (TopCat.homotopyGroupBasepointChangeMulEquiv_trans n X p q)).symm

private theorem basepointChange_homotopic_apply (n : ℕ) (X : TopCat.{u})
    {x y : X} {p q : _root_.Path x y} (h : p.Homotopic q)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X p a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n X q a :=
  congrArg (fun E : HomotopyGroup.Pi (n + 1) X x ≃*
    HomotopyGroup.Pi (n + 1) X y => E a)
      (TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic n X h)

private theorem leftGroupMap_unit (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (H : ContinuousMap.Homotopy (leftMap X mu e) (ContinuousMap.id X))
    (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X e) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X (leftTrace X mu e H)
      (leftGroupMap X mu e n a) = a := by
  let K : TopCat.Homotopy (TopCat.ofHom (leftMap X mu e) : X ⟶ X) (𝟙 X) := H
  have h := TopCat.homotopyGroup_map_homotopy_trace_of_eq
    (X := X) (Y := X) (f := TopCat.ofHom (leftMap X mu e)) (g := 𝟙 X)
    n K e rfl rfl a
  exact h.trans (HomotopyGroup.mapHomOfEq_id e n a)

private theorem leftGroupMap_surjective (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (H : ContinuousMap.Homotopy (leftMap X mu e) (ContinuousMap.id X)) (n : ℕ) :
    Function.Surjective (leftGroupMap X mu e n) := by
  let E := TopCat.homotopyGroupBasepointChangeMulEquiv n X (leftTrace X mu e H)
  intro b
  refine ⟨E b, ?_⟩
  apply E.injective
  exact leftGroupMap_unit X mu e H n (E b)

private def rightImageLoop (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (p : _root_.Path e e) : _root_.Path (productPoint X mu e) (productPoint X mu e) :=
  p.map (f := rightMap X mu e) (rightMap X mu e).continuous

private def multiplicationLoopHomotopy (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (p : _root_.Path e e) :
    ContinuousMap.Homotopy (leftMap X mu e) (leftMap X mu e) where
  toFun tx := mu (p tx.1, tx.2)
  continuous_toFun := mu.continuous.comp
    ((p.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left x := by rw [p.source]; rfl
  map_one_left x := by rw [p.target]; rfl

private theorem multiplicationLoopHomotopy_trace
    (X : TopCat.{u}) (mu : C(X × X, X)) (e : X) (p : _root_.Path e e) :
    ((multiplicationLoopHomotopy X mu e p).evalAt e).cast rfl rfl =
      rightImageLoop X mu e p := by
  ext t
  change mu (p t, e) =
    (p.map (f := rightMap X mu e) (rightMap X mu e).continuous) t
  rw [_root_.Path.map_coe, Function.comp_apply]
  rfl

private theorem rightImageLoop_action (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (H : ContinuousMap.Homotopy (leftMap X mu e) (ContinuousMap.id X))
    (n : ℕ) (p : _root_.Path e e)
    (b : HomotopyGroup.Pi (n + 1) X (productPoint X mu e)) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X (rightImageLoop X mu e p) b = b := by
  obtain ⟨a, rfl⟩ := leftGroupMap_surjective X mu e H n b
  have h := TopCat.homotopyGroup_map_homotopy_trace_of_eq
    (X := X) (Y := X) (f := TopCat.ofHom (leftMap X mu e))
    (g := TopCat.ofHom (leftMap X mu e)) n
    (multiplicationLoopHomotopy X mu e p) e rfl rfl a
  rw [multiplicationLoopHomotopy_trace] at h
  exact h

private theorem rightUnit_path_square (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (H : ContinuousMap.Homotopy (rightMap X mu e) (ContinuousMap.id X)) (p : _root_.Path e e) :
    ((rightImageLoop X mu e p).trans (rightTrace X mu e H)).Homotopic
      ((rightTrace X mu e H).trans p) := by
  have h := _root_.Path.Homotopic.map_trans_evalAt H p
  have hL : (p.map (f := rightMap X mu e) (rightMap X mu e).continuous).trans (H.evalAt e) =
      (rightImageLoop X mu e p).trans (rightTrace X mu e H) := by
    apply _root_.Path.ext
    rfl
  have hR : (H.evalAt e).trans (p.map (ContinuousMap.id X).continuous) =
      (rightTrace X mu e H).trans p := by
    apply _root_.Path.ext
    rfl
  exact Nonempty.map (fun F => _root_.Path.Homotopy.cast F hL hR) h

/-- The two genuine ordinary H-space unit homotopies force trivial positive loop action
at the unit. -/
theorem loop_action_eq_self_of_unit_homotopies
    (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (HL : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))) (ContinuousMap.id X))
    (HR : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X e))) (ContinuousMap.id X))
    (n : ℕ) (p : _root_.Path e e) (b : HomotopyGroup.Pi (n + 1) X e) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X p b = b := by
  let q := rightImageLoop X mu e p
  let r := rightTrace X mu e HR
  let E := TopCat.homotopyGroupBasepointChangeMulEquiv n X r
  let a := E.symm b
  have hAction : TopCat.homotopyGroupBasepointChangeMulEquiv n X q a = a :=
    rightImageLoop_action X mu e HL n p a
  have hPath : (q.trans r).Homotopic (r.trans p) := rightUnit_path_square X mu e HR p
  have h : E a = TopCat.homotopyGroupBasepointChangeMulEquiv n X p (E a) := by
    calc
      E a = E (TopCat.homotopyGroupBasepointChangeMulEquiv n X q a) :=
        (congrArg E hAction).symm
      _ = TopCat.homotopyGroupBasepointChangeMulEquiv n X (q.trans r) a :=
        basepointChange_trans_apply n X q r a
      _ = TopCat.homotopyGroupBasepointChangeMulEquiv n X (r.trans p) a :=
        basepointChange_homotopic_apply n X hPath a
      _ = TopCat.homotopyGroupBasepointChangeMulEquiv n X p (E a) :=
        (basepointChange_trans_apply n X r p a).symm
  have hValue : E a = b := E.apply_symm_apply b
  rw [hValue] at h
  exact h.symm

/-- The ordinary H-space structure supplies the genuine unit homotopies directly. -/
theorem loop_action_eq_self (X : TopCat.{u}) [HSpace X] (n : ℕ)
    (p : _root_.Path (HSpace.e : X) HSpace.e)
    (a : HomotopyGroup.Pi (n + 1) X HSpace.e) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X p a = a :=
  loop_action_eq_self_of_unit_homotopies X HSpace.hmul HSpace.e
    HSpace.eHmul.toHomotopy HSpace.hmulE.toHomotopy n p a

private theorem conjugated_loop_path_square (X : TopCat.{u}) {e x : X}
    (r : _root_.Path e x) (p : _root_.Path x x) :
    ((r.trans (p.trans r.symm)).trans r).Homotopic (r.trans p) := by
  have h₁ := _root_.Path.Homotopic.trans_assoc r (p.trans r.symm) r
  have h₂ := (_root_.Path.Homotopic.refl r).hcomp (_root_.Path.Homotopic.trans_assoc p r.symm r)
  have h₃ := (_root_.Path.Homotopic.refl r).hcomp
    ((_root_.Path.Homotopic.refl p).hcomp (_root_.Path.Homotopic.symm_trans r))
  have h₄ := (_root_.Path.Homotopic.refl r).hcomp (_root_.Path.Homotopic.trans_refl p)
  exact ((h₁.trans h₂).trans h₃).trans h₄

/-- In a path-connected H-space, the derived trivial action holds at every original point. -/
theorem loop_action_eq_self_at_point_of_unit_homotopies
    (X : TopCat.{u}) [PathConnectedSpace X] (mu : C(X × X, X)) (e : X)
    (HL : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))) (ContinuousMap.id X))
    (HR : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X e))) (ContinuousMap.id X))
    (n : ℕ) (x : X) (p : _root_.Path x x) (b : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X p b = b := by
  let r : _root_.Path e x := PathConnectedSpace.somePath e x
  let q : _root_.Path e e := r.trans (p.trans r.symm)
  let E := TopCat.homotopyGroupBasepointChangeMulEquiv n X r
  let a := E.symm b
  have hUnit : TopCat.homotopyGroupBasepointChangeMulEquiv n X q a = a :=
    loop_action_eq_self_of_unit_homotopies X mu e HL HR n q a
  have hPath : (q.trans r).Homotopic (r.trans p) := conjugated_loop_path_square X r p
  have h : E a = TopCat.homotopyGroupBasepointChangeMulEquiv n X p (E a) := by
    calc
      E a = E (TopCat.homotopyGroupBasepointChangeMulEquiv n X q a) :=
        (congrArg E hUnit).symm
      _ = TopCat.homotopyGroupBasepointChangeMulEquiv n X (q.trans r) a :=
        basepointChange_trans_apply n X q r a
      _ = TopCat.homotopyGroupBasepointChangeMulEquiv n X (r.trans p) a :=
        basepointChange_homotopic_apply n X hPath a
      _ = TopCat.homotopyGroupBasepointChangeMulEquiv n X p (E a) :=
        (basepointChange_trans_apply n X r p a).symm
  have hValue : E a = b := E.apply_symm_apply b
  rw [hValue] at h
  exact h.symm

/-- The standard H-space structure gives the full all-basepoint positive-action result. -/
theorem loop_action_eq_self_at_point
    (X : TopCat.{u}) [HSpace X] [PathConnectedSpace X] (n : ℕ) (x : X)
    (p : _root_.Path x x) (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X p a = a :=
  loop_action_eq_self_at_point_of_unit_homotopies X HSpace.hmul HSpace.e
    HSpace.eHmul.toHomotopy HSpace.hmulE.toHomotopy n x p a

private def unitTracePreimageLoop (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (HL : ContinuousMap.Homotopy (leftMap X mu e) (ContinuousMap.id X))
    (HR : ContinuousMap.Homotopy (rightMap X mu e) (ContinuousMap.id X))
    (p : _root_.Path e e) : _root_.Path e e :=
  (rightTrace X mu e HR).symm.trans
    (((leftTrace X mu e HL).trans (p.trans (leftTrace X mu e HL).symm)).trans
      (rightTrace X mu e HR))

private def unitLoopSelfHomotopy (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (HL : ContinuousMap.Homotopy (leftMap X mu e) (ContinuousMap.id X))
    (HR : ContinuousMap.Homotopy (rightMap X mu e) (ContinuousMap.id X))
    (p : _root_.Path e e) :
    ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.id X) :=
  HL.symm.trans
    ((multiplicationLoopHomotopy X mu e (unitTracePreimageLoop X mu e HL HR p)).trans HL)

private theorem rightImageLoop_conjugated_unit (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (HR : ContinuousMap.Homotopy (rightMap X mu e) (ContinuousMap.id X))
    (beta : _root_.Path (productPoint X mu e) (productPoint X mu e)) :
    (rightImageLoop X mu e
      ((rightTrace X mu e HR).symm.trans (beta.trans (rightTrace X mu e HR)))).Homotopic beta := by
  let m := productPoint X mu e
  let r := rightTrace X mu e HR
  let gamma := r.symm.trans (beta.trans r)
  let R : _root_.Path.Homotopic.Quotient m e := _root_.Path.Homotopic.Quotient.mk r
  let B : _root_.Path.Homotopic.Quotient m m := _root_.Path.Homotopic.Quotient.mk beta
  let G : _root_.Path.Homotopic.Quotient e e := _root_.Path.Homotopic.Quotient.mk gamma
  let K : _root_.Path.Homotopic.Quotient m m :=
    _root_.Path.Homotopic.Quotient.mk (rightImageLoop X mu e gamma)
  have hSquare : K.trans R = R.trans G :=
    _root_.Path.Homotopic.Quotient.eq.mpr (rightUnit_path_square X mu e HR gamma)
  have hG : G = R.symm.trans (B.trans R) := rfl
  have hEnd : K.trans R = B.trans R := by
    calc
      K.trans R = R.trans G := hSquare
      _ = R.trans (R.symm.trans (B.trans R)) := congrArg R.trans hG
      _ = B.trans R := by
        rw [← _root_.Path.Homotopic.Quotient.trans_assoc,
          _root_.Path.Homotopic.Quotient.trans_symm,
          _root_.Path.Homotopic.Quotient.refl_trans]
  apply _root_.Path.Homotopic.Quotient.eq.mp
  have hCancel := congrArg
    (fun q : _root_.Path.Homotopic.Quotient m e => q.trans R.symm) hEnd
  simpa only [_root_.Path.Homotopic.Quotient.trans_assoc,
    _root_.Path.Homotopic.Quotient.trans_symm,
    _root_.Path.Homotopic.Quotient.trans_refl] using hCancel

private theorem unitLoopSelfHomotopy_trace (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (HL : ContinuousMap.Homotopy (leftMap X mu e) (ContinuousMap.id X))
    (HR : ContinuousMap.Homotopy (rightMap X mu e) (ContinuousMap.id X))
    (p : _root_.Path e e) : ((unitLoopSelfHomotopy X mu e HL HR p).evalAt e).Homotopic p := by
  let l := leftTrace X mu e HL
  let r := rightTrace X mu e HR
  let beta := l.trans (p.trans l.symm)
  let gamma := unitTracePreimageLoop X mu e HL HR p
  have hImage : (rightImageLoop X mu e gamma).Homotopic beta :=
    rightImageLoop_conjugated_unit X mu e HR beta
  have hTrace : (unitLoopSelfHomotopy X mu e HL HR p).evalAt e =
      l.symm.trans ((rightImageLoop X mu e gamma).trans l) := by
    unfold unitLoopSelfHomotopy
    rw [homotopy_evalAt_trans X, homotopy_evalAt_symm X, homotopy_evalAt_trans X]
    have hMul : (multiplicationLoopHomotopy X mu e gamma).evalAt e =
        rightImageLoop X mu e gamma := by
      simpa only [_root_.Path.cast_rfl_rfl] using
        multiplicationLoopHomotopy_trace X mu e gamma
    dsimp only [gamma] at hMul
    dsimp only [gamma, l, leftTrace]
    rw [hMul]
    rfl
  apply _root_.Path.Homotopic.Quotient.eq.mp
  rw [hTrace]
  let L := _root_.Path.Homotopic.Quotient.mk l
  let P := _root_.Path.Homotopic.Quotient.mk p
  let K := _root_.Path.Homotopic.Quotient.mk (rightImageLoop X mu e gamma)
  have hK : K = L.trans (P.trans L.symm) :=
    _root_.Path.Homotopic.Quotient.eq.mpr hImage
  change L.symm.trans (K.trans L) = P
  rw [hK]
  simp only [_root_.Path.Homotopic.Quotient.trans_assoc,
    _root_.Path.Homotopic.Quotient.symm_trans,
    _root_.Path.Homotopic.Quotient.trans_refl]
  rw [← _root_.Path.Homotopic.Quotient.trans_assoc,
    _root_.Path.Homotopic.Quotient.symm_trans,
    _root_.Path.Homotopic.Quotient.refl_trans]

/-- Every original unit loop is the actual trace class of an identity self-homotopy. -/
theorem exists_selfHomotopy_with_trace_of_unit_homotopies
    (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (HL : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))) (ContinuousMap.id X))
    (HR : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X e))) (ContinuousMap.id X))
    (p : _root_.Path e e) :
    ∃ H : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.id X),
      (H.evalAt e).Homotopic p :=
  ⟨unitLoopSelfHomotopy X mu e HL HR p, unitLoopSelfHomotopy_trace X mu e HL HR p⟩

/-- Adjust the actual left unit homotopy using a derived identity self-homotopy. -/
def coherentLeftUnitHomotopy
    (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (HL : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))) (ContinuousMap.id X))
    (HR : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X e))) (ContinuousMap.id X)) :
    ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))) (ContinuousMap.id X) :=
  HL.trans (Classical.choose (exists_selfHomotopy_with_trace_of_unit_homotopies X mu e HL HR
    ((HL.evalAt e).symm.trans (HR.evalAt e))))

/-- The two actual ordinary unit traces are homotopic after the computed adjustment. -/
theorem coherentLeftUnitHomotopy_trace
    (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
    (HL : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))) (ContinuousMap.id X))
    (HR : ContinuousMap.Homotopy
      (mu.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X e))) (ContinuousMap.id X)) :
    ((coherentLeftUnitHomotopy X mu e HL HR).evalAt e).Homotopic (HR.evalAt e) := by
  let p : _root_.Path e e := (HL.evalAt e).symm.trans (HR.evalAt e)
  let H := Classical.choose (exists_selfHomotopy_with_trace_of_unit_homotopies X mu e HL HR p)
  have hH : (H.evalAt e).Homotopic p :=
    Classical.choose_spec (exists_selfHomotopy_with_trace_of_unit_homotopies X mu e HL HR p)
  have hTrace : (coherentLeftUnitHomotopy X mu e HL HR).evalAt e =
      (HL.evalAt e).trans (H.evalAt e) := by
    apply _root_.Path.ext
    rfl
  apply _root_.Path.Homotopic.Quotient.eq.mp
  rw [hTrace]
  have hClass : _root_.Path.Homotopic.Quotient.mk (H.evalAt e) =
      _root_.Path.Homotopic.Quotient.mk p := _root_.Path.Homotopic.Quotient.eq.mpr hH
  change (_root_.Path.Homotopic.Quotient.mk (HL.evalAt e)).trans
      (_root_.Path.Homotopic.Quotient.mk (H.evalAt e)) =
    _root_.Path.Homotopic.Quotient.mk (HR.evalAt e)
  rw [hClass]
  change (_root_.Path.Homotopic.Quotient.mk (HL.evalAt e)).trans
      ((_root_.Path.Homotopic.Quotient.mk (HL.evalAt e)).symm.trans
        (_root_.Path.Homotopic.Quotient.mk (HR.evalAt e))) = _
  rw [← _root_.Path.Homotopic.Quotient.trans_assoc,
    _root_.Path.Homotopic.Quotient.trans_symm,
    _root_.Path.Homotopic.Quotient.refl_trans]
  rfl

end TopCat.HSpaceHomotopyAction
