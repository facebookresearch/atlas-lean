/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.Homotopy.PointRelativeComposition

/-!
# Independent-carrier clients for both three-factor relative inverse families

The exact expression is the original Q carrier equivalence, the internally
constructed legacy comparison, and the identity product with the actual
plus carrier homeomorphism. These examples check the composition APIs on
five independent carrier universes. The production endpoint constructs all
these data internally.
-/

noncomputable section

open scoped ContinuousMap

universe uQ uLegacy uK uB uNative

variable {QN : Type uQ} {Q0 : Type uLegacy} {K : Type uK}
  {B0 : Type uB} {BN : Type uNative}
  [TopologicalSpace QN] [TopologicalSpace Q0] [TopologicalSpace K]
  [TopologicalSpace B0] [TopologicalSpace BN]

example
    (E_Q : QN ≃ₕ Q0) (e0 : Q0 ≃ₕ (K × B0)) (E_B : B0 ≃ₜ BN)
    (qN : QN) (q0 : Q0) (k : K) (b0 : B0) (bN : BN)
    (hQ : E_Q.toFun qN = q0) (hQI : E_Q.invFun q0 = qN)
    (h0 : e0.toFun q0 = (k, b0)) (h0I : e0.invFun (k, b0) = q0)
    (hB : E_B b0 = bN) (hBI : E_B.symm bN = b0)
    (LQ : ContinuousMap.HomotopyRel (E_Q.invFun.comp E_Q.toFun)
      (ContinuousMap.id QN) {qN})
    (RQ : ContinuousMap.HomotopyRel (E_Q.toFun.comp E_Q.invFun)
      (ContinuousMap.id Q0) {q0})
    (L0 : ContinuousMap.HomotopyRel (e0.invFun.comp e0.toFun)
      (ContinuousMap.id Q0) {q0})
    (R0 : ContinuousMap.HomotopyRel (e0.toFun.comp e0.invFun)
      (ContinuousMap.id (K × B0)) {(k, b0)}) :
    let idK := ContinuousMap.HomotopyEquiv.refl K
    let E_T := idK.prodCongr E_B.toHomotopyEquiv
    let E := (E_Q.trans e0).trans E_T
    E.toFun = ((ContinuousMap.id K).prodMap (E_B : C(B0, BN))).comp
      (e0.toFun.comp E_Q.toFun) ∧
    E.invFun = E_Q.invFun.comp (e0.invFun.comp
      ((ContinuousMap.id K).prodMap (E_B.symm : C(BN, B0)))) ∧
    E.toFun qN = (k, bN) ∧ E.invFun (k, bN) = qN ∧
    Nonempty (ContinuousMap.HomotopyRel (E.invFun.comp E.toFun)
      (ContinuousMap.id QN) {qN}) ∧
    Nonempty (ContinuousMap.HomotopyRel (E.toFun.comp E.invFun)
      (ContinuousMap.id (K × BN)) {(k, bN)}) ∧
    ∀ x : QN, (E.toFun x).1 = (e0.toFun (E_Q.toFun x)).1 := by
  let idK := ContinuousMap.HomotopyEquiv.refl K
  let EB := E_B.toHomotopyEquiv
  let E_T := idK.prodCongr EB
  let E_Q0 := E_Q.trans e0
  let E := E_Q0.trans E_T
  let LK : ContinuousMap.HomotopyRel (idK.invFun.comp idK.toFun)
      (ContinuousMap.id K) {k} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id K) {k}).cast
      (by apply ContinuousMap.ext; intro x; rfl) rfl
  let RK : ContinuousMap.HomotopyRel (idK.toFun.comp idK.invFun)
      (ContinuousMap.id K) {k} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id K) {k}).cast
      (by apply ContinuousMap.ext; intro x; rfl) rfl
  let LB : ContinuousMap.HomotopyRel (EB.invFun.comp EB.toFun)
      (ContinuousMap.id B0) {b0} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id B0) {b0}).cast
      (by
        apply ContinuousMap.ext
        intro x
        exact (E_B.symm_apply_apply x).symm) rfl
  let RB : ContinuousMap.HomotopyRel (EB.toFun.comp EB.invFun)
      (ContinuousMap.id BN) {bN} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id BN) {bN}).cast
      (by
        apply ContinuousMap.ext
        intro x
        exact (E_B.apply_symm_apply x).symm) rfl
  let LT := idK.prodCongrLeftHomotopyRel EB k b0 LK LB
  let RT := idK.prodCongrRightHomotopyRel EB k bN RK RB
  let LQ0 := E_Q.transLeftHomotopyRel e0 qN q0 hQ LQ L0
  let RQ0 := E_Q.transRightHomotopyRel e0 q0 (k, b0) h0I RQ R0
  have hQ0 : E_Q0.toFun qN = (k, b0) := (congrArg e0.toFun hQ).trans h0
  have hQ0I : E_Q0.invFun (k, b0) = qN := (congrArg E_Q.invFun h0I).trans hQI
  have hT : E_T.toFun (k, b0) = (k, bN) := Prod.ext rfl hB
  have hTI : E_T.invFun (k, bN) = (k, b0) := Prod.ext rfl hBI
  let L := E_Q0.transLeftHomotopyRel E_T qN (k, b0) hQ0 LQ0 LT
  let R := E_Q0.transRightHomotopyRel E_T (k, b0) (k, bN) hTI RQ0 RT
  refine ⟨?_, ?_, ?_, ?_, ⟨L⟩, ⟨R⟩, ?_⟩
  · apply ContinuousMap.ext
    intro x
    rfl
  · apply ContinuousMap.ext
    intro x
    rfl
  · exact (congrArg E_T.toFun hQ0).trans hT
  · exact (congrArg E_Q0.invFun hTI).trans hQ0I
  · intro x
    rfl

end
