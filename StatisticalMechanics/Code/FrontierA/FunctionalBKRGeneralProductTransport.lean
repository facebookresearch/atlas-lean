/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.FunctionalBKRGeneralProductCore

open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal

namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]



section DependentBlockExpectation

variable {D : E → Type*} [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
  [∀ e, Fintype (S e)] [∀ e, DecidableEq (S e)]



noncomputable def finitePiExpectation (w : ∀ e, S e → ℝ)
    (H : (∀ e, S e) → ℝ) : ℝ :=
  ∑ x, (∏ e, w e (x e)) * H x


noncomputable def finitePiDualExpectation (w : ∀ e, S e → ℝ)
    (H : ((∀ e, S e) × (∀ e, S e)) → ℝ) : ℝ :=
  finitePiExpectation w (fun x =>
    finitePiExpectation w (fun y => H (x, y)))

theorem dualProductExpectation_eq_iterated
    {I : Type*} [Fintype I] [DecidableEq I]
    (phi : I → Bool → ℝ)
    (H : (StatMech.ConfigSpace I × StatMech.ConfigSpace I) → ℝ) :
    dualProductExpectation phi H =
      productExpectation phi (fun omega =>
        productExpectation phi (fun eta => H (omega, eta))) := by
  unfold dualProductExpectation productExpectation
  apply Finset.sum_congr rfl
  intro omega _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  ring

theorem productExpectation_decodeDependent_point
    (phi : Sigma D → Bool → ℝ)
    (decode : ∀ e, (D e → Bool) → S e)
    (w : ∀ e, S e → ℝ)
    (hexpect : ∀ e (h : S e → ℝ),
      productExpectation (fun d b => phi ⟨e, d⟩ b) (h ∘ decode e) =
        ∑ s, w e s * h s)
    (x : ∀ e, S e) :
    productExpectation phi (fun omega =>
      if decodeDependentBlockConfig decode omega = x then 1 else 0) =
      ∏ e, w e (x e) := by
  classical
  let curryEquiv : (Sigma D → Bool) ≃ (∀ e, D e → Bool) :=
    Equiv.piCurry (fun (_ : E) (_ : D _) ↦ Bool)
  unfold productExpectation
  rw [← curryEquiv.symm.sum_comp]
  let term : ∀ e, (D e → Bool) → ℝ := fun e block =>
    pweight (fun d b => phi ⟨e, d⟩ b) block *
      if decode e block = x e then 1 else 0
  have hsummand : ∀ blocks : ∀ e, D e → Bool,
      pweight phi (curryEquiv.symm blocks) *
          (if decodeDependentBlockConfig decode (curryEquiv.symm blocks) = x
            then 1 else 0) =
        ∏ e, term e (blocks e) := by
    intro blocks
    have hweight : pweight phi (curryEquiv.symm blocks) =
        ∏ e, pweight (fun d b => phi ⟨e, d⟩ b) (blocks e) := by
      unfold pweight curryEquiv
      rw [Fintype.prod_sigma]
      rfl
    rw [hweight]
    by_cases hconfig : decodeDependentBlockConfig decode
        (curryEquiv.symm blocks) = x
    · have hcoord : ∀ e, decode e (blocks e) = x e := by
        intro e
        have := congrFun hconfig e
        simpa [decodeDependentBlockConfig, curryEquiv] using this
      simp only [hconfig, if_true, term, hcoord]
      simp
    · have hcoord : ∃ e, decode e (blocks e) ≠ x e := by
        by_contra h
        push_neg at h
        apply hconfig
        funext e
        simpa [decodeDependentBlockConfig, curryEquiv] using h e
      obtain ⟨e, he⟩ := hcoord
      simp only [hconfig, if_false, mul_zero]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [term, he]
  simp_rw [hsummand]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum (fun e =>
    (Finset.univ : Finset (D e → Bool))) term]
  apply Finset.prod_congr rfl
  intro e _
  change productExpectation (fun d b => phi ⟨e, d⟩ b)
      ((fun s => if s = x e then 1 else 0) ∘ decode e) = w e (x e)
  rw [hexpect]
  simp

theorem productExpectation_decodeDependent_eq_finitePiExpectation
    (phi : Sigma D → Bool → ℝ)
    (decode : ∀ e, (D e → Bool) → S e)
    (w : ∀ e, S e → ℝ)
    (hexpect : ∀ e (h : S e → ℝ),
      productExpectation (fun d b => phi ⟨e, d⟩ b) (h ∘ decode e) =
        ∑ s, w e s * h s)
    (H : (∀ e, S e) → ℝ) :
    productExpectation phi (H ∘ decodeDependentBlockConfig decode) =
      finitePiExpectation w H := by
  classical
  unfold productExpectation finitePiExpectation
  calc
    ∑ omega, pweight phi omega *
        (H ∘ decodeDependentBlockConfig decode) omega =
        ∑ omega, pweight phi omega *
          ∑ x, if decodeDependentBlockConfig decode omega = x
            then H x else 0 := by
      apply Finset.sum_congr rfl
      intro omega _
      congr 1
      simp [Function.comp_apply]
    _ = ∑ x, (∑ omega, pweight phi omega *
          (if decodeDependentBlockConfig decode omega = x then 1 else 0)) *
          H x := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro omega _
      by_cases hdecode : decodeDependentBlockConfig decode omega = x
      · simp [hdecode]
      · simp [hdecode]
    _ = ∑ x, (∏ e, w e (x e)) * H x := by
      apply Finset.sum_congr rfl
      intro x _
      change productExpectation phi (fun omega ↦
        if decodeDependentBlockConfig decode omega = x then 1 else 0) * H x = _
      rw [productExpectation_decodeDependent_point phi decode w hexpect x]

theorem dualProductExpectation_decodeDependent_eq_finitePiDualExpectation
    (phi : Sigma D → Bool → ℝ)
    (decode : ∀ e, (D e → Bool) → S e)
    (w : ∀ e, S e → ℝ)
    (hexpect : ∀ e (h : S e → ℝ),
      productExpectation (fun d b => phi ⟨e, d⟩ b) (h ∘ decode e) =
        ∑ s, w e s * h s)
    (H : ((∀ e, S e) × (∀ e, S e)) → ℝ) :
    dualProductExpectation phi (fun pair =>
      H (decodeDependentBlockConfig decode pair.1,
        decodeDependentBlockConfig decode pair.2)) =
      finitePiDualExpectation w H := by
  rw [dualProductExpectation_eq_iterated]
  calc
    productExpectation phi (fun omega =>
        productExpectation phi (fun eta =>
          H (decodeDependentBlockConfig decode omega,
            decodeDependentBlockConfig decode eta))) =
        productExpectation phi
          ((fun x => finitePiExpectation w (fun y => H (x, y))) ∘
            decodeDependentBlockConfig decode) := by
      apply congrArg (productExpectation phi)
      funext omega
      exact productExpectation_decodeDependent_eq_finitePiExpectation
        phi decode w hexpect
          (fun y => H (decodeDependentBlockConfig decode omega, y))
    _ = finitePiDualExpectation w H :=
      productExpectation_decodeDependent_eq_finitePiExpectation
        phi decode w hexpect _

end DependentBlockExpectation

end StatMech.FrontierA
