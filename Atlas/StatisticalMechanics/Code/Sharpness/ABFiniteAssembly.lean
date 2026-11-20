/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Sharpness.ABCouplingReindex
import Code.Sharpness.ABPhysicalDeriv
import Code.Sharpness.FieldGhostDict

open Finset Set SimpleGraph

namespace StatMech
namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abfaBaseCoupling (J : Sym2 V → ℝ) (e : Sym2 V) : ℝ :=
  if e ∈ G.edgeFinset then J e else 0



noncomputable def abfaLiftCoupling (J : Sym2 V → ℝ) : Sym2 (Option V) → ℝ :=
  FieldGhostDict.ghostCoupling 0 1 (abfaBaseCoupling G J)

@[simp] theorem abfaLiftCoupling_some_some (J : Sym2 V → ℝ) (x y : V) :
    abfaLiftCoupling G J s(some x, some y) =
      if s(x, y) ∈ G.edgeFinset then J s(x, y) else 0 := rfl

@[simp] theorem abfaLiftCoupling_some_none (J : Sym2 V → ℝ) (x : V) :
    abfaLiftCoupling G J s(some x, none) = 0 := rfl


noncomputable def abfaParams (J : Sym2 V → ℝ) (beta h : ℝ) :
    Sym2 (Option V) → ℝ :=
  abpdBetaFieldParams (FieldGhostDict.ghostEdges V) (qField h)
    (abfaLiftCoupling G J) beta


noncomputable def abfaMag (J : Sym2 V → ℝ) (o : V) (beta h : ℝ) : ℝ :=
  probV (abfaParams G J beta h)
    (connEvent (withGhost G) Set.univ (some o) {none})



theorem abfa_differentiableAt_mag_joint (J : Sym2 V → ℝ) (o : V)
    (beta h : ℝ) :
    DifferentiableAt ℝ (Function.uncurry (abfaMag G J o)) (beta, h) := by
  have hp : ∀ e : Sym2 (Option V), DifferentiableAt ℝ
      (fun z : ℝ × ℝ => abfaParams G J z.1 z.2 e) (beta, h) := by
    intro e
    by_cases he : e ∈ FieldGhostDict.ghostEdges V
    · simp [abfaParams, abpdBetaFieldParams, paramOn, he, qField]
    · simp [abfaParams, abpdBetaFieldParams, paramOn, he, pBeta]
      fun_prop
  unfold abfaMag probV configWeightV
  change DifferentiableAt ℝ (fun z : ℝ × ℝ =>
    ∑ omega,
      (connEvent (withGhost G) Set.univ (some o) {none}).indicator
          (fun _ => (1 : ℝ)) omega *
        ∏ e, edgeWeightV (abfaParams G J z.1 z.2) omega e) (beta, h)
  apply DifferentiableAt.fun_sum
  intro omega _
  apply (differentiableAt_const _).mul
  have hedge : ∀ e : Sym2 (Option V), DifferentiableAt ℝ
      (fun z : ℝ × ℝ => edgeWeightV (abfaParams G J z.1 z.2) omega e)
        (beta, h) := by
    intro e
    unfold edgeWeightV
    by_cases homega : omega e = true
    · simp only [homega, if_true]
      exact hp e
    · simp only [homega]
      exact (differentiableAt_const _).sub (hp e)
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (fun e _ => (hedge e).hasFDerivAt)).differentiableAt



theorem abfa_differentiableAt_prob_joint
    (J : Sym2 V → ℝ) (A : Set (ConfigSpace (Sym2 (Option V))))
    (beta h : ℝ) :
    DifferentiableAt ℝ (Function.uncurry
      (fun b t => probV (abfaParams G J b t) A)) (beta, h) := by
  have hp : ∀ e : Sym2 (Option V), DifferentiableAt ℝ
      (fun z : ℝ × ℝ => abfaParams G J z.1 z.2 e) (beta, h) := by
    intro e
    by_cases he : e ∈ FieldGhostDict.ghostEdges V
    · simp [abfaParams, abpdBetaFieldParams, paramOn, he, qField]
    · simp [abfaParams, abpdBetaFieldParams, paramOn, he, pBeta]
      fun_prop
  unfold probV configWeightV
  change DifferentiableAt ℝ (fun z : ℝ × ℝ =>
    ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
      ∏ e, edgeWeightV (abfaParams G J z.1 z.2) omega e) (beta, h)
  apply DifferentiableAt.fun_sum
  intro omega _
  apply (differentiableAt_const _).mul
  have hedge : ∀ e : Sym2 (Option V), DifferentiableAt ℝ
      (fun z : ℝ × ℝ => edgeWeightV (abfaParams G J z.1 z.2) omega e)
        (beta, h) := by
    intro e
    unfold edgeWeightV
    by_cases homega : omega e = true
    · simp only [homega, if_true]
      exact hp e
    · simp only [homega]
      exact (differentiableAt_const _).sub (hp e)
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (fun e _ => (hedge e).hasFDerivAt)).differentiableAt

theorem abfaLiftCoupling_nonneg (J : Sym2 V → ℝ) (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
    (e : Sym2 (Option V)) : 0 ≤ abfaLiftCoupling G J e := by
  induction e using Sym2.ind with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abfaLiftCoupling, FieldGhostDict.ghostCoupling]
      · simp [abfaLiftCoupling, FieldGhostDict.ghostCoupling]
      · simp [abfaLiftCoupling, FieldGhostDict.ghostCoupling]
      · simp only [abfaLiftCoupling_some_some]
        by_cases he : s(x, y) ∈ G.edgeFinset
        · simp [he, hJ _ he]
        · simp [he]

private theorem abfa_map_some_injective :
    Function.Injective (Sym2.map (some : V → Option V)) := by
  intro e₁ e₂ heq
  induction e₁ using Sym2.ind with
  | _ a b =>
      induction e₂ using Sym2.ind with
      | _ c d =>
          simp only [Sym2.map_mk] at heq
          rw [Sym2.eq_iff] at heq ⊢
          rcases heq with ⟨hac, hbd⟩ | ⟨had, hbc⟩
          · exact Or.inl ⟨Option.some.inj hac, Option.some.inj hbd⟩
          · exact Or.inr ⟨Option.some.inj had, Option.some.inj hbc⟩



theorem abfaParams_mem (J : Sym2 V → ℝ) (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (e : Sym2 (Option V)) :
    0 ≤ abfaParams G J beta h e ∧ abfaParams G J beta h e ≤ 1 := by
  unfold abfaParams abpdBetaFieldParams paramOn
  by_cases he : e ∈ FieldGhostDict.ghostEdges V
  · simp only [he, if_true]
    exact qField_mem h hh
  · simp only [he, if_false]
    exact ⟨pBeta_nonneg (mul_nonneg hbeta (abfaLiftCoupling_nonneg G J hJ e)),
      (pBeta_lt_one (abfaLiftCoupling G J e) beta).le⟩

private theorem abfa_not_orig_not_ghost_coupling_zero (J : Sym2 V → ℝ)
    (e : Sym2 (Option V)) (horig : e ∉ FieldGhostDict.origEdges G)
    (hghost : e ∉ FieldGhostDict.ghostEdges V) : abfaLiftCoupling G J e = 0 := by
  induction e using Sym2.ind with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abfaLiftCoupling, FieldGhostDict.ghostCoupling]
      · exact False.elim (hghost (by simp [FieldGhostDict.ghostEdges, Sym2.eq_swap]))
      · exact False.elim (hghost (by simp [FieldGhostDict.ghostEdges]))
      · simp only [abfaLiftCoupling_some_some]
        have hnot : s(x, y) ∉ G.edgeFinset := by
          intro he
          apply horig
          exact Finset.mem_image.mpr ⟨s(x, y), he, by simp⟩
        simp [hnot]


theorem abfa_deriv_beta_eq_origEdges (J : Sym2 V → ℝ) (o : V) (beta h : ℝ) :
    deriv (fun b => abfaMag G J o b h) beta =
      ∑ e ∈ FieldGhostDict.origEdges G,
        abfaLiftCoupling G J e *
          probV (abfaParams G J beta h)
            (abgiClosedPivotal e
              (connEvent (withGhost G) Set.univ (some o) {none})) := by
  unfold abfaMag abfaParams
  rw [abpd_deriv_beta_field_profile_closed _ _ _ _
    (isIncreasing_connEvent (withGhost G) Set.univ (some o) {none}) beta]
  rw [show (∑ e : Sym2 (Option V),
      if e ∈ FieldGhostDict.ghostEdges V then 0 else
        abfaLiftCoupling G J e *
          probV (abpdBetaFieldParams (FieldGhostDict.ghostEdges V) (qField h)
              (abfaLiftCoupling G J) beta)
            (abgiClosedPivotal e
              (connEvent (withGhost G) Set.univ (some o) {none}))) =
      ∑ e ∈ FieldGhostDict.origEdges G,
        abfaLiftCoupling G J e *
          probV (abpdBetaFieldParams (FieldGhostDict.ghostEdges V) (qField h)
              (abfaLiftCoupling G J) beta)
            (abgiClosedPivotal e
              (connEvent (withGhost G) Set.univ (some o) {none})) by
    symm
    apply Finset.sum_subset_zero_on_sdiff
      (s₁ := FieldGhostDict.origEdges G) (s₂ := Finset.univ)
      (f := fun e => abfaLiftCoupling G J e *
        probV (abpdBetaFieldParams (FieldGhostDict.ghostEdges V) (qField h)
            (abfaLiftCoupling G J) beta)
          (abgiClosedPivotal e (connEvent (withGhost G) Set.univ (some o) {none})))
      (g := fun e => if e ∈ FieldGhostDict.ghostEdges V then 0 else
        abfaLiftCoupling G J e *
          probV (abpdBetaFieldParams (FieldGhostDict.ghostEdges V) (qField h)
              (abfaLiftCoupling G J) beta)
            (abgiClosedPivotal e (connEvent (withGhost G) Set.univ (some o) {none})))
    · exact Finset.subset_univ _
    · intro e he
      have horig : e ∉ FieldGhostDict.origEdges G := (Finset.mem_sdiff.mp he).2
      by_cases hghost : e ∈ FieldGhostDict.ghostEdges V
      · simp [hghost]
      · simp [hghost, abfa_not_orig_not_ghost_coupling_zero G J e horig hghost]
    · intro e horig
      have hghost : e ∉ FieldGhostDict.ghostEdges V := by
        intro hg
        exact (Finset.disjoint_left.mp (FieldGhostDict.disjoint_orig_ghost G)) horig hg
      simp [hghost]]




theorem abfa_deriv_beta_connTarget_eq_origEdges
    (J : Sym2 V → ℝ) (o : V) (B : Set (Option V)) (beta h : ℝ) :
    deriv (fun b => probV (abfaParams G J b h)
      (connEvent (withGhost G) Set.univ (some o) B)) beta =
      ∑ e ∈ FieldGhostDict.origEdges G,
        abfaLiftCoupling G J e *
          probV (abfaParams G J beta h)
            (abgiClosedPivotal e
              (connEvent (withGhost G) Set.univ (some o) B)) := by
  unfold abfaParams
  rw [abpd_deriv_beta_field_profile_closed _ _ _ _
    (isIncreasing_connEvent (withGhost G) Set.univ (some o) B) beta]
  rw [show (∑ e : Sym2 (Option V),
      if e ∈ FieldGhostDict.ghostEdges V then 0 else
        abfaLiftCoupling G J e *
          probV (abpdBetaFieldParams (FieldGhostDict.ghostEdges V) (qField h)
              (abfaLiftCoupling G J) beta)
            (abgiClosedPivotal e
              (connEvent (withGhost G) Set.univ (some o) B))) =
      ∑ e ∈ FieldGhostDict.origEdges G,
        abfaLiftCoupling G J e *
          probV (abpdBetaFieldParams (FieldGhostDict.ghostEdges V) (qField h)
              (abfaLiftCoupling G J) beta)
            (abgiClosedPivotal e
              (connEvent (withGhost G) Set.univ (some o) B)) by
    symm
    apply Finset.sum_subset_zero_on_sdiff
      (s₁ := FieldGhostDict.origEdges G) (s₂ := Finset.univ)
      (f := fun e => abfaLiftCoupling G J e *
        probV (abpdBetaFieldParams (FieldGhostDict.ghostEdges V) (qField h)
            (abfaLiftCoupling G J) beta)
          (abgiClosedPivotal e
            (connEvent (withGhost G) Set.univ (some o) B)))
      (g := fun e => if e ∈ FieldGhostDict.ghostEdges V then 0 else
        abfaLiftCoupling G J e *
          probV (abpdBetaFieldParams (FieldGhostDict.ghostEdges V) (qField h)
              (abfaLiftCoupling G J) beta)
            (abgiClosedPivotal e
              (connEvent (withGhost G) Set.univ (some o) B)))
    · exact Finset.subset_univ _
    · intro e he
      have horig : e ∉ FieldGhostDict.origEdges G := (Finset.mem_sdiff.mp he).2
      by_cases hghost : e ∈ FieldGhostDict.ghostEdges V
      · simp [hghost]
      · simp [hghost, abfa_not_orig_not_ghost_coupling_zero G J e horig hghost]
    · intro e horig
      have hghost : e ∉ FieldGhostDict.ghostEdges V := by
        intro hg
        exact (Finset.disjoint_left.mp (FieldGhostDict.disjoint_orig_ghost G)) horig hg
      simp [hghost]]



theorem abfa_deriv_beta_nonneg (J : Sym2 V → ℝ) (o : V) (beta h : ℝ)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    0 ≤ deriv (fun b => abfaMag G J o b h) beta := by
  rw [abfa_deriv_beta_eq_origEdges G J o beta h]
  apply Finset.sum_nonneg
  intro e he
  exact mul_nonneg (abfaLiftCoupling_nonneg G J hJ e)
    (abgi_probV_nonneg (abfaParams G J beta h)
      (abfaParams_mem G J hJ beta h hbeta hh)
      (abgiClosedPivotal e
        (connEvent (withGhost G) Set.univ (some o) {none})))



theorem abfa_deriv_field_nonneg (J : Sym2 V → ℝ) (o : V) (beta h : ℝ)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    0 ≤ deriv (fun t => abfaMag G J o beta t) h := by
  have hfield := abgi_deriv_field_eq_sum_restricted G
    (fun e => pBeta (abfaLiftCoupling G J e) beta) h o
  change deriv (fun t => abfaMag G J o beta t) h =
    ∑ x : V,
      probV (abfaParams G J beta h)
        (connEvent (withGhost G) Set.univ (some o) {some x} ∩
          (connEvent (withGhost G) Set.univ (some o) {none})ᶜ) at hfield
  rw [hfield]
  exact Finset.sum_nonneg (fun x _ =>
    abgi_probV_nonneg (abfaParams G J beta h)
      (abfaParams_mem G J hJ beta h hbeta hh) _)



theorem abfaMag_monotoneOn_beta (J : Sym2 V → ℝ) (o : V) (h : ℝ)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) (hh : 0 ≤ h) :
    MonotoneOn (fun beta => abfaMag G J o beta h) (Set.Ici 0) := by
  have hdiff : ∀ beta : ℝ,
      DifferentiableAt ℝ (fun b => abfaMag G J o b h) beta := by
    intro beta
    have hjoint := abfa_differentiableAt_mag_joint G J o beta h
    have hline : DifferentiableAt ℝ (fun b : ℝ => (b, h)) beta :=
      differentiableAt_id.prodMk (differentiableAt_const h)
    simpa [Function.comp_def, Function.uncurry] using hjoint.comp beta hline
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro beta hbeta
    exact (hdiff beta).continuousAt.continuousWithinAt
  · intro beta hbeta
    exact (hdiff beta).differentiableWithinAt
  · intro beta hbeta
    have hbeta0 : 0 ≤ beta := interior_subset hbeta
    exact abfa_deriv_beta_nonneg G J o beta h hJ hbeta0 hh



theorem abfaMag_monotoneOn_field (J : Sym2 V → ℝ) (o : V) (beta : ℝ)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) (hbeta : 0 ≤ beta) :
    MonotoneOn (fun h => abfaMag G J o beta h) (Set.Ici 0) := by
  have hdiff : ∀ h : ℝ,
      DifferentiableAt ℝ (fun t => abfaMag G J o beta t) h := by
    intro h
    have hjoint := abfa_differentiableAt_mag_joint G J o beta h
    have hline : DifferentiableAt ℝ (fun t : ℝ => (beta, t)) h :=
      (differentiableAt_const beta).prodMk differentiableAt_id
    simpa [Function.comp_def, Function.uncurry] using hjoint.comp h hline
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro h hh
    exact (hdiff h).continuousAt.continuousWithinAt
  · intro h hh
    exact (hdiff h).differentiableWithinAt
  · intro h hh
    have hh0 : 0 ≤ h := interior_subset hh
    exact abfa_deriv_field_nonneg G J o beta h hJ hbeta hh0





theorem abfa_aizenmanBarsky (J : Sym2 V → ℝ) (o : V) (beta h J0 : ℝ)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
    (hrow : ∀ x, abcrIncidentCoupling G J x = J0)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hmag : ∀ x : V,
      probV (abfaParams G J beta h)
        (connEvent (withGhost G) Set.univ (some x) {none}) =
          abfaMag G J o beta h) :
    deriv (fun b => abfaMag G J o b h) beta ≤
      J0 * abfaMag G J o beta h * deriv (fun t => abfaMag G J o beta t) h := by
  let p := abfaParams G J beta h
  let A : Set (ConfigSpace (Sym2 (Option V))) :=
    connEvent (withGhost G) Set.univ (some o) {none}
  let R : V → ℝ := fun x =>
    probV p (connEvent (withGhost G) Set.univ (some o) {some x} ∩ Aᶜ)
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 := abfaParams_mem G J hJ beta h hbeta hh
  rw [abfa_deriv_beta_eq_origEdges G J o beta h]
  unfold FieldGhostDict.origEdges
  rw [Finset.sum_image (fun _ _ _ _ heq => abfa_map_some_injective heq)]
  calc
    (∑ e ∈ G.edgeFinset,
        abfaLiftCoupling G J (Sym2.map some e) *
          probV p (abgiClosedPivotal (Sym2.map some e) A)) ≤
      ∑ e ∈ G.edgeFinset,
        J e * (abfaMag G J o beta h * abcrEndpointSum R e) := by
      apply Finset.sum_le_sum
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
          rw [Sym2.map_mk]
          simp only [abfaLiftCoupling_some_some, he, if_true, abcrEndpointSum_mk]
          have hedge := abcc_closedPivotal_le_products (withGhost G) p hp
            (some o) (some x) (some y) none
          rw [hmag x, hmag y] at hedge
          change probV p (abgiClosedPivotal s(some x, some y) A) ≤
            R x * abfaMag G J o beta h + R y * abfaMag G J o beta h at hedge
          calc
            J s(x, y) * probV p (abgiClosedPivotal s(some x, some y) A) ≤
                J s(x, y) *
                  (R x * abfaMag G J o beta h + R y * abfaMag G J o beta h) :=
              mul_le_mul_of_nonneg_left hedge (hJ _ he)
            _ = J s(x, y) *
                (abfaMag G J o beta h * (R x + R y)) := by ring
    _ = abfaMag G J o beta h *
        (∑ e ∈ G.edgeFinset, J e * abcrEndpointSum R e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = abfaMag G J o beta h * (J0 * ∑ x : V, R x) := by
      rw [abcr_edgeSum_eq_rowSum G J R J0 hrow]
    _ = J0 * abfaMag G J o beta h * deriv (fun t => abfaMag G J o beta t) h := by
      have hfield := abgi_deriv_field_eq_sum_restricted G
        (fun e => pBeta (abfaLiftCoupling G J e) beta) h o
      change deriv (fun t => abfaMag G J o beta t) h = ∑ x : V, R x at hfield
      rw [hfield]
      ring






theorem abfa_aizenmanBarsky_le_envelope
    (J : Sym2 V → ℝ) (o : V) (beta h J0 U : ℝ)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
    (hrow : ∀ x, abcrIncidentCoupling G J x ≤ J0)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (hU : 0 ≤ U)
    (htarget : ∀ x : V,
      probV (abfaParams G J beta h)
        (connEvent (withGhost G) Set.univ (some x) {none}) ≤ U) :
    deriv (fun b => abfaMag G J o b h) beta ≤
      J0 * U * deriv (fun t => abfaMag G J o beta t) h := by
  let p := abfaParams G J beta h
  let A : Set (ConfigSpace (Sym2 (Option V))) :=
    connEvent (withGhost G) Set.univ (some o) {none}
  let R : V → ℝ := fun x =>
    probV p (connEvent (withGhost G) Set.univ (some o) {some x} ∩ Aᶜ)
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 :=
    abfaParams_mem G J hJ beta h hbeta hh
  have hR : ∀ x, 0 ≤ R x := fun x => abgi_probV_nonneg p hp _
  rw [abfa_deriv_beta_eq_origEdges G J o beta h]
  unfold FieldGhostDict.origEdges
  rw [Finset.sum_image (fun _ _ _ _ heq => abfa_map_some_injective heq)]
  calc
    (∑ e ∈ G.edgeFinset,
        abfaLiftCoupling G J (Sym2.map some e) *
          probV p (abgiClosedPivotal (Sym2.map some e) A)) ≤
      ∑ e ∈ G.edgeFinset, J e * (U * abcrEndpointSum R e) := by
      apply Finset.sum_le_sum
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
          rw [Sym2.map_mk]
          simp only [abfaLiftCoupling_some_some, he, if_true,
            abcrEndpointSum_mk]
          have hedge := abcc_closedPivotal_le_products (withGhost G) p hp
            (some o) (some x) (some y) none
          change probV p (abgiClosedPivotal s(some x, some y) A) ≤
            R x * probV p
                (connEvent (withGhost G) Set.univ (some y) {none}) +
              R y * probV p
                (connEvent (withGhost G) Set.univ (some x) {none}) at hedge
          have hedge' : probV p (abgiClosedPivotal s(some x, some y) A) ≤
              R x * U + R y * U :=
            hedge.trans (add_le_add
              (mul_le_mul_of_nonneg_left (htarget y) (hR x))
              (mul_le_mul_of_nonneg_left (htarget x) (hR y)))
          calc
            J s(x, y) * probV p
                (abgiClosedPivotal s(some x, some y) A) ≤
              J s(x, y) * (R x * U + R y * U) :=
                mul_le_mul_of_nonneg_left hedge' (hJ _ he)
            _ = J s(x, y) * (U * (R x + R y)) := by ring
    _ = U * (∑ e ∈ G.edgeFinset,
        J e * abcrEndpointSum R e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ U * (J0 * ∑ x : V, R x) :=
      mul_le_mul_of_nonneg_left
        (abcr_edgeSum_le_rowSum G J R J0 hR hrow) hU
    _ = J0 * U * deriv (fun t => abfaMag G J o beta t) h := by
      have hfield := abgi_deriv_field_eq_sum_restricted G
        (fun e => pBeta (abfaLiftCoupling G J e) beta) h o
      change deriv (fun t => abfaMag G J o beta t) h = ∑ x : V, R x at hfield
      rw [hfield]
      ring



theorem abfa_aizenmanBarsky_target_le_envelope
    (J : Sym2 V → ℝ) (o : V) (B : Set (Option V))
    (beta h J0 U : ℝ) (hghost : none ∈ B)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
    (hrow : ∀ x, abcrIncidentCoupling G J x ≤ J0)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (hU : 0 ≤ U)
    (htarget : ∀ x : V,
      probV (abfaParams G J beta h)
        (connEvent (withGhost G) Set.univ (some x) B) ≤ U) :
    deriv (fun b => probV (abfaParams G J b h)
        (connEvent (withGhost G) Set.univ (some o) B)) beta ≤
      J0 * U * deriv (fun t => probV (abfaParams G J beta t)
        (connEvent (withGhost G) Set.univ (some o) B)) h := by
  let p := abfaParams G J beta h
  let A : Set (ConfigSpace (Sym2 (Option V))) :=
    connEvent (withGhost G) Set.univ (some o) B
  let R : V → ℝ := fun x =>
    probV p (connEvent (withGhost G) Set.univ (some o) {some x} ∩ Aᶜ)
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 :=
    abfaParams_mem G J hJ beta h hbeta hh
  have hR : ∀ x, 0 ≤ R x := fun x => abgi_probV_nonneg p hp _
  rw [abfa_deriv_beta_connTarget_eq_origEdges G J o B beta h]
  unfold FieldGhostDict.origEdges
  rw [Finset.sum_image (fun _ _ _ _ heq => abfa_map_some_injective heq)]
  calc
    (∑ e ∈ G.edgeFinset,
        abfaLiftCoupling G J (Sym2.map some e) *
          probV p (abgiClosedPivotal (Sym2.map some e) A)) ≤
      ∑ e ∈ G.edgeFinset, J e * (U * abcrEndpointSum R e) := by
      apply Finset.sum_le_sum
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
          rw [Sym2.map_mk]
          simp only [abfaLiftCoupling_some_some, he, if_true,
            abcrEndpointSum_mk]
          have hedge := abcc_closedPivotal_le_products_set
            (withGhost G) p hp (some o) (some x) (some y) B
          change probV p (abgiClosedPivotal s(some x, some y) A) ≤
            R x * probV p (connEvent (withGhost G) Set.univ (some y) B) +
              R y * probV p (connEvent (withGhost G) Set.univ (some x) B) at hedge
          have hedge' : probV p (abgiClosedPivotal s(some x, some y) A) ≤
              R x * U + R y * U :=
            hedge.trans (add_le_add
              (mul_le_mul_of_nonneg_left (htarget y) (hR x))
              (mul_le_mul_of_nonneg_left (htarget x) (hR y)))
          calc
            J s(x, y) * probV p
                (abgiClosedPivotal s(some x, some y) A) ≤
              J s(x, y) * (R x * U + R y * U) :=
                mul_le_mul_of_nonneg_left hedge' (hJ _ he)
            _ = J s(x, y) * (U * (R x + R y)) := by ring
    _ = U * (∑ e ∈ G.edgeFinset,
        J e * abcrEndpointSum R e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ U * (J0 * ∑ x : V, R x) :=
      mul_le_mul_of_nonneg_left
        (abcr_edgeSum_le_rowSum G J R J0 hR hrow) hU
    _ = J0 * U * deriv (fun t => probV (abfaParams G J beta t)
        (connEvent (withGhost G) Set.univ (some o) B)) h := by
      have hfield := abgi_deriv_field_eq_sum_restricted_target G
        (fun e => pBeta (abfaLiftCoupling G J e) beta) h o B hghost
      change deriv (fun t => probV (abfaParams G J beta t)
        (connEvent (withGhost G) Set.univ (some o) B)) h = ∑ x : V, R x at hfield
      rw [hfield]
      ring

end Sharpness
end StatMech
