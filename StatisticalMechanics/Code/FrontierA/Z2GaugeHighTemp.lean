/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

section GaugeHypergraph

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

noncomputable local instance instPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p


abbrev GaugeConfig (E : Type*) := E -> Bool


def gaugeEdgeSpin (omega : GaugeConfig E) (e : E) : ℝ :=
  if omega e then 1 else -1


def plaquetteSpin (incidence : P -> Finset E) (omega : GaugeConfig E) (p : P) : ℝ :=
  ∏ e ∈ incidence p, gaugeEdgeSpin omega e


def plaquetteIncidenceCount (incidence : P -> Finset E) (A : Finset P) (e : E) : Nat :=
  ∑ p ∈ A, if e ∈ incidence p then 1 else 0


def IsClosedPlaquetteSet (incidence : P -> Finset E) (A : Finset P) : Prop :=
  ∀ e, Even (plaquetteIncidenceCount incidence A e)




def HasWilsonBoundary (incidence : P -> Finset E) (A : Finset P)
    (L : Finset E) : Prop :=
  ∀ e, Even (plaquetteIncidenceCount incidence A e + if e ∈ L then 1 else 0)



def wilsonSpin (L : Finset E) (omega : GaugeConfig E) : ℝ :=
  ∏ e ∈ L, gaugeEdgeSpin omega e


def gaugeAction (incidence : P -> Finset E) (K : P -> ℝ)
    (omega : GaugeConfig E) : ℝ :=
  ∑ p, K p * plaquetteSpin incidence omega p


noncomputable def gaugeWeight (incidence : P -> Finset E) (K : P -> ℝ)
    (omega : GaugeConfig E) : ℝ :=
  Real.exp (gaugeAction incidence K omega)


noncomputable def gaugePartition (incidence : P -> Finset E) (K : P -> ℝ) : ℝ :=
  ∑ omega : GaugeConfig E, gaugeWeight incidence K omega


noncomputable def gaugeWilsonNumerator (incidence : P -> Finset E) (K : P -> ℝ)
    (L : Finset E) : ℝ :=
  ∑ omega : GaugeConfig E, wilsonSpin L omega * gaugeWeight incidence K omega

omit [Fintype E] [Fintype P] [DecidableEq P] in
@[simp] theorem plaquetteIncidenceCount_empty (incidence : P -> Finset E) (e : E) :
    plaquetteIncidenceCount incidence (∅ : Finset P) e = 0 := by
  simp [plaquetteIncidenceCount]

omit [Fintype E] [Fintype P] in
theorem plaquetteIncidenceCount_insert (incidence : P -> Finset E)
    {p : P} {A : Finset P} (hp : p ∉ A) (e : E) :
    plaquetteIncidenceCount incidence (insert p A) e =
      (if e ∈ incidence p then 1 else 0) + plaquetteIncidenceCount incidence A e := by
  unfold plaquetteIncidenceCount
  rw [Finset.sum_insert hp]

omit [Fintype E] [Fintype P] [DecidableEq P] in
@[simp] theorem hasWilsonBoundary_empty_iff (incidence : P -> Finset E)
    (A : Finset P) :
    HasWilsonBoundary incidence A (∅ : Finset E) ↔ IsClosedPlaquetteSet incidence A := by
  simp [HasWilsonBoundary, IsClosedPlaquetteSet]

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem gaugeEdgeSpin_eq_one_or_neg_one (omega : GaugeConfig E) (e : E) :
    gaugeEdgeSpin omega e = 1 ∨ gaugeEdgeSpin omega e = -1 := by
  unfold gaugeEdgeSpin
  cases omega e <;> simp

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
@[simp] theorem gaugeEdgeSpin_sq (omega : GaugeConfig E) (e : E) :
    gaugeEdgeSpin omega e ^ 2 = 1 := by
  rcases gaugeEdgeSpin_eq_one_or_neg_one omega e with h | h <;> rw [h] <;> norm_num

omit [Fintype P] [DecidableEq P] in

theorem sum_gaugeEdgeSpin_pow (m : Nat) :
    (∑ b : Bool, (if b then (1 : ℝ) else -1) ^ m) = if Even m then 2 else 0 := by
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false, one_pow]
  by_cases hm : Even m
  · rw [if_pos hm, hm.neg_one_pow]
    norm_num
  · rw [if_neg hm, Nat.not_even_iff_odd] at *
    rw [hm.neg_one_pow]
    norm_num

omit [Fintype P] [DecidableEq P] in

theorem sum_gaugeEdgeSpin_monomial (m : E -> Nat) :
    (∑ omega : GaugeConfig E, ∏ e : E, (gaugeEdgeSpin omega e) ^ (m e)) =
      if (∀ e, Even (m e)) then (2 : ℝ) ^ Fintype.card E else 0 := by
  have hfactor :
      (∑ omega : GaugeConfig E, ∏ e : E, (gaugeEdgeSpin omega e) ^ (m e)) =
        ∏ e : E, ∑ b : Bool, (if b then (1 : ℝ) else -1) ^ (m e) := by
    unfold gaugeEdgeSpin
    exact (Fintype.prod_sum
      (fun (e : E) (b : Bool) => (if b then (1 : ℝ) else -1) ^ (m e))).symm
  rw [hfactor]
  simp_rw [sum_gaugeEdgeSpin_pow]
  by_cases hm : ∀ e, Even (m e)
  · rw [if_pos hm]
    have : (∏ e : E, if Even (m e) then (2 : ℝ) else 0) = ∏ _e : E, (2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro e _
      rw [if_pos (hm e)]
    rw [this, Finset.prod_const, Finset.card_univ]
  · rw [if_neg hm]
    push Not at hm
    obtain ⟨e, he⟩ := hm
    exact Finset.prod_eq_zero (Finset.mem_univ e) (if_neg he)

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem plaquetteSpin_eq_one_or_neg_one (incidence : P -> Finset E)
    (omega : GaugeConfig E) (p : P) :
    plaquetteSpin incidence omega p = 1 ∨ plaquetteSpin incidence omega p = -1 := by
  classical
  unfold plaquetteSpin
  generalize incidence p = S
  induction S using Finset.induction_on with
  | empty => simp
  | @insert e S he ih =>
      rw [Finset.prod_insert he]
      rcases gaugeEdgeSpin_eq_one_or_neg_one omega e with he' | he' <;>
        rcases ih with hS | hS <;> simp [he', hS]

omit [Fintype P] [DecidableEq P] in


theorem prod_plaquetteSpin_eq_prod_incidence_pow (incidence : P -> Finset E)
    (omega : GaugeConfig E) (A : Finset P) :
    (∏ p ∈ A, plaquetteSpin incidence omega p) =
      ∏ e : E, (gaugeEdgeSpin omega e) ^ (plaquetteIncidenceCount incidence A e) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [plaquetteIncidenceCount]
  | @insert p A hp ih =>
      rw [Finset.prod_insert hp, ih]
      have hpSpin : plaquetteSpin incidence omega p =
          ∏ e : E, (gaugeEdgeSpin omega e) ^ (if e ∈ incidence p then 1 else 0) := by
        unfold plaquetteSpin
        rw [show (∏ e : E, (gaugeEdgeSpin omega e) ^
            (if e ∈ incidence p then 1 else 0)) =
              ∏ e : E, if e ∈ incidence p then gaugeEdgeSpin omega e else 1 by
          apply Finset.prod_congr rfl
          intro e _
          by_cases he : e ∈ incidence p <;> simp [he]]
        rw [Finset.prod_ite_mem, Finset.univ_inter]
      rw [hpSpin, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro e _
      rw [← pow_add]
      congr 1
      exact (plaquetteIncidenceCount_insert incidence hp e).symm

omit [Fintype P] [DecidableEq P] in


theorem sum_prod_plaquetteSpin (incidence : P -> Finset E) (A : Finset P) :
    (∑ omega : GaugeConfig E, ∏ p ∈ A, plaquetteSpin incidence omega p) =
      if IsClosedPlaquetteSet incidence A then (2 : ℝ) ^ Fintype.card E else 0 := by
  classical
  simp_rw [prod_plaquetteSpin_eq_prod_incidence_pow incidence]
  rw [sum_gaugeEdgeSpin_monomial]
  by_cases hclosed : ∀ e, Even (plaquetteIncidenceCount incidence A e)
  · rw [if_pos hclosed]
    rw [if_pos (show IsClosedPlaquetteSet incidence A from hclosed)]
  · rw [if_neg hclosed]
    rw [if_neg (show ¬IsClosedPlaquetteSet incidence A from hclosed)]

omit [Fintype P] [DecidableEq P] in

theorem wilsonSpin_eq_prod_indicator_pow (L : Finset E) (omega : GaugeConfig E) :
    wilsonSpin L omega =
      ∏ e : E, (gaugeEdgeSpin omega e) ^ (if e ∈ L then 1 else 0) := by
  unfold wilsonSpin
  rw [show (∏ e : E, (gaugeEdgeSpin omega e) ^ (if e ∈ L then 1 else 0)) =
      ∏ e : E, if e ∈ L then gaugeEdgeSpin omega e else 1 by
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : e ∈ L <;> simp [he]]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

omit [Fintype P] [DecidableEq P] in


theorem sum_wilson_mul_prod_plaquetteSpin (incidence : P -> Finset E)
    (A : Finset P) (L : Finset E) :
    (∑ omega : GaugeConfig E,
        wilsonSpin L omega * ∏ p ∈ A, plaquetteSpin incidence omega p) =
      if HasWilsonBoundary incidence A L then (2 : ℝ) ^ Fintype.card E else 0 := by
  classical
  have hintegrand : ∀ omega : GaugeConfig E,
      wilsonSpin L omega * ∏ p ∈ A, plaquetteSpin incidence omega p =
        ∏ e : E, (gaugeEdgeSpin omega e) ^
          (plaquetteIncidenceCount incidence A e + if e ∈ L then 1 else 0) := by
    intro omega
    rw [wilsonSpin_eq_prod_indicator_pow, prod_plaquetteSpin_eq_prod_incidence_pow]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e _
    rw [← pow_add]
    congr 1
    omega
  simp_rw [hintegrand]
  rw [sum_gaugeEdgeSpin_monomial]
  by_cases hboundary : ∀ e,
      Even (plaquetteIncidenceCount incidence A e + if e ∈ L then 1 else 0)
  · rw [if_pos hboundary]
    rw [if_pos (show HasWilsonBoundary incidence A L from hboundary)]
  · rw [if_neg hboundary]
    rw [if_neg (show ¬HasWilsonBoundary incidence A L from hboundary)]

private theorem exp_mul_eq_cosh_mul_one_add (x b : ℝ) (hb : b = 1 ∨ b = -1) :
    Real.exp (x * b) = Real.cosh x * (1 + Real.tanh x * b) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  rcases hb with h | h
  · subst h
    rw [mul_one]
    field_simp
    rw [← Real.cosh_add_sinh]
  · subst h
    rw [show x * (-1) = -x by ring, Real.exp_neg]
    field_simp
    rw [show Real.cosh x + -Real.sinh x = Real.cosh x - Real.sinh x by ring,
      Real.cosh_sub_sinh, ← Real.exp_add, add_neg_cancel, Real.exp_zero]

omit [Fintype E] [DecidableEq E] [DecidableEq P] in


theorem gaugeWeight_eq_highTempFactors (incidence : P -> Finset E) (K : P -> ℝ)
    (omega : GaugeConfig E) :
    gaugeWeight incidence K omega =
      (∏ p : P, Real.cosh (K p)) *
        ∏ p : P, (1 + Real.tanh (K p) * plaquetteSpin incidence omega p) := by
  unfold gaugeWeight gaugeAction
  rw [Real.exp_sum]
  calc
    (∏ p : P, Real.exp (K p * plaquetteSpin incidence omega p)) =
        ∏ p : P, (Real.cosh (K p) *
          (1 + Real.tanh (K p) * plaquetteSpin incidence omega p)) := by
      apply Finset.prod_congr rfl
      intro p _
      exact exp_mul_eq_cosh_mul_one_add _ _
        (plaquetteSpin_eq_one_or_neg_one incidence omega p)
    _ = _ := by rw [Finset.prod_mul_distrib]

omit [DecidableEq P] in



theorem gaugePartition_highTemp (incidence : P -> Finset E) (K : P -> ℝ) :
    gaugePartition incidence K =
      (2 : ℝ) ^ Fintype.card E * (∏ p : P, Real.cosh (K p)) *
        ∑ A ∈ (Finset.univ : Finset P).powerset.filter
            (IsClosedPlaquetteSet incidence),
          ∏ p ∈ A, Real.tanh (K p) := by
  classical
  unfold gaugePartition
  simp_rw [gaugeWeight_eq_highTempFactors incidence K]
  rw [← Finset.mul_sum]
  have hexpand : ∀ omega : GaugeConfig E,
      (∏ p : P, (1 + Real.tanh (K p) * plaquetteSpin incidence omega p)) =
        ∑ A ∈ (Finset.univ : Finset P).powerset,
          ∏ p ∈ A, (Real.tanh (K p) * plaquetteSpin incidence omega p) := by
    intro omega
    exact Finset.prod_one_add _
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  have hterm : ∀ A : Finset P,
      (∑ omega : GaugeConfig E,
          ∏ p ∈ A, (Real.tanh (K p) * plaquetteSpin incidence omega p)) =
        (∏ p ∈ A, Real.tanh (K p)) *
          (if IsClosedPlaquetteSet incidence A then
            (2 : ℝ) ^ Fintype.card E else 0) := by
    intro A
    have hprod : ∀ omega : GaugeConfig E,
        (∏ p ∈ A, (Real.tanh (K p) * plaquetteSpin incidence omega p)) =
          (∏ p ∈ A, Real.tanh (K p)) *
            ∏ p ∈ A, plaquetteSpin incidence omega p := by
      intro omega
      rw [Finset.prod_mul_distrib]
    simp_rw [hprod, ← Finset.mul_sum, sum_prod_plaquetteSpin]
  simp_rw [hterm]
  rw [Finset.sum_filter]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hclosed : IsClosedPlaquetteSet incidence A
  · rw [if_pos hclosed, if_pos hclosed]
    ring
  · rw [if_neg hclosed, if_neg hclosed]
    ring

omit [DecidableEq P] in




theorem gaugeWilsonNumerator_highTemp (incidence : P -> Finset E) (K : P -> ℝ)
    (L : Finset E) :
    gaugeWilsonNumerator incidence K L =
      (2 : ℝ) ^ Fintype.card E * (∏ p : P, Real.cosh (K p)) *
        ∑ A ∈ (Finset.univ : Finset P).powerset.filter
            (fun A => HasWilsonBoundary incidence A L),
          ∏ p ∈ A, Real.tanh (K p) := by
  classical
  unfold gaugeWilsonNumerator
  simp_rw [gaugeWeight_eq_highTempFactors incidence K]
  rw [show (∑ omega : GaugeConfig E,
      wilsonSpin L omega *
        ((∏ p : P, Real.cosh (K p)) *
          ∏ p : P, (1 + Real.tanh (K p) * plaquetteSpin incidence omega p))) =
      (∏ p : P, Real.cosh (K p)) *
        ∑ omega : GaugeConfig E,
          (wilsonSpin L omega *
            ∏ p : P, (1 + Real.tanh (K p) * plaquetteSpin incidence omega p)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  have hexpand : ∀ omega : GaugeConfig E,
      (∏ p : P, (1 + Real.tanh (K p) * plaquetteSpin incidence omega p)) =
        ∑ A ∈ (Finset.univ : Finset P).powerset,
          ∏ p ∈ A, (Real.tanh (K p) * plaquetteSpin incidence omega p) := by
    intro omega
    exact Finset.prod_one_add _
  simp_rw [hexpand]
  have hswap :
      (∑ omega : GaugeConfig E,
          wilsonSpin L omega *
            ∑ A ∈ (Finset.univ : Finset P).powerset,
              ∏ p ∈ A, (Real.tanh (K p) * plaquetteSpin incidence omega p)) =
        ∑ A ∈ (Finset.univ : Finset P).powerset,
          ∑ omega : GaugeConfig E,
            wilsonSpin L omega *
              ∏ p ∈ A, (Real.tanh (K p) * plaquetteSpin incidence omega p) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hswap]
  have hterm : ∀ A : Finset P,
      (∑ omega : GaugeConfig E,
          wilsonSpin L omega *
            ∏ p ∈ A, (Real.tanh (K p) * plaquetteSpin incidence omega p)) =
        (∏ p ∈ A, Real.tanh (K p)) *
          (if HasWilsonBoundary incidence A L then
            (2 : ℝ) ^ Fintype.card E else 0) := by
    intro A
    have hprod : ∀ omega : GaugeConfig E,
        wilsonSpin L omega *
            ∏ p ∈ A, (Real.tanh (K p) * plaquetteSpin incidence omega p) =
          (∏ p ∈ A, Real.tanh (K p)) *
            (wilsonSpin L omega * ∏ p ∈ A, plaquetteSpin incidence omega p) := by
      intro omega
      rw [Finset.prod_mul_distrib]
      ring
    simp_rw [hprod, ← Finset.mul_sum, sum_wilson_mul_prod_plaquetteSpin]
  simp_rw [hterm]
  rw [Finset.sum_filter]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hboundary : HasWilsonBoundary incidence A L
  · rw [if_pos hboundary, if_pos hboundary]
    ring
  · rw [if_neg hboundary, if_neg hboundary]
    ring

end GaugeHypergraph

end StatMech.FrontierA
