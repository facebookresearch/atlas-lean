/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCaratheodoryApproximation











open Filter Set Topology Metric

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section



theorem exists_bounded_anchor_of_average_normSq_le
    {ι : Type} (s : Finset ι) (hs : s.Nonempty) (f : ι → Complex)
    (E : Real) (hE : 0 ≤ E)
    (haverage : (∑ x ∈ s, Complex.normSq (f x)) ≤ (s.card : Real) * E) :
    ∃ x ∈ s, ‖f x‖ ≤ Real.sqrt E := by
  by_contra hnone
  push Not at hnone
  have hterm : ∀ x ∈ s, E < Complex.normSq (f x) := by
    intro x hx
    have hxlt := hnone x hx
    rw [Complex.normSq_eq_norm_sq]
    rw [← Real.sq_sqrt hE]
    exact (sq_lt_sq₀ (Real.sqrt_nonneg E) (norm_nonneg (f x))).2 hxlt
  have hstrict : (∑ _x ∈ s, E) < ∑ x ∈ s, Complex.normSq (f x) := by
    apply Finset.sum_lt_sum_of_nonempty hs
    intro x hx
    exact hterm x hx
  have hconst : (∑ _x ∈ s, E) = (s.card : Real) * E := by
    simp [nsmul_eq_mul]
  rw [hconst] at hstrict
  exact (not_lt_of_ge haverage) hstrict



theorem finiteWindow_average_normSq_le_of_embedding
    {α β : Type} [Fintype α] (window : α ↪ β)
    (concrete : α → Complex) (abstract : β → Complex) (E : Real)
    (hvalue : ∀ x, abstract (window x) = concrete x)
    (haverage : (∑ x, Complex.normSq (concrete x)) ≤
      (Fintype.card α : Real) * E) :
    (∑ y ∈ Finset.univ.map window, Complex.normSq (abstract y)) ≤
      ((Finset.univ.map window).card : Real) * E := by
  simpa [hvalue] using haverage

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)




def HasEventualCompactAverageNormSq
    (support : ∀ n, Finset (A.M n)) : Prop :=
  ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    ∃ E : Real, 0 ≤ E ∧ ∀ᶠ n in atTop,
      (support n).Nonempty ∧
      (∑ a ∈ support n,
          Complex.normSq
            (@FKIsingDobrushinDomain.normalizedFermionicObservable
              (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) a)) ≤
        ((support n).card : Real) * E




def HasEventualCompactWindowDiameter
    (support : ∀ n, Finset (A.M n)) : Prop :=
  ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    ∃ D : Real, 0 ≤ D ∧ ∀ᶠ n in atTop,
      ∀ a ∈ support n, ∀ e : A.M n,
        (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) →
        dist (A.medialEmbedding n e) (A.medialEmbedding n a) ≤ D



theorem hasEventualCompactWindowDiameter_of_commonBall
    (support : ∀ n, Finset (A.M n))
    (hball : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
      ∃ center : Complex, ∃ R : Real, 0 ≤ R ∧ ∀ᶠ n in atTop,
        (∀ a ∈ support n, dist (A.medialEmbedding n a) center ≤ R) ∧
        ∀ e : A.M n,
          (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) →
          dist (A.medialEmbedding n e) center ≤ R) :
    A.HasEventualCompactWindowDiameter support := by
  intro K hK hKU
  obtain ⟨center, R, hR, hevent⟩ := hball K hK hKU
  refine ⟨2 * R, mul_nonneg (by norm_num) hR, ?_⟩
  filter_upwards [hevent] with n hn
  intro a ha e he
  calc
    dist (A.medialEmbedding n e) (A.medialEmbedding n a) ≤
        dist (A.medialEmbedding n e) center +
          dist center (A.medialEmbedding n a) := dist_triangle _ _ _
    _ ≤ R + R := add_le_add (hn.2 e he) (by
      simpa [dist_comm] using hn.1 a ha)
    _ = 2 * R := by ring


def HasEventualCompactAverageEnergy
    (support : ∀ n, Finset (A.M n)) : Prop :=
  A.HasEventualCompactAverageNormSq support ∧
    A.HasEventualCompactWindowDiameter support

variable (I : A.HolderInterpolation)




theorem eventualMedialBounds_of_holderInterpolation_and_averageEnergy
    (I : A.HolderInterpolation)
    (support : ∀ n, Finset (A.M n))
    (henergy : A.HasEventualCompactAverageEnergy support) :
    ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
      ∃ B : Real, ∀ᶠ n in atTop, ∀ e : A.M n,
        (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) →
        ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤ B := by
  intro K hK hKU
  obtain ⟨E, hE, henergyEvent⟩ := henergy.1 K hK hKU
  obtain ⟨D, hD, hdiameterEvent⟩ := henergy.2 K hK hKU
  refine ⟨Real.sqrt E + (I.constant : Real) * D ^ (I.exponent : Real), ?_⟩
  filter_upwards [henergyEvent, hdiameterEvent] with n hn hdiameter
  obtain ⟨a, haSupport, haBound⟩ :=
    exists_bounded_anchor_of_average_normSq_le
      (support n) hn.1
      (fun a ↦ @FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) a)
      E hE hn.2
  intro e he
  have hposition := hdiameter a haSupport e he
  have hholder :
      dist
          (@FKIsingDobrushinDomain.normalizedFermionicObservable
            (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e)
          (@FKIsingDobrushinDomain.normalizedFermionicObservable
            (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) a) ≤
        I.constant * D ^ (I.exponent : Real) := by
    rw [← A.normalizedInterpolant_medial n e,
      ← A.normalizedInterpolant_medial n a]
    exact (I.holder n).dist_le_of_le
      (A.medial_mem_carrier n e) (A.medial_mem_carrier n a) hposition
  calc
    ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤
      ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) a‖ +
      ‖@FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e -
        @FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) a‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ Real.sqrt E + (I.constant : Real) * D ^ (I.exponent : Real) := by
      rw [← dist_eq_norm]
      exact add_le_add haBound hholder




theorem scalingLimit_of_holderAverageEnergy_and_primitiveIm
    (I : A.HolderInterpolation) (support : ∀ n, Finset (A.M n))
    (target Phi : Complex → Complex)
    (hhol : ∀ n, DifferentiableOn Complex (A.normalizedInterpolant n) A.U)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (henergy : A.HasEventualCompactAverageEnergy support)
    (hidentifyPrimitive : ∀ (phi psi : Nat → Nat) (f : Complex → Complex),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn
        (fun n ↦ A.normalizedInterpolant (phi (psi n))) f atTop A.U →
      ∃ (P : Complex → Complex) (C : Real),
        DifferentiableOn Complex P A.U ∧
        Set.EqOn (deriv P) (fun z ↦ f z ^ 2) A.U ∧
        (∀ z ∈ A.U, (P z).im = (Phi z).im + C) ∧
        f A.root = target A.root) :
    TendstoLocallyUniformlyOn A.normalizedInterpolant target atTop A.U ∧
      TendstoLocallyUniformlyOn (deriv ∘ A.normalizedInterpolant)
        (deriv target) atTop A.U := by
  apply isingFermionic_scalingLimit_of_compactBounds_and_primitiveIm
    A.mesh A.rawInterpolant target Phi A.U A.root A.isOpen A.isPreconnected
    A.root_mem hhol htarget htarget_ne hPhi hPhideriv E
  · apply compactBounds_of_holderInterpolation_and_eventualMedialBounds
      A I hhol
    exact eventualMedialBounds_of_holderInterpolation_and_averageEnergy
      A I support henergy
  · exact hidentifyPrimitive

end FKIsingCaratheodoryApproximation

end

end StatMech.Universality
