/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Probability.AdaptiveFibreStep



open scoped BigOperators

namespace StatMech.Probability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]




theorem finiteEventMass_adaptive_fibre_lower
    (mu : Omega -> Real) (hmu : forall omega, 0 <= mu omega)
    (P : Omega -> Omega) (hP : forall omega, P (P omega) = P omega)
    (Base Goal : Set Omega) (Arm : Omega -> Set Omega) (c : Real)
    (hBase : forall {omega rho}, P omega = P rho ->
      (omega ∈ Base ↔ rho ∈ Base))
    (hglue : forall {omega}, omega ∈ Base ->
      omega ∈ Arm (P omega) -> omega ∈ Goal)
    (hfloor : forall psi, psi ∈ Finset.univ.image P ->
      c * (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          mu omega) <=
        ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator mu omega) :
    c * finiteEventMass mu Base <= finiteEventMass mu Goal := by
  classical
  rw [finiteEventMass_eq_sum_projectionFibres mu P Base,
    finiteEventMass_eq_sum_projectionFibres mu P Goal, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  obtain ⟨rho, _, hrho⟩ := Finset.mem_image.mp hpsi
  have hfixed : P psi = psi := by
    rw [← hrho, hP rho]
  by_cases hbasePsi : psi ∈ Base
  · have hbaseFibre : forall omega,
        omega ∈ (Finset.univ.filter fun omega => P omega = psi) ->
        omega ∈ Base := by
      intro omega homega
      have hproj : P omega = psi := (Finset.mem_filter.mp homega).2
      exact (hBase (hproj.trans hfixed.symm)).2 hbasePsi
    calc
      c * (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          Base.indicator mu omega) =
          c * (∑ omega ∈
            (Finset.univ.filter fun omega => P omega = psi), mu omega) := by
            congr 1
            apply Finset.sum_congr rfl
            intro omega homega
            rw [Set.indicator_of_mem (hbaseFibre omega homega)]
      _ <= ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator mu omega := hfloor psi hpsi
      _ <= ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          Goal.indicator mu omega := by
            apply Finset.sum_le_sum
            intro omega homega
            by_cases harm : omega ∈ Arm psi
            · have hproj : P omega = psi := (Finset.mem_filter.mp homega).2
              have hgoal : omega ∈ Goal := hglue
                (hbaseFibre omega homega) (by simpa [hproj] using harm)
              rw [Set.indicator_of_mem harm, Set.indicator_of_mem hgoal]
            · rw [Set.indicator_of_notMem harm]
              exact Set.indicator_nonneg (fun _ _ => hmu omega) _
  · have hnotBaseFibre : forall omega,
        omega ∈ (Finset.univ.filter fun omega => P omega = psi) ->
        omega ∉ Base := by
      intro omega homega hbase
      have hproj : P omega = psi := (Finset.mem_filter.mp homega).2
      exact hbasePsi ((hBase (hproj.trans hfixed.symm)).1 hbase)
    rw [show (∑ omega ∈
        (Finset.univ.filter fun omega => P omega = psi),
          Base.indicator mu omega) = 0 by
      apply Finset.sum_eq_zero
      intro omega homega
      rw [Set.indicator_of_notMem (hnotBaseFibre omega homega)]]
    simp only [mul_zero]
    exact Finset.sum_nonneg fun omega _ =>
      Set.indicator_nonneg (fun _ _ => hmu omega) _

end

end StatMech.Probability
