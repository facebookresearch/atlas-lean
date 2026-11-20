/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Probability.FiniteWitnessUnionBound










open scoped BigOperators

namespace StatMech.Probability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]



theorem finiteEventMass_eq_sum_projectionFibres
    (mu : Omega → Real) (P : Omega → Omega) (A : Set Omega) :
    finiteEventMass mu A =
      ∑ psi ∈ (Finset.univ.image P),
        ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          A.indicator mu omega := by
  classical
  unfold finiteEventMass
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := P) (t := Finset.univ.image P)
    (fun omega _ => Finset.mem_image.mpr
      ⟨omega, Finset.mem_univ omega, rfl⟩)]
  rfl







theorem finiteEventMass_adaptive_fibre_step
    (mu : Omega → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (P : Omega → Omega) (hP : ∀ omega, P (P omega) = P omega)
    (Base Inserted : Set Omega)
    (Arm : Omega → Set Omega) {a : Real}
    (hBase : ∀ {omega rho}, P omega = P rho →
      (omega ∈ Base ↔ rho ∈ Base))
    (hInserted : ∀ {omega}, omega ∈ Inserted →
      omega ∈ Base ∧ omega ∈ Arm (P omega))
    (hcap : ∀ psi ∈ Finset.univ.image P,
      (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator mu omega) ≤
        a * ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          mu omega) :
    finiteEventMass mu Inserted ≤ a * finiteEventMass mu Base := by
  classical
  rw [finiteEventMass_eq_sum_projectionFibres mu P Inserted,
    finiteEventMass_eq_sum_projectionFibres mu P Base, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  obtain ⟨rho, _, hrho⟩ := Finset.mem_image.mp hpsi
  have hfixed : P psi = psi := by
    rw [← hrho, hP rho]
  by_cases hbasePsi : psi ∈ Base
  · have hbaseFibre : ∀ omega,
        omega ∈ (Finset.univ.filter fun omega => P omega = psi) →
        omega ∈ Base := by
      intro omega homega
      have hproj : P omega = psi := (Finset.mem_filter.mp homega).2
      exact (hBase (hproj.trans hfixed.symm)).2 hbasePsi
    calc
      (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          Inserted.indicator mu omega) ≤
        ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator mu omega := by
            apply Finset.sum_le_sum
            intro omega homega
            by_cases hins : omega ∈ Inserted
            · rw [Set.indicator_of_mem hins,
                Set.indicator_of_mem (show omega ∈ Arm psi by
                  have h := (hInserted hins).2
                  simpa [(Finset.mem_filter.mp homega).2] using h)]
            · rw [Set.indicator_of_notMem hins]
              exact Set.indicator_nonneg (fun _ _ => hmu omega) _
      _ ≤ a * ∑ omega ∈
          (Finset.univ.filter fun omega => P omega = psi), mu omega :=
        hcap psi hpsi
      _ = a * ∑ omega ∈
          (Finset.univ.filter fun omega => P omega = psi),
            Base.indicator mu omega := by
        congr 1
        apply Finset.sum_congr rfl
        intro omega homega
        rw [Set.indicator_of_mem (hbaseFibre omega homega)]
  · have hnotBaseFibre : ∀ omega,
        omega ∈ (Finset.univ.filter fun omega => P omega = psi) →
        omega ∉ Base := by
      intro omega homega hbase
      have hproj : P omega = psi := (Finset.mem_filter.mp homega).2
      exact hbasePsi ((hBase (hproj.trans hfixed.symm)).1 hbase)
    have hnotInsertedFibre : ∀ omega,
        omega ∈ (Finset.univ.filter fun omega => P omega = psi) →
        omega ∉ Inserted := by
      intro omega homega hins
      exact hnotBaseFibre omega homega (hInserted hins).1
    rw [show (∑ omega ∈
        (Finset.univ.filter fun omega => P omega = psi),
          Inserted.indicator mu omega) = 0 by
      apply Finset.sum_eq_zero
      intro omega homega
      rw [Set.indicator_of_notMem (hnotInsertedFibre omega homega)]]
    rw [show (∑ omega ∈
        (Finset.univ.filter fun omega => P omega = psi),
          Base.indicator mu omega) = 0 by
      apply Finset.sum_eq_zero
      intro omega homega
      rw [Set.indicator_of_notMem (hnotBaseFibre omega homega)]]
    simp




theorem finiteEventMass_adaptive_fibre_step_on_base
    (mu : Omega → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (P : Omega → Omega) (hP : ∀ omega, P (P omega) = P omega)
    (Base Inserted : Set Omega)
    (Arm : Omega → Set Omega) {a : Real}
    (hBase : ∀ {omega rho}, P omega = P rho →
      (omega ∈ Base ↔ rho ∈ Base))
    (hInserted : ∀ {omega}, omega ∈ Inserted →
      omega ∈ Base ∧ omega ∈ Arm (P omega))
    (hcap : ∀ psi ∈ Finset.univ.image P, psi ∈ Base →
      (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator mu omega) ≤
        a * ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          mu omega) :
    finiteEventMass mu Inserted ≤ a * finiteEventMass mu Base := by
  classical
  rw [finiteEventMass_eq_sum_projectionFibres mu P Inserted,
    finiteEventMass_eq_sum_projectionFibres mu P Base, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  obtain ⟨rho, _, hrho⟩ := Finset.mem_image.mp hpsi
  have hfixed : P psi = psi := by
    rw [← hrho, hP rho]
  by_cases hbasePsi : psi ∈ Base
  · have hbaseFibre : ∀ omega,
        omega ∈ (Finset.univ.filter fun omega => P omega = psi) →
        omega ∈ Base := by
      intro omega homega
      have hproj : P omega = psi := (Finset.mem_filter.mp homega).2
      exact (hBase (hproj.trans hfixed.symm)).2 hbasePsi
    calc
      (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          Inserted.indicator mu omega) ≤
        ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator mu omega := by
            apply Finset.sum_le_sum
            intro omega homega
            by_cases hins : omega ∈ Inserted
            · rw [Set.indicator_of_mem hins,
                Set.indicator_of_mem (show omega ∈ Arm psi by
                  have h := (hInserted hins).2
                  simpa [(Finset.mem_filter.mp homega).2] using h)]
            · rw [Set.indicator_of_notMem hins]
              exact Set.indicator_nonneg (fun _ _ => hmu omega) _
      _ ≤ a * ∑ omega ∈
          (Finset.univ.filter fun omega => P omega = psi), mu omega :=
        hcap psi hpsi hbasePsi
      _ = a * ∑ omega ∈
          (Finset.univ.filter fun omega => P omega = psi),
            Base.indicator mu omega := by
        congr 1
        apply Finset.sum_congr rfl
        intro omega homega
        rw [Set.indicator_of_mem (hbaseFibre omega homega)]
  · have hnotBaseFibre : ∀ omega,
        omega ∈ (Finset.univ.filter fun omega => P omega = psi) →
        omega ∉ Base := by
      intro omega homega hbase
      have hproj : P omega = psi := (Finset.mem_filter.mp homega).2
      exact hbasePsi ((hBase (hproj.trans hfixed.symm)).1 hbase)
    have hnotInsertedFibre : ∀ omega,
        omega ∈ (Finset.univ.filter fun omega => P omega = psi) →
        omega ∉ Inserted := by
      intro omega homega hins
      exact hnotBaseFibre omega homega (hInserted hins).1
    rw [show (∑ omega ∈
        (Finset.univ.filter fun omega => P omega = psi),
          Inserted.indicator mu omega) = 0 by
      apply Finset.sum_eq_zero
      intro omega homega
      rw [Set.indicator_of_notMem (hnotInsertedFibre omega homega)]]
    rw [show (∑ omega ∈
        (Finset.univ.filter fun omega => P omega = psi),
          Base.indicator mu omega) = 0 by
      apply Finset.sum_eq_zero
      intro omega homega
      rw [Set.indicator_of_notMem (hnotBaseFibre omega homega)]]
    simp

end

end StatMech.Probability
