/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.FiniteWitnessUnionBound
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Order.Group.Indicator

/-!
# Fibrewise bounds for finite event masses

For a nonnegative weight `μ` on a finite set `Ω` and an idempotent map `P : Ω → Ω` (a projection,
e.g. onto the states explored so far by an algorithm), the mass of an event splits over the
fibres of `P`. If an event `Inserted` lies in `Base ∩ {ω : ω ∈ Arm (P ω)}`, where `Base` is a union
of fibres, and on each fibre the arm event has relative mass at most `a`, then
`μ(Inserted) ≤ a μ(Base)`. This is the step used to bound witness insertions one at a time.

## Main results

* `StatMech.Probability.finiteEventMass_eq_sum_projectionFibres`: the fibre decomposition.
* `StatMech.Probability.finiteEventMass_adaptive_fibre_step_on_base`: the bound with the fibre
  cap required only on fibres inside `Base`.
* `StatMech.Probability.finiteEventMass_adaptive_fibre_step`: the bound with the cap on every
  fibre.
-/

@[expose] public section

open scoped BigOperators

namespace StatMech.Probability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]

/-- The mass of `A` is the sum over the fibres of `P` of the mass of `A` in each fibre. -/
theorem finiteEventMass_eq_sum_projectionFibres
    (mu : Omega → ℝ) (P : Omega → Omega) (A : Set Omega) :
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

/-- If `Base` is a union of fibres of the projection `P`, every `ω ∈ Inserted` lies in `Base` and in
`Arm (P ω)`, and on each fibre inside `Base` the arm event has mass at most `a` times the fibre
mass, then `μ(Inserted) ≤ a μ(Base)`. -/
theorem finiteEventMass_adaptive_fibre_step_on_base
    (mu : Omega → ℝ) (hmu : ∀ omega, 0 ≤ mu omega)
    (P : Omega → Omega) (hP : ∀ omega, P (P omega) = P omega)
    (Base Inserted : Set Omega)
    (Arm : Omega → Set Omega) {a : ℝ}
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

/-- `finiteEventMass_adaptive_fibre_step_on_base` with the fibre cap assumed on every fibre. -/
theorem finiteEventMass_adaptive_fibre_step
    (mu : Omega → ℝ) (hmu : ∀ omega, 0 ≤ mu omega)
    (P : Omega → Omega) (hP : ∀ omega, P (P omega) = P omega)
    (Base Inserted : Set Omega)
    (Arm : Omega → Set Omega) {a : ℝ}
    (hBase : ∀ {omega rho}, P omega = P rho →
      (omega ∈ Base ↔ rho ∈ Base))
    (hInserted : ∀ {omega}, omega ∈ Inserted →
      omega ∈ Base ∧ omega ∈ Arm (P omega))
    (hcap : ∀ psi ∈ Finset.univ.image P,
      (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator mu omega) ≤
        a * ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          mu omega) :
    finiteEventMass mu Inserted ≤ a * finiteEventMass mu Base :=
  finiteEventMass_adaptive_fibre_step_on_base mu hmu P hP Base Inserted Arm hBase hInserted
    (fun psi hpsi _ => hcap psi hpsi)

end

end StatMech.Probability
