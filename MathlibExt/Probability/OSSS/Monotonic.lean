/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.FKG

/-!
# FKG lattice condition implies monotonicity of conditional edge probabilities

A strictly positive weight `μ` on `{0, 1}^E` is *monotonic* if, for every edge `e` and every
finite set `F`, the conditional probability that `e` is open given the states on `F` is
nondecreasing in those states. This is the hypothesis under which Duminil-Copin, Raoufi and
Tassion extend the OSSS inequality from product measures to random-cluster measures. This file
proves that a strictly positive weight satisfying the FKG lattice condition is monotonic, by
applying Holley's inequality to the two conditional weights.

## Main definitions

* `StatMech.OSSS.Monotonic.Agree`: `ω` agrees with `η` on `F`.
* `StatMech.OSSS.Monotonic.condNorm`, `condMass`: the normalizing sum and the conditional weight
  given agreement with `η` on `F`.
* `StatMech.OSSS.Monotonic.condProbOpen`: the conditional probability that `e` is open.
* `StatMech.OSSS.Monotonic.IsMonotonicMeasure`: monotonicity of `condProbOpen` in the boundary
  configuration.

## Main results

* `StatMech.OSSS.Monotonic.fkg_implies_monotonic`: a strictly positive weight satisfying the FKG
  lattice condition is monotonic.

## References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and
  Potts models via decision trees*, Ann. of Math. 189 (2019), 75–99.
* R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36 (1974), 227–231.
-/

@[expose] public section

open Finset

namespace StatMech
namespace OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `ω` agrees with `η` on every element of `F`. -/
def Agree (F : Finset E) (η ω : ConfigSpace E) : Prop := ∀ f ∈ F, ω f = η f

/-- Agreement on a finite set is decidable. -/
instance (F : Finset E) (η ω : ConfigSpace E) : Decidable (Agree F η ω) := by
  unfold Agree; infer_instance

omit [Fintype E] [DecidableEq E] in
/-- Every configuration agrees with itself. -/
lemma agree_self (F : Finset E) (η : ConfigSpace E) : Agree F η η := fun _ _ => rfl

omit [Fintype E] [DecidableEq E] in
/-- If `ξ ≤ ζ` on `F`, `a` agrees with `ξ` and `b` with `ζ` on `F`, then `a ⊓ b` agrees with `ξ`. -/
lemma agree_inf (F : Finset E) (ξ ζ a b : ConfigSpace E)
    (hle : ∀ f ∈ F, ξ f ≤ ζ f) (ha : Agree F ξ a) (hb : Agree F ζ b) :
    Agree F ξ (a ⊓ b) := by
  intro f hf
  change a f ⊓ b f = ξ f
  rw [ha f hf, hb f hf]
  exact inf_eq_left.mpr (hle f hf)

omit [Fintype E] [DecidableEq E] in
/-- If `ξ ≤ ζ` on `F`, `a` agrees with `ξ` and `b` with `ζ` on `F`, then `a ⊔ b` agrees with `ζ`. -/
lemma agree_sup (F : Finset E) (ξ ζ a b : ConfigSpace E)
    (hle : ∀ f ∈ F, ξ f ≤ ζ f) (ha : Agree F ξ a) (hb : Agree F ζ b) :
    Agree F ζ (a ⊔ b) := by
  intro f hf
  change a f ⊔ b f = ζ f
  rw [ha f hf, hb f hf]
  exact sup_eq_right.mpr (hle f hf)

/-- The total weight of the configurations agreeing with `η` on `F`. -/
noncomputable def condNorm (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E) : ℝ :=
  ∑ ω, if Agree F η ω then μ ω else 0

/-- The weight `μ` conditioned on agreeing with `η` on `F`. -/
noncomputable def condMass (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E) :
    ConfigSpace E → ℝ :=
  fun ω => (if Agree F η ω then μ ω else 0) / condNorm μ F η

/-- For a strictly positive weight the conditioning normalizer is positive. -/
lemma condNorm_pos {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (η : ConfigSpace E) : 0 < condNorm μ F η := by
  unfold condNorm
  refine Finset.sum_pos' (fun ω _ => ?_) ⟨η, Finset.mem_univ η, ?_⟩
  · split
    · exact (hpos ω).le
    · rfl
  · rw [ite_eq_left (agree_self F η)]; exact hpos η

/-- The conditional weight is nonnegative. -/
lemma condMass_nonneg {μ : ConfigSpace E → ℝ} (hμ : 0 ≤ μ) (F : Finset E)
    (η : ConfigSpace E) (hZ : 0 < condNorm μ F η) : 0 ≤ condMass μ F η := by
  intro ω
  unfold condMass
  apply div_nonneg _ hZ.le
  split
  · exact hμ ω
  · rfl

/-- The conditional weight sums to `1`. -/
lemma condMass_sum {μ : ConfigSpace E → ℝ} (F : Finset E) (η : ConfigSpace E)
    (hZ : condNorm μ F η ≠ 0) : ∑ ω, condMass μ F η ω = 1 := by
  have h : ∑ ω, condMass μ F η ω
      = (∑ ω, (if Agree F η ω then μ ω else 0)) / condNorm μ F η := by
    unfold condMass; rw [Finset.sum_div]
  rw [h]
  exact div_self hZ

/-- The FKG lattice condition for the weights restricted to agreement with `ξ` and with `ζ ≥ ξ`. -/
lemma cross_restricted {μ : ConfigSpace E → ℝ} (hμ : 0 ≤ μ)
    (hFKG : FKGLatticeCondition μ) (F : Finset E) (ξ ζ : ConfigSpace E)
    (hle : ∀ f ∈ F, ξ f ≤ ζ f) (a b : ConfigSpace E) :
    (if Agree F ξ a then μ a else 0) * (if Agree F ζ b then μ b else 0)
      ≤ (if Agree F ξ (a ⊓ b) then μ (a ⊓ b) else 0)
          * (if Agree F ζ (a ⊔ b) then μ (a ⊔ b) else 0) := by
  by_cases ha : Agree F ξ a
  · by_cases hb : Agree F ζ b
    · rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left (agree_inf F ξ ζ a b hle ha hb),
          ite_eq_left (agree_sup F ξ ζ a b hle ha hb), mul_comm (μ (a ⊓ b))]
      exact hFKG a b
    · rw [ite_eq_right hb, mul_zero]
      apply mul_nonneg <;> [split; split] <;> first | exact hμ _ | rfl
  · rw [ite_eq_right ha, zero_mul]
    apply mul_nonneg <;> [split; split] <;> first | exact hμ _ | rfl

/-- Holley's cross condition for the two conditional weights `condMass μ F ξ`, `condMass μ F ζ`
when `ξ ≤ ζ` on `F`. -/
lemma cross_condMass {μ : ConfigSpace E → ℝ} (hμ : 0 ≤ μ)
    (hFKG : FKGLatticeCondition μ) (F : Finset E) (ξ ζ : ConfigSpace E)
    (hle : ∀ f ∈ F, ξ f ≤ ζ f) (hZξ : 0 < condNorm μ F ξ) (hZζ : 0 < condNorm μ F ζ)
    (a b : ConfigSpace E) :
    condMass μ F ξ a * condMass μ F ζ b
      ≤ condMass μ F ξ (a ⊓ b) * condMass μ F ζ (a ⊔ b) := by
  unfold condMass
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right (cross_restricted hμ hFKG F ξ ζ hle a b)
    (mul_pos hZξ hZζ).le

/-- The event that the edge `e` is open. -/
def OpenAt (e : E) : Set (ConfigSpace E) := {ω | ω e = true}

omit [Fintype E] [DecidableEq E] in
/-- The event that `e` is open is increasing. -/
lemma isIncreasing_openAt (e : E) : IsIncreasing (OpenAt (E := E) e) := by
  intro x y hxy hx
  simp only [OpenAt, Set.mem_ofPred_eq] at *
  have h := hxy e
  rw [hx] at h
  exact le_antisymm le_top h

/-- The conditional probability that `e` is open given agreement with `η` on `F`. -/
noncomputable def condProbOpen (μ : ConfigSpace E → ℝ) (F : Finset E)
    (η : ConfigSpace E) (e : E) : ℝ :=
  ∑ ω, (OpenAt e).indicator (fun _ => (1 : ℝ)) ω * condMass μ F η ω

/-- The weight `μ` is monotonic: the conditional probability that `e` is open given the states on
`F` is nondecreasing in those states. -/
def IsMonotonicMeasure (μ : ConfigSpace E → ℝ) : Prop :=
  ∀ (e : E) (F : Finset E) (ξ ζ : ConfigSpace E), (∀ f ∈ F, ξ f ≤ ζ f) →
    0 < condNorm μ F ξ → 0 < condNorm μ F ζ →
    condProbOpen μ F ξ e ≤ condProbOpen μ F ζ e

/-- A strictly positive weight satisfying the FKG lattice condition is monotonic (via Holley's
inequality). This is the monotonicity input for the OSSS inequality for random-cluster measures in
Duminil-Copin–Raoufi–Tassion (2019). -/
theorem fkg_implies_monotonic {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) : IsMonotonicMeasure μ := by
  intro e F ξ ζ hle hZξ hZζ
  have hμ : 0 ≤ μ := fun ω => (hpos ω).le
  have hdom := holley_dominates
    (μ₁ := condMass μ F ξ) (μ₂ := condMass μ F ζ)
    (condMass_nonneg hμ F ξ hZξ) (condMass_nonneg hμ F ζ hZζ)
    (by rw [condMass_sum F ξ hZξ.ne', condMass_sum F ζ hZζ.ne'])
    (cross_condMass hμ hFKG F ξ ζ hle hZξ hZζ)
    (isIncreasing_openAt e)
  exact hdom

end OSSS.Monotonic
end StatMech
