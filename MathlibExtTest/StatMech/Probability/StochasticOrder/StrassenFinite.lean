/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.StochasticOrder.StrassenFinite

/-!
# Tests for `MathlibExt.Probability.StochasticOrder.StrassenFull`

* `StatMech.exists_monotoneCoupling_of_stochasticallyDominated` (Strassen's theorem for
  configurations on a finite set): applied to `δ_⊥ ≼ δ_⊤` on `Fin 2` (domination proved directly)
  and to `μ ≼ μ` for an arbitrary probability measure; the easy half then recovers domination.
* `StatMech.Transport.exists_coupling_vec` (Strassen's theorem on a finite poset): applied on
  `Bool` with `μ = δ_false`, `ν = δ_true`; the down-set hypothesis is proved, and the coupling is
  shown to put mass `1` on the pair `(false, true)`.
* `StatMech.Transport.IsDown`: decided for subsets of `Bool`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.StochasticOrder.StrassenFull

open MeasureTheory
open _root_.StatMech _root_.StatMech.Transport

/-- `{false}` is a down-set of `Bool`, `{true}` is not. -/
example : IsDown ({false} : Finset Bool) ∧ ¬ IsDown ({true} : Finset Bool) := by
  unfold IsDown; decide

/-- The finite-poset bridge has no nonemptiness requirement beyond the assumptions of the
canonical matrix-valued Strassen theorem. -/
example {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]
    [DecidableRel ((· ≤ ·) : P → P → Prop)] (μ ν : P → ℝ)
    (hμpos : ∀ x, 0 ≤ μ x) (hνpos : ∀ x, 0 ≤ ν x)
    (hTOT : ∑ x, μ x = ∑ x, ν x)
    (hDOM : ∀ D : Finset P, IsDown D → ∑ x ∈ D, ν x ≤ ∑ x ∈ D, μ x) :
    ∃ c : OrderPairs P → ℝ, (∀ q, 0 ≤ c q) ∧
      (∀ x, (∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0) = μ x) ∧
      (∀ y, (∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0) = ν y) :=
  exists_coupling_vec μ ν hμpos hνpos hTOT hDOM

/-- The canonical bridge also covers zero total mass on a nonempty finite poset. -/
example : ∃ c : OrderPairs Bool → ℝ, (∀ q, 0 ≤ c q) ∧
    (∀ x, (∑ q : OrderPairs Bool, if (q : Bool × Bool).1 = x then c q else 0) = 0) ∧
    (∀ y, (∑ q : OrderPairs Bool, if (q : Bool × Bool).2 = y then c q else 0) = 0) :=
  exists_coupling_vec (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl)
    (by simp) (by simp)

/-- `δ_⊥ ≼ δ_⊤` on `Fin 2`. -/
theorem dirac_bot_dominated :
    StochasticallyDominated (Measure.dirac (⊥ : ConfigSpace (Fin 2))) (Measure.dirac ⊤) := by
  intro A hA hinc
  simp only [measureReal_def, Measure.dirac_apply' _ hA]
  by_cases h : (⊥ : ConfigSpace (Fin 2)) ∈ A
  · simp [h, hinc bot_le h]
  · simp [h]

/-- Strassen's theorem for `δ_⊥ ≼ δ_⊤` on `Fin 2`, and back to domination via the easy half. -/
example : ∃ κ : Measure (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)),
    IsFiniteMeasure κ ∧ MonotoneCoupling (Measure.dirac ⊥) (Measure.dirac ⊤) κ :=
  exists_monotoneCoupling_of_stochasticallyDominated _ _ dirac_bot_dominated

/-- Strassen's theorem for `μ ≼ μ`, for any probability measure on a finite configuration space,
then the easy half. -/
example (μ : Measure (ConfigSpace (Fin 3))) [IsProbabilityMeasure μ] :
    StochasticallyDominated μ μ :=
  stochasticallyDominated_of_exists_monotoneCoupling
    (exists_monotoneCoupling_of_stochasticallyDominated μ μ (StochasticallyDominated.refl μ))

/-- The point masses `δ_false` and `δ_true` on `Bool`. -/
def δf : Bool → ℝ := fun b => if b = false then 1 else 0
/-- The point mass at `true`. -/
def δt : Bool → ℝ := fun b => if b = true then 1 else 0

/-- `δ_true` is dominated by `δ_false` on down-sets: a down-set containing `true` contains
`false`. -/
lemma dom_δ (D : Finset Bool) (hD : IsDown D) : ∑ x ∈ D, δt x ≤ ∑ x ∈ D, δf x := by
  simp only [δt, δf, Finset.sum_ite_eq']
  by_cases ht : true ∈ D
  · simp [ht, hD false true (by decide) ht]
  · by_cases hf : false ∈ D <;> simp [ht, hf]

/-- Strassen's theorem on the poset `Bool`: the coupling of `δ_false` and `δ_true` exists and
puts mass `1` on `(false, true)`. -/
example : ∃ c : OrderPairs Bool → ℝ, (∀ q, 0 ≤ c q) ∧
    c ⟨(false, true), by decide⟩ = 1 := by
  obtain ⟨c, hc, hrow, hcol⟩ := exists_coupling_vec δf δt
    (fun x => by unfold δf; split_ifs <;> norm_num)
    (fun x => by unfold δt; split_ifs <;> norm_num)
    (by simp [δf, δt]) dom_δ
  refine ⟨c, hc, ?_⟩
  have huniv : (Finset.univ : Finset (OrderPairs Bool)) =
      {⟨(false, false), by decide⟩, ⟨(false, true), by decide⟩, ⟨(true, true), by decide⟩} := by
    decide
  have h1 := hrow true
  have h2 := hcol true
  rw [huniv] at h1 h2
  simp [δf, δt] at h1 h2
  linarith

end MathlibExtTest.StatMech.Probability.StochasticOrder.StrassenFull
