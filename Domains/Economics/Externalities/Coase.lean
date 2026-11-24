/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Coase invariance under quasilinear transferable utility (Atlas AP02.T03)

Agents `i : ι` (finitely many, at least one) choose a physical allocation
`a : A` (for example, whether a polluting activity runs) and hold money `m i`.
Utility is quasilinear: `v i a + m i`. A property-rights assignment fixes a status
quo allocation `a₀` and money endowments `ω`. Transfers are costless: any money
vector with the same total as `ω` is feasible.

* An outcome is Pareto efficient iff its physical allocation maximizes total
  value `∑ i, v i a` (money only redistributes).
* Hence the efficient physical allocations are the same under every
  property-rights assignment.
* Under any assignment, a total-value maximizer can be reached by transfers that
  leave every agent at least as well off as at the status quo.

Assumptions, as in the textbook statement of the Coase theorem with quasilinear
utility: utility is quasilinear in money (no income effects); transfers are
costless and unrestricted, so money holdings may become negative (no wealth or
liquidity constraints); there are finitely many agents, at least one; and there
are no transaction costs or bargaining frictions (any feasible outcome can be
reached). The theorems describe efficient outcomes and individually rational
efficient outcomes; they do not model a particular bargaining procedure.

## References

* R. H. Coase, "The Problem of Social Cost", Journal of Law and Economics 3
  (1960), 1–44.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford
  University Press (1995), Section 11.B (bargaining over a bilateral
  externality with quasilinear utility).
-/

@[expose] public section

open Finset

namespace MathlibExt.Economics.Coase

/-- Total physical value of allocation `a`. -/
def totalValue {ι A : Type*} [Fintype ι] (v : ι → A → ℝ) (a : A) : ℝ := ∑ i, v i a

/-- Quasilinear utility of agent `i` at allocation `a` with money `m`. -/
def utility {ι A : Type*} (v : ι → A → ℝ) (a : A) (m : ι → ℝ) (i : ι) : ℝ := v i a + m i

/-- Money vector `m` is feasible from endowment `ω` (costless, budget-balanced
transfers). -/
def Feasible {ι : Type*} [Fintype ι] (ω m : ι → ℝ) : Prop := ∑ i, m i = ∑ i, ω i

/-- `(a, m)` is Pareto efficient given endowment `ω`: feasible, and no feasible
outcome makes every agent weakly better off and some agent strictly better off. -/
def ParetoEfficient {ι A : Type*} [Fintype ι] (v : ι → A → ℝ) (ω : ι → ℝ)
    (a : A) (m : ι → ℝ) : Prop :=
  Feasible ω m ∧ ¬ ∃ (a' : A) (m' : ι → ℝ), Feasible ω m' ∧
    (∀ i, utility v a m i ≤ utility v a' m' i) ∧ ∃ i, utility v a m i < utility v a' m' i

/-- Splitting `c` equally over all agents sums back to `c`. -/
theorem sum_const_div_card {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℝ) :
    (∑ _i : ι, c / Fintype.card ι) = c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel₀ c (ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos))

/-- Pareto efficiency under quasilinear utility is total-value maximization of the
physical allocation (plus feasibility of money). -/
theorem paretoEfficient_iff {ι A : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → A → ℝ) (ω : ι → ℝ) (a : A) (m : ι → ℝ) :
    ParetoEfficient v ω a m ↔ Feasible ω m ∧ ∀ a', totalValue v a' ≤ totalValue v a := by
  constructor
  · rintro ⟨hFeas, hNo⟩
    refine ⟨hFeas, fun a' => ?_⟩
    by_contra hle
    rw [not_le] at hle
    have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    set δ : ℝ := totalValue v a' - totalValue v a with hδ
    have hδpos : 0 < δ := sub_pos.mpr hle
    have htop : 0 < δ / Fintype.card ι := div_pos hδpos hcard
    set m' : ι → ℝ := fun i => m i + v i a - v i a' + δ / Fintype.card ι with hm'
    have hutil : ∀ i, utility v a' m' i = utility v a m i + δ / Fintype.card ι := by
      intro i
      simp only [utility, hm']
      abel
    have hFeasEq : ∑ i, m i = ∑ i, ω i := hFeas
    have hFeas' : Feasible ω m' := by
      simp only [Feasible]
      have e1 : ∀ i, m' i = m i + (v i a - v i a' + δ / Fintype.card ι) := by
        intro i
        simp only [hm']
        abel
      simp only [e1]
      rw [Finset.sum_add_distrib]
      have e2 : (∑ i, (v i a - v i a' + δ / (Fintype.card ι : ℝ))) = 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_const_div_card, hδ]
        simp only [totalValue]
        abel
      rw [e2, add_zero]
      exact hFeasEq
    have hle' : ∀ i, utility v a m i ≤ utility v a' m' i := fun i => by
      rw [hutil i]
      linarith
    obtain ⟨j⟩ := (inferInstance : Nonempty ι)
    have hlt' : utility v a m j < utility v a' m' j := by
      rw [hutil j]
      linarith
    exact hNo ⟨a', m', hFeas', hle', j, hlt'⟩
  · rintro ⟨hFeas, hmax⟩
    refine ⟨hFeas, ?_⟩
    rintro ⟨a', m', hFeas', hWeak, j, hStrict⟩
    have hsumlt : ∑ i, utility v a m i < ∑ i, utility v a' m' i :=
      Finset.sum_lt_sum (fun i _ => hWeak i) ⟨j, Finset.mem_univ j, hStrict⟩
    have hle := hmax a'
    have hFeasEq : ∑ i, m i = ∑ i, ω i := hFeas
    have hFeasEq' : ∑ i, m' i = ∑ i, ω i := hFeas'
    simp only [utility, Finset.sum_add_distrib, totalValue] at hsumlt hle
    linarith

/-- **Coase invariance.** Efficient physical allocations under two property-rights
assignments (endowments `ω`, `ω'`) have the same total value; in particular,
if the total-value maximizer is unique, they coincide. -/
theorem totalValue_eq_of_paretoEfficient {ι A : Type*} [Fintype ι] [Nonempty ι]
    {v : ι → A → ℝ} {ω ω' : ι → ℝ} {a a' : A} {m m' : ι → ℝ}
    (h : ParetoEfficient v ω a m) (h' : ParetoEfficient v ω' a' m') :
    totalValue v a = totalValue v a' := by
  rw [paretoEfficient_iff] at h h'
  obtain ⟨-, hmax⟩ := h
  obtain ⟨-, hmax'⟩ := h'
  exact le_antisymm (hmax' a) (hmax a')

/-- Under any property-rights assignment (status quo `a₀`, endowment `ω`), a
total-value maximizer `a` is reached by feasible transfers that make the outcome
Pareto efficient and individually rational relative to the status quo. -/
theorem exists_paretoEfficient_individuallyRational {ι A : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → A → ℝ) (ω : ι → ℝ) (a₀ a : A)
    (hmax : ∀ a', totalValue v a' ≤ totalValue v a) :
    ∃ m : ι → ℝ, ParetoEfficient v ω a m ∧ ∀ i, utility v a₀ ω i ≤ utility v a m i := by
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  set S : ℝ := totalValue v a - totalValue v a₀ with hS
  have hSnonneg : 0 ≤ S := sub_nonneg.mpr (hmax a₀)
  have htopnn : 0 ≤ S / Fintype.card ι := div_nonneg hSnonneg (le_of_lt hcard)
  set m : ι → ℝ := fun i => ω i + v i a₀ - v i a + S / Fintype.card ι with hm
  have hFeas : Feasible ω m := by
    have e1 : ∀ i, m i = ω i + (v i a₀ - v i a + S / Fintype.card ι) := by
      intro i
      simp only [hm]
      abel
    have hsum : ∑ i, m i = ∑ i, ω i := by
      simp only [e1]
      rw [Finset.sum_add_distrib]
      have e2 : (∑ i, (v i a₀ - v i a + S / (Fintype.card ι : ℝ))) = 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_const_div_card, hS]
        simp only [totalValue]
        abel
      rw [e2, add_zero]
    exact hsum
  have hPE : ParetoEfficient v ω a m := (paretoEfficient_iff v ω a m).mpr ⟨hFeas, hmax⟩
  refine ⟨m, hPE, fun i => ?_⟩
  have hutil : utility v a m i = utility v a₀ ω i + S / Fintype.card ι := by
    simp only [utility, hm]
    abel
  rw [hutil]
  linarith

end MathlibExt.Economics.Coase
