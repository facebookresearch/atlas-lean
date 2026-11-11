/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# First fundamental theorem of welfare economics for exchange economies (Atlas EC15.T02)

An exchange economy has finitely many agents `I` and goods `L`. Agent `i` owns
the endowment `endowment i : L → ℝ` and ranks bundles by `utility i`. The
consumption set of every agent is the nonnegative orthant. An allocation
`x : I → L → ℝ` is feasible when every bundle is nonnegative and the total
consumption does not exceed the total endowment good by good (free disposal).

A Walrasian (competitive) equilibrium is a nonnegative price vector `p` and a
feasible allocation `x` such that each `x i` is affordable at `p` and maximizes
`utility i` over the nonnegative bundles that are affordable at `p`. The first
welfare theorem: if utilities are locally nonsatiated, every Walrasian
equilibrium allocation is Pareto efficient. Existence of an equilibrium is not
assumed or claimed, and no convexity or continuity of utilities is used.

## References

* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*,
  Oxford University Press, 1995, Definition 3.B.3 (local nonsatiation),
  Definition 16.B.3 (Walrasian equilibrium) and Proposition 16.C.1 (first
  fundamental theorem of welfare economics).
* H. R. Varian, *Intermediate Microeconomics*, 9th ed., Norton, 2014,
  Chapter 32 (exchange).
* J. Levin, *General Equilibrium*, Stanford Econ 202 lecture notes, 2006,
  Definitions 1-3 and Theorem 1 (first welfare theorem, with the remark that
  local nonsatiation suffices).
-/

namespace MathlibExt.Economics

/-- A pure exchange economy with agents `I` and goods `L`. -/
structure ExchangeEconomy (I L : Type*) where
  /-- `endowment i` is agent `i`'s initial bundle. -/
  endowment : I → L → ℝ
  /-- `utility i y` is agent `i`'s utility of the bundle `y`. -/
  utility : I → (L → ℝ) → ℝ

namespace ExchangeEconomy

/-- An allocation is feasible: every agent's bundle is nonnegative and total
consumption is at most the total endowment in every good (free disposal). -/
def IsFeasible {I L : Type*} [Fintype I] (E : ExchangeEconomy I L)
    (x : I → L → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ ∑ i, E.endowment i

/-- Local nonsatiation on the nonnegative orthant: for every agent, every
nonnegative bundle `x`, and every `ε > 0`, some nonnegative bundle within
`ε` of `x` in every coordinate is strictly preferred to `x`. -/
def LocallyNonsatiated {I L : Type*} (E : ExchangeEconomy I L) : Prop :=
  ∀ (i : I) (x : L → ℝ), 0 ≤ x → ∀ ε : ℝ, 0 < ε →
    ∃ y : L → ℝ, 0 ≤ y ∧ (∀ l, |y l - x l| < ε) ∧ E.utility i x < E.utility i y

/-- `(p, x)` is a Walrasian equilibrium: prices are nonnegative, `x` is
feasible, and each agent's bundle is affordable at `p` and maximizes utility
over all nonnegative bundles affordable at `p`. -/
def IsWalrasianEquilibrium {I L : Type*} [Fintype I] [Fintype L]
    (E : ExchangeEconomy I L) (p : L → ℝ) (x : I → L → ℝ) : Prop :=
  0 ≤ p ∧ E.IsFeasible x ∧
    ∀ i, p ⬝ᵥ x i ≤ p ⬝ᵥ E.endowment i ∧
      ∀ y : L → ℝ, 0 ≤ y → p ⬝ᵥ y ≤ p ⬝ᵥ E.endowment i →
        E.utility i y ≤ E.utility i (x i)

/-- `x` is Pareto efficient: it is feasible and no feasible allocation makes
every agent at least as well off and some agent strictly better off. -/
def IsParetoEfficient {I L : Type*} [Fintype I] (E : ExchangeEconomy I L)
    (x : I → L → ℝ) : Prop :=
  E.IsFeasible x ∧
    ¬ ∃ y : I → L → ℝ, E.IsFeasible y ∧ (∀ i, E.utility i (x i) ≤ E.utility i (y i)) ∧
      ∃ i, E.utility i (x i) < E.utility i (y i)

/-- **First welfare theorem.** With locally nonsatiated utilities, every
Walrasian equilibrium allocation of an exchange economy is Pareto efficient. -/
theorem isParetoEfficient_of_isWalrasianEquilibrium {I L : Type*} [Fintype I] [Fintype L]
    (E : ExchangeEconomy I L) (hLNS : E.LocallyNonsatiated) {p : L → ℝ} {x : I → L → ℝ}
    (hx : E.IsWalrasianEquilibrium p x) : E.IsParetoEfficient x := by
  obtain ⟨hp, hxfeas, hopt⟩ := hx
  refine ⟨hxfeas, ?_⟩
  rintro ⟨y, hyfeas, hge, ⟨j, hlt⟩⟩
  have hstrict : p ⬝ᵥ E.endowment j < p ⬝ᵥ y j := by
    by_contra hle
    have hle' : p ⬝ᵥ y j ≤ p ⬝ᵥ E.endowment j := le_of_not_gt hle
    have h := (hopt j).2 (y j) (hyfeas.1 j) hle'
    exact absurd h (not_le_of_gt hlt)
  have hspend : ∀ i, p ⬝ᵥ E.endowment i ≤ p ⬝ᵥ y i := by
    intro i
    by_contra hcon
    have hlt_i : p ⬝ᵥ y i < p ⬝ᵥ E.endowment i := lt_of_not_ge hcon
    have hδpos : 0 < p ⬝ᵥ E.endowment i - p ⬝ᵥ y i := sub_pos.mpr hlt_i
    have hSnonneg : 0 ≤ ∑ l, |p l| := Finset.sum_nonneg (fun l _ => abs_nonneg _)
    have hεpos : 0 < (p ⬝ᵥ E.endowment i - p ⬝ᵥ y i) / ((∑ l, |p l|) + 1) :=
      div_pos hδpos (by linarith)
    obtain ⟨z, hz_nonneg, hclose, hbetter⟩ :=
      hLNS i (y i) (hyfeas.1 i) _ hεpos
    have hdecomp : p ⬝ᵥ z - p ⬝ᵥ y i = p ⬝ᵥ (z - y i) :=
      (dotProduct_sub p z (y i)).symm
    have hbound :
        |p ⬝ᵥ (z - y i)|
          ≤ (∑ l, |p l|) * ((p ⬝ᵥ E.endowment i - p ⬝ᵥ y i) / ((∑ l, |p l|) + 1)) := by
      have hdot : p ⬝ᵥ (z - y i) = ∑ l, p l * (z l - y i l) := rfl
      rw [hdot]
      calc |∑ l, p l * (z l - y i l)|
          ≤ ∑ l, |p l * (z l - y i l)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l, |p l| * ((p ⬝ᵥ E.endowment i - p ⬝ᵥ y i) / ((∑ l, |p l|) + 1)) := by
            apply Finset.sum_le_sum
            intro l _
            rw [abs_mul]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact le_of_lt (hclose l)
        _ = (∑ l, |p l|) * ((p ⬝ᵥ E.endowment i - p ⬝ᵥ y i) / ((∑ l, |p l|) + 1)) :=
            (Finset.sum_mul _ _ _).symm
    have hsmall :
        (∑ l, |p l|) * ((p ⬝ᵥ E.endowment i - p ⬝ᵥ y i) / ((∑ l, |p l|) + 1))
          < p ⬝ᵥ E.endowment i - p ⬝ᵥ y i := by
      have hpos : 0 < (∑ l, |p l|) + 1 := by linarith
      rw [← mul_div_assoc, div_lt_iff₀ hpos]
      nlinarith [hδpos, hSnonneg]
    have hzaff : p ⬝ᵥ z ≤ p ⬝ᵥ E.endowment i := by
      have hle_abs : p ⬝ᵥ (z - y i) ≤ |p ⬝ᵥ (z - y i)| := le_abs_self _
      linarith [hdecomp, hbound, hsmall, hle_abs]
    have h := (hopt i).2 z hz_nonneg hzaff
    exact lt_irrefl _ ((hbetter.trans_le h).trans_le (hge i))
  have hsum : ∑ i, p ⬝ᵥ E.endowment i < ∑ i, p ⬝ᵥ y i :=
    Finset.sum_lt_sum (fun i _ => hspend i) ⟨j, Finset.mem_univ j, hstrict⟩
  have hdistribE : p ⬝ᵥ (∑ i, E.endowment i) = ∑ i, p ⬝ᵥ E.endowment i :=
    dotProduct_sum p Finset.univ _
  have hdistribY : p ⬝ᵥ (∑ i, y i) = ∑ i, p ⬝ᵥ y i :=
    dotProduct_sum p Finset.univ _
  have hmono : p ⬝ᵥ (∑ i, y i) ≤ p ⬝ᵥ (∑ i, E.endowment i) := by
    simp only [dotProduct]
    apply Finset.sum_le_sum
    intro l _
    apply mul_le_mul_of_nonneg_left _ (hp l)
    exact hyfeas.2 l
  rw [hdistribE, hdistribY] at hmono
  exact absurd hmono (not_le_of_gt hsum)

end ExchangeEconomy

end MathlibExt.Economics
