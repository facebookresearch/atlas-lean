/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Market.SupplyDemand
public import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Existence and uniqueness of partial equilibrium

Continuous demand and supply schedules on a price interval `[a, b]`, with nonnegative excess
demand at `a` and nonpositive excess demand at `b`, have an equilibrium price in `[a, b]`
(intermediate value theorem). Strictly decreasing excess demand allows at most one equilibrium;
weakly decreasing demand with strictly increasing supply gives strictly decreasing excess demand.

## Main results

* `Economics.Market.exists_isEquilibrium_of_sign_change`
* `Economics.Market.IsEquilibrium.eq_of_strictAntiOn`
* `Economics.Market.existsUnique_isEquilibrium`

## References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Section 10.C.

Atlas roadmap target EC08.T01.
-/

@[expose] public section

namespace Economics.Market

/-- Equilibrium is zero excess demand. -/
theorem isEquilibrium_iff_excessDemand_eq_zero {D S : ℝ → ℝ} {p : ℝ} :
    IsEquilibrium D S p ↔ excessDemand D S p = 0 := by
  simp only [IsEquilibrium, excessDemand, sub_eq_zero]

/-- **Existence.** Continuous schedules on `[a, b]` with nonnegative excess demand at `a` and
nonpositive excess demand at `b` have an equilibrium price in `[a, b]`. -/
theorem exists_isEquilibrium_of_sign_change {D S : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hD : ContinuousOn D (Set.Icc a b)) (hS : ContinuousOn S (Set.Icc a b))
    (ha : 0 ≤ excessDemand D S a) (hb : excessDemand D S b ≤ 0) :
    ∃ p ∈ Set.Icc a b, IsEquilibrium D S p := by
  have hZ : ContinuousOn (excessDemand D S) (Set.Icc a b) := hD.sub hS
  have hsub := intermediate_value_Icc' hab hZ
  have h0 : (0 : ℝ) ∈ Set.Icc (excessDemand D S b) (excessDemand D S a) := ⟨hb, ha⟩
  obtain ⟨p, hp_mem, hp_eq⟩ := hsub h0
  exact ⟨p, hp_mem, isEquilibrium_iff_excessDemand_eq_zero.mpr hp_eq⟩

/-- **Uniqueness.** If excess demand is strictly decreasing on `s`, there is at most one
equilibrium price in `s`. -/
theorem IsEquilibrium.eq_of_strictAntiOn {D S : ℝ → ℝ} {s : Set ℝ} {p q : ℝ}
    (hZ : StrictAntiOn (excessDemand D S) s) (hp : p ∈ s) (hq : q ∈ s)
    (hep : IsEquilibrium D S p) (heq : IsEquilibrium D S q) : p = q := by
  have h1 : excessDemand D S p = 0 := isEquilibrium_iff_excessDemand_eq_zero.mp hep
  have h2 : excessDemand D S q = 0 := isEquilibrium_iff_excessDemand_eq_zero.mp heq
  exact hZ.injOn hp hq (h1.trans h2.symm)

/-- Weakly decreasing demand and strictly increasing supply give strictly decreasing excess
demand. -/
theorem strictAntiOn_excessDemand {D S : ℝ → ℝ} {s : Set ℝ} (hD : AntitoneOn D s)
    (hS : StrictMonoOn S s) : StrictAntiOn (excessDemand D S) s := by
  intro x hx y hy hxy
  show excessDemand D S y < excessDemand D S x
  have hD' : D y ≤ D x := hD hx hy hxy.le
  have hS' : S x < S y := hS hx hy hxy
  simp only [excessDemand]
  linarith

/-- **Existence and uniqueness** of the equilibrium price in `[a, b]`. -/
theorem existsUnique_isEquilibrium {D S : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hD : ContinuousOn D (Set.Icc a b)) (hS : ContinuousOn S (Set.Icc a b))
    (ha : 0 ≤ excessDemand D S a) (hb : excessDemand D S b ≤ 0)
    (hZ : StrictAntiOn (excessDemand D S) (Set.Icc a b)) :
    ∃! p, p ∈ Set.Icc a b ∧ IsEquilibrium D S p := by
  obtain ⟨p, hp_mem, hp_eq⟩ := exists_isEquilibrium_of_sign_change hab hD hS ha hb
  exact ⟨p, ⟨hp_mem, hp_eq⟩, fun q hq =>
    IsEquilibrium.eq_of_strictAntiOn hZ hq.1 hp_mem hq.2 hp_eq⟩

end Economics.Market
