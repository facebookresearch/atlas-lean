/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.Convex.Function
import Mathlib.Basic.Real.Pointwise

/-!
# Expenditure function: homogeneity and concavity in prices (Atlas EC04.T01)

The expenditure function `e(p, ū) = inf {p ⬝ᵥ x | x ∈ X, ū ≤ u x}` is the least
cost at prices `p` of a bundle in the consumption set `X` reaching utility at
least `ū`.

* It is homogeneous of degree one in prices: `e(t • p, ū) = t * e(p, ū)` for
  `t ≥ 0`. No hypothesis is needed (the real `sInf` conventions scale too).
* It is concave in prices on any convex set of prices on which the target is
  feasible and costs are bounded below: it is an infimum of the linear maps
  `p ↦ p ⬝ᵥ x`. No attainment (Hicksian demand) is needed.
* In particular it is concave on strictly positive prices when `X` lies in the
  nonnegative orthant and the target is feasible.

These are Mas-Colell, Whinston and Green's Proposition 3.E.2 (i) and (iii),
stated more generally: the source assumes a continuous, locally nonsatiated
utility on the nonnegative orthant and strictly positive prices; here concavity
needs only feasibility of the target and bounded-below costs on a convex price
set, and homogeneity needs no hypothesis. The positive-orthant corollary is the
source's setting.

Implementation note: this is the canonical expenditure declaration. Consumer duality
re-exports it as `Economics.Consumer.expenditure`.

## References

* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford
  University Press (1995), Section 3.E, Proposition 3.E.2.
-/

@[expose] public section

namespace MathlibExt.Economics.ExpenditureFunction

/-- The expenditure function `e(p, ū) = inf {p ⬝ᵥ x | x ∈ X, ū ≤ u x}`. As a real
infimum it is meaningful only when the target is feasible and costs are bounded
below. -/
noncomputable def expenditure {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ)
    (X : Set (ι → ℝ)) (p : ι → ℝ) (ubar : ℝ) : ℝ :=
  sInf ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x})

/-- **Homogeneity of degree one.** Scaling all prices by `t ≥ 0` scales
expenditure by `t`. -/
theorem expenditure_smul {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ) (X : Set (ι → ℝ))
    (p : ι → ℝ) (ubar : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    expenditure u X (t • p) ubar = t * expenditure u X p ubar := by
  unfold expenditure
  have hfun : (fun x => (t • p) ⬝ᵥ x) = (fun y => t • y) ∘ (fun x => p ⬝ᵥ x) := by
    funext x
    exact smul_dotProduct t p x
  rw [hfun, Set.image_comp, Set.image_smul, Real.sInf_smul_of_nonneg ht, smul_eq_mul]

/-- **Concavity in prices.** On a convex set `P` of prices at which the costs of
reaching `ubar` are bounded below, if the target `ubar` is feasible, expenditure
is concave in prices. -/
theorem concaveOn_expenditure {ι : Type*} [Fintype ι] {u : (ι → ℝ) → ℝ}
    {X : Set (ι → ℝ)} {ubar : ℝ} {P : Set (ι → ℝ)} (hP : Convex ℝ P)
    (hfeas : ∃ x ∈ X, ubar ≤ u x)
    (hbdd : ∀ p ∈ P, BddBelow ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x})) :
    ConcaveOn ℝ P (fun p => expenditure u X p ubar) := by
  refine ⟨hP, fun x hx y hy a b ha hb hab => ?_⟩
  obtain ⟨x0, hx0X, hx0u⟩ := hfeas
  have hSne : {z | z ∈ X ∧ ubar ≤ u z}.Nonempty := ⟨x0, hx0X, hx0u⟩
  have hne : ((fun z => (a • x + b • y) ⬝ᵥ z) '' {z | z ∈ X ∧ ubar ≤ u z}).Nonempty :=
    hSne.image _
  simp only [smul_eq_mul, expenditure]
  apply le_csInf hne
  intro c hc
  obtain ⟨z, ⟨hzX, hzu⟩, rfl⟩ := hc
  have hx_le : sInf ((fun z => x ⬝ᵥ z) '' {z | z ∈ X ∧ ubar ≤ u z}) ≤ x ⬝ᵥ z :=
    csInf_le (hbdd x hx) ⟨z, ⟨hzX, hzu⟩, rfl⟩
  have hy_le : sInf ((fun z => y ⬝ᵥ z) '' {z | z ∈ X ∧ ubar ≤ u z}) ≤ y ⬝ᵥ z :=
    csInf_le (hbdd y hy) ⟨z, ⟨hzX, hzu⟩, rfl⟩
  have hdot : (a • x + b • y) ⬝ᵥ z = a * (x ⬝ᵥ z) + b * (y ⬝ᵥ z) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  simp only [] at hdot ⊢
  rw [hdot]
  exact add_le_add (mul_le_mul_of_nonneg_left hx_le ha) (mul_le_mul_of_nonneg_left hy_le hb)

/-- Concavity on strictly positive prices when consumption bundles are
nonnegative and the target utility is feasible. -/
theorem concaveOn_expenditure_pos {ι : Type*} [Fintype ι] {u : (ι → ℝ) → ℝ}
    {X : Set (ι → ℝ)} {ubar : ℝ} (hX : ∀ x ∈ X, ∀ i, 0 ≤ x i)
    (hfeas : ∃ x ∈ X, ubar ≤ u x) :
    ConcaveOn ℝ {p : ι → ℝ | ∀ i, 0 < p i} (fun p => expenditure u X p ubar) := by
  have hP : Convex ℝ {p : ι → ℝ | ∀ i, 0 < p i} := by
    intro x hx y hy a b ha hb hab i
    have hx' := hx i
    have hy' := hy i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_ne a 0 with rfl | hane
    · simp only [zero_mul, zero_add]
      have hb1 : b = 1 := by linarith [hab]
      rw [hb1, one_mul]
      exact hy'
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hane)
      have h1 : 0 < a * x i := mul_pos hap hx'
      have h2 : 0 ≤ b * y i := mul_nonneg hb hy'.le
      linarith
  have hbdd : ∀ p ∈ {p : ι → ℝ | ∀ i, 0 < p i},
      BddBelow ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x}) := by
    intro p hp
    refine ⟨0, ?_⟩
    intro c hc
    obtain ⟨x, ⟨hxX, _⟩, rfl⟩ := hc
    simp only []
    apply dotProduct_nonneg_of_nonneg
    · intro i
      exact le_of_lt (hp i)
    · intro i
      exact hX x hxX i
  exact concaveOn_expenditure hP hfeas hbdd

end MathlibExt.Economics.ExpenditureFunction
