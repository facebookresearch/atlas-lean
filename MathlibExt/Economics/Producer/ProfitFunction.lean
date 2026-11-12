/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Producer.ProductionSet
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Matrix.Mul

/-!
# Convexity of the profit function

The profit function `profitFn Y p = sSup ((fun y => p ⬝ᵥ y) '' Y)` is a real `sSup`; it is the
economically meaningful value on `profitDomain Y`, the prices at which profit is bounded above
on `Y`. That domain is convex and the profit function is convex on it, with no convexity of
`Y`. At an attained maximum the profit function equals the maximal profit.

The profit function is the support function of `Y`, the Legendre transform of its indicator.
Atlas proves the extended-real epigraph form
(`MathlibExt.Probability.LegendreTransform.convex_epi_legendreTransform`), but its real-valued
corollary `MathlibExt.Probability.LegendreTransform.convexOn_legendreTransform` assumes the
transform is finite everywhere, which fails off `profitDomain Y`, and both are stated on
`EuclideanSpace`. The proof here is therefore the direct `le_csSup` / `csSup_le` argument on the
finite-valued domain, as the reuse audit allows.

## Main results

* `MathlibExt.Economics.Producer.convex_profitDomain`
* `MathlibExt.Economics.Producer.convexOn_profitFn`
* `MathlibExt.Economics.Producer.IsProfitMax.profitFn_eq`

## References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Proposition 5.C.1.

Atlas roadmap target EC06.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Producer

/-- The profit function `π(p) = sup_{y ∈ Y} p ⬝ᵥ y`, as a real `sSup`. It is the economically
meaningful value only on `profitDomain Y`, where the supremum is finite. -/
noncomputable def profitFn {ι : Type*} [Fintype ι] (Y : Set (ι → ℝ)) (p : ι → ℝ) : ℝ :=
  sSup ((fun y => p ⬝ᵥ y) '' Y)

/-- The finite-valued domain of the profit function: prices at which profit is bounded above
on `Y`. -/
def profitDomain {ι : Type*} [Fintype ι] (Y : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {p | BddAbove ((fun y => p ⬝ᵥ y) '' Y)}

/-- Linearity of the dot product in the price vector, for a convex combination. -/
private theorem dotProduct_convex_comb {ι : Type*} [Fintype ι] (p q y : ι → ℝ) (a b : ℝ) :
    (a • p + b • q) ⬝ᵥ y = a * (p ⬝ᵥ y) + b * (q ⬝ᵥ y) := by
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]

/-- The finite-valued domain of the profit function is convex. -/
theorem convex_profitDomain {ι : Type*} [Fintype ι] (Y : Set (ι → ℝ)) :
    Convex ℝ (profitDomain Y) := by
  intro p hp q hq a b ha hb hab
  simp only [profitDomain, Set.mem_ofPred_eq] at hp hq ⊢
  obtain ⟨Mp, hMp⟩ := hp
  obtain ⟨Mq, hMq⟩ := hq
  refine ⟨a * Mp + b * Mq, ?_⟩
  rintro _ ⟨y, hyY, rfl⟩
  have h1 : p ⬝ᵥ y ≤ Mp := hMp ⟨y, hyY, rfl⟩
  have h2 : q ⬝ᵥ y ≤ Mq := hMq ⟨y, hyY, rfl⟩
  calc (a • p + b • q) ⬝ᵥ y
      = a * (p ⬝ᵥ y) + b * (q ⬝ᵥ y) := dotProduct_convex_comb p q y a b
    _ ≤ a * Mp + b * Mq :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

/-- **The profit function is convex** in prices on its finite-valued domain. No convexity of
`Y` is assumed. -/
theorem convexOn_profitFn {ι : Type*} [Fintype ι] (Y : Set (ι → ℝ)) :
    ConvexOn ℝ (profitDomain Y) (profitFn Y) := by
  refine ⟨convex_profitDomain Y, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [profitDomain, Set.mem_ofPred_eq] at hx hy
  show profitFn Y (a • x + b • y) ≤ a • profitFn Y x + b • profitFn Y y
  by_cases hY : Y.Nonempty
  · have hne : ((fun z => (a • x + b • y) ⬝ᵥ z) '' Y).Nonempty := hY.image _
    have hle : sSup ((fun z => (a • x + b • y) ⬝ᵥ z) '' Y)
        ≤ a • profitFn Y x + b • profitFn Y y := by
      refine csSup_le hne ?_
      rintro _ ⟨z, hzY, rfl⟩
      have h1 : x ⬝ᵥ z ≤ profitFn Y x := le_csSup hx ⟨z, hzY, rfl⟩
      have h2 : y ⬝ᵥ z ≤ profitFn Y y := le_csSup hy ⟨z, hzY, rfl⟩
      calc (a • x + b • y) ⬝ᵥ z
          = a * (x ⬝ᵥ z) + b * (y ⬝ᵥ z) := dotProduct_convex_comb x y z a b
        _ ≤ a * profitFn Y x + b * profitFn Y y :=
            add_le_add (mul_le_mul_of_nonneg_left h1 ha)
              (mul_le_mul_of_nonneg_left h2 hb)
        _ = a • profitFn Y x + b • profitFn Y y := by rw [smul_eq_mul, smul_eq_mul]
    exact hle
  · rw [Set.not_nonempty_iff_eq_empty] at hY
    subst hY
    simp [profitFn]

/-- An attained maximum is in the finite-valued domain. -/
theorem IsProfitMax.mem_profitDomain {ι : Type*} [Fintype ι] {Y : Set (ι → ℝ)}
    {p y : ι → ℝ} (h : IsProfitMax Y p y) : p ∈ profitDomain Y := by
  show BddAbove ((fun y' => p ⬝ᵥ y') '' Y)
  refine ⟨p ⬝ᵥ y, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact h.2 y' hy'

/-- At an attained maximum, the profit function equals the maximal profit. -/
theorem IsProfitMax.profitFn_eq {ι : Type*} [Fintype ι] {Y : Set (ι → ℝ)} {p y : ι → ℝ}
    (h : IsProfitMax Y p y) : profitFn Y p = p ⬝ᵥ y := by
  show sSup ((fun y' => p ⬝ᵥ y') '' Y) = p ⬝ᵥ y
  apply IsGreatest.csSup_eq
  refine ⟨⟨y, h.1, rfl⟩, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact h.2 y' hy'

end MathlibExt.Economics.Producer
