/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Producer.ProductionSet
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# The law of supply

If `y` maximizes profit at prices `p` and `y'` at prices `p'` over the same production set,
then `(p - p') ⬝ᵥ (y - y') ≥ 0` (revealed profitability). When only the price of good `i`
changes, the net supply of good `i` moves weakly in the same direction as its price. No
convexity of the production set is used.

## Main results

* `MathlibExt.Economics.Producer.IsProfitMax.law_of_supply`
* `MathlibExt.Economics.Producer.IsProfitMax.law_of_supply_single`

## References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Section 5.C, p. 138.

Atlas roadmap target EC06.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Producer

/-- **Law of supply** (revealed profitability). If `y` maximizes profit at `p` and `y'` at
`p'` over the same production set, then `(p - p') ⬝ᵥ (y - y') ≥ 0`. -/
theorem IsProfitMax.law_of_supply {ι : Type*} [Fintype ι] {Y : Set (ι → ℝ)}
    {p p' y y' : ι → ℝ} (h : IsProfitMax Y p y) (h' : IsProfitMax Y p' y') :
    0 ≤ (p - p') ⬝ᵥ (y - y') := by
  obtain ⟨hy, hmax⟩ := h
  obtain ⟨hy', hmax'⟩ := h'
  have h1 : p ⬝ᵥ y' ≤ p ⬝ᵥ y := hmax y' hy'
  have h2 : p' ⬝ᵥ y ≤ p' ⬝ᵥ y' := hmax' y hy
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
  linarith

/-- Single-price law of supply: when only the price of good `i` changes, net supply of good `i`
moves weakly in the same direction as its price. -/
theorem IsProfitMax.law_of_supply_single {ι : Type*} [Fintype ι] {Y : Set (ι → ℝ)}
    {p p' y y' : ι → ℝ} (h : IsProfitMax Y p y) (h' : IsProfitMax Y p' y') (i : ι)
    (hp : ∀ j, j ≠ i → p j = p' j) :
    0 ≤ (p i - p' i) * (y i - y' i) := by
  have hmain : 0 ≤ (p - p') ⬝ᵥ (y - y') := h.law_of_supply h'
  have hexpand : (p - p') ⬝ᵥ (y - y') = (p i - p' i) * (y i - y' i) := by
    unfold dotProduct
    rw [Finset.sum_eq_single i]
    · simp only [Pi.sub_apply]
    · intro b _ hb
      have hpb : p b = p' b := hp b hb
      simp [Pi.sub_apply, hpb]
    · simp
  rw [hexpand] at hmain
  exact hmain

end MathlibExt.Economics.Producer
