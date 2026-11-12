/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.ExpenditureDuality
public import MathlibExt.Economics.Envelope
public import MathlibExt.Analysis.Calculus.DotProductGradient
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Shephard's lemma

The price derivative of the expenditure function is the Hicksian (compensated) demand. Fix a
consumption set `X`, a utility `u`, and a target utility `ubar`. If `h` is a Hicksian demand at
prices `p₀` (a cheapest bundle in `X` reaching `ubar`) and the expenditure function is
differentiable at `p₀` with derivative `e'`, then `e' v = h ⬝ᵥ v` for every direction `v`;
consequently the Hicksian demand at `p₀` is unique.

The proof is the envelope argument: `p ↦ p ⬝ᵥ h` lies above the expenditure function near `p₀`
and touches it at `p₀` (`Economics.hasFDerivAt_eq_of_eventually_le_of_eq`). It does not use the
Slutsky equation.

Two forms are given. The `IsGLB` form takes any function `e` that is, near `p₀`, the greatest lower
bound of the costs of reaching `ubar`. The `expenditure` form specializes to
`Economics.Consumer.expenditure`, assuming the costs are bounded below near `p₀`.

## Main definitions

* `Economics.Consumer.IsHicksianDemand`: a cost-minimizing bundle reaching the target utility.

## Main results

* `Economics.Consumer.hasFDerivAt_expenditure_eq_hicksianDemand`: Shephard's lemma, `IsGLB` form.
* `Economics.Consumer.hicksianDemand_unique_of_hasFDerivAt`: uniqueness, `IsGLB` form.
* `Economics.Consumer.hasFDerivAt_expenditure_eq_of_isHicksianDemand`: Shephard's lemma for
  `expenditure`.
* `Economics.Consumer.isHicksianDemand_unique_of_hasFDerivAt`: uniqueness for `expenditure`.
* `Economics.Consumer.hasFDerivAt_expenditure_eq_dotL_of_isHicksianDemand`: the derivative of
  `expenditure` is `Real.dotL h`, the repository's gradient representation on `ι → ℝ`.

## References

* R. W. Shephard, *Cost and Production Functions*, Princeton University Press (1953).
* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Proposition 3.G.1.
-/

@[expose] public section

open Filter Topology

namespace Economics.Consumer

/-- **Shephard's lemma.** Let `e` be the expenditure function for target
utility `ubar` on a neighborhood of `p₀` (the infimum of the cost `p ⬝ᵥ x` over
bundles `x ∈ X` with `ubar ≤ u x`), and let `h` be a Hicksian demand at `p₀`.
If `e` is differentiable at `p₀` with derivative `e'`, then `e' v = h ⬝ᵥ v` for
every direction `v`: the price gradient of expenditure is `h`. -/
theorem hasFDerivAt_expenditure_eq_hicksianDemand {ι : Type*} [Fintype ι]
    {u : (ι → ℝ) → ℝ} {X : Set (ι → ℝ)} {ubar : ℝ} {e : (ι → ℝ) → ℝ}
    {p₀ h : ι → ℝ} {e' : (ι → ℝ) →L[ℝ] ℝ}
    (he : ∀ᶠ p in 𝓝 p₀,
      IsGLB ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x}) (e p))
    (hX : h ∈ X) (hu : ubar ≤ u h) (hcost : p₀ ⬝ᵥ h = e p₀)
    (hdiff : HasFDerivAt e e' p₀) :
    ∀ v, e' v = h ⬝ᵥ v := by
  have hg : HasFDerivAt (fun p => p ⬝ᵥ h) (Real.dotL h) p₀ :=
    Real.hasFDerivAt_dotProduct h p₀
  have hle : ∀ᶠ p in 𝓝 p₀, e p ≤ (fun p => p ⬝ᵥ h) p := by
    filter_upwards [he] with p hp
    have hmem : p ⬝ᵥ h ∈ (fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x} :=
      ⟨h, ⟨hX, hu⟩, rfl⟩
    exact mem_lowerBounds.mp hp.1 _ hmem
  have heq : e p₀ = (fun p => p ⬝ᵥ h) p₀ := hcost.symm
  have hderiv : e' = Real.dotL h :=
    _root_.Economics.hasFDerivAt_eq_of_eventually_le_of_eq hle heq hdiff hg
  intro v
  rw [hderiv, Real.dotL_apply, dotProduct_comm]

/-- Uniqueness of Hicksian demand under differentiability of expenditure: two
Hicksian demands at `p₀` coincide when `e` is differentiable at `p₀`. -/
theorem hicksianDemand_unique_of_hasFDerivAt {ι : Type*} [Fintype ι]
    {u : (ι → ℝ) → ℝ} {X : Set (ι → ℝ)} {ubar : ℝ} {e : (ι → ℝ) → ℝ}
    {p₀ h k : ι → ℝ} {e' : (ι → ℝ) →L[ℝ] ℝ}
    (he : ∀ᶠ p in 𝓝 p₀,
      IsGLB ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x}) (e p))
    (hX : h ∈ X) (hu : ubar ≤ u h) (hcost : p₀ ⬝ᵥ h = e p₀)
    (kX : k ∈ X) (ku : ubar ≤ u k) (kcost : p₀ ⬝ᵥ k = e p₀)
    (hdiff : HasFDerivAt e e' p₀) :
    h = k := by
  classical
  have hh := hasFDerivAt_expenditure_eq_hicksianDemand he hX hu hcost hdiff
  have hk := hasFDerivAt_expenditure_eq_hicksianDemand he kX ku kcost hdiff
  have hdeq : ∀ v, h ⬝ᵥ v = k ⬝ᵥ v := fun v => by rw [← hh v, hk v]
  funext i
  have hsingle : ∀ x : ι → ℝ, x ⬝ᵥ (Pi.single i 1 : ι → ℝ) = x i := by
    intro x
    simp only [dotProduct]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun b _ hb => by
      show x b * Pi.single (M := fun _ => ℝ) i 1 b = 0
      rw [Pi.single_eq_of_ne hb, mul_zero])]
    show x i * Pi.single (M := fun _ => ℝ) i 1 i = x i
    rw [Pi.single_eq_same, mul_one]
  have htest := hdeq (Pi.single i 1 : ι → ℝ)
  rw [hsingle h, hsingle k] at htest
  exact htest

/-- `h` is a Hicksian (compensated) demand at prices `p` for target utility
`ubar`: a bundle in `X` reaching `ubar` whose cost is minimal among all bundles
in `X` reaching `ubar`. -/
def IsHicksianDemand {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ)
    (X : Set (ι → ℝ)) (p : ι → ℝ) (ubar : ℝ) (h : ι → ℝ) : Prop :=
  h ∈ X ∧ ubar ≤ u h ∧ ∀ y ∈ X, ubar ≤ u y → p ⬝ᵥ h ≤ p ⬝ᵥ y

/-- **Shephard's lemma** for the expenditure function `expenditure u X · ubar`.
If the costs of reaching `ubar` are bounded below for all prices near `p₀`, `h`
is a Hicksian demand at `p₀`, and `p ↦ expenditure u X p ubar` has derivative
`e'` at `p₀`, then `e' v = h ⬝ᵥ v` for every direction `v`. -/
theorem hasFDerivAt_expenditure_eq_of_isHicksianDemand {ι : Type*} [Fintype ι]
    {u : (ι → ℝ) → ℝ} {X : Set (ι → ℝ)} {ubar : ℝ} {p₀ h : ι → ℝ}
    {e' : (ι → ℝ) →L[ℝ] ℝ}
    (hbdd : ∀ᶠ p in 𝓝 p₀,
      BddBelow ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x}))
    (hh : IsHicksianDemand u X p₀ ubar h)
    (hdiff : HasFDerivAt (fun p => expenditure u X p ubar) e' p₀) :
    ∀ v, e' v = h ⬝ᵥ v := by
  have hh' : h ∈ X ∧ ubar ≤ u h ∧ ∀ y ∈ X, ubar ≤ u y → p₀ ⬝ᵥ h ≤ p₀ ⬝ᵥ y := hh
  obtain ⟨hX, hu, hmin⟩ := hh'
  have he : ∀ᶠ p in 𝓝 p₀,
      IsGLB ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x})
        ((fun p => expenditure u X p ubar) p) := by
    filter_upwards [hbdd] with p hp
    exact isGLB_csInf ⟨_, h, ⟨hX, hu⟩, rfl⟩ hp
  have hcost : p₀ ⬝ᵥ h = (fun p => expenditure u X p ubar) p₀ := by
    symm
    apply IsLeast.csInf_eq
    constructor
    · exact ⟨h, ⟨hX, hu⟩, rfl⟩
    · intro b hb
      obtain ⟨y, ⟨yX, yu⟩, rfl⟩ := hb
      exact hmin y yX yu
  exact hasFDerivAt_expenditure_eq_hicksianDemand he hX hu hcost hdiff

/-- Uniqueness of Hicksian demand when the expenditure function
`expenditure u X · ubar` is differentiable at `p₀` and costs are bounded below
near `p₀`. -/
theorem isHicksianDemand_unique_of_hasFDerivAt {ι : Type*} [Fintype ι]
    {u : (ι → ℝ) → ℝ} {X : Set (ι → ℝ)} {ubar : ℝ} {p₀ h k : ι → ℝ}
    {e' : (ι → ℝ) →L[ℝ] ℝ}
    (hbdd : ∀ᶠ p in 𝓝 p₀,
      BddBelow ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x}))
    (hh : IsHicksianDemand u X p₀ ubar h) (hk : IsHicksianDemand u X p₀ ubar k)
    (hdiff : HasFDerivAt (fun p => expenditure u X p ubar) e' p₀) :
    h = k := by
  have hh' : h ∈ X ∧ ubar ≤ u h ∧ ∀ y ∈ X, ubar ≤ u y → p₀ ⬝ᵥ h ≤ p₀ ⬝ᵥ y := hh
  obtain ⟨hX, hu, hmin⟩ := hh'
  have hk' : k ∈ X ∧ ubar ≤ u k ∧ ∀ y ∈ X, ubar ≤ u y → p₀ ⬝ᵥ k ≤ p₀ ⬝ᵥ y := hk
  obtain ⟨kX, ku, kmin⟩ := hk'
  have he : ∀ᶠ p in 𝓝 p₀,
      IsGLB ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x})
        ((fun p => expenditure u X p ubar) p) := by
    filter_upwards [hbdd] with p hp
    exact isGLB_csInf ⟨_, h, ⟨hX, hu⟩, rfl⟩ hp
  have hcost : p₀ ⬝ᵥ h = (fun p => expenditure u X p ubar) p₀ := by
    symm
    apply IsLeast.csInf_eq
    constructor
    · exact ⟨h, ⟨hX, hu⟩, rfl⟩
    · intro b hb
      obtain ⟨y, ⟨yX, yu⟩, rfl⟩ := hb
      exact hmin y yX yu
  have kcost : p₀ ⬝ᵥ k = (fun p => expenditure u X p ubar) p₀ := by
    symm
    apply IsLeast.csInf_eq
    constructor
    · exact ⟨k, ⟨kX, ku⟩, rfl⟩
    · intro b hb
      obtain ⟨y, ⟨yX, yu⟩, rfl⟩ := hb
      exact kmin y yX yu
  exact hicksianDemand_unique_of_hasFDerivAt he hX hu hcost kX ku kcost hdiff

/-- Shephard's lemma in canonical gradient form: the derivative of
`p ↦ expenditure u X p ubar` at `p₀` is `Real.dotL h`. -/
theorem hasFDerivAt_expenditure_eq_dotL_of_isHicksianDemand {ι : Type*} [Fintype ι]
    {u : (ι → ℝ) → ℝ} {X : Set (ι → ℝ)} {ubar : ℝ} {p₀ h : ι → ℝ}
    {e' : (ι → ℝ) →L[ℝ] ℝ}
    (hbdd : ∀ᶠ p in 𝓝 p₀,
      BddBelow ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x}))
    (hh : IsHicksianDemand u X p₀ ubar h)
    (hdiff : HasFDerivAt (fun p => expenditure u X p ubar) e' p₀) :
    e' = Real.dotL h := by
  have h1 := hasFDerivAt_expenditure_eq_of_isHicksianDemand hbdd hh hdiff
  apply ContinuousLinearMap.ext
  intro v
  rw [h1 v, Real.dotL_apply, dotProduct_comm]

end Economics.Consumer
