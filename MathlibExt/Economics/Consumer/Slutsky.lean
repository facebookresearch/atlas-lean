/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.Shephard
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The Slutsky equation

Let `x p w` be the Marshallian demand at prices `p` and wealth `w`, let `h p` be the Hicksian
demand for a target utility `ubar`, and write `e p = expenditure u X p ubar`. Near `p₀` the two
demands are linked by the duality `h p = x p (e p)`. If `e`, `(p, w) ↦ x p w` (at
`(p₀, e p₀)`) and `h` are differentiable, then for all goods `i, j`

  `∂h_i/∂p_j (p₀) = ∂x_i/∂p_j (p₀, w₀) + ∂x_i/∂w (p₀, w₀) · x_j (p₀, w₀)`,  `w₀ = e p₀`:

the substitution effect equals the price effect plus the income effect. Derivatives are written
with Fréchet derivatives: `∂/∂p_j` is evaluation at `(Pi.single j 1, 0)` and `∂/∂w` at `(0, 1)`.

The proof differentiates the duality identity by the chain rule and substitutes Shephard's lemma
(`Economics.Consumer.hasFDerivAt_expenditure_eq_of_isHicksianDemand`) for `∂e/∂p_j = h_j`. The
duality is a hypothesis; `x` is otherwise unconstrained, so the identity holds for any demand
system linked to the Hicksian demand in this way. No sign of the substitution effect is claimed.

## Main results

* `Economics.Consumer.slutsky_equation`.

## References

* E. Slutsky, *Sulla teoria del bilancio del consumatore*, Giornale degli Economisti 51 (1915),
  1–26.
* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Proposition 3.G.3.
-/

@[expose] public section

open Filter Topology

namespace Economics.Consumer

/-- **Slutsky equation.** Let the costs of reaching `ubar` be bounded below
near `p₀`, let `h p₀` be a Hicksian demand at `p₀`, and let the Hicksian and
Marshallian demands satisfy the duality `h p = x p (expenditure u X p ubar)`
for `p` near `p₀`. If the expenditure function is differentiable at `p₀`,
`(p, w) ↦ x p w` is differentiable at `(p₀, w₀)` with derivative `Dx`
(`w₀ = expenditure u X p₀ ubar`), and `h` is differentiable at `p₀` with
derivative `Dh`, then for all goods `i, j` the substitution effect
`∂h_i/∂p_j` equals the price effect `∂x_i/∂p_j` plus the income effect
`∂x_i/∂w · x_j`, all evaluated at `(p₀, w₀)`. -/
theorem slutsky_equation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : (ι → ℝ) → ℝ} {X : Set (ι → ℝ)} {ubar : ℝ}
    {x : (ι → ℝ) → ℝ → (ι → ℝ)} {h : (ι → ℝ) → (ι → ℝ)} {p₀ : ι → ℝ}
    {e' : (ι → ℝ) →L[ℝ] ℝ}
    {Dx : ((ι → ℝ) × ℝ) →L[ℝ] (ι → ℝ)} {Dh : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hbdd : ∀ᶠ p in 𝓝 p₀,
      BddBelow ((fun y => p ⬝ᵥ y) '' {y | y ∈ X ∧ ubar ≤ u y}))
    (hh : IsHicksianDemand u X p₀ ubar (h p₀))
    (hdual : ∀ᶠ p in 𝓝 p₀, h p = x p (expenditure u X p ubar))
    (hediff : HasFDerivAt (fun p => expenditure u X p ubar) e' p₀)
    (hxdiff : HasFDerivAt (fun q : (ι → ℝ) × ℝ => x q.1 q.2) Dx
      (p₀, expenditure u X p₀ ubar))
    (hhdiff : HasFDerivAt h Dh p₀) (i j : ι) :
    Dh (Pi.single j 1) i =
      Dx (Pi.single j 1, 0) i +
        Dx (0, 1) i * x p₀ (expenditure u X p₀ ubar) j := by
  have hShep : ∀ v, e' v = (h p₀) ⬝ᵥ v :=
    hasFDerivAt_expenditure_eq_of_isHicksianDemand hbdd hh hediff
  have hinner : HasFDerivAt (fun p : ι → ℝ => (p, expenditure u X p ubar))
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod e') p₀ :=
    (hasFDerivAt_id p₀).prodMk hediff
  have hcomp : HasFDerivAt ((fun q : (ι → ℝ) × ℝ => x q.1 q.2) ∘
      (fun p : ι → ℝ => (p, expenditure u X p ubar)))
      (Dx.comp ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod e')) p₀ :=
    hxdiff.comp p₀ hinner
  have heq : h =ᶠ[𝓝 p₀] ((fun q : (ι → ℝ) × ℝ => x q.1 q.2) ∘
      (fun p : ι → ℝ => (p, expenditure u X p ubar))) := by
    filter_upwards [hdual] with p hp
    show h p = x p (expenditure u X p ubar)
    exact hp
  have hDh : HasFDerivAt h
      (Dx.comp ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod e')) p₀ :=
    hcomp.congr_of_eventuallyEq heq
  have hDeq : Dh = Dx.comp ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod e') :=
    hhdiff.unique hDh
  rw [hDeq, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  have hsplit : ((Pi.single j 1 : ι → ℝ), e' (Pi.single j 1)) =
      (Pi.single j 1, 0) + e' (Pi.single j 1) • ((0 : ι → ℝ), 1) := by
    simp only [Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, smul_eq_mul,
      mul_one, zero_add]
  rw [hsplit, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hev : e' (Pi.single j 1) = x p₀ (expenditure u X p₀ ubar) j := by
    rw [hShep _, dotProduct_single_one]
    have h0 : h p₀ = x p₀ (expenditure u X p₀ ubar) := hdual.self_of_nhds
    rw [h0]
  congr 1
  rw [hev, mul_comm]

end Economics.Consumer
