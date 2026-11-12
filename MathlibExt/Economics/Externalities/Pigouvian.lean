/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Extrema
public import Mathlib.Analysis.Convex.Deriv

/-!
# Pigouvian tax (Atlas AP02.T01)

A competitive market produces quantity `q` of a good. Consumers' gross benefit is
`B q`, producers' cost is `C q`, and production causes an external damage `Dm q`
borne by third parties. Social welfare is `B q - C q - Dm q`. Market participants
ignore the damage; under a per-unit tax `τ` their joint (taxed private) surplus is
`B q - C q - τ q`, which a competitive market maximizes.

At an interior social optimum `q`, the first-order condition is
`B'(q) = C'(q) + Dm'(q)`. Setting the tax equal to the marginal damage at the
optimum, `τ = Dm'(q)`, makes `q` satisfy the taxed market condition
`B'(q) = C'(q) + τ`; if the taxed private surplus is concave on a convex
neighborhood set `S` of `q`, then `q` maximizes it on `S`, so the tax implements
the social optimum.
-/

@[expose] public section

open Topology

namespace MathlibExt.Economics.Pigouvian

/-- Social welfare: benefit minus private cost minus external damage. -/
def socialWelfare (B C Dm : ℝ → ℝ) (q : ℝ) : ℝ := B q - C q - Dm q

/-- Taxed private surplus under a per-unit tax `τ`: benefit minus cost minus tax
payments. -/
def taxedSurplus (B C : ℝ → ℝ) (τ q : ℝ) : ℝ := B q - C q - τ * q

/-- At an interior social optimum, marginal benefit equals marginal private cost
plus marginal damage: with `τ = Dm'(q)`, `q` satisfies the taxed market
condition `B'(q) = C'(q) + τ`. -/
theorem marginalBenefit_eq_marginalCost_add_tax {B C Dm : ℝ → ℝ} {q b c d : ℝ}
    (hopt : IsLocalMax (socialWelfare B C Dm) q)
    (hB : HasDerivAt B b q) (hC : HasDerivAt C c q) (hD : HasDerivAt Dm d q) :
    b = c + d := by
  have hderiv : HasDerivAt (socialWelfare B C Dm) (b - c - d) q :=
    (hB.sub hC).sub hD
  have h0 := hopt.hasDerivAt_eq_zero hderiv
  linarith

/-- **The Pigouvian tax implements the social optimum.** Let `q` be an interior
social optimum and set the tax to the marginal damage `d = Dm'(q)`. If the taxed
private surplus is concave on a set `S` that is a neighborhood of `q`, then `q`
maximizes the taxed private surplus on `S`. -/
theorem isMaxOn_taxedSurplus_of_isLocalMax {B C Dm : ℝ → ℝ} {S : Set ℝ} {q b c d : ℝ}
    (hS : S ∈ 𝓝 q) (hopt : IsLocalMax (socialWelfare B C Dm) q)
    (hB : HasDerivAt B b q) (hC : HasDerivAt C c q) (hD : HasDerivAt Dm d q)
    (hconc : ConcaveOn ℝ S (taxedSurplus B C d)) :
    IsMaxOn (taxedSurplus B C d) S q := by
  have hFOC : b = c + d :=
    marginalBenefit_eq_marginalCost_add_tax hopt hB hC hD
  have hlin : HasDerivAt (fun q : ℝ => d * q) d q := by
    have h := (hasDerivAt_id' q).const_mul d
    simpa only [mul_one] using h
  have hderiv : HasDerivAt (taxedSurplus B C d) (b - c - d) q :=
    (hB.sub hC).sub hlin
  have h0 : b - c - d = 0 := by linarith
  rw [h0] at hderiv
  have hqS : q ∈ S := mem_of_mem_nhds hS
  intro x hx
  change taxedSurplus B C d x ≤ taxedSurplus B C d q
  rcases lt_trichotomy x q with hlt | heq | hgt
  · have hle := hconc.le_slope_of_hasDerivAt hx hqS hlt hderiv
    rw [slope_def_field] at hle
    have hpos : (0:ℝ) < q - x := sub_pos.mpr hlt
    have h := (le_div_iff₀ hpos).mp hle
    linarith
  · simp only [heq, le_refl]
  · have hle := hconc.slope_le_of_hasDerivAt hqS hx hgt hderiv
    rw [slope_def_field] at hle
    have hpos : (0:ℝ) < x - q := sub_pos.mpr hgt
    have h := (div_le_iff₀ hpos).mp hle
    linarith

end MathlibExt.Economics.Pigouvian
