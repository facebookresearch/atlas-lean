/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_realize_eq_div.lean`,
`Definitions/Def_ModularCurve_ComplexPlaceDictionary.lean`
and
`P2M/Sol/S_ModularCurve_realize_eq_div.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.LaurentSeries

@[expose] public section

open UpperHalfPlane

namespace ModularCurve

/-- Pointwise realization of a Laurent series as a quotient of two modular
forms of the same weight for `Γ₀ N`: if some pair of same-weight forms `g, h`
has `x * h̃ = g̃` for their `q`-expansions and also `h τ ≠ 0`, the value at `τ`
is `g τ / h τ` for such a pair, and `0` when no pair satisfies both. -/
noncomputable def realize (N : ℕ) (x : LaurentSeries ℂ) (τ : ℍ) : ℂ := by
  classical
  exact
    if H : ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
          ModularForm (CongruenceSubgroup.Gamma0 N) k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
    else 0

/-- If the Laurent series `x` satisfies the multiplied `q`-expansion identity
`x * q(h) = q(g)` for same-weight modular forms `g, h`, and `h` does not vanish
at `τ`, then the realization of `x` at `τ` is the pointwise quotient `g τ / h τ`. -/
public theorem realize_eq_div (N : ℕ) {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (x : LaurentSeries ℂ)
    (hx : x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (τ : ℍ) (hτ : (h : ℍ → ℂ) τ ≠ 0) :
    ModularCurve.realize N x τ = (g : ℍ → ℂ) τ / (h : ℍ → ℂ) τ := by
  classical
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  have H : ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
        ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
        x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
    ⟨⟨k, g, h⟩, hτ, hx⟩
  have hval : ModularCurve.realize N x τ = (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ := by
    simp only [ModularCurve.realize, dif_pos H]
  rw [hval]
  obtain ⟨hτ', hx'⟩ := H.choose_spec
  set p := H.choose with hp
  obtain ⟨k', g', h'⟩ := p
  simp only at hτ' hx' ⊢
  have hq : qExpansion 1 ((g' : ℍ → ℂ) * (h : ℍ → ℂ)) =
      qExpansion 1 ((g : ℍ → ℂ) * (h' : ℍ → ℂ)) := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
    rw [ModularForm.qExpansion_mul_coe one_pos h1, ModularForm.qExpansion_mul_coe one_pos h1,
      PowerSeries.coe_mul, PowerSeries.coe_mul, ← hx, ← hx']
    ring
  have hAB : (g'.mul h : ModularForm (CongruenceSubgroup.Gamma0 N) (k' + k)) =
      ModularForm.mcast (add_comm k k') (g.mul h') := by
    rw [← sub_eq_zero, ← ModularForm.qExpansion_eq_zero_iff one_pos h1, ModularForm.coe_sub,
      ModularForm.qExpansion_sub one_pos h1, sub_eq_zero, ModularForm.coe_mcast,
      ModularForm.coe_mul, ModularForm.coe_mul, hq]
  have hτeq : (g' : ℍ → ℂ) τ * (h : ℍ → ℂ) τ = (g : ℍ → ℂ) τ * (h' : ℍ → ℂ) τ := by
    have := congrArg (fun f : ModularForm (CongruenceSubgroup.Gamma0 N) (k' + k) => (f : ℍ → ℂ) τ)
      hAB
    simpa [ModularForm.coe_mul, ModularForm.coe_mcast] using this
  rw [div_eq_div_iff hτ' hτ, hτeq]

end ModularCurve
