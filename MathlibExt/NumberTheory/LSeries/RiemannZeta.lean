/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section

/-!
# Meromorphicity of the Riemann zeta function

`riemannZeta` is meromorphic on `ℂ`: away from its pole at `s = 1` it equals
`(s - 1)⁻¹ + riemannZeta₀ s`, and `riemannZeta₀` is entire.
-/

/-- **Meromorphy of the Riemann zeta function.** The Riemann zeta function $\zeta$ is
meromorphic on all of $\mathbb{C}$. -/
theorem meromorphicOn_riemannZeta : MeromorphicOn riemannZeta Set.univ := by
  have hInv : MeromorphicOn (fun s : ℂ => (s - 1)⁻¹) Set.univ :=
    (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.inv
  have h0 : AnalyticOnNhd ℂ riemannZeta₀ Set.univ := fun x _ =>
    differentiable_riemannZeta₀.analyticAt x
  have heq : (fun s : ℂ => (s - 1)⁻¹ + riemannZeta₀ s) =ᶠ[Filter.codiscreteWithin Set.univ]
      riemannZeta := by
    apply Filter.mem_of_superset (compl_singleton_mem_codiscreteWithin (1 : ℂ))
    intro s hs
    exact (riemannZeta_eq_inv_sub_add hs).symm
  exact (hInv.add h0.meromorphicOn).congr_codiscreteWithin heq isOpen_univ
