/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.CompletedFunction
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for the completed function of a Selberg functional equation
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

/-- `FunctionalEquation.congr`: changing `ζ` at `s = 1` keeps the functional equation. -/
noncomputable def zetaFE' : FunctionalEquation (Function.update riemannZeta 1 0) :=
  zetaFE.congr fun _ hs => Function.update_of_ne hs _ _

example : zetaFE'.degree = 1 := by rw [zetaFE', FunctionalEquation.degree_congr, zetaFE_degree]

/-- The completed zeta function, from the entire function `G = (s - 1)^m ζ(s)` of the
definition of `𝒮`. -/
example : ∃ (m : ℕ) (G H : ℂ → ℂ), Differentiable ℂ H ∧
    (∀ s, H (1 - starRingEnd ℂ s) = zetaFE.w * starRingEnd ℂ (H s)) ∧
    (∀ s : ℂ, 0 < s.re → H s = s ^ m * (zetaFE.Q : ℂ) ^ s *
      (∏ i, Gamma (zetaFE.α i * s + zetaFE.r i)) * G s) := by
  obtain ⟨-, ⟨F, hF, ⟨m, G, -, hGd, -, hGF⟩, -⟩, -⟩ := zeta_mem_selbergClass
  have hGF' : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * riemannZeta s := fun s hs => by
    rw [hGF s hs, hF.eqOn_compl_one isLSeriesContinuation_zeta s hs]
  exact ⟨m, G, exists_completed riemannZeta G m hGd hGF' zetaFE⟩

end SelbergClassTest
