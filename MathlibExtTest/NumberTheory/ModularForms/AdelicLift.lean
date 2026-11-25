/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.AdelicLift

@[expose] public section

open NumberField

/-- Consumer with the original binders for the adelic-lift relation. -/
private theorem exactSource {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (h : CuspForm.IsAdelicLiftOf g φ) : CuspForm.IsAdelicLiftOf g φ :=
  h

/-- The zero function is not asserted to be a lift; the three characterizing
projections of a lift are available individually. -/
example {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (h : CuspForm.IsAdelicLiftOf g φ)
    (γ : GL (Fin 2) ℚ) (x : NumberField.AdelicGL2 (𝓞 ℚ) ℚ) :
    φ (NumberField.globalPoints (𝓞 ℚ) ℚ γ * x) = φ x :=
  h.left_inv γ x

/-- Boundary case: the level at `N = 1` is the whole integer ideal, so the
rational level is nontrivial exactly for nonzero level. -/
example : AdelicDock.ratLevel 1 = ⊤ :=
  AdelicDock.ratLevel_one

example {N : ℕ} (hN : N ≠ 0) : AdelicDock.ratLevel N ≠ ⊥ :=
  AdelicDock.ratLevel_ne_bot hN

/-- The finite embedding recovers its input under the finite projection,
so the level-invariance condition cannot be stated with the archimedean
projection instead. -/
example (u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ
      (NumberField.AdelicLevel.finEmbed (𝓞 ℚ) ℚ u) = u :=
  NumberField.AdelicLevel.glFin_finEmbed _ _ _
