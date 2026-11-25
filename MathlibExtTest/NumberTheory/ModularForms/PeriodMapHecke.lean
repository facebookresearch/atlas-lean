/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.PeriodMapHecke

@[expose] public section

/-- The weight-two period map intertwines the analytic Hecke operator `T_ℓ`
with the cohomological Hecke operator, for a prime `ℓ` not dividing the
level. This is the statement of `ModularCurve.periodMap_heckeTLin` with its
source form preserved. -/
private theorem exactSource {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMap N (CuspForm.heckeTLin 2 hℓ hℓN f)
      = HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f) :=
  ModularCurve.periodMap_heckeTLin hℓ hℓN f

/-- The same intertwining identity stated as a plain equation, with the
`NeZero ℓ` instance supplied by the caller. -/
example {N : ℕ} {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ModularCurve.periodMap N (CuspForm.heckeTLin 2 hℓ hℓN f)
      = HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f) :=
  ModularCurve.periodMap_heckeTLin hℓ hℓN f
