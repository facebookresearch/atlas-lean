/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.GammaH

@[expose] public section

open scoped MatrixGroups

/-- Source-shaped consumer: the original binders, in the original form. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) k,
      (⇑g : UpperHalfPlane → ℂ) = ⇑f :=
  CuspForm.exists_gamma1_coe_eq_of_gammaH M H k f

/-- Boundary: for `H = ⊤`, `GammaH M ⊤` is contained in `Gamma0 M`, so the
intermediate subgroup is a genuine level structure. -/
example (M : ℕ) (A : SL(2, ℤ)) (hA : A ∈ CongruenceSubgroup.GammaH M ⊤) :
    A ∈ CongruenceSubgroup.Gamma0 M :=
  CongruenceSubgroup.GammaH_le_Gamma0 M ⊤ hA

/-- The lower inclusion defining `GammaH` as an intermediate subgroup. -/
example (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.GammaH M H :=
  CongruenceSubgroup.gamma1_le_gammaH M H

/-- Downstream consumers can synthesize finite index for `GammaH`. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CongruenceSubgroup.GammaH M H).FiniteIndex :=
  inferInstance

/-- The zero cusp form restricts to the zero cusp form. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) k,
      (⇑g : UpperHalfPlane → ℂ) = ⇑(0 : CuspForm (CongruenceSubgroup.GammaH M H) k) :=
  CuspForm.exists_gamma1_coe_eq_of_gammaH M H k 0
