/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_DoubleCoset_natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.GroupTheory.DoubleCosetFibre

@[expose] public section

private theorem exactSource
    {G : Type*} [Group G] {Γ U : Subgroup G} (V : Subgroup G) (hΓU : Γ ≤ U) (β : G) :
    Nat.card {q : DoubleCoset.Quotient (Γ : Set G) (V : Set G) //
        ∃ g : G, DoubleCoset.mk Γ V g = q ∧ DoubleCoset.mk U V g = DoubleCoset.mk U V β}
      = Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf U : Subgroup U) : Set U)
          (((U ⊓ V.map (MulAut.conj β).toMonoidHom).subgroupOf U : Subgroup U) : Set U)) :=
  DoubleCoset.natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj V hΓU β

-- Higher-universe consumer: the group lives in `Type 1`.
example {G : Type 1} [Group G] {Γ U : Subgroup G} (V : Subgroup G) (hΓU : Γ ≤ U)
    (β : G) :
    Nat.card {q : DoubleCoset.Quotient (Γ : Set G) (V : Set G) //
        ∃ g : G, DoubleCoset.mk Γ V g = q ∧ DoubleCoset.mk U V g = DoubleCoset.mk U V β}
      = Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf U : Subgroup U) : Set U)
          (((U ⊓ V.map (MulAut.conj β).toMonoidHom).subgroupOf U : Subgroup U) : Set U)) :=
  DoubleCoset.natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj V hΓU β

-- When `Γ = U`, both sides count the same quotient of `U`: the statement
-- specializes to the quotient by `Γ` in `U` and by `U ∩ β V β⁻¹` in `U`.
example {G : Type*} [Group G] {Γ : Subgroup G} (V : Subgroup G) (β : G) :
    Nat.card {q : DoubleCoset.Quotient (Γ : Set G) (V : Set G) //
        ∃ g : G, DoubleCoset.mk Γ V g = q ∧ DoubleCoset.mk Γ V g = DoubleCoset.mk Γ V β}
      = Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf Γ : Subgroup Γ) : Set Γ)
          (((Γ ⊓ V.map (MulAut.conj β).toMonoidHom).subgroupOf Γ : Subgroup Γ) : Set Γ)) :=
  DoubleCoset.natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj V (le_refl Γ) β
