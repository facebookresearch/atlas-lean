/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_
moduleFinite_of_henselianLocalRing.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RingTheory.Henselian.EtaleResidueFieldLifting

@[expose] public section

open scoped TensorProduct

universe u v w

-- `exactSource` consumer with the original binders and universes.
example (R : Type u) [CommRing R] [HenselianLocalRing R]
    (O : Type v) [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
    (C : Type w) [CommRing C] [Algebra R C] [Module.Finite R C]
    (ψbar : IsLocalRing.ResidueField R ⊗[R] O →ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField R ⊗[R] C) :
    ∃! ψ : O →ₐ[R] C,
      Algebra.TensorProduct.map
        (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) ψ = ψbar :=
  Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
    R O C ψbar

-- Higher-universe consumer: the source and target live in larger universes
-- than the Henselian base.
example (R : Type) [CommRing R] [HenselianLocalRing R]
    (O : Type 1) [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
    (C : Type 2) [CommRing C] [Algebra R C] [Module.Finite R C]
    (ψbar : IsLocalRing.ResidueField R ⊗[R] O →ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField R ⊗[R] C) :
    ∃! ψ : O →ₐ[R] C,
      Algebra.TensorProduct.map
        (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) ψ = ψbar :=
  Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
    R O C ψbar

-- Boundary use: the target need not be local. For `C = R × R`, which is
-- finite over `R` but not local when `R` is nontrivial, the residue-field
-- map still lifts uniquely.
example (R : Type) [CommRing R] [HenselianLocalRing R] [Nontrivial R] :
    ∃! ψ : R →ₐ[R] R × R,
      Algebra.TensorProduct.map
          (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) ψ =
        Algebra.TensorProduct.map
          (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R))
          (Algebra.ofId R (R × R)) :=
  Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
    R R (R × R)
    (Algebra.TensorProduct.map
      (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R))
      (Algebra.ofId R (R × R)))
