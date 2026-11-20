/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
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
