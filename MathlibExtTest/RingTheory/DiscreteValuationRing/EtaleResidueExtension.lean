/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.EtaleResidueExtension

@[expose] public section

universe u

-- exactSource consumer: the original binders apply verbatim.
private theorem exactSource
    (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (k : Type u) [Field k] [Algebra (IsLocalRing.ResidueField W) k]
    [FiniteDimensional (IsLocalRing.ResidueField W) k]
    [Algebra.IsSeparable (IsLocalRing.ResidueField W) k] :
    ∃ (W' : Type u) (_ : CommRing W') (_ : IsDomain W')
      (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W') W') (_ : Algebra W W')
      (_ : Module.Finite W W') (_ : Module.Free W W') (_ : Module.Flat W W')
      (_ : FaithfulSMul W W') (_ : Algebra.Etale W W')
      (ι : IsLocalRing.ResidueField W' ≃+* k),
      Ideal.map (algebraMap W W') (IsLocalRing.maximalIdeal W) =
        IsLocalRing.maximalIdeal W' ∧
      (∀ w : W, ι (IsLocalRing.residue W' (algebraMap W W' w)) =
        algebraMap (IsLocalRing.ResidueField W) k (IsLocalRing.residue W w)) ∧
      Module.finrank W W' = Module.finrank (IsLocalRing.ResidueField W) k ∧
      Finite (W' ≃ₐ[W] W') ∧
      (IsGalois (IsLocalRing.ResidueField W) k →
        Nat.card (W' ≃ₐ[W] W') = Module.finrank W W' ∧
        ∀ w' : W', (∀ γ : W' ≃ₐ[W] W', γ • w' = w') ↔
          w' ∈ Set.range (algebraMap W W')) :=
by
  obtain ⟨W', _, _, _, _, _, _, _, _, _, _, _, ι, hmap, hrank, hfin, hgal⟩ :=
    IsDiscreteValuationRing.exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete
      W k
  exact ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ι.toRingEquiv, hmap, fun w => by
      have h := AlgEquiv.commutes ι (IsLocalRing.residue W w)
      rwa [IsLocalRing.ResidueField.algebraMap_residue] at h, hrank, hfin, hgal⟩

-- The rank conclusion extracted from the package: the realizing
-- extension has rank equal to the residue-field extension degree.
example
    (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (k : Type u) [Field k] [Algebra (IsLocalRing.ResidueField W) k]
    [FiniteDimensional (IsLocalRing.ResidueField W) k]
    [Algebra.IsSeparable (IsLocalRing.ResidueField W) k] :
    ∃ (W' : Type u) (_ : CommRing W') (_ : Algebra W W'),
      Module.finrank W W' = Module.finrank (IsLocalRing.ResidueField W) k := by
  obtain ⟨W', _, _, _, _, _, _, _, _, _, _, _, h⟩ := exactSource W k
  exact ⟨W', inferInstance, inferInstance, h.2.2.1⟩
