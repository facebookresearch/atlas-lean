/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.DVRPoints

universe u

/-- Smoke test: the DVR-points theorem applies with `P = 𝒪`. -/
example {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪] : True := by
  have _h := IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot (𝒪 := 𝒪) (P := 𝒪)
  trivial

/-- The construction keeps a genuinely higher-universe algebra and all its DVR targets there. -/
example {𝒪 : Type u} {P : Type (u + 1)} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪]
    [CommRing P] [IsLocalRing P] [IsReduced P] [Algebra 𝒪 P] [Module.Finite 𝒪 P]
    [Module.IsTorsionFree 𝒪 P] :
    ∃ (n : ℕ) (A : Fin n → Type (u + 1)) (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, IsDomain (A i)) (_ : ∀ i, IsDiscreteValuationRing (A i))
      (_ : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (A i))) (_ : ∀ i, CharZero (A i))
      (_ : ∀ i, Algebra 𝒪 (A i)) (_ : ∀ i, Module.Finite 𝒪 (A i))
      (_ : ∀ i, IsLocalHom (algebraMap 𝒪 (A i)))
      (χ : ∀ i, P →ₐ[𝒪] A i),
      (∀ i, IsLocalHom (χ i).toRingHom) ∧ ⨅ i, RingHom.ker (χ i).toRingHom = ⊥ ∧
        ∃ a : 𝒪, a ≠ 0 ∧ ∀ y : ∀ i, A i, ∃ x : P, ∀ i, χ i x = a • y i := by
  exact IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot (𝒪 := 𝒪) (P := P)
