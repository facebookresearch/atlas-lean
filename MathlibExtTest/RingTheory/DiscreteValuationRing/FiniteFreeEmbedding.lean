/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.FiniteFreeEmbedding

@[expose] public section

-- Exact-source consumer, with the original binders.
private theorem exactSource
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (T : Type) [CommRing T] [IsReduced T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    [Module.Free 𝒪 T] :
    ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι :=
  IsDiscreteValuationRing.exists_algHom_pi_of_module_finite_free T

-- Higher-universe consumer: the same statement one universe up.
private theorem exactSourceUniverse
    {𝒪 : Type 1} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (T : Type 1) [CommRing T] [IsReduced T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    [Module.Free 𝒪 T] :
    ∃ (n : ℕ) (R : Fin n → Type 1) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι :=
  IsDiscreteValuationRing.exists_algHom_pi_of_module_finite_free T

-- Boundary: for a nontrivial algebra the product is nonempty, since an
-- injective map into an empty product would identify `0` and `1`.
example
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (T : Type) [CommRing T] [IsReduced T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    [Module.Free 𝒪 T] [Nontrivial T] : True := by
  obtain ⟨n, R, _, _, _, _, _, _, _, _, ι, hι⟩ :=
    IsDiscreteValuationRing.exists_algHom_pi_of_module_finite_free (𝒪 := 𝒪) T
  have hn : n ≠ 0 := by
    rintro rfl
    have h10 : ι 1 = ι 0 := funext fun j => j.elim0
    exact one_ne_zero (hι h10)
  trivial
