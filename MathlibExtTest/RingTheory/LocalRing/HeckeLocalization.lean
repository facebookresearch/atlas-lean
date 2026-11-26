/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.HeckeLocalization

@[expose] public section

-- Consumer with the original binders (`Type`, not `Type*`).
example {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : HeckeData 𝒪 V k) :
    Module.Finite 𝒪 D.ML ∧ (Module.Free 𝒪 V → Module.Free 𝒪 D.ML) :=
  HeckeData.finite_and_free_localizedModule hk D

-- Higher-universe consumer.
example {𝒪 : Type 1} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type 2} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type 3} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : HeckeData 𝒪 V k) :
    Module.Finite 𝒪 D.ML ∧ (Module.Free 𝒪 V → Module.Free 𝒪 D.ML) :=
  HeckeData.finite_and_free_localizedModule hk D

-- Consumer of the form that only asks for `mTheta` to be maximal.
example {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k) [D.mTheta.IsMaximal] :
    Module.Finite 𝒪 D.ML ∧ (Module.Free 𝒪 V → Module.Free 𝒪 D.ML) :=
  HeckeData.finite_and_free_localizedModule_of_isMaximal D

-- Consumer of the idempotent splitting of a finite algebra.
example {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B] :
    Nonempty (IdempotentSplitting B) :=
  nonempty_idempotentSplitting_of_finite 𝒪 B

namespace HeckeLocalizationTest

attribute [local instance] HeckeData.moduleFreeAlg

/-- One generator acting on the field `K` by the zero operator, with prescribed
eigenvalue `c`. -/
private def zeroOp (K : Type) [Field K] (c : K) : HeckeData K K K where
  Gen := Unit
  op _ := 0
  comm _ _ := rfl
  θbar _ := c

/-- With eigenvalue `0`, the free algebra acts on `K` through the eigenvalue
character. -/
private theorem zeroOp_zero_smul (K : Type) [Field K] (s : (zeroOp K 0).FreeAlg) (v : K) :
    s • v = (zeroOp K 0).thetaTilde s * v := by
  have h : (zeroOp K 0).opAlgHom =
      (Algebra.ofId K (Module.End K K)).comp (zeroOp K 0).thetaTilde :=
    MvPolynomial.algHom_ext fun g => by
      rw [HeckeData.opAlgHom_X, AlgHom.comp_apply]
      change (zeroOp K 0).op g =
        Algebra.ofId K _ (MvPolynomial.aeval (zeroOp K 0).θbar (MvPolynomial.X g))
      rw [MvPolynomial.aeval_X]
      exact (map_zero _).symm
  change (zeroOp K 0).opAlgHom s v = _
  rw [h, AlgHom.comp_apply, Algebra.ofId_apply, Module.algebraMap_end_apply, smul_eq_mul]

-- Eigenvalue `0`: `mTheta` is the kernel of the action, and the class of `1` survives.
example (K : Type) [Field K] : (zeroOp K 0).toML 1 ≠ 0 := by
  intro h
  have hker : (1 : K) ∈
      LinearMap.ker (LocalizedModule.mkLinearMap (zeroOp K 0).mTheta.primeCompl K) := h
  obtain ⟨s, hs, hs0⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp hker
  rw [zeroOp_zero_smul, mul_one] at hs0
  exact Ideal.mem_primeCompl_iff.mp hs (RingHom.mem_ker.mpr hs0)

-- Eigenvalue `1`: the generator lies outside `mTheta` but acts by `0`, so the localized
-- module vanishes.
example (K : Type) [Field K] : Subsingleton (zeroOp K 1).ML := by
  obtain ⟨g⟩ : Nonempty (zeroOp K 1).Gen := ⟨()⟩
  refine LocalizedModule.subsingleton_iff.mpr fun v => ⟨MvPolynomial.X g, ?_, ?_⟩
  · rw [Ideal.mem_primeCompl_iff]
    intro hX
    have h1 : (zeroOp K 1).thetaTilde (MvPolynomial.X g) = 0 := RingHom.mem_ker.mp hX
    change MvPolynomial.aeval (zeroOp K 1).θbar (MvPolynomial.X g) = 0 at h1
    rw [MvPolynomial.aeval_X] at h1
    exact one_ne_zero (h1 : (1 : K) = 0)
  · change (zeroOp K 1).opAlgHom (MvPolynomial.X g) v = 0
    rw [HeckeData.opAlgHom_X]
    rfl

end HeckeLocalizationTest
