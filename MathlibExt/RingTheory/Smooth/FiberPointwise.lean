/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_isSmoothAt_of_isSmoothAt_fiber.lean`
and
`P2M/Sol/S_Algebra_isSmoothAt_of_isSmoothAt_fiber.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.RingTheory.Localization.LocalizationLocalization

@[expose] public section

open TensorProduct

universe u

private theorem includeRight_surjective_of_residueField (Rp Sq : Type u)
    [CommRing Rp] [IsLocalRing Rp] [CommRing Sq] [Algebra Rp Sq] :
    Function.Surjective (Algebra.TensorProduct.includeRight :
      Sq →ₐ[Rp] IsLocalRing.ResidueField Rp ⊗[Rp] Sq) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c t =>
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨a • t, ?_⟩
    rw [map_smul, Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy =>
    obtain ⟨s, rfl⟩ := hx; obtain ⟨t, rfl⟩ := hy
    exact ⟨s + t, map_add _ _ _⟩

namespace Algebra

/-- Smoothness at one prime of the fiber implies smoothness upstairs.

Let `S` be a flat, finitely presented `R`-algebra, `q` a prime of `S`
lying over `p`, and `Q` a prime of the fiber `p.Fiber S` whose contraction
along `S → p.Fiber S` is `q`. If the fiber is smooth at `Q` alone, then
`S` is smooth at `q`. -/
public theorem isSmoothAt_of_isSmoothAt_fiber
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [Algebra.FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight :
      S →ₐ[R] p.Fiber S).toRingHom = q)
    [Algebra.IsSmoothAt p.ResidueField Q] :
    Algebra.IsSmoothAt R q := by
  classical
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  letI instRpSq : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have hle : Algebra.algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩ h
    apply hx
    have : x ∈ q.under R := Ideal.mem_comap.mpr h
    rwa [← Ideal.over_def q p] at this
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom
    (M := Algebra.algebraMapSubmonoid S p.primeCompl)
    (f := Algebra.ofId S Sq) (fun y => IsLocalization.map_units Sq ⟨y.1, hle y.2⟩)
  letI instSpSq : Algebra Sp Sq := f.toRingHom.toAlgebra
  haveI : IsScalarTower S Sp Sq := IsScalarTower.of_algebraMap_eq
    fun s => (f.commutes s).symm
  haveI : IsScalarTower R Sp Sq := IsScalarTower.to₁₃₄ R S Sp Sq
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    IsLocalization.isLocalization_of_submonoid_le Sp Sq
      (Algebra.algebraMapSubmonoid S p.primeCompl) q.primeCompl hle
  haveI : Algebra.IsPushout R Rp S Sp :=
    (Algebra.isPushout_of_isLocalization p.primeCompl Rp S Sp).symm
  haveI : Algebra.FinitePresentation Rp Sp :=
    Algebra.FinitePresentation.equiv (Algebra.IsPushout.equiv R Rp S Sp)
  letI instSF : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let T : Type u := (p.Fiber S) ⊗[S] Sq
  let M : Submonoid (p.Fiber S) := Algebra.algebraMapSubmonoid (p.Fiber S) q.primeCompl
  haveI : IsLocalization M T := IsLocalization.tensor Sq q.primeCompl
  have halg : ∀ s : S, algebraMap S (p.Fiber S) s =
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) s :=
    fun _ => rfl
  have hMQ : Disjoint (M : Set (p.Fiber S)) (Q : Set (p.Fiber S)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsQ
    apply hs
    rw [← hQ]
    exact hsQ
  haveI hQT : (Q.map (algebraMap (p.Fiber S) T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M T Q ‹_› hMQ
  haveI : Nontrivial T := nontrivial_of_ne 0 1 fun h =>
    hQT.ne_top ((Ideal.eq_top_iff_one _).mpr (by rw [← h]; exact Ideal.zero_mem _))
  let κ := p.ResidueField
  let e : κ ⊗[R] S ≃ₐ[S] S ⊗[R] κ :=
    { Algebra.TensorProduct.comm R κ S with commutes' := fun _ => rfl }
  let e₁ : T ≃ₐ[S] Sq ⊗[S] (κ ⊗[R] S) := Algebra.TensorProduct.comm S (κ ⊗[R] S) Sq
  let e₂ : Sq ⊗[S] (κ ⊗[R] S) ≃ₐ[S] Sq ⊗[S] (S ⊗[R] κ) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : Sq ≃ₐ[S] Sq) e
  let e₃ : Sq ⊗[S] (S ⊗[R] κ) ≃ₐ[S] Sq ⊗[R] κ :=
    Algebra.TensorProduct.cancelBaseChange R S S Sq κ
  let e₄ : Sq ⊗[R] κ ≃ₐ[R] κ ⊗[R] Sq := Algebra.TensorProduct.comm R Sq κ
  let e₅ : κ ⊗[R] Sq ≃ₐ[R] κ ⊗[Rp] Sq :=
    Algebra.TensorProduct.equivOfCompatibleSMul Rp R R κ Sq
  let e' : T ≃ₐ[R] κ ⊗[Rp] Sq :=
    (((e₁.trans e₂).trans e₃).restrictScalars R).trans (e₄.trans e₅)
  haveI : IsLocalRing T := by
    refine IsLocalRing.of_surjective' (e'.symm.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := Rp) (A := κ) (B := Sq)).toRingHom) ?_
    exact e'.symm.surjective.comp (includeRight_surjective_of_residueField Rp Sq)
  let P : Ideal (p.Fiber S) := (IsLocalRing.maximalIdeal T).comap (algebraMap (p.Fiber S) T)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hQP : Q ≤ P := le_trans Ideal.le_comap_map
    (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQT.ne_top))
  have hMP : Disjoint (M : Set (p.Fiber S)) (P : Set (p.Fiber S)) := by
    rw [Set.disjoint_left]
    intro y hy hyP
    exact (IsLocalRing.mem_maximalIdeal _).mp hyP (IsLocalization.map_units T ⟨y, hy⟩)
  have hPq : P.comap (Algebra.TensorProduct.includeRight :
      S →ₐ[R] p.Fiber S).toRingHom = q := by
    apply le_antisymm
    · intro s hs
      by_contra hsq
      exact Set.disjoint_left.mp hMP ⟨s, hsq, rfl⟩ hs
    · rw [← hQ]
      exact Ideal.comap_mono hQP
  have hPQ : P = Q := by
    have h := (PrimeSpectrum.preimageEquivFiber R S ⟨p, ‹_›⟩).symm.injective
      (a₁ := ⟨P, hP⟩) (a₂ := ⟨Q, ‹_›⟩)
      (Subtype.ext (PrimeSpectrum.ext (hPq.trans hQ.symm)))
    exact congrArg PrimeSpectrum.asIdeal h
  haveI : IsLocalization.AtPrime T Q := by
    refine IsLocalization.of_le M Q.primeCompl
      (fun y hy hyQ => Set.disjoint_left.mp hMQ hy hyQ) ?_
    intro y hy
    by_contra h
    apply hy
    rw [← hPQ]
    exact (IsLocalRing.mem_maximalIdeal _).mpr h
  haveI : IsScalarTower κ (p.Fiber S) T := inferInstance
  let eQ : Localization.AtPrime Q ≃ₐ[p.Fiber S] T :=
    IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) T
  have hsm : Algebra.FormallySmooth κ (Localization.AtPrime Q) := ‹Algebra.IsSmoothAt κ Q›
  haveI : Algebra.FormallySmooth κ T :=
    @Algebra.FormallySmooth.of_equiv κ _ (Localization.AtPrime Q) T _ _ _ _ hsm
      (eQ.restrictScalars κ)
  have hcomm : ((e' : T →ₐ[R] κ ⊗[Rp] Sq).comp
        (IsScalarTower.toAlgHom R κ T)).comp (IsScalarTower.toAlgHom R R κ) =
      ((IsScalarTower.toAlgHom R κ (κ ⊗[Rp] Sq))).comp
        (IsScalarTower.toAlgHom R R κ) := by
    ext
  have hcomm' : (e' : T →ₐ[R] κ ⊗[Rp] Sq).comp (IsScalarTower.toAlgHom R κ T) =
      IsScalarTower.toAlgHom R κ (κ ⊗[Rp] Sq) :=
    Ideal.ResidueField.algHom_ext hcomm
  let e'' : T ≃ₐ[κ] κ ⊗[Rp] Sq :=
    AlgEquiv.ofRingEquiv (f := e'.toRingEquiv) (fun c => congrArg (fun g => g c) hcomm')
  haveI : Algebra.FormallySmooth (IsLocalRing.ResidueField Rp)
      (IsLocalRing.ResidueField Rp ⊗[Rp] Sq) :=
    @Algebra.FormallySmooth.of_equiv κ _ T (κ ⊗[Rp] Sq) _ _ _ _
      ‹Algebra.FormallySmooth κ T› e''
  haveI : IsScalarTower Rp Sp Sq := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.ringHom_ext p.primeCompl (by
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R Rp Sp,
        ← IsScalarTower.algebraMap_eq R Sp Sq,
        ← IsScalarTower.algebraMap_eq R Rp Sq]))
  haveI : Algebra.FormallySmooth Rp Sq :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
      (Algebra.algebraMapSubmonoid Sp q.primeCompl)
  exact Algebra.FormallySmooth.comp R Rp Sq

end Algebra
