/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Unramified.Basic

import Mathlib.RingTheory.Filtration

/-!
# DVR residue-field functoriality: source-map stage for ATLAS N211

This file is a prerequisite stage for ATLAS NumberTheoryI item N211,
Theorem 10.13 (Section 10.2), at atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`. See the immutable
[N211 / Theorem 10.13 target, lines 1465-1483](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1465-L1483):
equivalence between finite unramified extensions
of the fraction field of a complete DVR and finite separable extensions of its
residue field; on morphisms a field map is sent to reduction of a lifted
element, with the induced Hom-set bijection and isomorphism-class
correspondence.

This file works at the finite local DVR-ring level, one step below the fraction
fields and residue fields of the theorem. Source implementation:
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean).

Source map from ATLAS N211 / Theorem 10.13 to this module's API:

* `DVRResidue.AlgHom.isLocalHom_of_isDiscreteValuationRing` supplies locality for
  an algebra homomorphism under this file's DVR, finite-module, and
  local-algebra hypotheses.
* `DVRResidue.residueFieldMapAlgHom` is the induced residue-field algebra map
  corresponding to the morphism part of Theorem 10.13; cf.
  [`residueFieldFunctorAlg`, lines 1001-1011](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1001-L1011),
  where a homomorphism of finite
  local DVR extensions induces the residue-field algebra homomorphism by
  reducing a lift.
* `DVRResidue.residueFieldMapAlgHom_residue` states reduction of a lift.
* `DVRResidue.residueFieldMapAlgHom_id` and
  `DVRResidue.residueFieldMapAlgHom_comp` give the identity and composition laws
  needed for functoriality.
* Stage B, `DVRResidue.residueFieldMapAlgHom_injective`, formalizes only the
  faithfulness/injectivity direction of the Hom-set bijection in Theorem 10.13;
  cf. the
  [injectivity half of `residueFieldFunctor_full_faithfulness`, lines
  1013-1165](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1013-L1165).
  This theorem does not require `Module.Finite A B`, so it genuinely
  generalizes the source's finite extension `B`. The target `C` remains finite
  over `A`, as required by the locality construction. The hypothesis
  `Algebra.FormallyUnramified A B` specializes the source's unramifiedness
  assumption, while Krull intersection in the target DVR converts equality
  after residue reduction into equality of algebra homomorphisms.

This stage proves the faithfulness part but not the full N211 target:
fullness/surjectivity on Hom sets, essential surjectivity, compatible lifting
of residue-field equivalences, and the category-equivalence/isomorphism-class
conclusion remain later stages, corresponding to the remainder of
`residueFieldFunctor_full_faithfulness` and to
[`residueFieldFunctor_isEquivalence`, lines 1320-1338](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1320-L1338).
-/

@[expose] public section

variable {A B C D : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D]
variable [Module.Finite A B] [Module.Finite A C] [Module.Finite A D]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [IsLocalHom (algebraMap A D)]

namespace DVRResidue

namespace AlgHom

omit [Module.Finite A B] [IsLocalHom (algebraMap A B)] in
/-- **Algebra maps from a DVR into a finite local DVR extension are local.** Let $A$, $B$, $C$
be discrete valuation rings, with $B$ and $C$ algebras over $A$, where $C$ is finite as an
$A$-module and the structure map $A \to C$ is a local homomorphism. Then every $A$-algebra
homomorphism $B \to C$ is a local homomorphism. -/
theorem isLocalHom_of_isDiscreteValuationRing (f : B →ₐ[A] C) :
    IsLocalHom f := by
  have hmaxC : (IsLocalRing.maximalIdeal C).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal C
  have hprimeC : (IsLocalRing.maximalIdeal C).IsPrime := hmaxC.isPrime
  have hPprime :
      (Ideal.comap (f : B →+* C) (IsLocalRing.maximalIdeal C)).IsPrime :=
    Ideal.comap_isPrime (f := (f : B →+* C))
      (K := IsLocalRing.maximalIdeal C)
  have hPne :
      Ideal.comap (f : B →+* C) (IsLocalRing.maximalIdeal C) ≠ ⊥ := by
    by_contra hbot
    have hker :
        IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A C) := by
      intro a ha
      rw [RingHom.mem_ker]
      have hC : algebraMap A C a ∈ IsLocalRing.maximalIdeal C :=
        map_nonunit (algebraMap A C) a ha
      have hcomm :
          (f : B →+* C) (algebraMap A B a) = algebraMap A C a :=
        f.commutes a
      have hmem :
          algebraMap A B a ∈
            Ideal.comap (f : B →+* C) (IsLocalRing.maximalIdeal C) := by
        rw [Ideal.mem_comap, hcomm]
        exact hC
      rw [hbot] at hmem
      have hzero : algebraMap A B a = 0 := Ideal.mem_bot.mp hmem
      rw [← hcomm, hzero, map_zero]
    let K := IsLocalRing.ResidueField A
    have hmem_zero :
        ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A C a = 0 := by
      intro a ha
      exact RingHom.mem_ker.mp (hker ha)
    let g : K →+* C :=
      Ideal.Quotient.lift _ (algebraMap A C) hmem_zero
    have hcomp : g.comp (IsLocalRing.residue A) = algebraMap A C := by
      ext x
      rfl
    let : Algebra K C := g.toAlgebra
    have : IsScalarTower A K C := by
      refine IsScalarTower.of_algebraMap_eq ?_
      intro a
      change g (algebraMap A K a) = algebraMap A C a
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      exact DFunLike.congr_fun hcomp a
    have : Module.Finite K C :=
      Module.Finite.of_restrictScalars_finite A K C
    have : Algebra.IsIntegral K C := inferInstance
    have hne_comap :
        Ideal.comap (algebraMap K C) (IsLocalRing.maximalIdeal C) ≠ ⊥ :=
      Ideal.IsIntegral.comap_ne_bot K (IsDiscreteValuationRing.not_a_field C)
    obtain ⟨k, hk_mem, hk_ne⟩ :=
      (Ideal.comap (algebraMap K C) (IsLocalRing.maximalIdeal C)).ne_bot_iff.mp
        hne_comap
    have hk_unit : IsUnit k := isUnit_iff_ne_zero.mpr hk_ne
    have htop :
        Ideal.comap (algebraMap K C) (IsLocalRing.maximalIdeal C) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ hk_mem hk_unit
    have h1mem : (1 : C) ∈ IsLocalRing.maximalIdeal C := by
      have h1 :
          (1 : K) ∈
            Ideal.comap (algebraMap K C) (IsLocalRing.maximalIdeal C) := by
        rw [htop]
        exact Submodule.mem_top
      rw [Ideal.mem_comap, map_one] at h1
      exact h1
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1mem)
  have hPmax :
      (Ideal.comap (f : B →+* C) (IsLocalRing.maximalIdeal C)).IsMaximal :=
    hPprime.isMaximal hPne
  have heq :
      Ideal.comap (f : B →+* C) (IsLocalRing.maximalIdeal C) =
        IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal hPmax
  refine ⟨fun b hb => ?_⟩
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hbmem
  have hmem_comap :
      b ∈ Ideal.comap (f : B →+* C) (IsLocalRing.maximalIdeal C) := by
    rw [heq]
    exact hbmem
  have hmemC : (f : B →+* C) b ∈ IsLocalRing.maximalIdeal C :=
    Ideal.mem_comap.mp hmem_comap
  have hbC : (f : B →+* C) b ∉ IsLocalRing.maximalIdeal C := by
    have hunit : IsUnit ((f : B →+* C) b) := by
      simpa using hb
    exact IsLocalRing.notMem_maximalIdeal.mpr hunit
  exact hbC hmemC

end AlgHom

/-- **Induced map on residue fields of DVR extensions.** Let $A$, $B$, $C$ be discrete valuation
rings, with $B$ and $C$ algebras over $A$ whose structure maps are local homomorphisms, where $C$
is finite as an $A$-module. Write $\kappa(R)$ for the residue field of a local ring $R$. An
$A$-algebra homomorphism $f \colon B \to C$ induces the $\kappa(A)$-algebra homomorphism
$\kappa(B) \to \kappa(C)$ that sends the residue class of $b \in B$ to the residue class of
$f(b)$. -/
noncomputable def residueFieldMapAlgHom (f : B →ₐ[A] C) :
    IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField C :=
  haveI := AlgHom.isLocalHom_of_isDiscreteValuationRing f
  IsLocalRing.ResidueField.mapAlgHom' f

omit [Module.Finite A B] in
@[simp]
theorem residueFieldMapAlgHom_residue (f : B →ₐ[A] C) (b : B) :
    residueFieldMapAlgHom f (IsLocalRing.residue B b) =
      IsLocalRing.residue C (f b) := by
  let := AlgHom.isLocalHom_of_isDiscreteValuationRing f
  simpa only [residueFieldMapAlgHom] using
    IsLocalRing.ResidueField.mapAlgHom'_residue f b

theorem residueFieldMapAlgHom_id :
    residueFieldMapAlgHom (AlgHom.id A B) = AlgHom.id _ _ := by
  ext x
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
  simp

omit [Module.Finite A B] in
theorem residueFieldMapAlgHom_comp (f : B →ₐ[A] C) (g : C →ₐ[A] D) :
    residueFieldMapAlgHom (g.comp f) =
      (residueFieldMapAlgHom g).comp (residueFieldMapAlgHom f) := by
  ext x
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
  simp

omit [Module.Finite A B] in
/-- **Residue-field maps determine algebra maps out of a formally unramified DVR extension.**
Let $A$, $B$, $C$ be discrete valuation rings, with $B$ and $C$ algebras over $A$ whose structure
maps are local homomorphisms, where $C$ is finite as an $A$-module and $B$ is formally unramified
over $A$. Write $\kappa(R)$ for the residue field of a local ring $R$. Then two $A$-algebra
homomorphisms $B \to C$ that induce the same $\kappa(A)$-algebra homomorphism
$\kappa(B) \to \kappa(C)$ are equal. -/
theorem residueFieldMapAlgHom_injective
    [Algebra.FormallyUnramified A B] :
    Function.Injective
      (residueFieldMapAlgHom (A := A) (B := B) (C := C)) := by
  intro f g hfg
  have hne : IsLocalRing.maximalIdeal C ≠ ⊤ :=
    (IsLocalRing.maximalIdeal.isMaximal C).ne_top
  have hKrull : ⨅ n, (IsLocalRing.maximalIdeal C) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal C) hne
  refine Algebra.FormallyUnramified.ext_of_iInf (IsLocalRing.maximalIdeal C)
    hKrull fun b => ?_
  have hres : IsLocalRing.residue C (f b) = IsLocalRing.residue C (g b) := by
    have h := DFunLike.congr_fun hfg (IsLocalRing.residue B b)
    simpa only [residueFieldMapAlgHom_residue] using h
  exact hres

end DVRResidue
