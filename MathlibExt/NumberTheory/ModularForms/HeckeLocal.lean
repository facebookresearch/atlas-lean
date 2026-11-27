/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CuspForm_HeckeLocal.lean`,
`Theorems/Thm_CuspForm_heckeLocal_residue_pi.lean`, and
`P2M/Sol/S_CuspForm_heckeLocal_residue_pi.lean`
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

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import MathlibExt.NumberTheory.ModularForms.HeckeAlgebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Submodule
import MathlibExt.RingTheory.AdicCompletion.ModuleFinite
import MathlibExt.RingTheory.LocalRing.FiniteAlgebraDecomposition

/-!
# The local Hecke algebra at a residual Hecke character

Let `θ` be a ring homomorphism from the Hecke algebra `CuspForm.heckeAlgebra N 2 S`
to the residue field of a complete discrete valuation ring `𝒪`. Restricting the
Hecke algebra to the integral lattice of weight-two cusp forms and extending
scalars to `𝒪` gives a finite free `𝒪`-algebra. `CuspForm.heckeLocal N S 𝒪 θ` is
its localization at the image of the complement of the kernel of the residual
character induced by `θ`, and it is finite and free over `𝒪`. When the kernel of
the base-changed restriction map lies in the kernel of the residual character, this
is the localization at the maximal ideal cut out by `θ`; otherwise it is the zero
ring. An integral structure gives that kernel containment, and then the local Hecke
algebra is a complete local ring.

## Main declarations

* `CuspForm.heckeLocal`: the localized Hecke algebra.
* `CuspForm.heckeLocal.π`: the canonical map from the Hecke algebra.
* `CuspForm.heckeLocal.residue_pi`: under an integral structure, `π` reduces to `θ`
  modulo the maximal ideal.
-/

@[expose] public section

noncomputable section

universe u

open scoped TensorProduct

namespace CuspForm

variable (N : ℕ) [NeZero N] (S : Set ℕ)

/-- An element of the Hecke algebra restricted to the integral lattice of weight-two cusp
forms, which it preserves. -/
def latticeRestrict {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)}
    (ht : t ∈ heckeAlgebra N 2 S) : Module.End ℤ ↥(intLattice N 2) :=
  LinearMap.restrict (t.restrictScalars ℤ)
    (fun _f hf => mem_intLattice_of_mem_heckeAlgebra one_le_two ht hf)

/-- The action of the Hecke algebra on the integral lattice. -/
def latticeActionHom : ↥(heckeAlgebra N 2 S) →+* Module.End ℤ ↥(intLattice N 2) where
  toFun t := latticeRestrict N S t.2
  map_one' := LinearMap.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl
  map_zero' := LinearMap.ext fun _ => Subtype.ext rfl
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext rfl

/-- The image of the Hecke algebra in the `ℤ`-linear endomorphisms of the integral
lattice. -/
def heckeLatticeAlgebra : Subalgebra ℤ (Module.End ℤ ↥(intLattice N 2)) :=
  ((latticeActionHom N S).toIntAlgHom).range

theorem intLattice.moduleFinite : Module.Finite ℤ ↥(intLattice N 2) :=
  Module.Finite.iff_fg.mpr (intLattice_fg N 2)

omit [NeZero N] in
private theorem hasUniqueDiv_cuspForm :
    HasUniqueDiv (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  .of_isTorsionFree ℂ _

omit [NeZero N] in
private theorem intLattice.isTorsionFree : Module.IsTorsionFree ℤ ↥(intLattice N 2) := by
  have := hasUniqueDiv_cuspForm N
  infer_instance

theorem intLattice.moduleFree : Module.Free ℤ ↥(intLattice N 2) := by
  have := intLattice.moduleFinite N
  have := intLattice.isTorsionFree N
  exact Module.free_of_finite_type_torsion_free'

instance heckeLatticeAlgebra.instModuleFinite : Module.Finite ℤ ↥(heckeLatticeAlgebra N S) := by
  have := intLattice.moduleFinite N
  have := intLattice.moduleFree N
  exact Module.Finite.of_injective (heckeLatticeAlgebra N S).val.toLinearMap Subtype.val_injective

instance heckeLatticeAlgebra.instModuleFree : Module.Free ℤ ↥(heckeLatticeAlgebra N S) := by
  have := intLattice.isTorsionFree N
  have : Module.IsTorsionFree ℤ ↥(heckeLatticeAlgebra N S) := Subalgebra.instIsTorsionFree _
  exact Module.free_of_finite_type_torsion_free'

/-- The Hecke algebra maps onto its image on the integral lattice. -/
def latticeRestrictHom : ↥(heckeAlgebra N 2 S) →ₐ[ℤ] ↥(heckeLatticeAlgebra N S) :=
  ((latticeActionHom N S).toIntAlgHom).rangeRestrict

instance heckeLatticeAlgebra.instCommRing : CommRing ↥(heckeLatticeAlgebra N S) :=
  { (inferInstance : Ring ↥(heckeLatticeAlgebra N S)) with
    mul_comm := by
      rintro ⟨_, s, rfl⟩ ⟨_, t, rfl⟩
      exact Subtype.ext ((map_mul _ s t).symm.trans
        ((congrArg _ (mul_comm s t)).trans (map_mul _ t s))) }

theorem latticeRestrict_injective (hint : HasIntegralStructure N 2)
    (t : ↥(heckeAlgebra N 2 S)) (h : latticeRestrict N S t.2 = 0) : t = 0 := by
  refine Subtype.ext (LinearMap.ext_on hint fun f hf => ?_)
  exact congrArg Subtype.val (LinearMap.congr_fun h ⟨f, hf⟩)

theorem latticeActionHom_injective (hint : HasIntegralStructure N 2) :
    Function.Injective (latticeActionHom N S) :=
  (injective_iff_map_eq_zero _).mpr fun t ht => latticeRestrict_injective N S hint t ht

theorem latticeRestrictHom_surjective : Function.Surjective (latticeRestrictHom N S) :=
  AlgHom.rangeRestrict_surjective _

theorem latticeRestrictHom_bijective (hint : HasIntegralStructure N 2) :
    Function.Bijective (latticeRestrictHom N S) :=
  ⟨fun _ _ h => latticeActionHom_injective N S hint (congrArg Subtype.val h),
    latticeRestrictHom_surjective N S⟩

variable (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
variable (θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)

/-- The `𝒪`-linear extension of `θ` to `𝒪 ⊗[ℤ] heckeAlgebra N 2 S`, with values in the
residue field of `𝒪`. -/
def residualCharacter :
    (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) →ₐ[ℤ] IsLocalRing.ResidueField 𝒪 :=
  Algebra.TensorProduct.productMap
    (algebraMap 𝒪 (IsLocalRing.ResidueField 𝒪)).toIntAlgHom θ.toIntAlgHom

/-- The kernel of the residual character: a maximal ideal. -/
def heckeCharKernel : Ideal (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) :=
  RingHom.ker (residualCharacter N S 𝒪 θ)

instance heckeCharKernel.instIsPrime : (heckeCharKernel N S 𝒪 θ).IsPrime :=
  RingHom.ker_isPrime _

/-- The lattice Hecke algebra with scalars extended to `𝒪`, a finite free `𝒪`-algebra. -/
def heckeBaseAlgebra : Type u := 𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)

instance heckeBaseAlgebra.instCommRing : CommRing (heckeBaseAlgebra N S 𝒪) :=
  inferInstanceAs (CommRing (𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)))

instance heckeBaseAlgebra.instAlgebra : Algebra 𝒪 (heckeBaseAlgebra N S 𝒪) :=
  inferInstanceAs (Algebra 𝒪 (𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)))

/-- The base change to `𝒪` of the map from the Hecke algebra to the lattice Hecke
algebra. -/
def latticeBaseChange : (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) →+* heckeBaseAlgebra N S 𝒪 :=
  (Algebra.TensorProduct.map (AlgHom.id ℤ 𝒪) (latticeRestrictHom N S)).toRingHom

/-- The image in `heckeBaseAlgebra N S 𝒪` of the complement of the kernel of the residual
character. -/
def heckeLocalSubmonoid : Submonoid (heckeBaseAlgebra N S 𝒪) :=
  (heckeCharKernel N S 𝒪 θ).primeCompl.map (latticeBaseChange N S 𝒪)

/-- The local Hecke algebra: the localization of `heckeBaseAlgebra N S 𝒪` at
`heckeLocalSubmonoid N S 𝒪 θ`, the image of the complement of the kernel of the residual
character. When the kernel of `latticeBaseChange N S 𝒪` lies in the kernel of the residual
character, as it does under an integral structure (`HasIntegralStructure N 2`), this is the
localization at the maximal ideal `heckeLocalIdeal N S 𝒪 θ` cut out by `θ`; otherwise the
submonoid contains `0` and the localization is the zero ring. -/
def heckeLocal : Type u :=
  Localization (heckeLocalSubmonoid N S 𝒪 θ)

instance heckeLocal.instCommRing : CommRing (heckeLocal N S 𝒪 θ) :=
  inferInstanceAs (CommRing (Localization (heckeLocalSubmonoid N S 𝒪 θ)))

instance heckeLocal.instAlgebra : Algebra 𝒪 (heckeLocal N S 𝒪 θ) :=
  inferInstanceAs (Algebra 𝒪 (Localization (heckeLocalSubmonoid N S 𝒪 θ)))

instance heckeLocal.instAlgebraBase : Algebra (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ) :=
  inferInstanceAs (Algebra (heckeBaseAlgebra N S 𝒪) (Localization (heckeLocalSubmonoid N S 𝒪 θ)))

instance heckeLocal.instIsScalarTower :
    IsScalarTower 𝒪 (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ) :=
  inferInstanceAs
    (IsScalarTower 𝒪 (heckeBaseAlgebra N S 𝒪) (Localization (heckeLocalSubmonoid N S 𝒪 θ)))

instance heckeLocal.instIsLocalization :
    IsLocalization (heckeLocalSubmonoid N S 𝒪 θ) (heckeLocal N S 𝒪 θ) :=
  inferInstanceAs
    (IsLocalization (heckeLocalSubmonoid N S 𝒪 θ) (Localization (heckeLocalSubmonoid N S 𝒪 θ)))

/-- The canonical ring homomorphism from the Hecke algebra to the local Hecke algebra. -/
def heckeLocal.π : ↥(heckeAlgebra N 2 S) →+* heckeLocal N S 𝒪 θ :=
  ((algebraMap (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ)).comp (latticeBaseChange N S 𝒪)).comp
    Algebra.TensorProduct.includeRight.toRingHom

section Structure


omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]

theorem residualCharacter_tmul (a : 𝒪) (t : ↥(heckeAlgebra N 2 S)) :
    residualCharacter N S 𝒪 θ (a ⊗ₜ t) = IsLocalRing.residue 𝒪 a * θ t := rfl

theorem residualCharacter_algebraMap (a : 𝒪) :
    residualCharacter N S 𝒪 θ (algebraMap 𝒪 _ a) = IsLocalRing.residue 𝒪 a := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    residualCharacter_tmul, map_one, mul_one]

theorem residualCharacter_surjective : Function.Surjective (residualCharacter N S 𝒪 θ) :=
  fun x => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨algebraMap 𝒪 _ a, residualCharacter_algebraMap N S 𝒪 θ a⟩

instance heckeCharKernel.instIsMaximal : (heckeCharKernel N S 𝒪 θ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (residualCharacter_surjective N S 𝒪 θ)

theorem mem_heckeCharKernel_iff (x : 𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) :
    x ∈ heckeCharKernel N S 𝒪 θ ↔ residualCharacter N S 𝒪 θ x = 0 := RingHom.mem_ker

theorem algebraMap_mem_heckeCharKernel_iff (a : 𝒪) :
    algebraMap 𝒪 (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) a ∈ heckeCharKernel N S 𝒪 θ ↔
      a ∈ IsLocalRing.maximalIdeal 𝒪 := by
  rw [mem_heckeCharKernel_iff, residualCharacter_algebraMap, IsLocalRing.residue_eq_zero_iff]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem latticeBaseChange_tmul (a : 𝒪) (t : ↥(heckeAlgebra N 2 S)) :
    latticeBaseChange N S 𝒪 (a ⊗ₜ t) =
      (a ⊗ₜ[ℤ] latticeRestrictHom N S t : 𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)) := rfl

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem latticeBaseChange_algebraMap (a : 𝒪) :
    latticeBaseChange N S 𝒪 (algebraMap 𝒪 _ a) = algebraMap 𝒪 (heckeBaseAlgebra N S 𝒪) a := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    latticeBaseChange_tmul, map_one]
  rfl

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem latticeBaseChange_surjective : Function.Surjective (latticeBaseChange N S 𝒪) :=
  Algebra.TensorProduct.map_surjective _ _ Function.surjective_id
    (latticeRestrictHom_surjective N S)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem latticeBaseChange_injective (hint : HasIntegralStructure N 2) :
    Function.Injective (latticeBaseChange N S 𝒪) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : 𝒪 ≃ₐ[ℤ] 𝒪)
    (AlgEquiv.ofBijective (latticeRestrictHom N S)
      (latticeRestrictHom_bijective N S hint))).injective

/-- The image of the kernel of the residual character in `heckeBaseAlgebra N S 𝒪`. -/
def heckeLocalIdeal : Ideal (heckeBaseAlgebra N S 𝒪) :=
  (heckeCharKernel N S 𝒪 θ).map (latticeBaseChange N S 𝒪)

theorem comap_heckeLocalIdeal
    (hker : RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ) :
    (heckeLocalIdeal N S 𝒪 θ).comap (latticeBaseChange N S 𝒪) = heckeCharKernel N S 𝒪 θ := by
  rw [heckeLocalIdeal, Ideal.comap_map_of_surjective _ (latticeBaseChange_surjective N S 𝒪),
    sup_eq_left]
  exact hker

theorem heckeLocalIdeal_isMaximal
    (hker : RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ) :
    (heckeLocalIdeal N S 𝒪 θ).IsMaximal := by
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ (latticeBaseChange_surjective N S 𝒪)
    (heckeCharKernel.instIsMaximal N S 𝒪 θ)).resolve_left fun htop => ?_
  apply (heckeCharKernel.instIsMaximal N S 𝒪 θ).ne_top
  rw [← comap_heckeLocalIdeal N S 𝒪 θ hker, heckeLocalIdeal, htop, Ideal.comap_top]

theorem mem_heckeLocalSubmonoid_iff
    (hker : RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ)
    (x : heckeBaseAlgebra N S 𝒪) :
    x ∈ heckeLocalSubmonoid N S 𝒪 θ ↔ x ∉ heckeLocalIdeal N S 𝒪 θ := by
  constructor
  · rintro ⟨a, ha, rfl⟩ hx
    refine Ideal.mem_primeCompl_iff.mp ha ?_
    rw [← comap_heckeLocalIdeal N S 𝒪 θ hker]
    exact Ideal.mem_comap.mpr hx
  · intro hx
    obtain ⟨a, rfl⟩ := latticeBaseChange_surjective N S 𝒪 x
    exact ⟨a, Ideal.mem_primeCompl_iff.mpr fun ha => hx (Ideal.mem_map_of_mem _ ha), rfl⟩

section Hint

variable [Fact (HasIntegralStructure N 2)]

theorem ker_latticeBaseChange_le_heckeCharKernel :
    RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ := fun x hx => by
  rw [RingHom.mem_ker] at hx
  rw [latticeBaseChange_injective N S 𝒪 Fact.out (hx.trans (map_zero _).symm)]
  exact zero_mem _

instance heckeLocalIdeal.instIsMaximal : (heckeLocalIdeal N S 𝒪 θ).IsMaximal :=
  heckeLocalIdeal_isMaximal N S 𝒪 θ (ker_latticeBaseChange_le_heckeCharKernel N S 𝒪 θ)

theorem heckeLocalSubmonoid_eq_primeCompl :
    heckeLocalSubmonoid N S 𝒪 θ = (heckeLocalIdeal N S 𝒪 θ).primeCompl :=
  Submonoid.ext fun x =>
    (mem_heckeLocalSubmonoid_iff N S 𝒪 θ (ker_latticeBaseChange_le_heckeCharKernel N S 𝒪 θ) x).trans
      Ideal.mem_primeCompl_iff.symm

instance heckeLocal.instIsLocalizationAtPrime :
    IsLocalization.AtPrime (heckeLocal N S 𝒪 θ) (heckeLocalIdeal N S 𝒪 θ) := by
  rw [IsLocalization.AtPrime, ← heckeLocalSubmonoid_eq_primeCompl N S 𝒪 θ]
  exact heckeLocal.instIsLocalization N S 𝒪 θ

theorem heckeLocal.isLocalRing : IsLocalRing (heckeLocal N S 𝒪 θ) :=
  IsLocalization.AtPrime.isLocalRing (heckeLocal N S 𝒪 θ) (heckeLocalIdeal N S 𝒪 θ)

theorem heckeLocal.isLocalHom_algebraMap : IsLocalHom (algebraMap 𝒪 (heckeLocal N S 𝒪 θ)) := by
  constructor
  intro a ha
  rw [IsScalarTower.algebraMap_apply 𝒪 (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ),
    IsLocalization.AtPrime.isUnit_to_map_iff (heckeLocal N S 𝒪 θ) (heckeLocalIdeal N S 𝒪 θ),
    Ideal.mem_primeCompl_iff, ← latticeBaseChange_algebraMap, ← Ideal.mem_comap,
    comap_heckeLocalIdeal N S 𝒪 θ (ker_latticeBaseChange_le_heckeCharKernel N S 𝒪 θ),
    algebraMap_mem_heckeCharKernel_iff] at ha
  exact IsLocalRing.notMem_maximalIdeal.mp ha

end Hint

end Structure

section TrioEngines


omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma trio_moduleFinite_base : Module.Finite 𝒪 (heckeBaseAlgebra N S 𝒪) :=
  inferInstanceAs (Module.Finite 𝒪 (𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)))

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma trio_moduleFree_base : Module.Free 𝒪 (heckeBaseAlgebra N S 𝒪) :=
  inferInstanceAs (Module.Free 𝒪 (𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)))

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma trio_isNoetherianRing_base : IsNoetherianRing (heckeBaseAlgebra N S 𝒪) := by
  have := trio_moduleFinite_base N S 𝒪
  exact IsNoetherianRing.of_finite 𝒪 (heckeBaseAlgebra N S 𝒪)

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma trio_subsingleton_or_ker_le :
    Subsingleton (heckeLocal N S 𝒪 θ) ∨
      RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ := by
  by_cases hker : RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ
  · exact Or.inr hker
  · refine Or.inl ?_
    obtain ⟨x, hxk, hxm⟩ := IsConcreteLE.not_le_iff_exists.mp hker
    have h0 : (0 : heckeBaseAlgebra N S 𝒪) ∈ heckeLocalSubmonoid N S 𝒪 θ :=
      ⟨x, Ideal.mem_primeCompl_iff.mpr hxm, by
        rw [RingHom.mem_ker] at hxk
        exact hxk⟩
    exact IsLocalization.subsingleton h0

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma trio_isLocalization_atPrime
    (hker : RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ) :
    haveI := (heckeLocalIdeal_isMaximal N S 𝒪 θ hker).isPrime
    IsLocalization (heckeLocalIdeal N S 𝒪 θ).primeCompl (heckeLocal N S 𝒪 θ) := by
  have := (heckeLocalIdeal_isMaximal N S 𝒪 θ hker).isPrime
  have hsub : heckeLocalSubmonoid N S 𝒪 θ = (heckeLocalIdeal N S 𝒪 θ).primeCompl :=
    Submonoid.ext fun x => (mem_heckeLocalSubmonoid_iff N S 𝒪 θ hker x).trans
      Ideal.mem_primeCompl_iff.symm
  rw [← hsub]
  exact heckeLocal.instIsLocalization N S 𝒪 θ

end TrioEngines

instance heckeLocal.instIsNoetherianRing : IsNoetherianRing (heckeLocal N S 𝒪 θ) := by
  have := trio_isNoetherianRing_base N S 𝒪
  exact IsLocalization.isNoetherianRing (heckeLocalSubmonoid N S 𝒪 θ) (heckeLocal N S 𝒪 θ)
    inferInstance

instance heckeLocal.instModuleFinite : Module.Finite 𝒪 (heckeLocal N S 𝒪 θ) := by
  rcases trio_subsingleton_or_ker_le N S 𝒪 θ with hsub | hker
  · exact Module.Finite.of_surjective (0 : 𝒪 →ₗ[𝒪] heckeLocal N S 𝒪 θ)
      fun y => ⟨0, Subsingleton.elim _ _⟩
  · have := trio_moduleFinite_base N S 𝒪
    have hPmax : (heckeLocalIdeal N S 𝒪 θ).IsMaximal := heckeLocalIdeal_isMaximal N S 𝒪 θ hker
    have hloc := trio_isLocalization_atPrime N S 𝒪 θ hker
    obtain ⟨-, -, hfin, -⟩ :=
      Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite (𝒪 := 𝒪)
      (heckeBaseAlgebra N S 𝒪)
    have := hfin ⟨heckeLocalIdeal N S 𝒪 θ, hPmax⟩
    have e := IsLocalization.algEquiv (heckeLocalIdeal N S 𝒪 θ).primeCompl
      (Localization.AtPrime (heckeLocalIdeal N S 𝒪 θ)) (heckeLocal N S 𝒪 θ)
    exact Module.Finite.equiv (e.toLinearEquiv.restrictScalars 𝒪)

instance heckeLocal.instModuleFree : Module.Free 𝒪 (heckeLocal N S 𝒪 θ) := by
  have := trio_moduleFree_base N S 𝒪
  have : Module.Flat 𝒪 (heckeLocal N S 𝒪 θ) :=
    inferInstanceAs (Module.Flat 𝒪 (Localization (heckeLocalSubmonoid N S 𝒪 θ)))
  exact Module.free_of_flat_of_isLocalRing

instance heckeLocal.instIsLocalRing [Fact (HasIntegralStructure N 2)] :
    IsLocalRing (heckeLocal N S 𝒪 θ) :=
  heckeLocal.isLocalRing N S 𝒪 θ

instance heckeLocal.instIsAdicComplete [Fact (HasIntegralStructure N 2)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (heckeLocal N S 𝒪 θ)) (heckeLocal N S 𝒪 θ) := by
  have := heckeLocal.isLocalHom_algebraMap N S 𝒪 θ
  exact IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪)

instance heckeLocal.instIsLocalHom [Fact (HasIntegralStructure N 2)] :
    IsLocalHom (algebraMap 𝒪 (heckeLocal N S 𝒪 θ)) :=
  heckeLocal.isLocalHom_algebraMap N S 𝒪 θ


omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
/-- Under an integral structure, the image of a Hecke operator in the local Hecke algebra
reduces, modulo its maximal ideal, to the value of the residual Hecke character. -/
theorem heckeLocal.residue_pi [Fact (HasIntegralStructure N 2)] (t : ↥(heckeAlgebra N 2 S)) :
    IsLocalRing.residue (heckeLocal N S 𝒪 θ) (heckeLocal.π N S 𝒪 θ t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 (heckeLocal N S 𝒪 θ)) (θ t) := by
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (θ t)
  have hx : (1 : 𝒪) ⊗ₜ[ℤ] t - algebraMap 𝒪 _ a ∈ heckeCharKernel N S 𝒪 θ := by
    rw [mem_heckeCharKernel_iff, map_sub, residualCharacter_tmul, residualCharacter_algebraMap,
      map_one, one_mul, ha, sub_self]
  have h1 : algebraMap (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ)
      (latticeBaseChange N S 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] t) - algebraMap 𝒪 _ a) ∈
        IsLocalRing.maximalIdeal (heckeLocal N S 𝒪 θ) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (heckeLocal N S 𝒪 θ)
      (heckeLocalIdeal N S 𝒪 θ), ← latticeBaseChange_algebraMap, ← map_sub]
    exact Ideal.mem_map_of_mem _ hx
  rw [map_sub, ← IsScalarTower.algebraMap_apply, ← Ideal.Quotient.eq] at h1
  rw [← ha, IsLocalRing.ResidueField.map_residue]
  exact h1

end CuspForm

end
