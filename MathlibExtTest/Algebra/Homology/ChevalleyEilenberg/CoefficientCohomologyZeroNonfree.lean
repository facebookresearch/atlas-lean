/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientCohomologyZero
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# A nonfree Lie algebra with nonzero first coboundary and nonzero H⁰

The ground ring is Z/4, the abelian Lie algebra is Z/2, and its generator
acts on the original Z/4 coefficient module by multiplication by 2.
The first coboundary is nonzero, while the actual invariants are exactly
0 and 2. A splitting obstruction proves that the Lie module is neither
projective nor free over the ground ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MathlibExtTest.ChevalleyEilenberg.CoefficientCohomologyZeroNonfree

abbrev R := ZMod 4
abbrev L := ZMod 2

def quotientRing : R →+* L := ZMod.castHom (by decide : 2 ∣ 4) L

local instance : Algebra R L := quotientRing.toAlgebra
local instance : LieRing L := LieRing.ofAssociativeRing
local instance : LieAlgebra R L := LieAlgebra.ofAssociativeAlgebra

/-- The actual R-linear map sending the generator of Z/2 to 2 in Z/4. -/
def actionScalar : L →ₗ[R] R where
  toFun x := 2 * (x.val : R)
  map_add' x y := by
    fin_cases x <;> fin_cases y <;> decide
  map_smul' r x := by
    fin_cases r <;> fin_cases x <;> decide

local instance : LieRingModule L R where
  bracket x m := actionScalar x * m
  add_lie x y m := by
    change actionScalar (x + y) * m = actionScalar x * m + actionScalar y * m
    rw [actionScalar.map_add, add_mul]
  lie_add x m n := mul_add _ _ _
  leibniz_lie x y m := by
    change actionScalar x * (actionScalar y * m) =
      actionScalar ⁅x, y⁆ * m + actionScalar y * (actionScalar x * m)
    have hxy : ⁅x, y⁆ = 0 := by
      change x * y - y * x = 0
      rw [mul_comm x y, sub_self]
    rw [hxy, actionScalar.map_zero, zero_mul, zero_add]
    ring

local instance : LieModule R L R where
  smul_lie r x m := by
    change actionScalar (r • x) * m = r • (actionScalar x * m)
    rw [actionScalar.map_smul]
    change (r * actionScalar x) * m = r * (actionScalar x * m)
    ring
  lie_smul r x m := by
    change actionScalar x * (r * m) = r * (actionScalar x * m)
    ring

def lieObject : ModuleCat R := ModuleCat.of R L
def coefficients : LieModuleCat R L := LieModuleCat.of R L R

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The represented coefficient object retains the original Z/4 carrier. -/
def leftCoefficients : ModuleCat U :=
  LieModuleCat.UniversalEnveloping.representObj R L coefficients

@[simp]
theorem coefficient_lie (x : L) (m : R) :
    ⁅x, (show coefficients from m)⁆ = actionScalar x * m := rfl

/-- In this actual representation the invariant elements are exactly 0 and 2. -/
theorem coefficient_invariants_iff (m : R) :
    (show coefficients from m) ∈ LieModule.maxTrivSubmodule R L coefficients ↔
      m = 0 ∨ m = 2 := by
  rw [LieModule.mem_maxTrivSubmodule]
  constructor
  · intro hm
    have h := hm (1 : L)
    change (2 : R) * m = 0 at h
    fin_cases m
    · exact Or.inl rfl
    · exact False.elim ((by decide : (2 : R) * (1 : R) ≠ 0) h)
    · exact Or.inr rfl
    · exact False.elim ((by decide : (2 : R) * (3 : R) ≠ 0) h)
  · rintro (rfl | rfl)
    · intro x
      change actionScalar x * 0 = 0
      exact mul_zero _
    · intro x
      change actionScalar x * (2 : R) = 0
      fin_cases x <;> decide

def twoInvariant : ChevalleyEilenberg.leftCoefficientInvariants R L leftCoefficients :=
  (ChevalleyEilenberg.representedCoefficientInvariantsEquiv R L coefficients).symm
    ⟨(2 : R), (coefficient_invariants_iff 2).mpr (Or.inr rfl)⟩

@[simp]
theorem twoInvariant_value : (show R from twoInvariant.1) = 2 := rfl

def unitCochain : (⋀[R]^0 L) →ₗ[R] leftCoefficients :=
  (ChevalleyEilenberg.leftCochainZeroEquiv R L leftCoefficients).symm (show leftCoefficients from (1 : R))

/-- The actual first coboundary sends the original generator to 2, not to zero. -/
theorem first_coboundary_generator :
    ChevalleyEilenberg.leftCochainDifferential R L leftCoefficients 0 unitCochain
      (exteriorPower.ιMulti R 1 (fun _ => (1 : L))) = (2 : R) := by
  let E := ChevalleyEilenberg.leftCochainZeroEquiv R L leftCoefficients
  let oneM : leftCoefficients := (show leftCoefficients from (1 : R))
  have hRound : @Eq leftCoefficients (E (E.symm oneM)) oneM := E.apply_symm_apply oneM
  have hAct : @Eq leftCoefficients
      (UniversalEnvelopingAlgebra.ι R (1 : L) • oneM)
      (show leftCoefficients from (2 : R)) := by
    have h := (LieModuleCat.UniversalEnveloping.restrictObj_lie R L leftCoefficients
      (1 : L) (show LieModuleCat.UniversalEnveloping.restrictObj R L leftCoefficients from oneM)).symm.trans
        (LieModuleCat.UniversalEnveloping.restrict_represent_lie R L coefficients
          (1 : L) (show LieModuleCat.UniversalEnveloping.restrictObj R L leftCoefficients from oneM))
    have hc : @Eq R (actionScalar (1 : L) * (1 : R)) (2 : R) := by decide
    exact h.trans ((coefficient_lie (1 : L) (1 : R)).trans hc)
  exact (ChevalleyEilenberg.leftCochainDifferential_zero_apply
    R L leftCoefficients unitCochain (1 : L)).trans
      ((congrArg (fun m : leftCoefficients => UniversalEnvelopingAlgebra.ι R (1 : L) • m)
        hRound).trans hAct)

theorem first_coboundary_ne_zero :
    ChevalleyEilenberg.leftCochainDifferential R L leftCoefficients 0 unitCochain ≠ 0 := by
  intro h
  have h0 : (2 : R) = 0 := first_coboundary_generator.symm.trans
    (congrArg (fun f : (⋀[R]^1 L) →ₗ[R] leftCoefficients =>
      f (exteriorPower.ιMulti R 1 (fun _ => (1 : L)))) h)
  exact (by decide : (2 : R) ≠ 0) h0

def twoClass : (ChevalleyEilenberg.leftCoefficientCochainComplex R L leftCoefficients).homology 0 :=
  ChevalleyEilenberg.leftCoefficientCohomologyZeroClass R L leftCoefficients twoInvariant

/-- The canonical native H⁰ class has its actual nonzero coefficient value 2. -/
theorem twoClass_value :
    (show R from
      (ChevalleyEilenberg.leftCoefficientCohomologyZeroLinearEquiv R L leftCoefficients
        twoClass).1) = 2 := by
  let ν : ChevalleyEilenberg.leftCoefficientInvariants R L leftCoefficients → R :=
    fun m => show R from m.1
  exact (congrArg ν
    (ChevalleyEilenberg.leftCoefficientCohomologyZeroLinearEquiv_class
      R L leftCoefficients twoInvariant)).trans twoInvariant_value

/-- The public adapter for arbitrary native Lie coefficients computes the same original class. -/
theorem native_twoClass_value :
    (show R from
      (ChevalleyEilenberg.coefficientCohomologyZeroLinearEquiv R L coefficients twoClass).1) = 2 := by
  change (show R from
    ((ChevalleyEilenberg.representedCoefficientInvariantsEquiv R L coefficients)
      (ChevalleyEilenberg.leftCoefficientCohomologyZeroLinearEquiv R L leftCoefficients
        (ChevalleyEilenberg.leftCoefficientCohomologyZeroClass R L leftCoefficients twoInvariant))).1) = 2
  rw [ChevalleyEilenberg.leftCoefficientCohomologyZeroLinearEquiv_class]
  rfl

theorem twoClass_ne_zero : twoClass ≠ 0 := by
  intro h
  let E := ChevalleyEilenberg.leftCoefficientCohomologyZeroLinearEquiv R L leftCoefficients
  let ν : ChevalleyEilenberg.leftCoefficientInvariants R L leftCoefficients → R :=
    fun m => show R from m.1
  have hz : ν (E (0 :
      (ChevalleyEilenberg.leftCoefficientCochainComplex R L leftCoefficients).homology 0)) = 0 :=
    (congrArg ν E.map_zero).trans rfl
  have h0 : (2 : R) = 0 := twoClass_value.symm.trans
    ((congrArg (fun a :
      (ChevalleyEilenberg.leftCoefficientCochainComplex R L leftCoefficients).homology 0 =>
        ν (E a)) h).trans hz)
  exact (by decide : (2 : R) ≠ 0) h0

/-- The original quotient map R→L is R-linear for the actual restricted action. -/
def quotientLinear : R →ₗ[R] L where
  toFun := quotientRing
  map_add' := quotientRing.map_add
  map_smul' r a := quotientRing.map_mul r a

private theorem quotient_zero_of_twice_zero (m : R) (h : (2 : R) * m = 0) :
    quotientLinear m = 0 := by
  fin_cases m
  · rfl
  · exact False.elim ((by decide : (2 : R) * (1 : R) ≠ 0) h)
  · rfl
  · exact False.elim ((by decide : (2 : R) * (3 : R) ≠ 0) h)

/-- The genuine quotient cannot split: any lift of 1 annihilated by 2 maps to 0. -/
theorem lieObject_not_projective : ¬CategoryTheory.Projective lieObject := by
  intro hP
  letI := hP
  let q : ModuleCat.of R R ⟶ lieObject := ModuleCat.ofHom quotientLinear
  letI : Epi q := (ModuleCat.epi_iff_surjective q).mpr
    (ZMod.castHom_surjective (by decide : 2 ∣ 4))
  obtain ⟨s, hs⟩ := CategoryTheory.Projective.factors (𝟙 lieObject) q
  let m : R := s.hom (1 : L)
  have hm : quotientLinear m = 1 :=
    congrArg (fun f : lieObject ⟶ lieObject => f.hom (1 : L)) hs
  have hL : (2 : R) • (1 : L) = 0 := by decide
  have h2 : (2 : R) * m = 0 :=
    (s.hom.map_smul (2 : R) (1 : L)).symm.trans
      ((congrArg s.hom hL).trans s.hom.map_zero)
  have h01 : (0 : L) = 1 := (quotient_zero_of_twice_zero m h2).symm.trans hm
  exact (by decide : (0 : L) ≠ 1) h01

theorem lieModule_not_projective : ¬Module.Projective R lieObject := by
  intro h
  letI := h
  exact lieObject_not_projective (inferInstance : CategoryTheory.Projective lieObject)

theorem lieModule_not_free : ¬Module.Free R lieObject := by
  intro h
  letI := h
  exact lieModule_not_projective
    (Module.Projective.of_basis (Module.Free.chooseBasis R lieObject))

end MathlibExtTest.ChevalleyEilenberg.CoefficientCohomologyZeroNonfree
