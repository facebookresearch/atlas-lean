/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.KoszulComplexFamilyBaseChange
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Residue reduction of finite-family Koszul terms

A Koszul differential whose coefficient functional lands in an ideal has
image in the ideal multiple of its target exterior power. For a finite family
over a local ring, quotienting an exterior-power term by the maximal-ideal
multiple is canonically equivalent to the corresponding exterior power over
the residue field.

## Main declarations

* `KoszulComplex.differential_range_le_ideal_smul`
* `KoszulComplex.familyResidueComponentEquiv`
* `KoszulComplex.familyResidueComponentEquiv_mk_ιMulti`
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory
open IsLocalRing
open scoped TensorProduct

universe u v

namespace KoszulComplex

/-- If the coefficient functional lands in `I`, then its Koszul differential
lands in the ideal multiple of the target exterior power. -/
theorem differential_range_le_ideal_smul
    (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (I : Ideal R) (x : M →ₗ[R] R)
    (hx : LinearMap.range x ≤ I) (n : ℕ) :
    LinearMap.range (differential R M x n) ≤
      I • (⊤ : Submodule R (⋀[R]^n M)) := by
  apply (LinearMap.range_le_iff_comap).2
  apply top_unique
  calc
    ⊤ = Submodule.span R
        (Set.range (exteriorPower.ιMulti R (n + 1) (M := M))) :=
      (exteriorPower.ιMulti_span R (n + 1) M).symm
    _ ≤ Submodule.comap (differential R M x n)
        (I • (⊤ : Submodule R (⋀[R]^n M))) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      change differential R M x n
          (exteriorPower.ιMulti R (n + 1) a) ∈
        I • (⊤ : Submodule R (⋀[R]^n M))
      rw [differential_apply_ιMulti]
      apply Submodule.sum_mem
        (I • (⊤ : Submodule R (⋀[R]^n M)))
      intro i _
      exact
        (I • (⊤ : Submodule R (⋀[R]^n M))).smul_mem
          ((-1 : R) ^ (i : ℕ))
          (Submodule.smul_mem_smul
            (hx (LinearMap.mem_range_self x (a i)))
            Submodule.mem_top)

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable {J : Type v} [Fintype J]

-- These coherence instances identify the residue-field spelling with the raw
-- quotient spelling only inside this module. They must not become global.
/-- Residue scalars on the underlying quotient ring. -/
local instance residueQuotientModule :
    Module (ResidueField R) (R ⧸ maximalIdeal R) :=
  inferInstanceAs
    (Module (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R))

local instance residueQuotientTower :
    IsScalarTower R (ResidueField R) (R ⧸ maximalIdeal R) :=
  inferInstanceAs
    (IsScalarTower R (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R))

local instance residueQuotientSmulComm :
    SMulCommClass R (ResidueField R) (R ⧸ maximalIdeal R) :=
  inferInstanceAs
    (SMulCommClass R (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R))

/-- Residue scalars on a base-changed exterior term. -/
local instance residueTensorModule (n : ℕ) :
    Module (ResidueField R)
      ((ResidueField R) ⊗[R] (⋀[R]^n (J → R))) :=
  inferInstanceAs
    (Module (R ⧸ maximalIdeal R)
      ((R ⧸ maximalIdeal R) ⊗[R] (⋀[R]^n (J → R))))

local instance residueTensorTower (n : ℕ) :
    IsScalarTower R (ResidueField R)
      ((ResidueField R) ⊗[R] (⋀[R]^n (J → R))) :=
  inferInstanceAs
    (IsScalarTower R (R ⧸ maximalIdeal R)
      ((R ⧸ maximalIdeal R) ⊗[R] (⋀[R]^n (J → R))))

/-- Residue scalars on an exterior term modulo the maximal ideal. -/
local instance residueExteriorQuotientModule (n : ℕ) :
    Module (ResidueField R)
      ((⋀[R]^n (J → R)) ⧸
        (maximalIdeal R •
          (⊤ : Submodule R (⋀[R]^n (J → R))))) :=
  inferInstanceAs
    (Module (R ⧸ maximalIdeal R)
      ((⋀[R]^n (J → R)) ⧸
        (maximalIdeal R •
          (⊤ : Submodule R (⋀[R]^n (J → R))))))

local instance residueExteriorQuotientTower (n : ℕ) :
    IsScalarTower R (ResidueField R)
      ((⋀[R]^n (J → R)) ⧸
        (maximalIdeal R •
          (⊤ : Submodule R (⋀[R]^n (J → R))))) :=
  inferInstanceAs
    (IsScalarTower R (R ⧸ maximalIdeal R)
      ((⋀[R]^n (J → R)) ⧸
        (maximalIdeal R •
          (⊤ : Submodule R (⋀[R]^n (J → R))))))

/-- Quotient reduction of a finite-family exterior-power term, identified
with the corresponding exterior power over the residue field. -/
@[no_expose]
noncomputable def familyResidueComponentEquiv (n : ℕ) :
    ((⋀[R]^n (J → R)) ⧸
      (maximalIdeal R •
        (⊤ : Submodule R (⋀[R]^n (J → R)))))
      ≃ₗ[ResidueField R]
    ⋀[ResidueField R]^n (J → ResidueField R) :=
  let q :=
    (TensorProduct.quotTensorEquivQuotSMul
      (⋀[R]^n (J → R))
      (maximalIdeal R)).extendScalarsOfSurjective
        (residue_surjective (R := R))
  q.symm.trans
    ((familyBaseChangeComponentEquiv R (ResidueField R)
      (I := J) n).trans ULift.moduleEquiv)

/-- On a decomposable wedge, residue-component reduction applies the residue
map to every factor. -/
@[simp]
theorem familyResidueComponentEquiv_mk_ιMulti
    (n : ℕ) (b : Fin n → (J → R)) :
    familyResidueComponentEquiv R (J := J) n
        (Submodule.Quotient.mk (exteriorPower.ιMulti R n b)) =
      exteriorPower.ιMulti (ResidueField R) n
        (fun q j => residue R (b q j)) := by
  rw [familyResidueComponentEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply]
  change ULift.down
      (familyBaseChangeComponentEquiv R (ResidueField R) (I := J) n
        ((TensorProduct.quotTensorEquivQuotSMul
          (⋀[R]^n (J → R)) (maximalIdeal R)).symm
            (Submodule.Quotient.mk
              (exteriorPower.ιMulti R n b)))) = _
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk,
    familyBaseChangeComponentEquiv_apply_tmul_ιMulti]
  simp only [one_smul]
  change exteriorPower.ιMulti (ResidueField R) n
      (fun q j => algebraMap R (ResidueField R) (b q j)) = _
  rw [ResidueField.algebraMap_eq]

end KoszulComplex
