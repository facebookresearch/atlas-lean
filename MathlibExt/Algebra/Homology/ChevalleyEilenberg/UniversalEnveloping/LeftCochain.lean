/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.LeftHom
public import MathlibExt.Algebra.Category.LieModuleCat.UniversalEnveloping
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Canonical

/-!
# Exterior cochains from left enveloping Hom

Transporting the enveloping-linear Hom differential gives the exterior
cochain complex in every nonnegative degree. Its generator formula combines
the bracket boundary with positive left coefficient-action terms. The
bracket has the negative degree-two sign, and square-zero follows from the
Hom-complex differential.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

variable (M : ModuleCat.{w} (UniversalEnvelopingAlgebra R L))

/-- The all-degree exterior cochain differential, transported from
the original UEA-linear Hom differential. -/
def leftCochainDifferential (n : ℕ) :
    ((⋀[R]^n L) →ₗ[R] M) →ₗ[R] ((⋀[R]^(n + 1) L) →ₗ[R] M) :=
  (envelopingHomCoordinates R L M (n + 1)).toLinearMap.comp
    ((envelopingHomDifferential R L M n).comp
      (envelopingHomCoordinates R L M n).symm.toLinearMap)

/-- Hom cochains commute with the transported differential. -/
theorem leftCochainDifferential_of_hom (n : ℕ) (f : envelopingHomTerm R L M n) :
    leftCochainDifferential R L M n (envelopingHomCoordinates R L M n f) =
      envelopingHomCoordinates R L M (n + 1) (envelopingHomDifferential R L M n f) := by
  change envelopingHomCoordinates R L M (n + 1)
    (envelopingHomDifferential R L M n
      ((envelopingHomCoordinates R L M n).symm (envelopingHomCoordinates R L M n f))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The all-degree exterior cochain differential squares to zero by Hom transport, by transport
through the Hom-complex comparison. -/
theorem leftCochainDifferential_comp (n : ℕ) :
    (leftCochainDifferential R L M (n + 1)).comp (leftCochainDifferential R L M n) = 0 := by
  apply LinearMap.ext
  intro f
  change envelopingHomCoordinates R L M (n + 2)
    (envelopingHomDifferential R L M (n + 1)
      ((envelopingHomCoordinates R L M (n + 1)).symm
        (envelopingHomCoordinates R L M (n + 1)
          (envelopingHomDifferential R L M n ((envelopingHomCoordinates R L M n).symm f))))) = 0
  rw [LinearEquiv.symm_apply_apply]
  have h := LinearMap.congr_fun (envelopingHomDifferential_comp R L M n)
    ((envelopingHomCoordinates R L M n).symm f)
  change envelopingHomDifferential R L M (n + 1)
    (envelopingHomDifferential R L M n ((envelopingHomCoordinates R L M n).symm f)) = 0 at h
  rw [h, map_zero]

/-- The original all-degree exterior cochain model with differential. -/
def leftCoefficientCochainComplex : CochainComplex (ModuleCat.{max u v w} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R ((⋀[R]^n L) →ₗ[R] M))
    (fun n => ModuleCat.ofHom (leftCochainDifferential R L M n)) (by
      intro n
      rw [← ModuleCat.ofHom_comp, leftCochainDifferential_comp, ModuleCat.ofHom_zero])

@[simp]
theorem leftCoefficientCochainComplex_d_succ (n : ℕ) :
    (leftCoefficientCochainComplex R L M).d n (n + 1) =
      ModuleCat.ofHom (leftCochainDifferential R L M n) := by
  simp only [leftCoefficientCochainComplex, CochainComplex.of_d]

/-- The exterior cochain model is isomorphic to Hom of the original
enveloping CE complex. -/
def envelopingHomCoefficientIso :
    envelopingHomComplex R L M ≅ leftCoefficientCochainComplex R L M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (envelopingHomCoordinates R L M n).toModuleIso) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ModuleCat.hom_ext
      rw [envelopingHomComplex_d_succ, leftCoefficientCochainComplex_d_succ]
      apply LinearMap.ext
      intro f
      exact leftCochainDifferential_of_hom R L M i f)

/-- The all-degree formula in ordered exterior coordinates: the
existing bracket boundary plus one positive left-action term per deletion. -/
theorem leftCochainDifferential_apply_ιMulti (n : ℕ)
    (f : (⋀[R]^n L) →ₗ[R] M) (v : Fin (n + 1) → L) :
    leftCochainDifferential R L M n f (exteriorPower.ιMulti R (n + 1) v) =
      f (differential R L n (exteriorPower.ιMulti R (n + 1) v)) +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          (UniversalEnvelopingAlgebra.ι R (v i) • f (exteriorPower.ιMulti R n (v ∘ i.succAbove))) := by
  change envelopingHomCoordinates R L M (n + 1)
    (envelopingHomDifferential R L M n ((envelopingHomCoordinates R L M n).symm f))
      (exteriorPower.ιMulti R (n + 1) v) = _
  rw [envelopingHomCoordinates_apply]
  let F := (envelopingHomCoordinates R L M n).symm f
  let z : (envelopingComplex R L).X (n + 1) :=
    exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] (1 : regularCoefficients R L)
  refine (envelopingHomDifferential_apply R L M n F z).trans ?_
  change envelopingHomGroundMap R L M n ((envelopingHomCoordinates R L M n).symm f)
    (envelopingGroundDifferential R L n
      (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] (1 : regularCoefficients R L))) = _
  rw [envelopingGroundDifferential_apply_ιMulti_tmul]
  rw [map_add, map_sum]
  simp only [map_smul]
  have hTerm (a : ⋀[R]^n L) (u : regularCoefficients R L) :
      envelopingHomGroundMap R L M n F (a ⊗ₜ[R] u) = u • f a :=
    (envelopingHomGroundMap_apply R L M n F
      (show envelopingGroundObject R L n from a ⊗ₜ[R] u)).trans
      (envelopingHomCoordinates_symm_tmul R L M n f a u)
  apply congrArg₂ (fun x y : M => x + y)
  · exact (hTerm (differential R L n (exteriorPower.ιMulti R (n + 1) v)) 1).trans
      (one_smul U (f (differential R L n (exteriorPower.ιMulti R (n + 1) v))))
  · apply Finset.sum_congr rfl
    intro i hi
    rw [one_mul]
    change (-1 : R) ^ i.val •
      envelopingHomGroundMap R L M n F
        (exteriorPower.ιMulti R n (v ∘ i.succAbove) ⊗ₜ[R] UniversalEnvelopingAlgebra.ι R (v i)) = _
    exact congrArg (fun y : M => (-1 : R) ^ i.val • y)
      (hTerm (exteriorPower.ιMulti R n (v ∘ i.succAbove)) (UniversalEnvelopingAlgebra.ι R (v i)))

/-- The formula uses the already canonical bracket boundary. -/
theorem leftCochainDifferential_apply_bracketBoundary (n : ℕ)
    (f : (⋀[R]^n L) →ₗ[R] M) (v : Fin (n + 1) → L) :
    leftCochainDifferential R L M n f (exteriorPower.ιMulti R (n + 1) v) =
      f (bracketBoundary R L n v) +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          (UniversalEnvelopingAlgebra.ι R (v i) • f (exteriorPower.ιMulti R n (v ∘ i.succAbove))) := by
  rw [leftCochainDifferential_apply_ιMulti, differential_apply_ιMulti]

/-- The strict-pair sum in the native compressed indices. The pair
`(i,j)` here represents original indices `(i,j+1)`, so its sign is precisely
the original `(-1)^(i+(j+1))`. The bracket is first and survivor order is retained. -/
theorem leftCochainDifferential_apply_orderedPairs (n : ℕ)
    (f : (⋀[R]^(n + 1) L) →ₗ[R] M) (v : Fin (n + 2) → L) :
    leftCochainDifferential R L M (n + 1) f (exteriorPower.ιMulti R (n + 2) v) =
      (∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
        (-1 : R) ^ (i.val + j.val + 1) •
          f (exteriorPower.ιMulti R (n + 1)
            (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
              (j.removeNth (i.castSucc.removeNth v))))) +
        ∑ i : Fin (n + 2), (-1 : R) ^ i.val •
          (UniversalEnvelopingAlgebra.ι R (v i) •
            f (exteriorPower.ιMulti R (n + 1) (v ∘ i.succAbove))) := by
  rw [leftCochainDifferential_apply_bracketBoundary]
  simp only [bracketBoundary, map_sum, map_smul]

/-- Degree zero is exactly the original positive Lie action on coefficients. -/
theorem leftCochainDifferential_zero_apply (f : (⋀[R]^0 L) →ₗ[R] M) (x : L) :
    leftCochainDifferential R L M 0 f (exteriorPower.ιMulti R 1 (fun _ => x)) =
      UniversalEnvelopingAlgebra.ι R x • f (exteriorPower.ιMulti R 0 Fin.elim0) := by
  have hdelete : (fun _ : Fin 1 => x) ∘ (0 : Fin 1).succAbove =
      (Fin.elim0 : Fin 0 → L) := by
    funext i
    exact Fin.elim0 i
  rw [leftCochainDifferential_apply_bracketBoundary]
  rw [Fin.sum_univ_one]
  simp only [bracketBoundary, map_zero, zero_add, Fin.val_zero, pow_zero, one_smul, hdelete]

/-- Express the action term in the native left Lie coefficient module
provided by the UEA/Lie restriction, with the same ordered signs. -/
theorem leftCochainDifferential_apply_lie (n : ℕ)
    (f : (⋀[R]^n L) →ₗ[R] M) (v : Fin (n + 1) → L) :
    leftCochainDifferential R L M n f (exteriorPower.ιMulti R (n + 1) v) =
      f (bracketBoundary R L n v) +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          (show M from
            @Bracket.bracket L (LieModuleCat.UniversalEnveloping.restrictObj R L M)
              (LieModuleCat.UniversalEnveloping.restrictObj R L M).lieRingModule.toBracket
              (v i) (f (exteriorPower.ιMulti R n (v ∘ i.succAbove)))) := by
  refine (leftCochainDifferential_apply_bracketBoundary R L M n f v).trans ?_
  apply congrArg (fun y : M => f (bracketBoundary R L n v) + y)
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (fun y : M => (-1 : R) ^ i.val • y)
  exact (LieModuleCat.UniversalEnveloping.restrictObj_lie R L M
    (v i) (f (exteriorPower.ιMulti R n (v ∘ i.succAbove)))).symm

end ChevalleyEilenberg
