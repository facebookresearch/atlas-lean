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
# Exterior cochains with left enveloping coefficients

Let `R` be a commutative ring, `L` an `R`-Lie algebra, and `M` a left module over `U_R(L)` in
an independent coefficient universe. The cochain term in degree `n` is `Hom_R(⋀ⁿ[R] L, M)`,
identified with enveloping-linear Hom from the degree-`n` enveloping chain term.

Under this identification, `δf(v₀ ∧ ⋯ ∧ vₙ)` is `f` of the bracket boundary plus `∑ᵢ (-1)^i
ι(vᵢ) • f(v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ)`. A bracket pair `i<j` has sign `(-1)^(i+j)`, with the
bracket placed first and surviving arguments in order. In particular the degree-two bracket
boundary is `-[v₀,v₁]`. The transported differential squares to zero.

Reference: Weibel, *An Introduction to Homological Algebra*, Chapter 7.
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

/-- The differential on exterior cochains with left coefficients.

For a left `U_R(L)`-module `M`, this map `Hom_R(⋀ⁿ L,M) → Hom_R(⋀^(n+1) L,M)` is the
enveloping Hom differential expressed through the exterior-coordinate equivalences. -/
def leftCochainDifferential (n : ℕ) :
    ((⋀[R]^n L) →ₗ[R] M) →ₗ[R] ((⋀[R]^(n + 1) L) →ₗ[R] M) :=
  (envelopingHomCoordinates R L M (n + 1)).toLinearMap.comp
    ((envelopingHomDifferential R L M n).comp
      (envelopingHomCoordinates R L M n).symm.toLinearMap)

/-- The Hom-coordinate equation for the exterior cochain differential.

The coordinate image of an enveloping Hom cochain commutes with its differential: exterior
transport of the Hom boundary equals the exterior differential of its coordinate image. -/
theorem leftCochainDifferential_of_hom (n : ℕ) (f : envelopingHomTerm R L M n) :
    leftCochainDifferential R L M n (envelopingHomCoordinates R L M n f) =
      envelopingHomCoordinates R L M (n + 1) (envelopingHomDifferential R L M n f) := by
  change envelopingHomCoordinates R L M (n + 1)
    (envelopingHomDifferential R L M n
      ((envelopingHomCoordinates R L M n).symm (envelopingHomCoordinates R L M n f))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The square-zero equation for the exterior cochain differential.

For every `n ∈ ℕ`, the composite `δ_(n+1) ∘ δ_n` on `Hom_R(⋀ⁿ L,M)` is zero. -/
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

/-- The exterior cochain complex of a left enveloping module.

For a left `U_R(L)`-module `M`, this cochain complex has degree `n` equal to `Hom_R(⋀ⁿ[R]
L,M)` and differential given by the transported bracket-and-action formula. Its carrier
universe includes `R`, `L`, and `M`. -/
def leftCoefficientCochainComplex : CochainComplex (ModuleCat.{max u v w} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R ((⋀[R]^n L) →ₗ[R] M))
    (fun n => ModuleCat.ofHom (leftCochainDifferential R L M n)) (by
      intro n
      rw [← ModuleCat.ofHom_comp, leftCochainDifferential_comp, ModuleCat.ofHom_zero])

/-- The successor differential of the left coefficient cochain complex.

The map from degree `n` to degree `n+1` is the categorical module map of the exterior cochain
differential `δ_n`. -/
@[simp]
theorem leftCoefficientCochainComplex_d_succ (n : ℕ) :
    (leftCoefficientCochainComplex R L M).d n (n + 1) =
      ModuleCat.ofHom (leftCochainDifferential R L M n) := by
  simp only [leftCoefficientCochainComplex, CochainComplex.of_d]

/-- The complex comparison between enveloping Hom and exterior cochains.

The degreewise exterior Hom-coordinate equivalences give an isomorphism from the enveloping
Hom cochain complex to the exterior cochain complex with left coefficients. -/
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

/-- The action-and-bracket formula for left exterior cochains.

For `f : ⋀ⁿ L →ₗ[R] M`, evaluation on `v₀ ∧ ⋯ ∧ vₙ` gives `f` of the bracket boundary plus `∑ᵢ
(-1)^i ι(vᵢ) • f(v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ)`. -/
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

/-- The canonical bracket form of the left cochain formula.

The differential is `f(bracketBoundary(v))` plus the signed left-action deletion sum `∑ᵢ
(-1)^i ι(vᵢ) • f(⋀_(j≠i) vⱼ)`. -/
theorem leftCochainDifferential_apply_bracketBoundary (n : ℕ)
    (f : (⋀[R]^n L) →ₗ[R] M) (v : Fin (n + 1) → L) :
    leftCochainDifferential R L M n f (exteriorPower.ιMulti R (n + 1) v) =
      f (bracketBoundary R L n v) +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          (UniversalEnvelopingAlgebra.ι R (v i) • f (exteriorPower.ιMulti R n (v ∘ i.succAbove))) := by
  rw [leftCochainDifferential_apply_ιMulti, differential_apply_ιMulti]

/-- The ordered-pair formula for the left cochain differential.

On a wedge of `n+2` Lie elements, the bracket contribution sums over pairs `(i,j+1)` with `i ≤
j`, with sign `(-1)^(i+j+1)`, bracket `[v_i,v_(j+1)]` first, and survivors in order. The
action contribution deletes one argument with sign `(-1)^i` and acts on the left. -/
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

/-- The positive coefficient action in cochain degree zero.

For a degree-zero cochain `f` and `x ∈ L`, its differential evaluated on the one-element wedge
is `ι(x) • f(1)`, where `1` denotes the empty exterior wedge. -/
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

/-- The left Lie-action form of the exterior cochain differential.

Restricting the `U_R(L)`-action on `M` to `L`, the action part of `δf` is `∑ᵢ (-1)^i [vᵢ,
f(⋀_(j≠i) vⱼ)]`, in addition to `f` of the bracket boundary. -/
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
