/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.FilteredDifferential
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Ground-scalar coordinates for enveloping chains

Let `R` be a commutative ring, `L` an `R`-Lie algebra, and `U = U_R(L)`. Restricting the
enveloping Chevalley–Eilenberg terms along `R → U` gives ground-scalar modules. The coordinate
equivalence sends the exterior-first tensor `w ⊗ a` to `a ⊗ w` in `U ⊗[R] ⋀ⁿ[R] L`.

Ground scalars act by `r • (w ⊗ a) = (r • w) ⊗ a`. The restricted differential has the same
bracket term and signed right-multiplication terms `(-1)^i ŵᵢ ⊗ aι(vᵢ)`. These formulas
specify the ground-linear maps used in balanced tensor and Hom comparisons.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local instance] rightRegularLieRingModule rightRegularLieModule
attribute [local implicit_reducible] coefficientComplex

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The ground module of an enveloping chain term.

In degree `n`, this is the enveloping Chevalley–Eilenberg term restricted from `U_R(L)` to `R`
along the scalar inclusion. -/
abbrev envelopingGroundObject (n : ℕ) : ModuleCat.{max u v} R :=
  (ModuleCat.restrictScalars (algebraMap R U)).obj ((envelopingComplex R L).X n)

/-- The ground-linear coordinates of an enveloping chain term.

The degree-`n` restricted term is `R`-linearly equivalent to `U_R(L) ⊗[R] ⋀ⁿ[R] L`, with
coordinate map `w ⊗ a ↦ a ⊗ w`. -/
def envelopingGroundCoordinates (n : ℕ) :
    envelopingGroundObject R L n ≃ₗ[R] U ⊗[R] (⋀[R]^n L) := by
  letI : Module R ((envelopingComplex R L).X n) :=
    Module.compHom ((envelopingComplex R L).X n) (algebraMap R U)
  letI : IsScalarTower R U ((envelopingComplex R L).X n) :=
    IsScalarTower.of_compHom R U ((envelopingComplex R L).X n)
  exact (envelopingCoordinates R L n).restrictScalars R

/-- The tensor formula for ground enveloping coordinates.

For `w ∈ ⋀ⁿ[R] L` and `a ∈ U_R(L)`, the coordinate equivalence sends the chain tensor `w ⊗ a`
to `a ⊗ w`. -/
@[simp]
theorem envelopingGroundCoordinates_tmul (n : ℕ) (w : ⋀[R]^n L)
    (a : regularCoefficients R L) :
    envelopingGroundCoordinates R L n (w ⊗ₜ[R] a) = a ⊗ₜ[R] w :=
  envelopingCoordinates_tmul R L n w a

/-- The ground scalar action on an enveloping chain tensor.

In the restricted degree-`n` module, `r • (w ⊗ a) = (r • w) ⊗ a` for `r ∈ R`. -/
theorem envelopingGround_smul_tmul (n : ℕ) (r : R) (w : ⋀[R]^n L)
    (a : regularCoefficients R L) :
    r • (show envelopingGroundObject R L n from w ⊗ₜ[R] a) = (r • w) ⊗ₜ[R] a := by
  apply (envelopingGroundCoordinates R L n).injective
  calc
    _ = r • envelopingGroundCoordinates R L n (w ⊗ₜ[R] a) :=
      (envelopingGroundCoordinates R L n).map_smul r (w ⊗ₜ[R] a)
    _ = r • (a ⊗ₜ[R] w) :=
      congrArg (fun z : U ⊗[R] (⋀[R]^n L) => r • z) (envelopingGroundCoordinates_tmul R L n w a)
    _ = a ⊗ₜ[R] (r • w) := (TensorProduct.tmul_smul r a w).symm
    _ = _ := (envelopingGroundCoordinates_tmul R L n (r • w) a).symm

/-- The ground-linear tensor map with a fixed enveloping coefficient.

For `a ∈ U_R(L)`, this sends `w ∈ ⋀ⁿ[R] L` to `w ⊗ a` in the ground module of the degree-`n`
enveloping chain term. -/
def envelopingGroundTmul (n : ℕ) (a : regularCoefficients R L) :
    (⋀[R]^n L) →ₗ[R] envelopingGroundObject R L n where
  toFun w := w ⊗ₜ[R] a
  map_add' w z := TensorProduct.add_tmul w z a
  map_smul' r w := (envelopingGround_smul_tmul R L n r w a).symm

/-- The value of a fixed-coefficient ground tensor map.

The map with fixed coefficient `a` has value `w ⊗ a` at `w ∈ ⋀ⁿ[R] L`. -/
@[simp]
theorem envelopingGroundTmul_apply (n : ℕ) (a : regularCoefficients R L) (w : ⋀[R]^n L) :
    envelopingGroundTmul R L n a w = w ⊗ₜ[R] a := rfl

/-- The ground-linear enveloping differential.

This is the successor differential of the enveloping Chevalley–Eilenberg complex, restricted
along `R → U_R(L)`, from degree `n+1` to degree `n`. -/
@[implicit_reducible]
def envelopingGroundDifferential (n : ℕ) :
    envelopingGroundObject R L (n + 1) →ₗ[R] envelopingGroundObject R L n :=
  ((ModuleCat.restrictScalars (algebraMap R U)).map ((envelopingComplex R L).d (n + 1) n)).hom

/-- The value of the restricted enveloping differential.

The ground-linear differential has the same value as the underlying enveloping-linear
successor differential. -/
@[simp]
theorem envelopingGroundDifferential_apply (n : ℕ)
    (z : envelopingGroundObject R L (n + 1)) :
    envelopingGroundDifferential R L n z =
      ((envelopingComplex R L).d (n + 1) n).hom z := rfl

/-- The coefficient boundary formula for the ground differential.

The restricted successor differential equals the Chevalley–Eilenberg coefficient differential
for the regular coefficients `[x,a] = -aι(x)`. -/
theorem envelopingGroundDifferential_apply_coefficient (n : ℕ)
    (z : envelopingGroundObject R L (n + 1)) :
    envelopingGroundDifferential R L n z =
      coefficientDifferential R L (regularCoefficients R L) n z := by
  rw [envelopingGroundDifferential_apply]
  unfold envelopingComplex coefficientScalarComplex
  simp only [ChainComplex.of_d]
  change ((coefficientComplex R L (regularCoefficients R L)).d (n + 1) n).hom z = _
  rw [coefficientComplex_d_succ]
  rfl

/-- The signed ground-coordinate formula for enveloping boundaries.

For `v : Fin (n+1) → L`, the boundary of `(⋀ᵢ vᵢ) ⊗ a` is the bracket boundary tensored with
`a`, plus `∑ᵢ (-1)^i (⋀_(j≠i) vⱼ) ⊗ aι(vᵢ)`. The exterior survivors retain their order. -/
theorem envelopingGroundDifferential_apply_ιMulti_tmul (n : ℕ)
    (v : Fin (n + 1) → L) (a : regularCoefficients R L) :
    envelopingGroundDifferential R L n
      (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] a) =
      envelopingGroundTmul R L n a
        (differential R L n (exteriorPower.ιMulti R (n + 1) v)) +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          envelopingGroundTmul R L n (a * UniversalEnvelopingAlgebra.ι R (v i))
            (exteriorPower.ιMulti R n (v ∘ i.succAbove)) := by
  refine (envelopingGroundDifferential_apply_coefficient R L n
    (show envelopingGroundObject R L (n + 1) from
      exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] a)).trans ?_
  calc
    _ = differential R L n (exteriorPower.ιMulti R (n + 1) v) ⊗ₜ[R] a +
        ∑ i : Fin (n + 1),
          ((-1 : R) ^ i.val • exteriorPower.ιMulti R n (v ∘ i.succAbove)) ⊗ₜ[R]
            (a * UniversalEnvelopingAlgebra.ι R (v i)) := by
      simpa only [TensorProduct.smul_tmul'] using
        envelopingDifferential_apply_ιMulti_tmul R L n v a
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (envelopingGround_smul_tmul R L n ((-1 : R) ^ i.val)
        (exteriorPower.ιMulti R n (v ∘ i.succAbove))
        (a * UniversalEnvelopingAlgebra.ι R (v i))).symm

end ChevalleyEilenberg
