/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.LieModuleCat.CoefficientULift
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.LieNaturalityULift
public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.Algebra.Category.ModuleCat.UliftCoherence
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Coefficient lifts of Chevalley–Eilenberg chains and homology

Let `R` be a commutative ring, `L` an `R`-Lie algebra, and `M` a left Lie coefficient module.
Lifting the entire degree tensor `⋀ⁿ[R] L ⊗[R] M` is linearly equivalent to retaining the
exterior factor and lifting only `M`, by `up(a ⊗ m) ↦ a ⊗ up(m)`.

These degree maps give a chain isomorphism and homology comparisons. Successive lifts flatten
by `up(up(x)) ↦ up(x)`. The comparisons are natural in Lie maps and equivariant coefficient
maps, including independent source and target carrier universes. The corresponding lifted
homology maps also define ground-linear maps between the unlifted homology carriers.
-/

@[expose] public section

noncomputable section

universe u v w z v' w' t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex coefficientComplexULift

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The tensor comparison between full-chain and coefficient-only lifts.

In degree `n`, the equivalence removes the lift of the full exterior tensor and applies the
coefficient lift to its right factor. -/
def coefficientULiftDegreeEquiv (M : LieModuleCat.{w} R L) (n : ℕ) :
    (coefficientComplexULift.{u, v, w, z} R L M).X n ≃ₗ[R]
      (coefficientComplex R L (LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M)).X n :=
  (ULift.moduleEquiv : ULift.{z} ((⋀[R]^n L) ⊗[R] M) ≃ₗ[R] ((⋀[R]^n L) ⊗[R] M)).trans
    ((ULift.moduleEquiv : ULift.{z} M ≃ₗ[R] M).symm.lTensor (⋀[R]^n L))

/-- The coefficient-lift formula for a lifted CE tensor.

The comparison sends `up(a)` to the tensor map induced by the identity exterior map and the
coefficient inclusion `M → ULift M`. -/
theorem coefficientULiftDegreeEquiv_up (M : LieModuleCat.{w} R L) (n : ℕ)
    (a : (⋀[R]^n L) ⊗[R] M) :
    coefficientULiftDegreeEquiv.{u, v, w, z} R L M n (ULift.up a) =
      (LieModuleCat.CoefficientULift.up.{u, v, w, z} R L M).toLinearMap.lTensor (⋀[R]^n L) a := by
  change ((ULift.moduleEquiv : ULift.{z} M ≃ₗ[R] M).symm.lTensor (⋀[R]^n L)) a = _
  rfl

/-- The pure-tensor formula for the CE coefficient-lift comparison.

The degree comparison sends `up(a ⊗ m)` to `a ⊗ up(m)`, retaining exterior-first order. -/
theorem coefficientULiftDegreeEquiv_up_tmul (M : LieModuleCat.{w} R L) (n : ℕ)
    (a : ⋀[R]^n L) (m : M) :
    coefficientULiftDegreeEquiv.{u, v, w, z} R L M n (ULift.up (a ⊗ₜ[R] m)) =
      a ⊗ₜ[R] (ULift.up m : LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M) := by
  rw [coefficientULiftDegreeEquiv_up, LinearMap.lTensor_tmul]
  rfl

/-- The chain comparison of full CE lifting and lifted coefficients.

The degreewise tensor equivalences identify the whole-complex lift with the CE complex of the
lifted Lie coefficient module. -/
def coefficientULiftComplexIso (M : LieModuleCat.{w} R L) :
    coefficientComplexULift.{u, v, w, z} R L M ≅
      coefficientComplex R L (LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coefficientULiftDegreeEquiv.{u, v, w, z} R L M n).toModuleIso) (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      ext p
      cases p with
      | up p =>
          rw [coefficientComplex_d_succ]
          change coefficientDifferential R L
            (LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M) j
              (coefficientULiftDegreeEquiv.{u, v, w, z} R L M (j + 1) (ULift.up p)) =
            coefficientULiftDegreeEquiv.{u, v, w, z} R L M j
              (ULift.up (((coefficientComplex R L M).d (j + 1) j).hom p))
          rw [coefficientComplex_d_succ, coefficientULiftDegreeEquiv_up,
            coefficientULiftDegreeEquiv_up]
          exact (LinearMap.congr_fun (coefficientDifferential_naturality R L M
            (LieModuleCat.CoefficientULift.up.{u, v, w, z} R L M) j) p).symm)

/-- Homology preservation by the CE coefficient universe lift.

The exact module lift functor preserves homology of the coefficient chain complexes. -/
local instance coefficientHomologyULift_preservesHomology :
    (ModuleCat.uliftFunctor.{z, max u v w} R).PreservesHomology :=
  Functor.preservesHomologyOfExact (ModuleCat.uliftFunctor.{z, max u v w} R)

/-- The homology comparison for a whole CE complex lift.

The lifted degree-`n` homology object is isomorphic to degree-`n` homology of the whole lifted
coefficient complex. -/
def coefficientHomologyULiftIso (M : LieModuleCat.{w} R L) (n : ℕ) :
    (ModuleCat.uliftFunctor.{z, max u v w} R).obj ((coefficientComplex R L M).homology n) ≅
      (coefficientComplexULift.{u, v, w, z} R L M).homology n := by
  letI : (ModuleCat.uliftFunctor.{z, max u v w} R).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.uliftFunctor.{z, max u v w} R)
  exact ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
    (ModuleCat.uliftFunctor.{z, max u v w} R)).app (coefficientComplex R L M)).symm

/-- The linear lift equivalence of a CE homology carrier.

The homology carrier is ground-linearly equivalent to its module lift by `x ↦ up(x)` and
`up(x) ↦ x`. -/
def coefficientHomologyCarrierLiftEquiv (M : LieModuleCat.{w} R L) (n : ℕ) :
    (coefficientComplex R L M).homology n ≃ₗ[R]
      (ModuleCat.uliftFunctor.{z, max u v w} R).obj ((coefficientComplex R L M).homology n) :=
  (ULift.moduleEquiv : ULift.{z} ((coefficientComplex R L M).homology n) ≃ₗ[R]
    (coefficientComplex R L M).homology n).symm

/-- The homology comparison with CE of lifted coefficients.

The lifted homology object of the coefficient complex is isomorphic to homology of the CE
complex whose coefficient carrier is lifted. -/
def coefficientHomologyCoefficientLiftIso (M : LieModuleCat.{w} R L) (n : ℕ) :
    (ModuleCat.uliftFunctor.{z, max u v w} R).obj ((coefficientComplex R L M).homology n) ≅
      (coefficientComplex R L (LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M)).homology n :=
  coefficientHomologyULiftIso.{u, v, w, z} R L M n ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w z} R) (ComplexShape.down ℕ) n).mapIso
        (coefficientULiftComplexIso.{u, v, w, z} R L M)

/-- The carrier equivalence of CE homology under coefficient lifting.

Combining the homology-carrier lift and the coefficient-complex comparison gives a ground-
linear equivalence between the two homology carriers. -/
def coefficientHomologyCoefficientLiftEquiv (M : LieModuleCat.{w} R L) (n : ℕ) :
    (coefficientComplex R L M).homology n ≃ₗ[R]
      (coefficientComplex R L (LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M)).homology n :=
  (coefficientHomologyCarrierLiftEquiv.{u, v, w, z} R L M n).trans
    (coefficientHomologyCoefficientLiftIso.{u, v, w, z} R L M n).toLinearEquiv

/-- The flattening isomorphism of successive CE complex lifts.

Lifting the coefficient complex first by `z` and then by `t` is isomorphic to its lift by `max
z t`. -/
def coefficientComplexULiftFlattenIso (M : LieModuleCat.{w} R L) :
    ((ModuleCat.uliftFunctor.{t, max u v w z} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (coefficientComplexULift.{u, v, w, z} R L M) ≅
        coefficientComplexULift.{u, v, w, max z t} R L M :=
  ((Functor.mapHomologicalComplexCompIso
    (F := ModuleCat.uliftFunctor.{z, max u v w} R)
    (G := ModuleCat.uliftFunctor.{t, max u v w z} R)
    (Iso.refl _) (ComplexShape.down ℕ)).app (coefficientComplex R L M)) ≪≫
      ((NatIso.mapHomologicalComplex (ModuleCat.uliftFunctorCompIso.{z, t, max u v w} R)
        (ComplexShape.down ℕ)).app (coefficientComplex R L M))

/-- The component formula for flattening successive CE lifts.

The flattening map sends `up(up(a))` to `up(a)` in every degree. -/
theorem coefficientComplexULiftFlattenIso_up (M : LieModuleCat.{w} R L) (n : ℕ)
    (a : (coefficientComplex R L M).X n) :
    ((coefficientComplexULiftFlattenIso.{u, v, w, z, t} R L M).hom.f n).hom
      (ULift.up (ULift.up a)) = ULift.up a := rfl

section JointMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L')
  (M : LieModuleCat.{w} R L) (M' : LieModuleCat.{w'} R L')
  (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

/-- The lifted joint CE map at a common carrier height.

For a Lie homomorphism `f` and an equivariant coefficient map `h`, lift the joint CE chain map
and flatten the source and target into the universe joining both Lie and coefficient carriers. -/
def coefficientLieComplexMapULiftAt :
    coefficientComplexULift.{u, v, w, max u v v' w w' z} R L M ⟶
      coefficientComplexULift.{u, v', w', max u v v' w w' z} R L' M' :=
  (coefficientComplexULiftFlattenIso.{u, v, w, max u v v' w w', z} R L M).inv ≫
    ((ModuleCat.uliftFunctor.{z, max u v v' w w'} R).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (coefficientLieComplexMapULift R L f M M' h) ≫
        (coefficientComplexULiftFlattenIso.{u, v', w', max u v v' w w', z} R L' M').hom

/-- The pure-tensor formula for a lifted joint CE map.

The degree-`n` map sends `up(a ⊗ m)` to `up(⋀ⁿ(f)(a) ⊗ h(m))`. -/
@[simp]
theorem coefficientLieComplexMapULiftAt_up_tmul (n : ℕ) (a : ⋀[R]^n L) (m : M) :
    ((coefficientLieComplexMapULiftAt R L f M M' h).f n).hom (ULift.up (a ⊗ₜ[R] m)) =
      ULift.up (exteriorPower.map n f.toLinearMap a ⊗ₜ[R] h m) := by
  change ULift.up
    ((((coefficientLieComplexMapULift R L f M M' h).f n).hom (ULift.up (a ⊗ₜ[R] m))).down) = _
  rw [coefficientLieComplexMapULift_f_tmul]

/-- Naturality of the coefficient-lift comparison in joint CE maps.

The full lifted joint chain map followed by the coefficient-lift comparison equals the source
comparison followed by the joint map on lifted Lie coefficients. -/
theorem coefficientULiftComplexIso_joint_naturality :
    coefficientLieComplexMapULiftAt R L f M M' h ≫
      (coefficientULiftComplexIso.{u, v', w', max u v v' w w' z} R L' M').hom =
    (coefficientULiftComplexIso.{u, v, w, max u v v' w w' z} R L M).hom ≫
      (ChainComplex.ofHom
        (fun n => ModuleCat.ofHom (coefficientLieDegreeMap R L f
          (LieModuleCat.CoefficientULift.obj.{u, v, w, max u v v' w w' z} R L M)
          (LieModuleCat.CoefficientULift.obj.{u, v', w', max u v v' w w' z} R L' M')
          (LieModuleCat.CoefficientULift.jointMap R L f M M' h) n))
        (fun n => by
          simp only [coefficientComplex_d_succ]
          exact congrArg ModuleCat.ofHom (coefficientLieDifferential_naturality R L f
            (LieModuleCat.CoefficientULift.obj.{u, v, w, max u v v' w w' z} R L M)
            (LieModuleCat.CoefficientULift.obj.{u, v', w', max u v v' w w' z} R L' M')
            (LieModuleCat.CoefficientULift.jointMap R L f M M' h) n).symm)) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  let A := (coefficientULiftDegreeEquiv.{u, v', w', max u v v' w w' z} R L' M' n).toLinearMap.comp
    ((coefficientLieComplexMapULiftAt R L f M M' h).f n).hom
  let B := (coefficientLieDegreeMap R L f
    (LieModuleCat.CoefficientULift.obj.{u, v, w, max u v v' w w' z} R L M)
    (LieModuleCat.CoefficientULift.obj.{u, v', w', max u v v' w w' z} R L' M')
    (LieModuleCat.CoefficientULift.jointMap R L f M M' h) n).comp
      (coefficientULiftDegreeEquiv.{u, v, w, max u v v' w w' z} R L M n).toLinearMap
  change A = B
  apply LinearMap.ext
  intro p
  cases p with
  | up p =>
      induction p using TensorProduct.inductionOn with
      | add p q hp hq =>
          let p₀ : (coefficientComplexULift.{u, v, w, max u v v' w w' z} R L M).X n := ULift.up p
          let q₀ : (coefficientComplexULift.{u, v, w, max u v v' w w' z} R L M).X n := ULift.up q
          change A (p₀ + q₀) = B (p₀ + q₀)
          have hp₀ : A p₀ = B p₀ := hp
          have hq₀ : A q₀ = B q₀ := hq
          exact (A.map_add p₀ q₀).trans
            ((congrArg₂ (fun x y => x + y) hp₀ hq₀).trans (B.map_add p₀ q₀).symm)
      | tmul a m =>
          change coefficientULiftDegreeEquiv.{u, v', w', max u v v' w w' z} R L' M' n
            (((coefficientLieComplexMapULiftAt R L f M M' h).f n).hom (ULift.up (a ⊗ₜ[R] m))) =
            coefficientLieDegreeMap R L f
              (LieModuleCat.CoefficientULift.obj.{u, v, w, max u v v' w w' z} R L M)
              (LieModuleCat.CoefficientULift.obj.{u, v', w', max u v v' w w' z} R L' M')
              (LieModuleCat.CoefficientULift.jointMap R L f M M' h) n
                (coefficientULiftDegreeEquiv.{u, v, w, max u v v' w w' z} R L M n (ULift.up (a ⊗ₜ[R] m)))
          rw [coefficientLieComplexMapULiftAt_up_tmul, coefficientULiftDegreeEquiv_up_tmul,
            coefficientULiftDegreeEquiv_up_tmul, coefficientLieDegreeMap_tmul]
          rfl

/-- The joint CE homology map between lifted carrier objects.

Transport the homology map of the lifted joint chain map through the full-complex homology
lift isomorphisms. -/
def coefficientRawHomologyMapAt (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((coefficientComplex R L M).homology n) ⟶
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v' w'} R).obj
      ((coefficientComplex R L' M').homology n) :=
  (coefficientHomologyULiftIso.{u, v, w, max u v v' w w' z} R L M n).hom ≫
      HomologicalComplex.homologyMap (coefficientLieComplexMapULiftAt R L f M M' h) n ≫
        (coefficientHomologyULiftIso.{u, v', w', max u v v' w w' z} R L' M' n).inv

/-- The joint CE homology map on independent unlifted carriers.

The lifted joint homology map, composed with coefficient-carrier up and down equivalences,
gives a ground-linear map between the unlifted homology carriers. -/
def coefficientOriginalHomologyMapAt (n : ℕ) :
    (coefficientComplex R L M).homology n →ₗ[R] (coefficientComplex R L' M').homology n :=
  (ULift.moduleEquiv : ULift.{max u v v' w w' z} ((coefficientComplex R L' M').homology n) ≃ₗ[R]
    (coefficientComplex R L' M').homology n).toLinearMap.comp
      ((coefficientRawHomologyMapAt R L f M M' h n).hom.comp
        (coefficientHomologyCarrierLiftEquiv.{u, v, w, max u v v' w w' z} R L M n).toLinearMap)

end JointMaps

end ChevalleyEilenberg
