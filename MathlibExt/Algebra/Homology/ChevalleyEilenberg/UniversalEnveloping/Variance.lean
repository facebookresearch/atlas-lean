/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.ExtComparison
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RightCoefficients
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.LieNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ExactPrecomposition

/-!
# Lie and coefficient maps of enveloping chains

Let `f : L → L'` be a Lie homomorphism over a commutative ring `R`, and let `U(f) : U_R(L) →
U_R(L')` be its induced enveloping map. A right coefficient map semilinear over `U(f)ᵐᵒᵖ` is
ground-linear and intertwines the negative generator Lie actions. It induces the coefficient
chain map `w ⊗ m ↦ ⋀ⁿ(f)(w) ⊗ g(m)`.

For regular coefficients the degree map is semilinear over `U(f)` and commutes with the
differential. If the underlying modules of `L` and `L'` are free, universe lifts bundle these
maps from the source resolution to scalar restriction of the target resolution. The induced
trivial-module map and augmentation square retain the scalar augmentation values. The two Lie-
carrier universes are independent.
-/

@[expose] public section

noncomputable section

universe u v v' w

open CategoryTheory MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local instance] LieRing.ofAssociativeRing rightRegularLieRingModule rightRegularLieModule
attribute [local implicit_reducible] coefficientComplex

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]
  {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  (f : L →ₗ⁅R⁆ L')

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "U'" => UniversalEnvelopingAlgebra R L'

variable {N : ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ}
  {N' : ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L')ᵐᵒᵖ}
    (g : N →ₛₗ[((UniversalEnvelopingAlgebra.map R f).toRingHom).op] N')

/-- Ground-linearity of a semilinear right coefficient map.

If `g : N → N'` is semilinear over the opposite of `U(f)`, the scalar equation
`U(f)(algebraMap(R,U)(r)) = algebraMap(R,U')(r)` makes `g` an `R`-linear coefficient map. -/
def rightCoefficientGroundMap : N →ₗ[R] N' where
  toFun := g
  map_add' := g.map_add
  map_smul' r m := by
    change g (op (algebraMap R U r) • m) = op (algebraMap R U' r) • g m
    rw [g.map_smulₛₗ]
    change op (UniversalEnvelopingAlgebra.map R f (algebraMap R U r)) • g m = _
    rw [(UniversalEnvelopingAlgebra.map R f).commutes]

/-- Lie compatibility of a semilinear right coefficient map.

For `f : L → L'`, a coefficient map semilinear over `U(f)ᵐᵒᵖ` intertwines the negative right-
generator action of `L` with the action of `L'` restricted along `f`. -/
def rightCoefficientLieMap :
    rightCoefficients R L N →ₗ⁅R,L⁆ LieModuleCat.restrictObj f (rightCoefficients R L' N') where
  toLinearMap := rightCoefficientGroundMap R L f g
  map_lie' := by
    intro x m
    change g (-(op (UniversalEnvelopingAlgebra.ι R x) • m)) =
      -(op (UniversalEnvelopingAlgebra.ι R (f x)) • g m)
    rw [map_neg, g.map_smulₛₗ]
    change -(op (UniversalEnvelopingAlgebra.map R f (UniversalEnvelopingAlgebra.ι R x)) • g m) = _
    rw [UniversalEnvelopingAlgebra.map_ι]

/-- The joint Lie-and-right-coefficient chain map.

A Lie map `f` and a right coefficient map semilinear over `U(f)ᵐᵒᵖ` induce a chain map between
their Chevalley–Eilenberg coefficient complexes in the common coefficient universe. -/
def rightEnvelopingCoefficientLieComplexMap :
    rightEnvelopingCoefficientComplex R L N ⟶ rightEnvelopingCoefficientComplex R L' N' :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom
      (coefficientLieDegreeMap R L f (rightCoefficients R L N) (rightCoefficients R L' N')
        (rightCoefficientLieMap R L f g) n)) (fun n => by
      simp only [coefficientComplex_d_succ]
      exact congrArg ModuleCat.ofHom
        (coefficientLieDifferential_naturality R L f (rightCoefficients R L N)
          (rightCoefficients R L' N') (rightCoefficientLieMap R L f g) n).symm)

/-- The tensor formula for a jointly varying right coefficient map.

In degree `n`, the induced chain map sends `a ⊗ m` to `⋀ⁿ(f)(a) ⊗ g(m)`. -/
theorem rightEnvelopingCoefficientLieComplexMap_f_tmul (n : ℕ) (a : ⋀[R]^n L) (m : N) :
    ((rightEnvelopingCoefficientLieComplexMap R L f g).f n).hom (a ⊗ₜ[R] (show rightCoefficients R L N from m)) =
      exteriorPower.map n f.toLinearMap a ⊗ₜ[R] (show rightCoefficients R L' N' from g m) :=
  coefficientLieDegreeMap_tmul R L f (rightCoefficients R L N) (rightCoefficients R L' N')
    (rightCoefficientLieMap R L f g) n a m

/-- The regular coefficient Lie map induced by a Lie homomorphism.

For `f : L → L'`, the enveloping algebra map `U(f)` intertwines the regular coefficient
actions `[x,a] = -aι(x)` along `f`. -/
def envelopingRegularLieMap :
    regularCoefficients R L →ₗ⁅R,L⁆ LieModuleCat.restrictObj f (regularCoefficients R L') where
  toLinearMap := (UniversalEnvelopingAlgebra.map R f).toLinearMap
  map_lie' := by
    intro x a
    change UniversalEnvelopingAlgebra.map R f (-(a * UniversalEnvelopingAlgebra.ι R x)) =
      -(UniversalEnvelopingAlgebra.map R f a * UniversalEnvelopingAlgebra.ι R (f x))
    rw [map_neg, map_mul, UniversalEnvelopingAlgebra.map_ι]

/-- The left enveloping action on an exterior-first chain tensor.

For `a, b ∈ U_R(L)` and `x ∈ ⋀ⁿ L`, the enveloping scalar action satisfies `a • (x ⊗ b) = x ⊗
(a*b)`. -/
theorem enveloping_smul_tmul (n : ℕ) (a : U) (b : regularCoefficients R L) (x : ⋀[R]^n L) :
    @SMul.smul U ((envelopingComplex R L).X n)
      ((envelopingComplex R L).X n).isModule.toDistribMulAction.toMulAction.toSMul
      a (x ⊗ₜ[R] b) = (x ⊗ₜ[R] (a * (show U from b)) : (envelopingComplex R L).X n) := by
  change coefficientDegreeRingAction R L (regularCoefficients R L)
      (regularLeftAction R L) (regularLeftAction_lie R L) n a (x ⊗ₜ[R] b) = _
  rw [coefficientDegreeRingAction_apply, coefficientComplexRingAction_f_tmul]
  rfl

/-- The semilinear enveloping chain-term map of a Lie homomorphism.

For `f : L → L'`, the degree-`n` map combines `⋀ⁿ(f)` with `U(f)` and is semilinear over the
ring homomorphism `U(f)`. -/
def envelopingLieTermMap (n : ℕ) :
    (envelopingComplex R L).X n →ₛₗ[((UniversalEnvelopingAlgebra.map R f).toRingHom)] (envelopingComplex R L').X n where
  toFun := coefficientLieDegreeMap R L f (regularCoefficients R L) (regularCoefficients R L')
    (envelopingRegularLieMap R L f) n
  map_add' := (coefficientLieDegreeMap R L f (regularCoefficients R L) (regularCoefficients R L')
    (envelopingRegularLieMap R L f) n).map_add
  map_smul' a z := by
    let A := coefficientLieDegreeMap R L f (regularCoefficients R L) (regularCoefficients R L')
      (envelopingRegularLieMap R L f) n
    letI : Module U ((envelopingComplex R L).X n) := ((envelopingComplex R L).X n).isModule
    letI : Module U' ((envelopingComplex R L').X n) := ((envelopingComplex R L').X n).isModule
    change A (a • (show (envelopingComplex R L).X n from z)) =
      UniversalEnvelopingAlgebra.map R f a • (show (envelopingComplex R L').X n from A z)
    induction z using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
    | tmul x b =>
        have hSource := enveloping_smul_tmul R L n a b x
        have hTarget := enveloping_smul_tmul R L' n
          (UniversalEnvelopingAlgebra.map R f a) (UniversalEnvelopingAlgebra.map R f b)
          (exteriorPower.map n f.toLinearMap x)
        have hMap := coefficientLieDegreeMap_tmul R L f (regularCoefficients R L)
          (regularCoefficients R L') (envelopingRegularLieMap R L f) n x (a * b)
        have hWord := coefficientLieDegreeMap_tmul R L f (regularCoefficients R L)
          (regularCoefficients R L') (envelopingRegularLieMap R L f) n x b
        have hMul := (UniversalEnvelopingAlgebra.map R f).map_mul a b
        exact (congrArg A hSource).trans
          (hMap.trans ((congrArg (fun y : regularCoefficients R L' =>
            exteriorPower.map n f.toLinearMap x ⊗ₜ[R] y) hMul).trans
              (hTarget.symm.trans (congrArg (fun y : (envelopingComplex R L').X n =>
                UniversalEnvelopingAlgebra.map R f a • y) hWord.symm))))


/-- The exterior-and-enveloping tensor formula for a Lie term map.

The map induced by `f` sends `a ⊗ u` to `⋀ⁿ(f)(a) ⊗ U(f)(u)`. -/
theorem envelopingLieTermMap_tmul (n : ℕ) (a : ⋀[R]^n L) (u : regularCoefficients R L) :
    envelopingLieTermMap R L f n (a ⊗ₜ[R] u) =
      exteriorPower.map n f.toLinearMap a ⊗ₜ[R] UniversalEnvelopingAlgebra.map R f u :=
  coefficientLieDegreeMap_tmul R L f (regularCoefficients R L) (regularCoefficients R L')
    (envelopingRegularLieMap R L f) n a u

/-- Differential compatibility of semilinear enveloping Lie maps.

The degree maps induced by a Lie homomorphism commute with the enveloping Chevalley–Eilenberg
successor differentials. -/
theorem envelopingLieTermMap_d_apply (n : ℕ) (z : (envelopingComplex R L).X (n + 1)) :
    envelopingLieTermMap R L f n (((envelopingComplex R L).d (n + 1) n).hom z) =
      ((envelopingComplex R L').d (n + 1) n).hom (envelopingLieTermMap R L f (n + 1) z) := by
  have hS := envelopingComplex_d_succ_apply R L n z
  have hT := envelopingComplex_d_succ_apply R L' n (envelopingLieTermMap R L f (n + 1) z)
  refine (congrArg (envelopingLieTermMap R L f n) hS).trans ?_
  refine Eq.trans ?_ hT.symm
  exact LinearMap.congr_fun
    (coefficientLieDifferential_naturality R L f (regularCoefficients R L) (regularCoefficients R L')
      (envelopingRegularLieMap R L f) n) z

section LiftedResolution

variable [Module.Free R L] [Module.Free R L']


/-- The lifted semilinear map between enveloping resolution terms.

For free underlying modules of `L` and `L'`, lifting the semilinear Lie term map gives a map
between their resolution terms in the joint carrier universe. -/
def liftedEnvelopingLieTermMap (n : ℕ) :
    (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex.X n
      →ₛₗ[((UniversalEnvelopingAlgebra.map R f).toRingHom)]
      (liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').complex.X n :=
  (ULift.moduleEquiv : ULift.{max u v v' w} ((envelopingComplex R L').X n) ≃ₗ[U']
    (envelopingComplex R L').X n).symm.toLinearMap.comp
      ((envelopingLieTermMap R L f n).comp
        (ULift.moduleEquiv : ULift.{max u v v' w} ((envelopingComplex R L).X n) ≃ₗ[U]
          (envelopingComplex R L).X n).toLinearMap)

/-- The coefficient formula for a lifted enveloping Lie map.

The lifted degree map sends `ULift.up z` to `ULift.up` of the enveloping Lie term map applied
to `z`. -/
theorem liftedEnvelopingLieTermMap_up (n : ℕ) (z : (envelopingComplex R L).X n) :
    liftedEnvelopingLieTermMap R L f n (ULift.up z) = ULift.up (envelopingLieTermMap R L f n z) := rfl

/-- The Lie-induced map into a scalar-restricted target resolution.

For free underlying modules of `L` and `L'`, the lifted degree maps form a chain map from the
source enveloping resolution to the target resolution restricted along `U(f)`. -/
def liftedEnvelopingLieComplexMap :
    (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex ⟶
      ((ModuleCat.restrictScalars ((UniversalEnvelopingAlgebra.map R f).toRingHom)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
      (liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').complex where
  f n := ModuleCat.semilinearMapAddEquiv ((UniversalEnvelopingAlgebra.map R f).toRingHom)
    ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex.X n)
    ((liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').complex.X n)
    (liftedEnvelopingLieTermMap R L f n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    ext z
    change ULift.up (((envelopingComplex R L').d (j + 1) j).hom
      (envelopingLieTermMap R L f (j + 1) z.down)) =
        ULift.up (envelopingLieTermMap R L f j
          (((envelopingComplex R L).d (j + 1) j).hom z.down))
    exact (congrArg ULift.up (envelopingLieTermMap_d_apply R L f j z.down)).symm

/-- The scalar-preserving map of lifted trivial enveloping modules.

For a Lie map `f`, the lifted trivial-module map takes values in restriction of the target
along `U(f)` and retains the twice-lifted scalar value. Its linearity follows from
augmentation naturality. -/
def liftedEnvelopingTrivialLieMap :
    liftedEnvelopingTrivial.{u, v, max u v v' w} R L ⟶
      (ModuleCat.restrictScalars ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj
        (liftedEnvelopingTrivial.{u, v', max u v v' w} R L') :=
  ModuleCat.ofHom
    (X := liftedEnvelopingTrivial.{u, v, max u v v' w} R L)
    (Y := (ModuleCat.restrictScalars ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj
      (liftedEnvelopingTrivial.{u, v', max u v v' w} R L'))
    { toFun := fun x => ULift.up (ULift.up x.down.down)
      map_add' x y := rfl
      map_smul' u x := by
        apply ULift.ext
        apply ULift.ext
        change UniversalEnvelopingAlgebra.augmentation R L u * x.down.down =
          UniversalEnvelopingAlgebra.augmentation R L'
            (UniversalEnvelopingAlgebra.map R f u) * x.down.down
        have h := congrArg (fun a : U →ₐ[R] R => a u)
          (UniversalEnvelopingAlgebra.augmentation_naturality R f)
        change UniversalEnvelopingAlgebra.augmentation R L'
          (UniversalEnvelopingAlgebra.map R f u) = UniversalEnvelopingAlgebra.augmentation R L u at h
        rw [h] }

omit [Module.Free R L] [Module.Free R L'] in
/-- The scalar coordinate of a Lie-induced exterior-degree-zero map.

For `f : L → L'`, the exterior-degree-zero map preserves the regular-ring coordinate under
`⋀⁰[R] L ≃ₗ[R] R` and `⋀⁰[R] L' ≃ₗ[R] R`. -/
theorem exteriorZeroCoordinates_map (x : ⋀[R]^0 L) :
    exteriorPower.zeroEquiv R L' (exteriorPower.map 0 f.toLinearMap x) =
      exteriorPower.zeroEquiv R L x := by
  exact LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality f.toLinearMap) x

/-- The tensor formula for a lifted enveloping augmentation.

In degree zero, the lifted augmentation sends `up(x ⊗ u)` to the twice-lifted scalar
`(exteriorPower.zeroEquiv x) • ε(u)`, where `ε : U_R(L) → R` is the enveloping augmentation. -/
theorem liftedEnvelopingAugmentation_tmul (x : ⋀[R]^0 L) (u : regularCoefficients R L) :
    ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).π.f 0).hom (ULift.up (x ⊗ₜ[R] u)) =
      ULift.up (ULift.up ((exteriorPower.zeroEquiv R L x) •
        UniversalEnvelopingAlgebra.augmentation R L u)) := by
  rw [liftedEnvelopingProjectiveResolution_π_f_zero.{u, v, max u v v' w}]
  change ULift.up ((envelopingAugmentation R L).f 0
    (x ⊗ₜ[R] u)) = _
  rw [envelopingAugmentation_f_zero]
  let p : (envelopingComplex R L).X 0 := x ⊗ₜ[R] u
  have h := envelopingAugmentationComponent_apply R L p
  have hZero := envelopingZeroEquiv_tmul R L x u
  have hValue : envelopingAugmentationComponent R L p =
      ULift.up ((exteriorPower.zeroEquiv R L x) • UniversalEnvelopingAlgebra.augmentation R L u) :=
    h.trans (congrArg ULift.up
      ((congrArg (UniversalEnvelopingAlgebra.augmentation R L) hZero).trans
        ((UniversalEnvelopingAlgebra.augmentation R L).toLinearMap.map_smul _ _)))
  exact congrArg ULift.up hValue

/-- The augmentation square for lifted enveloping Lie maps.

For a Lie map between free underlying modules, the lifted resolution map followed by the
restricted target augmentation equals the source augmentation followed by the lifted trivial-
module map. -/
theorem liftedEnvelopingLieComplexMap_augmentation :
    liftedEnvelopingLieComplexMap R L f ≫ Functor.mapChainAugmentation
      (ModuleCat.restrictScalars ((UniversalEnvelopingAlgebra.map R f).toRingHom))
        (liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').π =
      (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).π ≫
        (ChainComplex.single₀ (ModuleCat.{max u v v' w} U)).map
        (liftedEnvelopingTrivialLieMap R L f) := by
  apply (ChainComplex.toSingle₀Equiv (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex
    ((ModuleCat.restrictScalars ((UniversalEnvelopingAlgebra.map R f).toRingHom)).obj
      (liftedEnvelopingTrivial.{u, v', max u v v' w} R L'))).injective
  apply Subtype.ext
  change (liftedEnvelopingLieComplexMap R L f).f 0 ≫
      (Functor.mapChainAugmentation (ModuleCat.restrictScalars ((UniversalEnvelopingAlgebra.map R f).toRingHom))
        (liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').π).f 0 =
    (liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).π.f 0 ≫ liftedEnvelopingTrivialLieMap R L f
  rw [Functor.mapChainAugmentation_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let A := ((liftedEnvelopingLieComplexMap R L f).f 0 ≫
    (ModuleCat.restrictScalars ((UniversalEnvelopingAlgebra.map R f).toRingHom)).map
      ((liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').π.f 0)).hom
  let B := ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).π.f 0 ≫
    liftedEnvelopingTrivialLieMap R L f).hom
  change A z = B z
  cases z with
  | up z =>
      induction z using TensorProduct.induction_on with
      | zero =>
          change A 0 = B 0
          exact A.map_zero.trans B.map_zero.symm
      | add z z' hz hz' =>
          change A (ULift.up z + ULift.up z') = B (ULift.up z + ULift.up z')
          exact (A.map_add _ _).trans ((congrArg₂ (fun x y => x + y) hz hz').trans
            (B.map_add _ _).symm)
      | tmul x u =>
          change ((liftedEnvelopingProjectiveResolution.{u, v', max u v v' w} R L').π.f 0).hom
            (ULift.up (envelopingLieTermMap R L f 0 (x ⊗ₜ[R] u))) =
              (liftedEnvelopingTrivialLieMap R L f).hom
                (((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).π.f 0).hom
                  (ULift.up (x ⊗ₜ[R] u)))
          rw [envelopingLieTermMap_tmul, liftedEnvelopingAugmentation_tmul.{u, v', v, w},
            liftedEnvelopingAugmentation_tmul.{u, v, v', w}, exteriorZeroCoordinates_map]
          apply ULift.ext
          apply ULift.ext
          have h := congrArg (fun a : U →ₐ[R] R => a u)
            (UniversalEnvelopingAlgebra.augmentation_naturality R f)
          change UniversalEnvelopingAlgebra.augmentation R L'
            (UniversalEnvelopingAlgebra.map R f u) = UniversalEnvelopingAlgebra.augmentation R L u at h
          rw [h]
          rfl

end LiftedResolution

end ChevalleyEilenberg
