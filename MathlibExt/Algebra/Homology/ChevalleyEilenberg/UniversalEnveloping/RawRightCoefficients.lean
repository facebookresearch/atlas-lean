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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RawCoefficientHeightNaturality
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.RightCoefficients

/-!
# Right Lie coefficients and enveloping Tor

A right Lie module over a commutative ground ring extends to a right enveloping module whose
generator action is the given right Lie action. Its coefficient-first Chevalley–Eilenberg
chains are `M ⊗[R] (⋀[R]^n L)`.

For a free underlying Lie module, coefficient homology identifies with enveloping Tor against
the trivial module. The comparisons, degree-zero tensor classes, and compatible
Lie/coefficient maps retain the ground-ring action and allow independent carrier universes.
-/

@[expose] public section

noncomputable section

universe u v v' w w' z t a b c

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex coefficientComplexULift rightCoefficientComplex
  rightCoefficientComplexULift HomologicalComplex.homologyFunctor rawLieCoefficientLiftAt

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  (A : RightLieModuleCat.{w} R L)

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "M" => RightLieModuleCat.toLeft A

local instance rawRightHomologySourceLift_preservesHomology {A : Type a} [Ring A] :
    (ModuleCat.uliftFunctor.{c, b} A).PreservesHomology := Functor.preservesHomologyOfExact _
local instance rawRightTensor_additive {A : Type a} [Ring A] [Algebra R A]
    (N : ModuleCat.{b} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, a, b, c} R A N).Additive :=
  ModuleCat.BalancedTensor.additive R A N

/-- The coefficient-carrier lift, expressed as a right Lie module on the lift of the raw right
coefficient. -/
def rawRightLieCoefficientLiftAt : RightLieModuleCat.{max u v v' w w' z} R L :=
  RightLieModuleCat.fromLeft (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)

@[simp]
theorem rawRightLieCoefficientLiftAt_act_up (m : A) (x : L) :
    RightLieModuleCat.act (rawRightLieCoefficientLiftAt.{u, v, v', w, w', z} R L A)
      (ULift.up m) x = ULift.up (RightLieModuleCat.act A m x) := by
  change ULift.up (-(-(A.action x m))) = ULift.up (A.action x m)
  rw [neg_neg]

/-- The enveloping algebra coefficient object on the lifted right Lie carrier, with the
representation constructed from its negative-left structure. -/
abbrev rawRightEnvelopingCoefficientsAt : ModuleCat.{max u v v' w w' z} Uᵐᵒᵖ :=
  LieModuleCat.RightUniversalEnveloping.representObj R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)

theorem rawRightEnvelopingCoefficientsAt_op_ι_up (m : A) (x : L) :
    @SMul.smul Uᵐᵒᵖ (rawRightEnvelopingCoefficientsAt.{u, v, v', w, w', z} R L A)
      (rawRightEnvelopingCoefficientsAt.{u, v, v', w, w', z} R L A).isModule.toDistribMulAction.toMulAction.toSMul
      (MulOpposite.op (UniversalEnvelopingAlgebra.ι R x)) (ULift.up m) =
      ULift.up (RightLieModuleCat.act A m x) := by
  have h := LieModuleCat.RightUniversalEnveloping.representObj_op_ι R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) x (ULift.up m)
  refine h.trans ?_
  change ULift.up (-(-(A.action x m))) = ULift.up (A.action x m)
  rw [neg_neg]

/-- Tor of the lifted right enveloping algebra coefficient at the trivial left module, derived in
the sufficient working universe. -/
abbrev rawRightLieCoefficientTorAt (n : ℕ) : ModuleCat.{max u v v' w w' z} R :=
  rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n

/-- The coefficient-first homology and the exterior-first negative-left homology have their tensor
comparison. -/
def rawRightCoefficientHomologyToLeftIso (n : ℕ) :
    (rightCoefficientComplex R L A).homology n ≅ (coefficientComplex R L M).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) (ComplexShape.down ℕ) n).mapIso
    (rightCoefficientComplexIso R L A)

/-- Full coefficient-first right CE/Tor comparison on the exact raw homology carrier, with
input/output up/down. -/
def rawRightCoefficientHomologyEquivTorAt [Module.Free R L] (n : ℕ) :
    (rightCoefficientComplex R L A).homology n ≃ₗ[R]
      rawRightLieCoefficientTorAt.{u, v, v', w, w', z} R L A n :=
  (rawRightCoefficientHomologyToLeftIso R L A n).toLinearEquiv.trans
    (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n)

/-- Explicit output transport to the raw coefficient-first right CE homology carrier. -/
def rawRightCoefficientTorEquivHomologyAt [Module.Free R L] (n : ℕ) :
    rawRightLieCoefficientTorAt.{u, v, v', w, w', z} R L A n ≃ₗ[R]
      (rightCoefficientComplex R L A).homology n :=
  (rawRightCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L A n).symm

/-- The tensor-coordinate comparison preserves the coefficient-first empty-exterior class. -/
theorem rawRightCoefficientHomologyToLeftIso_zero_class (m : A) :
    (rawRightCoefficientHomologyToLeftIso R L A 0).hom
      ((rightCoefficientComplex R L A).isoHomologyι₀.inv
        ((rightCoefficientComplex R L A).pOpcycles 0
          (m ⊗ₜ[R] exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L)))) =
    (coefficientComplex R L M).isoHomologyι₀.inv
      ((coefficientComplex R L M).pOpcycles 0
        (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] (show M from m))) := by
  let K := rightCoefficientComplex R L A
  let K' := coefficientComplex R L M
  let E := rightCoefficientComplexIso R L A
  let a : K.X 0 := m ⊗ₜ[R] exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L)
  have hι := congrArg (fun f : K.opcycles 0 ⟶ K'.homology 0 => f.hom ((K.pOpcycles 0).hom a))
    (ChainComplex.isoHomologyι₀_inv_naturality E.hom)
  have hp := congrArg (fun f : K.X 0 ⟶ K'.opcycles 0 => f.hom a)
    (HomologicalComplex.p_opcyclesMap E.hom 0)
  have hx := rightCoefficientComplexIso_hom_f_tmul R L A 0 m
    (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L))
  exact hι.trans (congrArg (fun b : K'.opcycles 0 => K'.isoHomologyι₀.inv.hom b)
    (hp.trans (congrArg (fun b => (K'.pOpcycles 0).hom b) hx)))

/-- Canonical H₀ comparison to the exact raw right-representation tensor with the trivial left
module. -/
def rawRightCoefficientHomologyZeroTensorEquivAt :
    (rightCoefficientComplex R L A).homology 0 ≃ₗ[R]
      (ModuleCat.BalancedTensor.functor R U
        (LieModuleCat.RightUniversalEnveloping.representObj R L M)).obj (envelopingTrivialObject R L) :=
  (rawRightCoefficientHomologyToLeftIso R L A 0).toLinearEquiv.trans
    (rawCoefficientHomologyZeroTensorEquivAt.{u, v, v', w, w', z} R L M)

/-- The coefficient-first class keeps the raw right coefficient and scalar unit. -/
theorem rawRightCoefficientHomologyZeroTensorEquivAt_class (m : A) :
    rawRightCoefficientHomologyZeroTensorEquivAt.{u, v, v', w, w', z} R L A
      ((rightCoefficientComplex R L A).isoHomologyι₀.inv
        ((rightCoefficientComplex R L A).pOpcycles 0
          (m ⊗ₜ[R] exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L)))) =
    TensorProduct.Balanced.mk R U (LieModuleCat.RightUniversalEnveloping.representObj R L M)
      ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L))
        m (ULift.up (1 : R)) := by
  change rawCoefficientHomologyZeroTensorEquivAt.{u, v, v', w, w', z} R L M
    ((rawRightCoefficientHomologyToLeftIso R L A 0).hom
      ((rightCoefficientComplex R L A).isoHomologyι₀.inv
        ((rightCoefficientComplex R L A).pOpcycles 0
          (m ⊗ₜ[R] exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L))))) = _
  rw [rawRightCoefficientHomologyToLeftIso_zero_class, rawCoefficientHomologyZeroTensorEquivAt_class]

/-- The derived-zero map agrees with the canonical coefficient-first H₀ comparison, after input
and output transport. -/
theorem rawRightCoefficientHomologyEquivTorAt_zero_original [Module.Free R L]
    (a : (rightCoefficientComplex R L A).homology 0) :
    let N := rawRightEnvelopingCoefficientsAt.{u, v, v', w, w', z} R L A
    let F := (ModuleCat.BalancedTensor.functor R U N :
      ModuleCat.{max u v v' w w' z} U ⥤ ModuleCat.{max u v v' w w' z} R)
    letI : F.Additive := ModuleCat.BalancedTensor.additive R U N
    rawCoefficientTrivialTensorEquiv.{u, v, v', w, w', z} R L M
      (rightTrivialTensorLiftEquiv.{u, v, v', max w w' z} R L N
        ((F.fromLeftDerivedZero.app (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L)).hom
          (rawRightCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L A 0 a))) =
    rawRightCoefficientHomologyZeroTensorEquivAt.{u, v, v', w, w', z} R L A a :=
  rawCoefficientHomologyEquivTorAt_zero_original.{u, v, v', w, w', z} R L M
    ((rawRightCoefficientHomologyToLeftIso R L A 0).toLinearEquiv a)

/-- The raw coefficient-first comparison commutes with the canonical Tor height map, retaining the
same homology value. -/
theorem rawRightCoefficientHomologyEquivTorAt_height [Module.Free R L] (n : ℕ)
    (a : (rightCoefficientComplex R L A).homology n) :
    (rawLieCoefficientTorHeightIsoAt.{u, v, v', w, w', z, t} R L M n).inv
      (rawRightCoefficientHomologyEquivTorAt.{u, v, v', w, w', max z t} R L A n a) =
    ULift.up (rawRightCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L A n a) :=
  rawCoefficientHomologyEquivTorAt_height.{u, v, v', w, w', z, t} R L M n
    ((rawRightCoefficientHomologyToLeftIso R L A n).toLinearEquiv a)

section JointMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L')
  (A' : RightLieModuleCat.{w'} R L') (g : RightLieModuleCat.HomOver f A A')

local notation "M'" => RightLieModuleCat.toLeft A'
local notation "h" => rightCoefficientLieMapToLeft R L f A A' g

/-- The joint map on the two lifted right coefficient carriers, with its right-action
compatibility from the map. -/
def rawRightLieCoefficientMapAt : RightLieModuleCat.HomOver f
    (rawRightLieCoefficientLiftAt.{u, v, v', w, w', z} R L A)
    (rawRightLieCoefficientLiftAt.{u, v', v, w', w, z} R L' A') :=
  ⟨(ULift.moduleEquiv : ULift.{max u v v' w w' z} A' ≃ₗ[R] A').symm.toLinearMap.comp
    (g.toLinearMap.comp (ULift.moduleEquiv : ULift.{max u v v' w w' z} A ≃ₗ[R] A).toLinearMap), by
      intro x m
      cases m with
      | up m =>
          have hSource := rawRightLieCoefficientLiftAt_act_up.{u, v, v', w, w', z} R L A m x
          have hTarget := rawRightLieCoefficientLiftAt_act_up.{u, v', v, w', w, z} R L' A'
            (g.toLinearMap m) (f x)
          refine (congrArg ((ULift.moduleEquiv : ULift.{max u v v' w w' z} A' ≃ₗ[R] A').symm.toLinearMap.comp
            (g.toLinearMap.comp (ULift.moduleEquiv : ULift.{max u v v' w w' z} A ≃ₗ[R] A).toLinearMap))
              hSource).trans ?_
          exact (congrArg ULift.up (g.map_action x m)).trans hTarget.symm⟩

@[simp]
theorem rawRightLieCoefficientMapAt_up (m : A) :
    (rawRightLieCoefficientMapAt.{u, v, v', w, w', z} R L A f A' g).toLinearMap (ULift.up m) =
      ULift.up (g.toLinearMap m) := rfl

/-- The coefficient-first right CE map at the true maximum working universe, through the right and
left CE lift adapters. -/
def rawRightCoefficientLieComplexMapULiftAt :
    rightCoefficientComplexULift.{u, v, w, max u v v' w w' z} R L A ⟶
      rightCoefficientComplexULift.{u, v', w', max u v v' w w' z} R L' A' :=
  (rightCoefficientComplexIsoULift.{u, v, w, max u v v' w w' z} R L A).hom ≫
    coefficientLieComplexMapULiftAt.{u, v, w, z, v', w'} R L f M M' h ≫
      (rightCoefficientComplexIsoULift.{u, v', w', max u v v' w w' z} R L' A').inv

@[simp]
theorem rawRightCoefficientLieComplexMapULiftAt_up_tmul (n : ℕ) (m : A) (a : ⋀[R]^n L) :
    ((rawRightCoefficientLieComplexMapULiftAt.{u, v, v', w, w', z} R L A f A' g).f n).hom (ULift.up (m ⊗ₜ[R] a)) =
      ULift.up (g.toLinearMap m ⊗ₜ[R] exteriorPower.map n f.toLinearMap a) := by
  let e := (rightCoefficientComplexIsoULift.{u, v, w, max u v v' w w' z} R L A).hom.f n
  let c := (coefficientLieComplexMapULiftAt.{u, v, w, z, v', w'} R L f M M' h).f n
  let e' := (rightCoefficientComplexIsoULift.{u, v', w', max u v v' w w' z} R L' A').inv.f n
  let p : (rightCoefficientComplexULift.{u, v, w, max u v v' w w' z} R L A).X n :=
    ULift.up (m ⊗ₜ[R] a)
  have h₀ := rightCoefficientComplexIsoULift_hom_f_tmul.{u, v, w, max u v v' w w' z} R L A n m a
  have h₁ := coefficientLieComplexMapULiftAt_up_tmul.{u, v, w, v', w', z} R L f M M' h n a m
  have h₂ := rightCoefficientComplexIsoULift_inv_f_tmul.{u, v', w', max u v v' w w' z} R L' A' n
    (exteriorPower.map n f.toLinearMap a) (h m)
  change e'.hom (c.hom (e.hom p)) = _
  exact (congrArg (fun q => e'.hom (c.hom q)) h₀).trans
    ((congrArg e'.hom h₁).trans h₂)

/-- Homology map of the coefficient-first right CE variance map, with homology-lift input/output
comparisons. -/
def rawRightCoefficientHomologyMapAt (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((rightCoefficientComplex R L A).homology n) ⟶
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v' w'} R).obj
      ((rightCoefficientComplex R L' A').homology n) :=
  (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R)).inv.app
      (rightCoefficientComplex R L A) ≫
    HomologicalComplex.homologyMap (rawRightCoefficientLieComplexMapULiftAt.{u, v, v', w, w', z} R L A f A' g) n ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
        (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v' w'} R)).hom.app
          (rightCoefficientComplex R L' A')

private theorem rawRightCoefficientHomologyMapAt_tensor_coordinates (n : ℕ) :
    rawRightCoefficientHomologyMapAt.{u, v, v', w, w', z} R L A f A' g n =
      (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).map
        (rawRightCoefficientHomologyToLeftIso R L A n).hom ≫
      rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n ≫
        (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v' w'} R).map
          (rawRightCoefficientHomologyToLeftIso R L' A' n).inv := by
  let V := ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R
  let V' := ModuleCat.uliftFunctor.{max u v v' w w' z, max u v' w'} R
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact V
  letI : V'.PreservesHomology := Functor.preservesHomologyOfExact V'
  let m := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V
  let m' := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V'
  have hs := (m.inv.naturality (rightCoefficientComplexIso R L A).hom).symm
  have ht := m'.hom.naturality (rightCoefficientComplexIso R L' A').inv
  let K := rightCoefficientComplex R L A
  let K' := rightCoefficientComplex R L' A'
  let C := coefficientComplex R L M
  let C' := coefficientComplex R L' M'
  let E := (rightCoefficientComplexIsoULift.{u, v, w, max u v v' w w' z} R L A).hom
  let E' := (rightCoefficientComplexIsoULift.{u, v', w', max u v v' w w' z} R L' A').inv
  let c := coefficientLieComplexMapULiftAt.{u, v, w, z, v', w'} R L f M M' h
  have hs' : m.inv.app K ≫ HomologicalComplex.homologyMap E n =
      V.map (rawRightCoefficientHomologyToLeftIso R L A n).hom ≫ m.inv.app C := hs
  have ht' : HomologicalComplex.homologyMap E' n ≫ m'.hom.app K' =
      m'.hom.app C' ≫ V'.map (rawRightCoefficientHomologyToLeftIso R L' A' n).inv := ht
  have hMap : rawRightCoefficientHomologyMapAt.{u, v, v', w, w', z} R L A f A' g n =
      m.inv.app K ≫ (HomologicalComplex.homologyMap E n ≫
        HomologicalComplex.homologyMap c n ≫ HomologicalComplex.homologyMap E' n) ≫ m'.hom.app K' := by
    exact congrArg (fun q => m.inv.app K ≫ q ≫ m'.hom.app K')
      ((HomologicalComplex.homologyMap_comp E (c ≫ E') n).trans
        (congrArg (fun q => HomologicalComplex.homologyMap E n ≫ q)
          (HomologicalComplex.homologyMap_comp c E' n)))
  have hLeft : m.inv.app K ≫ (HomologicalComplex.homologyMap E n ≫
      HomologicalComplex.homologyMap c n ≫ HomologicalComplex.homologyMap E' n) ≫ m'.hom.app K' =
    (m.inv.app K ≫ HomologicalComplex.homologyMap E n) ≫
      HomologicalComplex.homologyMap c n ≫ (HomologicalComplex.homologyMap E' n ≫ m'.hom.app K') := by
    simp only [Category.assoc]
  have hCalc : (m.inv.app K ≫ HomologicalComplex.homologyMap E n) ≫
      HomologicalComplex.homologyMap c n ≫ (HomologicalComplex.homologyMap E' n ≫ m'.hom.app K') =
    V.map (rawRightCoefficientHomologyToLeftIso R L A n).hom ≫
      rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n ≫
        V'.map (rawRightCoefficientHomologyToLeftIso R L' A' n).inv := by
    have hRaw : rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n =
        m.inv.app C ≫ HomologicalComplex.homologyMap c n ≫ m'.hom.app C' := rfl
    have hAssoc :
        (V.map (rawRightCoefficientHomologyToLeftIso R L A n).hom ≫ m.inv.app C) ≫
          HomologicalComplex.homologyMap c n ≫
            (m'.hom.app C' ≫ V'.map (rawRightCoefficientHomologyToLeftIso R L' A' n).inv) =
        V.map (rawRightCoefficientHomologyToLeftIso R L A n).hom ≫
          (m.inv.app C ≫ HomologicalComplex.homologyMap c n ≫ m'.hom.app C') ≫
            V'.map (rawRightCoefficientHomologyToLeftIso R L' A' n).inv := by
      simp only [Category.assoc]
    exact (congrArg₂ (fun f g => f ≫ HomologicalComplex.homologyMap c n ≫ g) hs' ht').trans
      (hAssoc.trans
        (congrArg (fun q => V.map (rawRightCoefficientHomologyToLeftIso R L A n).hom ≫ q ≫
          V'.map (rawRightCoefficientHomologyToLeftIso R L' A' n).inv) hRaw.symm))
  exact hMap.trans (hLeft.trans hCalc)

/-- Ground-linear right CE homology map with independently sized coefficient-first carriers,
carried through up/down. -/
def rawOriginalRightCoefficientHomologyMapAt (n : ℕ) :
    (rightCoefficientComplex R L A).homology n →ₗ[R] (rightCoefficientComplex R L' A').homology n :=
  (ULift.moduleEquiv : ULift.{max u v v' w w' z} ((rightCoefficientComplex R L' A').homology n) ≃ₗ[R]
    (rightCoefficientComplex R L' A').homology n).toLinearMap.comp
      ((rawRightCoefficientHomologyMapAt.{u, v, v', w, w', z} R L A f A' g n).hom.comp
        (ULift.moduleEquiv : ULift.{max u v v' w w' z} ((rightCoefficientComplex R L A).homology n) ≃ₗ[R]
          (rightCoefficientComplex R L A).homology n).symm.toLinearMap)

/-- The canonical joint right-coefficient Tor map is the derived square on the right enveloping
algebra representations, independently of CE. -/
def rawRightLieCoefficientTorMapAt (n : ℕ) :
    rawRightLieCoefficientTorAt.{u, v, v', w, w', z} R L A n ⟶
      rawRightLieCoefficientTorAt.{u, v', v, w', w, z} R L' A' n :=
  rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n

/-- Full joint naturality of the coefficient-first right CE/Tor comparison on its exact raw
homology carriers. -/
theorem rawRightCoefficientHomologyEquivTorAt_naturality
    [Module.Free R L] [Module.Free R L'] (n : ℕ) :
    (rawRightCoefficientHomologyEquivTorAt.{u, v', v, w', w, z} R L' A' n).toLinearMap.comp
      (rawOriginalRightCoefficientHomologyMapAt.{u, v, v', w, w', z} R L A f A' g n) =
    (rawRightLieCoefficientTorMapAt.{u, v, v', w, w', z} R L A f A' g n).hom.comp
      (rawRightCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L A n).toLinearMap := by
  ext a
  have hMap := congrArg (fun f => f.hom (ULift.up a))
    (rawRightCoefficientHomologyMapAt_tensor_coordinates.{u, v, v', w, w', z} R L A f A' g n)
  have hDown := congrArg
    (fun b : ULift.{max u v v' w w' z} ((rightCoefficientComplex R L' A').homology n) => b.down) hMap
  change rawOriginalRightCoefficientHomologyMapAt.{u, v, v', w, w', z} R L A f A' g n a =
    (rawRightCoefficientHomologyToLeftIso R L' A' n).toLinearEquiv.symm
      (rawOriginalCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n
        ((rawRightCoefficientHomologyToLeftIso R L A n).toLinearEquiv a)) at hDown
  change rawCoefficientHomologyEquivTorAt.{u, v', v, w', w, z} R L' M' n
      ((rawRightCoefficientHomologyToLeftIso R L' A' n).toLinearEquiv
        (rawOriginalRightCoefficientHomologyMapAt.{u, v, v', w, w', z} R L A f A' g n a)) =
    (rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n).hom
      (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n
        ((rawRightCoefficientHomologyToLeftIso R L A n).toLinearEquiv a))
  rw [hDown, LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (rawCoefficientHomologyEquivTorAt_naturality.{u, v, v', w, w', z} R L f M M' h n) _

end JointMaps

end ChevalleyEilenberg
