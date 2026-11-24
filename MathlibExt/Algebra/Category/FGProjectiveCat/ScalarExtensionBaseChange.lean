/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionModuleHom
public import MathlibExt.Algebra.Category.FGProjectiveCat.BaseChange

/-!
# The actual balanced scalar extension and commutative base change

For same-universe commutative rings, the existing base-change adjunction unit
and the original balanced universal map give the actual comparison. Its
inverse is the same adjunction's inverse Hom map applied to the original
balanced unit. Both inverse laws and naturality are derived on the actual
pure classes and unit generators. Neither functor is replaced.
-/

public section
noncomputable section

open CategoryTheory
open scoped ChangeOfRings

universe u

namespace ModuleCat.RingHomScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

private abbrev standardAdj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} f

private def balancedToBaseChange (M : ModuleCat.{u} R) :
    (functor f).obj M ⟶ (ModuleCat.extendScalars f).obj M :=
  fromRestrictHom f ((standardAdj f).unit.app M)

private theorem balancedToBaseChangePureComputed (f : R →+* S)
    (M : ModuleCat.{u} R) (s : S) (p : M) :
    let unitPoint : (ModuleCat.extendScalars f).obj M := (standardAdj f).unit.app M p
    balancedToBaseChange f M (show (functor f).obj M from pure f M s p) =
      s • unitPoint := by
  dsimp only
  change fromRestrictHom f ((standardAdj f).unit.app M) (pure f M s p) = _
  exact fromRestrictHom_pure f (N := (ModuleCat.extendScalars f).obj M)
    ((standardAdj f).unit.app M) s p

private def baseChangeToBalanced (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars f).obj M ⟶ (functor f).obj M :=
  ((standardAdj f).homEquiv M ((functor f).obj M)).symm (unitHom f M)

private theorem baseChangeToBalancedUnit (M : ModuleCat.{u} R) (p : M) :
    baseChangeToBalanced f M ((standardAdj f).unit.app M p) = pure f M 1 p := by
  have h := ((standardAdj f).homEquiv M ((functor f).obj M)).apply_symm_apply (unitHom f M)
  rw [Adjunction.homEquiv_unit] at h
  have hv := ConcreteCategory.congr_hom h p
  change baseChangeToBalanced f M ((standardAdj f).unit.app M p) = unitHom f M p at hv
  exact hv.trans (unitHom_value f M p)

/-- The actual module comparison, with both inverse laws for the existing carriers. -/
def scalarExtensionBaseChangeModuleIso (M : ModuleCat.{u} R) :
    (functor f).obj M ≅ (ModuleCat.extendScalars f).obj M where
  hom := balancedToBaseChange f M
  inv := baseChangeToBalanced f M
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    let := rightModule f
    apply TensorProduct.Balanced.addHom_ext ℤ R S M
    intro s p
    let TM := (ModuleCat.extendScalars f).obj M
    let unitPoint : TM := (standardAdj f).unit.app M p
    let inverse : TM →ₗ[S] (functor f).obj M := (baseChangeToBalanced f M).hom
    have hForward : balancedToBaseChange f M (pure f M s p) = s • unitPoint :=
      balancedToBaseChangePureComputed f M s p
    have hInverse : inverse unitPoint = pure f M 1 p := baseChangeToBalancedUnit f M p
    have hLinear := inverse.map_smul s unitPoint
    change inverse (balancedToBaseChange f M (pure f M s p)) = pure f M s p
    exact (congrArg inverse hForward).trans
      (hLinear.trans ((congrArg (fun x : (functor f).obj M => s • x) hInverse).trans
        ((smul_pure f M s 1 p).trans (congrArg (fun a => pure f M a p) (mul_one s)))))
  inv_hom_id := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro p
    let TM := (ModuleCat.extendScalars f).obj M
    let unitPoint : TM := (standardAdj f).unit.app M p
    let tensorPoint : TM := (1 : S) ⊗ₜ[R,f] p
    let forward : (functor f).obj M →ₗ[S] TM := (balancedToBaseChange f M).hom
    let inverse : TM →ₗ[S] (functor f).obj M := (baseChangeToBalanced f M).hom
    have hUnitTensor : unitPoint = tensorPoint :=
      ModuleCat.extendRestrictScalarsAdj_unit_app_apply f M p
    have hInverse : inverse unitPoint = pure f M 1 p := baseChangeToBalancedUnit f M p
    have hForward : forward (pure f M 1 p) = (1 : S) • unitPoint :=
      balancedToBaseChangePureComputed f M 1 p
    have hReturn : forward (inverse unitPoint) = unitPoint :=
      (congrArg forward hInverse).trans (hForward.trans (one_smul S unitPoint))
    change forward (inverse tensorPoint) = tensorPoint
    exact (congrArg (fun z : TM => forward (inverse z)) hUnitTensor.symm).trans
      (hReturn.trans hUnitTensor)

private theorem scalarExtensionBaseChangeModuleIsoNatural
    {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    (functor f).map g ≫ (scalarExtensionBaseChangeModuleIso f N).hom =
      (scalarExtensionBaseChangeModuleIso f M).hom ≫ (ModuleCat.extendScalars f).map g  := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  let := rightModule f
  apply TensorProduct.Balanced.addHom_ext ℤ R S M
  intro s p
  let T := (functor f).obj M
  let U := (functor f).obj N
  let TM := (ModuleCat.extendScalars f).obj M
  let TN := (ModuleCat.extendScalars f).obj N
  let v : T := pure f M s p
  let vN : U := pure f N s (g.hom p)
  let gActual : T →ₗ[S] U := ((functor f).map g).hom
  let forwardM : T →ₗ[S] TM := (balancedToBaseChange f M).hom
  let forwardN : U →ₗ[S] TN := (balancedToBaseChange f N).hom
  let standardG : TM →ₗ[S] TN := ((ModuleCat.extendScalars f).map g).hom
  have hPure : gActual v = vN := functor_map_pure f g s p
  let unitM : TM := (standardAdj f).unit.app M p
  let unitN : TN := (standardAdj f).unit.app N (g.hom p)
  have hM : forwardM v = s • unitM := balancedToBaseChangePureComputed f M s p
  have hN : forwardN vN = s • unitN := balancedToBaseChangePureComputed f N s (g.hom p)
  have hUnit : unitN = standardG unitM := by
    have h := ConcreteCategory.congr_hom ((standardAdj f).unit.naturality g) p
    change unitN = standardG unitM at h
    exact h
  have hLinear := standardG.map_smul s unitM
  change forwardN (gActual v) = standardG (forwardM v)
  exact (congrArg forwardN hPure).trans
    (hN.trans ((congrArg (fun x : TN => s • x) hUnit).trans
      (hLinear.symm.trans (congrArg standardG hM.symm))))

/-- Natural isomorphism between the SAME actual balanced and standard module functors. -/
def scalarExtensionBaseChangeModuleNatIso : functor f ≅ ModuleCat.extendScalars f :=
  NatIso.ofComponents (scalarExtensionBaseChangeModuleIso f)
    (fun g => scalarExtensionBaseChangeModuleIsoNatural f g)

end ModuleCat.RingHomScalarExtension

namespace FGProjectiveCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual same-universe scalar-extension/base-change isomorphism on finite projectives. -/
def scalarExtensionBaseChangeIso (f : R →+* S) :
    scalarExtension.{u, u, u} f ≅ baseChange.{u, u, u} f :=
  NatIso.ofComponents
    (fun P => (ModuleCat.isFGProjective.{u} S).isoMk
      (eqToIso (scalarExtension_obj_obj f P) ≪≫
        (ModuleCat.RingHomScalarExtension.scalarExtensionBaseChangeModuleNatIso f).app P.obj ≪≫
          (eqToIso (baseChange_obj_obj f P)).symm))
    (by
      intro P Q g
      apply FGProjectiveCat.hom_ext
      apply LinearMap.ext
      intro x
      exact ConcreteCategory.congr_hom
        ((ModuleCat.RingHomScalarExtension.scalarExtensionBaseChangeModuleNatIso f).hom.naturality
          g.hom) x)

end FGProjectiveCat

end
