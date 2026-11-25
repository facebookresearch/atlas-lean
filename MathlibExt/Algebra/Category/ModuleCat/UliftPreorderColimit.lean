/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import MathlibExt.Algebra.Category.ModuleCat.DirectLimit

/-!
# Universe lifts preserve module preorder colimits

The module direct-limit cocone transports through `ULift`. Composing its
universal map with the module equivalence from `ULift` proves colimit
preservation for independent ring, index, carrier and lift universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe r i m z

namespace ModuleCat

variable (R : Type r) [Ring R] {I : Type i} [Preorder I]
  (F : I ⥤ ModuleCat.{max i m} R)

/-- The universe lift preserves the module direct-limit cocone. -/
def uliftDirectLimitCoconeIsColimit :
    IsColimit ((uliftFunctor.{z, max i m} R).mapCocone (directLimitCoconeOfFunctor F)) := by
  classical
  let U := uliftFunctor.{z, max i m} R
  let e : U.obj (directLimitCoconeOfFunctor F).pt ≃ₗ[R] (directLimitCoconeOfFunctor F).pt :=
    ULift.moduleEquiv
  let g (s : Cocone (F ⋙ U)) (j : I) : F.obj j →ₗ[R] s.pt :=
    (show U.obj (F.obj j) ⟶ s.pt from s.ι.app j).hom.comp
      (ULift.moduleEquiv : ULift.{z} (F.obj j) ≃ₗ[R] F.obj j).symm.toLinearMap
  let hg (s : Cocone (F ⋙ U)) :
      ∀ j j' (h : j ≤ j') (x : F.obj j),
        g s j' ((F.map (homOfLE h)).hom x) = g s j x := by
    intro j j' h x
    have hw := congrArg (fun f : U.obj (F.obj j) ⟶ s.pt => f.hom (ULift.up x))
      (s.w (homOfLE h))
    change (s.ι.app j').hom (ULift.up ((F.map (homOfLE h)).hom x)) =
      (s.ι.app j).hom (ULift.up x) at hw
    exact hw
  let L (s : Cocone (F ⋙ U)) :=
    Module.DirectLimit.lift R I (fun j => F.obj j)
      (fun j j' h => (F.map (homOfLE h)).hom) (g s) (hg s)
  refine
    { desc := fun s => ModuleCat.ofHom ((L s).comp e.toLinearMap)
      fac := ?_
      uniq := ?_ }
  · intro s j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x⟩
    change L s (Module.DirectLimit.of R I (fun j => F.obj j)
      (fun j j' h => (F.map (homOfLE h)).hom) j x) = (s.ι.app j).hom (ULift.up x)
    exact Module.DirectLimit.lift_of (R := R) (ι := I) (G := fun j => F.obj j)
      (f := fun j j' h => (F.map (homOfLE h)).hom) (g s) (hg s) x
  · intro s f hf
    let a : (directLimitCoconeOfFunctor F).pt →ₗ[R] s.pt :=
      f.hom.comp e.symm.toLinearMap
    have ha : a = L s := by
      apply Module.DirectLimit.hom_ext (R := R) (ι := I) (G := fun j => F.obj j)
        (f := fun j j' h => (F.map (homOfLE h)).hom)
      intro j
      apply LinearMap.ext
      intro x
      have hj := congrArg (fun q : U.obj (F.obj j) ⟶ s.pt => q.hom (ULift.up x)) (hf j)
      change a (Module.DirectLimit.of R I (fun j => F.obj j)
        (fun j j' h => (F.map (homOfLE h)).hom) j x) = (s.ι.app j).hom (ULift.up x) at hj
      exact hj.trans (Module.DirectLimit.lift_of (R := R) (ι := I) (G := fun j => F.obj j)
        (f := fun j j' h => (F.map (homOfLE h)).hom) (g s) (hg s) x).symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x⟩
    exact LinearMap.congr_fun ha x

/-- The existing universe lift preserves every preorder-diagram colimit at its carrier height. -/
instance uliftFunctor_preservesPreorderColimit :
    PreservesColimit F (uliftFunctor.{z, max i m} R) :=
  preservesColimit_of_preserves_colimit_cocone (directLimitCoconeOfFunctorIsColimit F)
    (uliftDirectLimitCoconeIsColimit.{r,i,m,z} R F)

end ModuleCat
