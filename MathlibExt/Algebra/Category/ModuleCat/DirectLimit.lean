/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Module direct limits as categorical colimits

The module direct-limit carrier, inclusions and universal linear map form
a colimit cocone for a preorder-indexed module functor. The carrier universe
contains the index universe; the ring universe remains independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe r i m

namespace ModuleCat

variable {R : Type r} [Ring R] {ι : Type i} [Preorder ι]
  (F : ι ⥤ ModuleCat.{max i m} R)

open scoped Classical in
/-- The cocone whose point and injections are the module direct limit. -/
def directLimitCoconeOfFunctor : Cocone F where
  pt := ModuleCat.of R
    (Module.DirectLimit (fun j => F.obj j) (fun j j' h => (F.map (homOfLE h)).hom))
  ι :=
    { app := fun j => ModuleCat.ofHom
        (Module.DirectLimit.of R ι (fun j => F.obj j)
          (fun j j' h => (F.map (homOfLE h)).hom) j)
      naturality := by
        intro j j' f
        apply ModuleCat.hom_ext
        ext x
        simp only [Functor.const_obj_map, ModuleCat.hom_comp,
          LinearMap.comp_apply]
        change Module.DirectLimit.of R ι (fun j => F.obj j)
            (fun j j' h => (F.map (homOfLE h)).hom) j' ((F.map f).hom x) =
          Module.DirectLimit.of R ι (fun j => F.obj j)
            (fun j j' h => (F.map (homOfLE h)).hom) j x
        have h := Module.DirectLimit.of_f (R := R) (ι := ι) (G := fun j => F.obj j)
          (f := fun j j' h => (F.map (homOfLE h)).hom) (i := j) (j := j')
          (hij := leOfHom f) (x := x)
        exact h }

open scoped Classical in
/-- Lift and hom_ext prove the universal property without a directedness assumption. -/
def directLimitCoconeOfFunctorIsColimit : IsColimit (directLimitCoconeOfFunctor F) where
  desc s := ModuleCat.ofHom
    (Module.DirectLimit.lift R ι (fun j => F.obj j)
      (fun j j' h => (F.map (homOfLE h)).hom) (fun j => (s.ι.app j).hom) (by
        intro j j' h x
        have hw := congrArg (fun f : F.obj j ⟶ s.pt => f.hom x) (s.w (homOfLE h))
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hw))
  fac s j := by
    apply ModuleCat.hom_ext
    ext x
    simp only [directLimitCoconeOfFunctor, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_ofHom, Module.DirectLimit.lift_of]
  uniq s f hf := by
    dsimp only [directLimitCoconeOfFunctor] at f hf ⊢
    apply ModuleCat.hom_ext
    apply Module.DirectLimit.hom_ext (R := R) (ι := ι)
      (G := fun j => F.obj j) (f := fun j j' h => (F.map (homOfLE h)).hom)
    intro j
    ext x
    have hj := congrArg (fun g : F.obj j ⟶ s.pt => g.hom x) (hf j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_ofHom] at hj
    have hg : ∀ i j hij x, (s.ι.app j).hom ((F.map (homOfLE hij)).hom x) =
        (s.ι.app i).hom x := by
      intro i j hij x
      have hw := congrArg (fun g : F.obj i ⟶ s.pt => g.hom x) (s.w (homOfLE hij))
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hw
    change f.hom (Module.DirectLimit.of R ι (fun j => F.obj j)
      (fun j j' h => (F.map (homOfLE h)).hom) j x) =
      Module.DirectLimit.lift R ι (fun j => F.obj j)
        (fun j j' h => (F.map (homOfLE h)).hom) (fun j => (s.ι.app j).hom) hg
          (Module.DirectLimit.of R ι (fun j => F.obj j)
            (fun j j' h => (F.map (homOfLE h)).hom) j x)
    rw [Module.DirectLimit.lift_of]
    exact hj

end ModuleCat
