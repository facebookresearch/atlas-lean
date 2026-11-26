/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.DirectLimit
public import MathlibExt.Algebra.Category.ModuleCat.ExteriorPower
public import MathlibExt.LinearAlgebra.ExteriorPower.DirectLimit

/-!
# Exterior powers preserve directed module colimits

Let R be a commutative ring, I a nonempty directed preorder, and
F : I → ModuleCat^max(i,m)(R) a module diagram. For every finite
exterior degree n ≥ 0, the canonical direct-limit cocone remains
a colimit cocone after applying ⋀_R^n.

Equivalently, colim_a ⋀_R^n(F_a) ≅ ⋀_R^n(colim_a F_a).
On a wedge represented at stage a, the comparison applies the
stage injection to every exterior factor. The diagram maps are
arbitrary R-linear maps. The ring world u, index world i and
carrier height m are independent, and the exterior-power target
category has height max(u,i,m).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u i m

namespace ModuleCat

variable (R : Type u) [CommRing R]
  {I : Type i} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (F : I ⥤ ModuleCat.{max i m} R)

/-- For a commutative ring R, a nonempty directed preorder I
and F : I → ModuleCat^max(i,m)(R), the image under ⋀_R^n of the
direct-limit cocone of F is a colimit cocone, for every n ≥ 0.
Its maps are exterior powers of the stage injections, with
target category ModuleCat^max(u,i,m)(R). -/
def exteriorPowerDirectLimitIsColimit (n : ℕ) :
    IsColimit ((exteriorPowerFunctorAt R n).mapCocone (directLimitCoconeOfFunctor F)) := by
  classical
  let G : I → Type (max i m) := fun a => F.obj a
  let f : ∀ a b, a ≤ b → G a →ₗ[R] G b := fun a b h => (F.map (homOfLE h)).hom
  let : DirectedSystem G (f · · ·) :=
    { map_self := by
        intro a x
        change (F.map (homOfLE (le_rfl : a ≤ a))).hom x = x
        have h : (homOfLE (le_rfl : a ≤ a) : a ⟶ a) = 𝟙 a := rfl
        rw [h, F.map_id, ModuleCat.hom_id, LinearMap.id_apply]
      map_map := by
        intro c b a hab hbc x
        change (F.map (homOfLE hbc)).hom ((F.map (homOfLE hab)).hom x) =
          (F.map (homOfLE (hab.trans hbc))).hom x
        rw [← ModuleCat.comp_apply, ← F.map_comp, homOfLE_comp] }
  let E : ModuleCat.{max i m} R ⥤ ModuleCat.{max u i m} R := exteriorPowerFunctorAt.{u, max i m} R n
  let S := directLimitCoconeOfFunctor.{u, i, m} F
  let P := directLimitCoconeOfFunctor.{u, i, max u m} (F ⋙ E)
  let eM : S.pt ≃ₗ[R] DirectLimit G f :=
    Module.DirectLimit.linearEquiv (R := R) (ι := I) (G := G) (f := f)
  let eP := exteriorPower.mapEquiv R S.pt n eM
  let eD : P.pt ≃ₗ[R] (⋀[R]^n (DirectLimit G f)) := exteriorPower.directLimitEquiv R G f n
  let e : P.pt ≃ₗ[R] E.obj S.pt := eD.trans eP.symm
  have hs : IsColimit P := directLimitCoconeOfFunctorIsColimit.{u, i, max u m} (F ⋙ E)
  have he : P ≅ E.mapCocone S :=
    Cocone.ext e.toModuleIso (by
      intro a
      apply ModuleCat.hom_ext
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro x
      change e (Module.DirectLimit.of R I (fun a => ⋀[R]^n (G a))
          (exteriorPower.directLimitTransition R G f n) a (exteriorPower.ιMulti R n x)) =
        exteriorPower.map n (Module.DirectLimit.of R I G f a) (exteriorPower.ιMulti R n x)
      apply eP.injective
      change eP (eP.symm (exteriorPower.directLimitComparison R G f n
          (Module.DirectLimit.of R I (fun a => ⋀[R]^n (G a))
            (exteriorPower.directLimitTransition R G f n) a (exteriorPower.ιMulti R n x)))) = _
      rw [LinearEquiv.apply_symm_apply, exteriorPower.directLimitComparison_of]
      change exteriorPower.map n (DirectLimit.Module.of R I G f a) (exteriorPower.ιMulti R n x) =
        eP ((E.map (S.ι.app a)).hom (exteriorPower.ιMulti R n x))
      let y : Fin n → S.pt := (S.ι.app a).hom ∘ x
      have hv : (E.map (S.ι.app a)).hom (exteriorPower.ιMulti R n x) =
          exteriorPower.ιMulti R n y :=
        exteriorPower.map_apply_ιMulti (S.ι.app a).hom x
      have hp : eP (exteriorPower.ιMulti R n y) = exteriorPower.ιMulti R n (eM ∘ y) :=
        exteriorPower.mapEquiv_apply_ιMulti R S.pt n eM y
      have hy : eM ∘ y = (DirectLimit.Module.of R I G f a) ∘ x := by
        funext b
        exact Module.DirectLimit.linearEquiv_of (R := R) (ι := I) (G := G) (f := f)
          (i := a) (g := x b)
      have hr : eP ((E.map (S.ι.app a)).hom (exteriorPower.ιMulti R n x)) =
          exteriorPower.map n (DirectLimit.Module.of R I G f a) (exteriorPower.ιMulti R n x) :=
        (congrArg eP hv).trans (hp.trans
          ((congrArg (exteriorPower.ιMulti R n) hy).trans
            (exteriorPower.map_apply_ιMulti (DirectLimit.Module.of R I G f a) x).symm))
      exact hr.symm)
  exact IsColimit.ofIsoColimit hs he

/-- For a commutative ring R, a nonempty directed preorder I,
a diagram F : I → ModuleCat^max(i,m)(R) and n ≥ 0, the
exterior-power functor ⋀_R^n preserves the colimit of F.
The ring, index and module-carrier worlds are independent. -/
instance exteriorPowerFunctorAt_preservesDirectedColimit (n : ℕ) :
    PreservesColimit F (exteriorPowerFunctorAt R n) :=
  preservesColimit_of_preserves_colimit_cocone (directLimitCoconeOfFunctorIsColimit.{u, i, m} F)
    (exteriorPowerDirectLimitIsColimit R F n)

end ModuleCat
