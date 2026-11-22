/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.EquivalenceCategorical
import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreBifunctor

/-!
# Actual complete functor-core paths preserve categorical weakness

Whisker the real equivalence edge through the original full composition
bifunctor. At every target it yields an actual natural Iso of the complete
precomposition functors. Categorical weakness therefore has an exact iff.
No weak map or localization outcome is a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalClosed Opposite
open scoped Simplicial

namespace SSet

/-- A genuine equivalence edge of the WHOLE functor object gives the exact categorical-weakness iff. -/
theorem categoricalEquivalences_iff_of_isEquivalence_edge {X Y : SSet.{u}} (f g : X ⟶ Y)
    (e : Edge (ihomVertexEquiv X Y f) (ihomVertexEquiv X Y g)) (he : e.IsEquivalence) :
    categoricalEquivalences f ↔ categoricalEquivalences g := by
  let alpha : HomotopyCategory.mk (ihomVertexEquiv X Y f) ≅
      HomotopyCategory.mk (ihomVertexEquiv X Y g) := @asIso _ _ _ _ e.toHoHom he
  have hIso (Q : SSet.{u}) :
      (hoFunctor.map ((pre f).app Q)).toFunctor ≅ (hoFunctor.map ((pre g).app Q)).toFunctor :=
    (eqToIso (hoCompSlice_mk_ihomVertexEquiv_eq_hoPre f Q)).symm ≪≫
      hoCompSliceIso alpha ≪≫ eqToIso (hoCompSlice_mk_ihomVertexEquiv_eq_hoPre g Q)
  constructor
  · intro hf Q hQ
    let _ := hf Q hQ
    exact Functor.isEquivalence_of_iso (hIso Q)
  · intro hg Q hQ
    let _ := hg Q hQ
    exact Functor.isEquivalence_of_iso (hIso Q).symm

/-- The SAME full core path and BOTH actual functor endpoints give categorical weakness in either direction. -/
theorem categoricalEquivalences_iff_of_corePath {X Y : SSet.{u}} [Quasicategory Y] (f g : X ⟶ Y)
    (phi : (Δ[1] : SSet.{u}) ⟶ (core ((ihom X).obj Y) : SSet.{u}))
    (h1 : stdSimplex.δ (1 : Fin 2) ≫ phi = yonedaEquiv.symm (FunctorCore.vertex f))
    (h0 : stdSimplex.δ (0 : Fin 2) ≫ phi = yonedaEquiv.symm (FunctorCore.vertex g)) :
    categoricalEquivalences f ↔ categoricalEquivalences g := by
  let K : SSet.{u} := (core ((ihom X).obj Y) : SSet.{u})
  let _ : KanComplex ((FunctorCore.functor X).obj Y) := FunctorCore.isKan X Y
  let e : Edge (FunctorCore.vertex f) (FunctorCore.vertex g) :=
    Edge.mk (yonedaEquiv phi)
      ((SSet.yonedaEquiv_naturality (SimplexCategory.δ (1 : Fin 2)) phi).trans
        ((congrArg SSet.yonedaEquiv h1).trans (SSet.yonedaEquiv.apply_symm_apply _)))
      ((SSet.yonedaEquiv_naturality (SimplexCategory.δ (0 : Fin 2)) phi).trans
        ((congrArg SSet.yonedaEquiv h0).trans (SSet.yonedaEquiv.apply_symm_apply _)))
  exact categoricalEquivalences_iff_of_isEquivalence_edge f g (e.map (core ((ihom X).obj Y)).ι)
    ((Edge.isEquivalence_of_kanComplex e).map (core ((ihom X).obj Y)).ι)

end SSet
