/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionProductFiber

/-!
# Simplex-resolution product-fiber tests

These tests pin the target-pullback orientation, all iso projections, the
represented component, the source-first left-fiber pair formula, and the
all-object two-out-of-three result.
-/

open CategoryTheory Limits Opposite Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SimplexResolutionProductFiberTests

variable {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
variable {m : ℕ} (a : (Δ[m] : SSet.{u}) ⟶ Y)

/-- The target-pullback iso puts the standard simplex first. -/
example :
    (SSet.simplexProdFstPullbackIso (T := T) a).hom ≫ prod.fst =
      pullback.snd (prod.fst : Y ⨯ T ⟶ Y) a :=
  SSet.simplexProdFstPullbackIso_hom_fst a

/-- The target-pullback iso puts `T` second. -/
example :
    (SSet.simplexProdFstPullbackIso (T := T) a).hom ≫ prod.snd =
      pullback.fst (prod.fst : Y ⨯ T ⟶ Y) a ≫ prod.snd :=
  SSet.simplexProdFstPullbackIso_hom_snd a

example :
    (SSet.simplexProdFstPullbackIso (T := T) a).inv ≫
        pullback.snd (prod.fst : Y ⨯ T ⟶ Y) a =
      prod.fst :=
  SSet.simplexProdFstPullbackIso_inv_snd a

example :
    (SSet.simplexProdFstPullbackIso (T := T) a).inv ≫
        pullback.fst (prod.fst : Y ⨯ T ⟶ Y) a ≫ prod.snd =
      prod.snd :=
  SSet.simplexProdFstPullbackIso_inv_fst_snd a

example :
    (SSet.simplexProdFstPullbackIso (T := T) a).inv ≫
        pullback.fst (prod.fst : Y ⨯ T ⟶ Y) a ≫ prod.fst =
      prod.fst ≫ a :=
  SSet.simplexProdFstPullbackIso_inv_fst_fst a

example :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (SSet.simplexProdFstPullbackToT (T := T) a)) :=
  SSet.simplexProdFstPullbackToT_mem_weakHomotopyEquivalences a

/-- The represented component maps the source coordinate into `Y ⨯ T`. -/
example :
    SSet.simplexProdFstComponent f g a ≫
        pullback.fst (prod.fst : Y ⨯ T ⟶ Y) a =
      pullback.fst f a ≫ prod.lift f g :=
  SSet.simplexProdFstComponent_fst f g a

/-- The represented component preserves the standard-simplex coordinate. -/
example :
    SSet.simplexProdFstComponent f g a ≫
        pullback.snd (prod.fst : Y ⨯ T ⟶ Y) a =
      pullback.snd f a :=
  SSet.simplexProdFstComponent_snd f g a

/-- The ordered-pair formula catches a factor swap. -/
example :
    SSet.simplexProdFstComponent f g a ≫
        (SSet.simplexProdFstPullbackIso (T := T) a).hom =
      prod.lift (pullback.snd f a) (pullback.fst f a ≫ g) :=
  SSet.simplexProdFstComponent_comp_iso_hom f g a

example :
    SSet.simplexProdFstComponent f g a ≫
        SSet.simplexProdFstPullbackToT (T := T) a =
      pullback.fst f a ≫ g :=
  SSet.simplexProdFstComponent_comp_toT f g a

example
    (h : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (pullback.fst f a ≫ g))) :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (SSet.simplexProdFstComponent f g a)) :=
  SSet.simplexProdFstComponent_mem_weakHomotopyEquivalences f g a h

section LeftFiber

variable (y : Y _⦋1⦌)

/-- At a nonzero degree, the standard-simplex coordinate remains first and
the map to `T` remains second. -/
example :
    SSet.leftFiberProductComponent f g y ≫
        (SSet.simplexProdFstPullbackIso (T := T)
          (SSet.yonedaEquiv.symm y)).hom =
      prod.lift (SSet.leftFiber.toSimplex f y)
        (SSet.leftFiber.π f y ≫ g) :=
  SSet.leftFiberProductComponent_comp_iso_hom f g y

example :
    SSet.leftFiberProductComponent f g y ≫
        (SSet.simplexProdFstPullbackIso (T := T)
          (SSet.yonedaEquiv.symm y)).hom ≫ prod.fst =
      SSet.leftFiber.toSimplex f y :=
  SSet.leftFiberProductComponent_iso_fst f g y

example :
    SSet.leftFiberProductComponent f g y ≫
        (SSet.simplexProdFstPullbackIso (T := T)
          (SSet.yonedaEquiv.symm y)).hom ≫ prod.snd =
      SSet.leftFiber.π f y ≫ g :=
  SSet.leftFiberProductComponent_iso_snd f g y

end LeftFiber

/-- The final objectwise theorem applies to arbitrary simplex-index objects,
not only a syntactically named `leftFiberSimplexIndex`. -/
example
    (h : ∀ (n : ℕ) (y : Y _⦋n⦌),
      TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (SSet.leftFiber.π f y ≫ g)))
    (s : SSet.SimplexIndex Y) :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map
        ((SSet.simplexPullbackDiagramMap
          (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
          (prod.lift f g) (prod.lift_fst f g)).app s)) :=
  SSet.simplexPullbackDiagramMap_prod_obj_mem f g h s

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SimplexResolutionProductFiberTests
