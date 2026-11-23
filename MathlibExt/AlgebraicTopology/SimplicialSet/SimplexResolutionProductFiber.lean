/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolution
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexProductProjection
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Product fibers in the simplex resolution

For `u = prod.lift f g : X ⟶ Y ⨯ T`, the target pullback of
`prod.fst : Y ⨯ T ⟶ Y` over an `m`-simplex is canonically
`Δ[m] ⨯ T`.  Under this isomorphism, the induced pullback component sends a
left-fiber simplex to its standard-simplex coordinate first and its image in
`T` second.

The projection of the target pullback to `T` is a realized weak equivalence.
Consequently, if every left-fiber projection followed by `g` is a realized
weak equivalence, two-out-of-three makes every component of the induced
simplex-pullback diagram map a realized weak equivalence.

This file makes no homotopy-colimit, bar-diagonal, simplex-resolution,
Theorem A, or additivity claim.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial
open scoped MonoidalCategory

universe u

namespace SSet

/-- The pullback of `Y ⨯ T ⟶ Y` along a represented `m`-simplex is
canonically `Δ[m] ⨯ T`, with the standard-simplex coordinate first. -/
noncomputable def simplexProdFstPullbackIso
    {Y T : SSet.{u}} {m : ℕ}
    (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    pullback (prod.fst : Y ⨯ T ⟶ Y) a ≅
      (Δ[m] : SSet.{u}) ⨯ T :=
  pullbackSymmetry _ _ ≪≫ pullbackProdFstIsoProd a T

/-- Under the target-fiber iso, the first projection is the original
standard-simplex projection. -/
@[reassoc (attr := simp)]
theorem simplexProdFstPullbackIso_hom_fst
    {Y T : SSet.{u}} {m : ℕ}
    (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    (simplexProdFstPullbackIso (T := T) a).hom ≫ prod.fst =
      pullback.snd (prod.fst : Y ⨯ T ⟶ Y) a := by
  simp only [simplexProdFstPullbackIso, Iso.trans_hom,
    Category.assoc, pullbackProdFstIsoProd_hom_fst,
    pullbackSymmetry_hom_comp_fst]

/-- Under the target-fiber iso, the second projection is the `T` projection
of the original product coordinate. -/
@[reassoc (attr := simp)]
theorem simplexProdFstPullbackIso_hom_snd
    {Y T : SSet.{u}} {m : ℕ}
    (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    (simplexProdFstPullbackIso (T := T) a).hom ≫ prod.snd =
      pullback.fst (prod.fst : Y ⨯ T ⟶ Y) a ≫ prod.snd := by
  simp only [simplexProdFstPullbackIso, Iso.trans_hom,
    Category.assoc, pullbackProdFstIsoProd_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc]

/-- The inverse target-fiber iso sends its first coordinate to the original
standard-simplex projection. -/
@[reassoc (attr := simp)]
theorem simplexProdFstPullbackIso_inv_snd
    {Y T : SSet.{u}} {m : ℕ}
    (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    (simplexProdFstPullbackIso (T := T) a).inv ≫
        pullback.snd (prod.fst : Y ⨯ T ⟶ Y) a =
      prod.fst := by
  simp only [simplexProdFstPullbackIso, Iso.trans_inv,
    Category.assoc, pullbackSymmetry_inv_comp_snd,
    pullbackProdFstIsoProd_inv_fst]

/-- The `T` projection of the inverse target-fiber iso is the second product
projection. -/
@[reassoc (attr := simp)]
theorem simplexProdFstPullbackIso_inv_fst_snd
    {Y T : SSet.{u}} {m : ℕ}
    (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    (simplexProdFstPullbackIso (T := T) a).inv ≫
        pullback.fst (prod.fst : Y ⨯ T ⟶ Y) a ≫ prod.snd =
      prod.snd := by
  simp only [simplexProdFstPullbackIso, Iso.trans_inv,
    Category.assoc, pullbackSymmetry_inv_comp_fst_assoc,
    pullbackProdFstIsoProd_inv_snd_snd]

/-- The `Y` projection of the inverse target-fiber iso is the representing
simplex map applied to the first product coordinate. -/
@[reassoc (attr := simp)]
theorem simplexProdFstPullbackIso_inv_fst_fst
    {Y T : SSet.{u}} {m : ℕ}
    (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    (simplexProdFstPullbackIso (T := T) a).inv ≫
        pullback.fst (prod.fst : Y ⨯ T ⟶ Y) a ≫ prod.fst =
      prod.fst ≫ a := by
  simp only [simplexProdFstPullbackIso, Iso.trans_inv,
    Category.assoc, pullbackSymmetry_inv_comp_fst_assoc,
    pullbackProdFstIsoProd_inv_snd_fst]

/-- Projection of a target product fiber to `T`. -/
noncomputable def simplexProdFstPullbackToT
    {Y T : SSet.{u}} {m : ℕ}
    (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    pullback (prod.fst : Y ⨯ T ⟶ Y) a ⟶ T :=
  pullback.fst _ _ ≫ prod.snd

/-- The projection of a target product fiber to `T` is a realized weak
homotopy equivalence. -/
theorem simplexProdFstPullbackToT_mem_weakHomotopyEquivalences
    {Y T : SSet.{u}} {m : ℕ}
    (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (simplexProdFstPullbackToT (T := T) a)) := by
  have h := MorphismProperty.RespectsIso.precomp
    TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (simplexProdFstPullbackIso (T := T) a).hom)
    (SSet.toTop.map
      (prod.snd : (Δ[m] : SSet.{u}) ⨯ T ⟶ T))
    (stdSimplexProdSnd_mem_weakHomotopyEquivalences m T)
  simpa only [← Functor.map_comp,
    simplexProdFstPullbackIso_hom_snd,
    simplexProdFstPullbackToT] using h

/-- The component between the pullbacks over a represented simplex induced by
`prod.lift f g : X ⟶ Y ⨯ T`. -/
noncomputable def simplexProdFstComponent
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    pullback f a ⟶ pullback (prod.fst : Y ⨯ T ⟶ Y) a :=
  simplexPullbackTriangleMap
    (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
    (prod.lift f g) (prod.lift_fst f g) (CostructuredArrow.mk a)

/-- The represented component is exactly the corresponding component of the
BK1 diagram map. -/
theorem simplexProdFstComponent_eq_diagramMap_app
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    simplexProdFstComponent f g a =
      (simplexPullbackDiagramMap
        (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
        (prod.lift f g) (prod.lift_fst f g)).app
          (CostructuredArrow.mk a) :=
  rfl

/-- The source-product projection of the represented component. -/
@[reassoc (attr := simp)]
theorem simplexProdFstComponent_fst
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    simplexProdFstComponent f g a ≫
        pullback.fst (prod.fst : Y ⨯ T ⟶ Y) a =
      pullback.fst f a ≫ prod.lift f g :=
  simplexPullbackTriangleMap_fst
    (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
    (prod.lift f g) (prod.lift_fst f g) (CostructuredArrow.mk a)

/-- The standard-simplex projection of the represented component is
unchanged. -/
@[reassoc (attr := simp)]
theorem simplexProdFstComponent_snd
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    simplexProdFstComponent f g a ≫
        pullback.snd (prod.fst : Y ⨯ T ⟶ Y) a =
      pullback.snd f a :=
  simplexPullbackTriangleMap_snd
    (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
    (prod.lift f g) (prod.lift_fst f g) (CostructuredArrow.mk a)

/-- Under the target-fiber iso, the represented component is the ordered pair
of the standard-simplex projection and the map to `T`. -/
theorem simplexProdFstComponent_comp_iso_hom
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    simplexProdFstComponent f g a ≫
        (simplexProdFstPullbackIso (T := T) a).hom =
      prod.lift (pullback.snd f a) (pullback.fst f a ≫ g) := by
  apply prod.hom_ext
  · simp only [Category.assoc, simplexProdFstPullbackIso_hom_fst,
      simplexProdFstComponent_snd, prod.lift_fst]
  · simp only [Category.assoc, simplexProdFstPullbackIso_hom_snd,
      simplexProdFstComponent_fst_assoc, prod.lift_snd]

/-- The represented component followed by the target projection to `T` is
the source projection followed by `g`. -/
@[reassoc]
theorem simplexProdFstComponent_comp_toT
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (a : (Δ[m] : SSet.{u}) ⟶ Y) :
    simplexProdFstComponent f g a ≫
        simplexProdFstPullbackToT (T := T) a =
      pullback.fst f a ≫ g := by
  simp only [simplexProdFstPullbackToT,
    simplexProdFstComponent_fst_assoc, prod.lift_snd]

/-- Two-out-of-three for the represented product-fiber component. -/
theorem simplexProdFstComponent_mem_weakHomotopyEquivalences
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (a : (Δ[m] : SSet.{u}) ⟶ Y)
    (h : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (pullback.fst f a ≫ g))) :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (simplexProdFstComponent f g a)) := by
  apply TopCat.weakHomotopyEquivalences.of_postcomp
    (SSet.toTop.map (simplexProdFstComponent f g a))
    (SSet.toTop.map (simplexProdFstPullbackToT (T := T) a))
    (simplexProdFstPullbackToT_mem_weakHomotopyEquivalences a)
  simpa only [← Functor.map_comp,
    simplexProdFstComponent_comp_toT] using h

/-- The product-fiber component at the simplex represented by `y`. -/
noncomputable def leftFiberProductComponent
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (y : Y _⦋m⦌) :
    SSet.leftFiber f y ⟶
      pullback (prod.fst : Y ⨯ T ⟶ Y)
        (SSet.yonedaEquiv.symm y) :=
  simplexProdFstComponent f g (SSet.yonedaEquiv.symm y)

/-- The named left-fiber component is exactly the BK1 diagram-map component. -/
theorem leftFiberProductComponent_eq_diagramMap_app
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (y : Y _⦋m⦌) :
    leftFiberProductComponent f g y =
      (simplexPullbackDiagramMap
        (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
        (prod.lift f g) (prod.lift_fst f g)).app
          (leftFiberSimplexIndex y) :=
  rfl

/-- Under the target-fiber iso, a left-fiber component is source-first:
standard-simplex coordinate first and mapped source coordinate second. -/
theorem leftFiberProductComponent_comp_iso_hom
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (y : Y _⦋m⦌) :
    leftFiberProductComponent f g y ≫
        (simplexProdFstPullbackIso (T := T)
          (SSet.yonedaEquiv.symm y)).hom =
      prod.lift (SSet.leftFiber.toSimplex f y)
        (SSet.leftFiber.π f y ≫ g) :=
  simplexProdFstComponent_comp_iso_hom
    f g (SSet.yonedaEquiv.symm y)

/-- First-factor computation for the left-fiber component. -/
@[reassoc (attr := simp)]
theorem leftFiberProductComponent_iso_fst
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (y : Y _⦋m⦌) :
    leftFiberProductComponent f g y ≫
        (simplexProdFstPullbackIso (T := T)
          (SSet.yonedaEquiv.symm y)).hom ≫ prod.fst =
      SSet.leftFiber.toSimplex f y := by
  rw [← Category.assoc, leftFiberProductComponent_comp_iso_hom,
    prod.lift_fst]

/-- Second-factor computation for the left-fiber component. -/
@[reassoc (attr := simp)]
theorem leftFiberProductComponent_iso_snd
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    {m : ℕ} (y : Y _⦋m⦌) :
    leftFiberProductComponent f g y ≫
        (simplexProdFstPullbackIso (T := T)
          (SSet.yonedaEquiv.symm y)).hom ≫ prod.snd =
      SSet.leftFiber.π f y ≫ g := by
  rw [← Category.assoc, leftFiberProductComponent_comp_iso_hom,
    prod.lift_snd]

/-- If every left-fiber projection followed by `g` realizes to a weak
homotopy equivalence, then every component of the product-induced pullback
diagram map realizes to a weak homotopy equivalence. -/
theorem simplexPullbackDiagramMap_prod_obj_mem
    {X Y T : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ T)
    (h : ∀ (m : ℕ) (y : Y _⦋m⦌),
      TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (SSet.leftFiber.π f y ≫ g)))
    (s : SSet.SimplexIndex Y) :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map
        ((SSet.simplexPullbackDiagramMap
          (p := f) (q := (prod.fst : Y ⨯ T ⟶ Y))
          (prod.lift f g) (prod.lift_fst f g)).app s)) := by
  obtain ⟨A, a, rfl⟩ := CostructuredArrow.mk_surjective s
  obtain ⟨m⟩ := A
  let y : Y _⦋m⦌ := SSet.yonedaEquiv a
  have ha : SSet.yonedaEquiv.symm y = a := by
    exact SSet.yonedaEquiv.symm_apply_apply a
  rw [← ha]
  apply simplexProdFstComponent_mem_weakHomotopyEquivalences
    f g (SSet.yonedaEquiv.symm y)
  exact h m y

end SSet

end
