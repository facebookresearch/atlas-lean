/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUniverseLift

/-!
# Original simplicial carrier-lift realization values

Both original realization lift charts retain every original simplex point.
The actual mixed carrier map has a continuous realization on unchanged
original spaces. Ordinary pre/postcomposition follows from actual lift
naturality and the original chart inverse laws; no map comparison is input.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe u v

namespace SSet

/-- The SAME original lifted realization down chart. -/
def originalRealizationDown (X : SSet.{u}) :
    C(toTop.obj (uliftFunctor.{v, u}.obj X), toTop.obj X) :=
  ⟨fun z => (toTopULiftIso.{u, v}.hom.app X z).down,
    continuous_uliftDown.comp (toTopULiftIso.{u, v}.hom.app X).hom.continuous⟩

/-- The SAME original inverse chart, including original ULift.up. -/
def originalRealizationUp (X : SSet.{u}) :
    C(toTop.obj X, toTop.obj (uliftFunctor.{v, u}.obj X)) :=
  ⟨fun z => toTopULiftIso.{u, v}.inv.app X (ULift.up z),
    (toTopULiftIso.{u, v}.inv.app X).hom.continuous.comp continuous_uliftUp⟩

private theorem originalDownSimplexComputed
    (X : SSet.{u}) (n : SimplexCategory) (σ : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    originalRealizationDown.{u, v} X
        (toTop.map (yonedaEquiv.symm
          (ULift.up σ : (uliftFunctor.{v, u}.obj X).obj (op n)))
          ((toTopSimplex.{max u v}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max u v}.obj n))) =
      toTop.map (yonedaEquiv.symm σ) ((toTopSimplex.{u}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{u}.obj n)) := by
  let J : stdSimplex.{max u v}.obj n ⟶ uliftFunctor.{v, u}.obj (stdSimplex.{u}.obj n) :=
    { app Δ := ↾fun a => ULift.up (ULift.up a.down)
      naturality := by intro Δ Γ f; ext a; rfl }
  let g : stdSimplex.{u}.obj n ⟶ X := yonedaEquiv.symm σ
  let y : SimplexCategory.toTop.{max u v}.obj n := ULift.up t
  let z := toTop.map J ((toTopSimplex.{max u v}.inv.app n) y)
  have hJ : J ≫ uliftFunctor.{v, u}.map g =
      yonedaEquiv.symm (ULift.up σ : (uliftFunctor.{v, u}.obj X).obj (op n)) := by
    ext Δ a
    rfl
  have hLift : toTop.map (yonedaEquiv.symm
      (ULift.up σ : (uliftFunctor.{v, u}.obj X).obj (op n)))
        ((toTopSimplex.{max u v}.inv.app n) y) =
      toTop.map (uliftFunctor.{v, u}.map g) z := by
    calc
      _ = toTop.map (J ≫ uliftFunctor.{v, u}.map g)
          ((toTopSimplex.{max u v}.inv.app n) y) :=
        congrArg (fun f : stdSimplex.{max u v}.obj n ⟶ uliftFunctor.{v, u}.obj X =>
          toTop.map f ((toTopSimplex.{max u v}.inv.app n) y)) hJ.symm
      _ = (toTop.map J ≫ toTop.map (uliftFunctor.{v, u}.map g))
          ((toTopSimplex.{max u v}.inv.app n) y) :=
        ConcreteCategory.congr_hom (toTop.map_comp J (uliftFunctor.{v, u}.map g))
          ((toTopSimplex.{max u v}.inv.app n) y)
      _ = toTop.map (uliftFunctor.{v, u}.map g) z := TopCat.comp_app _ _ _
  have hStandard := toTopULiftIso_hom_simplexValue.{u, v} n t
  change toTopULiftIso.{u, v}.hom.app (stdSimplex.{u}.obj n) z =
    (ULift.up ((toTopSimplex.{u}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{u}.obj n)) :
        TopCat.uliftFunctor.{v, u}.obj (toTop.obj (stdSimplex.{u}.obj n))) at hStandard
  have hNat := ConcreteCategory.congr_hom
    (toTopULiftIso.{u, v}.hom.naturality g) z
  have hValue : toTopULiftIso.{u, v}.hom.app X
      (toTop.map (uliftFunctor.{v, u}.map g) z) =
      (ULift.up (toTop.map g ((toTopULiftIso.{u, v}.hom.app (stdSimplex.{u}.obj n)) z).down) :
        TopCat.uliftFunctor.{v, u}.obj (toTop.obj X)) := by
    change toTopULiftIso.{u, v}.hom.app X
      (toTop.map (uliftFunctor.{v, u}.map g) z) =
      (ULift.up (toTop.map g
        ((toTopULiftIso.{u, v}.hom.app (stdSimplex.{u}.obj n)) z).down) :
          TopCat.uliftFunctor.{v, u}.obj (toTop.obj X)) at hNat
    exact hNat
  change (toTopULiftIso.{u, v}.hom.app X
      (toTop.map (yonedaEquiv.symm (ULift.up σ))
        ((toTopSimplex.{max u v}.inv.app n) y))).down = _
  exact (congrArg (fun q => (toTopULiftIso.{u, v}.hom.app X q).down) hLift).trans
    ((congrArg ULift.down hValue).trans
      (congrArg (toTop.map g) (congrArg ULift.down hStandard)))

/-- Every original lifted simplex and barycentric point returns unchanged. -/
theorem originalRealizationDown_simplexValue
    (X : SSet.{u}) (n : SimplexCategory) (σ : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    originalRealizationDown.{u, v} X
        (toTop.map (yonedaEquiv.symm
          (ULift.up σ : (uliftFunctor.{v, u}.obj X).obj (op n)))
          ((toTopSimplex.{max u v}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max u v}.obj n))) =
      toTop.map (yonedaEquiv.symm σ) ((toTopSimplex.{u}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{u}.obj n)) :=
  originalDownSimplexComputed X n σ t

/-- Actual mixed realization of a map between the two original carrier lifts. -/
def originalMixedRealization {X : SSet.{u}} {Y : SSet.{v}}
    (M : uliftFunctor.{v, u}.obj X ⟶ uliftFunctor.{u, v}.obj Y) :
    C(toTop.obj X, toTop.obj Y) :=
  (originalRealizationDown.{v, u} Y).comp
    ((toTop.map M).hom.comp (originalRealizationUp.{u, v} X))


/-- Both original realization charts are inverse on every original point. -/
theorem originalRealizationDown_up (X : SSet.{u}) (x : toTop.obj X) :
    originalRealizationDown.{u, v} X (originalRealizationUp.{u, v} X x) = x := by
  have h := ConcreteCategory.congr_hom (toTopULiftIso.{u, v}.app X).inv_hom_id (ULift.up x)
  exact congrArg ULift.down h

/-- The other original chart composition is identity on every lifted point. -/
theorem originalRealizationUp_down (X : SSet.{u})
    (z : toTop.obj (uliftFunctor.{v, u}.obj X)) :
    originalRealizationUp.{u, v} X (originalRealizationDown.{u, v} X z) = z := by
  have h := ConcreteCategory.congr_hom (toTopULiftIso.{u, v}.app X).hom_inv_id z
  exact h

/-- The original down chart commutes with an actual original same-universe
simplicial map, using the original universe-change naturality. -/
theorem originalRealizationDown_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (z : toTop.obj (uliftFunctor.{v, u}.obj X)) :
    originalRealizationDown.{u, v} Y (toTop.map (uliftFunctor.{v, u}.map f) z) =
      toTop.map f (originalRealizationDown.{u, v} X z) := by
  have h := ConcreteCategory.congr_hom (toTopULiftIso.{u, v}.hom.naturality f) z
  change toTopULiftIso.{u, v}.hom.app Y (toTop.map (uliftFunctor.{v, u}.map f) z) =
    (ULift.up (toTop.map f (toTopULiftIso.{u, v}.hom.app X z).down) :
      TopCat.uliftFunctor.{v, u}.obj (toTop.obj Y)) at h
  exact congrArg ULift.down h

/-- The original up chart also commutes with actual simplicial maps. -/
theorem originalRealizationUp_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : toTop.obj X) :
    toTop.map (uliftFunctor.{v, u}.map f) (originalRealizationUp.{u, v} X x) =
      originalRealizationUp.{u, v} Y (toTop.map f x) := by
  have h := ConcreteCategory.congr_hom (toTopULiftIso.{u, v}.inv.naturality f) (ULift.up x)
  exact h.symm

/-- Actual mixed realization respects original ordinary source precomposition. -/
theorem originalMixedRealization_precomp
    {X Z : SSet.{u}} {Y : SSet.{v}} (f : X ⟶ Z)
    (M : uliftFunctor.{v, u}.obj Z ⟶ uliftFunctor.{u, v}.obj Y) :
    originalMixedRealization (uliftFunctor.{v, u}.map f ≫ M) =
      (originalMixedRealization M).comp (toTop.map f).hom := by
  apply ContinuousMap.ext
  intro x
  have hComp := ConcreteCategory.congr_hom (toTop.map_comp (uliftFunctor.{v, u}.map f) M)
    (originalRealizationUp.{u, v} X x)
  have hUp := originalRealizationUp_naturality.{u, v} f x
  change originalRealizationDown.{v, u} Y
    (toTop.map (uliftFunctor.{v, u}.map f ≫ M) (originalRealizationUp.{u, v} X x)) = _
  exact (congrArg (originalRealizationDown.{v, u} Y) hComp).trans
    (congrArg (fun z => originalRealizationDown.{v, u} Y (toTop.map M z)) hUp)

/-- Actual mixed realization respects original ordinary target postcomposition. -/
theorem originalMixedRealization_postcomp
    {X : SSet.{u}} {Y Z : SSet.{v}}
    (M : uliftFunctor.{v, u}.obj X ⟶ uliftFunctor.{u, v}.obj Y) (g : Y ⟶ Z) :
    originalMixedRealization (M ≫ uliftFunctor.{u, v}.map g) =
      (toTop.map g).hom.comp (originalMixedRealization M) := by
  apply ContinuousMap.ext
  intro x
  have hComp := ConcreteCategory.congr_hom (toTop.map_comp M (uliftFunctor.{u, v}.map g))
    (originalRealizationUp.{u, v} X x)
  change originalRealizationDown.{v, u} Z
    (toTop.map (M ≫ uliftFunctor.{u, v}.map g) (originalRealizationUp.{u, v} X x)) = _
  exact (congrArg (originalRealizationDown.{v, u} Z) hComp).trans
    (originalRealizationDown_naturality.{v, u} g (toTop.map M (originalRealizationUp.{u, v} X x)))

/-- The SAME actual lifted simplicial square yields a whole equality of the
original mixed realization maps, without identifying the original worlds. -/
theorem originalMixedRealization_square
    {X Z : SSet.{u}} {Y W : SSet.{v}}
    (M : uliftFunctor.{v, u}.obj X ⟶ uliftFunctor.{u, v}.obj Y)
    (N : uliftFunctor.{v, u}.obj Z ⟶ uliftFunctor.{u, v}.obj W)
    (f : X ⟶ Z) (g : Y ⟶ W)
    (h : M ≫ uliftFunctor.{u, v}.map g = uliftFunctor.{v, u}.map f ≫ N) :
    (toTop.map g).hom.comp (originalMixedRealization M) =
      (originalMixedRealization N).comp (toTop.map f).hom :=
  (originalMixedRealization_postcomp M g).symm.trans
    ((congrArg originalMixedRealization h).trans (originalMixedRealization_precomp f N))


private theorem originalSimplexMapValueComputed
    {X Y : SSet.{u}} (f : X ⟶ Y) (n : SimplexCategory) (σ : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    toTop.map f (toTop.map (yonedaEquiv.symm σ)
      ((toTopSimplex.{u}.inv.app n) (ULift.up t : SimplexCategory.toTop.{u}.obj n))) =
    toTop.map (yonedaEquiv.symm (f.app (op n) σ))
      ((toTopSimplex.{u}.inv.app n) (ULift.up t : SimplexCategory.toTop.{u}.obj n)) := by
  let z := (toTopSimplex.{u}.inv.app n) (ULift.up t : SimplexCategory.toTop.{u}.obj n)
  exact (TopCat.comp_app (toTop.map (yonedaEquiv.symm σ)) (toTop.map f) z).symm.trans
    ((ConcreteCategory.congr_hom (toTop.map_comp (yonedaEquiv.symm σ) f).symm z).trans
      (congrArg (fun g : stdSimplex.{u}.obj n ⟶ Y => toTop.map g z)
        (yonedaEquiv_symm_comp σ f)))

/-- The actual same-universe simplicial map retains every original simplex value. -/
theorem originalSimplexMapValue
    {X Y : SSet.{u}} (f : X ⟶ Y) (n : SimplexCategory) (σ : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    toTop.map f (toTop.map (yonedaEquiv.symm σ)
      ((toTopSimplex.{u}.inv.app n) (ULift.up t : SimplexCategory.toTop.{u}.obj n))) =
    toTop.map (yonedaEquiv.symm (f.app (op n) σ))
      ((toTopSimplex.{u}.inv.app n) (ULift.up t : SimplexCategory.toTop.{u}.obj n)) :=
  originalSimplexMapValueComputed f n σ t

/-- EVERY original point of a realization has an actual simplex/barycentric
presentation. No presentation or surjectivity outcome is supplied. -/
theorem originalSimplexPresentation (X : SSet.{u}) (x : toTop.obj X) :
    ∃ (n : SimplexCategory) (σ : X.obj (op n))
      (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))),
      toTop.map (yonedaEquiv.symm σ)
        ((toTopSimplex.{u}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{u}.obj n)) = x := by
  let c := Presheaf.tautologicalCocone' (C := SimplexCategory) (P := X)
  have hc : IsColimit c := Presheaf.isColimitTautologicalCocone' X
  have hcTop : IsColimit (toTop.mapCocone c) := isColimitOfPreserves toTop hc
  have hcType : IsColimit ((toTop ⋙ forget TopCat).mapCocone c) :=
    isColimitOfPreserves (forget TopCat) hcTop
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcType x
  let σ : X.obj (op j.left) := CategoryTheory.uliftYonedaEquiv j.hom
  let t := (SimplexCategory.toTopHomeo.{u} j.left) y
  have hσ : yonedaEquiv.symm σ = j.hom := yonedaEquiv.symm_apply_apply j.hom
  have hPoint : (toTopSimplex.{u}.inv.app j.left)
      (ULift.up t : SimplexCategory.toTop.{u}.obj j.left) = y :=
    (SimplexCategory.toTopHomeo.{u} j.left).symm_apply_apply y
  exact ⟨j.left, σ, t,
    (congrArg (fun f : stdSimplex.{u}.obj j.left ⟶ X => toTop.map f
      ((toTopSimplex.{u}.inv.app j.left) (ULift.up t : SimplexCategory.toTop.{u}.obj j.left)))
        hσ).trans ((congrArg (toTop.map j.hom) hPoint).trans hy)⟩

private theorem originalMixedSimplexValueComputed
    {X : SSet.{u}} {Y : SSet.{v}}
    (M : uliftFunctor.{v, u}.obj X ⟶ uliftFunctor.{u, v}.obj Y)
    (n : SimplexCategory) (σ : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    originalMixedRealization M
        (toTop.map (yonedaEquiv.symm σ)
          ((toTopSimplex.{u}.inv.app n) (ULift.up t : SimplexCategory.toTop.{u}.obj n))) =
      toTop.map (yonedaEquiv.symm (M.app (op n) (ULift.up σ)).down)
        ((toTopSimplex.{v}.inv.app n) (ULift.up t : SimplexCategory.toTop.{v}.obj n)) := by
  let x := toTop.map (yonedaEquiv.symm σ)
    ((toTopSimplex.{u}.inv.app n) (ULift.up t : SimplexCategory.toTop.{u}.obj n))
  let z := toTop.map
    (yonedaEquiv.symm
      (ULift.up σ : (uliftFunctor.{v, u}.obj X).obj (op n)) :
        stdSimplex.{max u v}.obj n ⟶ uliftFunctor.{v, u}.obj X)
      ((toTopSimplex.{max u v}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{max u v}.obj n))
  have hDown : originalRealizationDown.{u, v} X z = x :=
    originalRealizationDown_simplexValue X n σ t
  have hUp : originalRealizationUp.{u, v} X x = z :=
    (congrArg (originalRealizationUp.{u, v} X) hDown).symm.trans
      (originalRealizationUp_down X z)
  have hMap := originalSimplexMapValue M n
    (ULift.up σ : (uliftFunctor.{v, u}.obj X).obj (op n)) t
  have hTarget := originalRealizationDown_simplexValue.{v, u} Y n
    (M.app (op n) (ULift.up σ)).down t
  change originalRealizationDown.{v, u} Y
    (toTop.map M (originalRealizationUp.{u, v} X x)) = _
  exact (congrArg (fun q => originalRealizationDown.{v, u} Y (toTop.map M q)) hUp).trans
    ((congrArg (originalRealizationDown.{v, u} Y) hMap).trans hTarget)

/-- EVERY original simplex point of the mixed realization map retains its
actual original chain image, in independent source and target worlds. -/
theorem originalMixedRealization_simplexValue
    {X : SSet.{u}} {Y : SSet.{v}}
    (M : uliftFunctor.{v, u}.obj X ⟶ uliftFunctor.{u, v}.obj Y)
    (n : SimplexCategory) (σ : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    originalMixedRealization M
        (toTop.map (yonedaEquiv.symm σ)
          ((toTopSimplex.{u}.inv.app n) (ULift.up t : SimplexCategory.toTop.{u}.obj n))) =
      toTop.map (yonedaEquiv.symm (M.app (op n) (ULift.up σ)).down)
        ((toTopSimplex.{v}.inv.app n) (ULift.up t : SimplexCategory.toTop.{v}.obj n)) :=
  originalMixedSimplexValueComputed M n σ t

end SSet

end


public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe u v

namespace SSet

private theorem originalMixedRealizationValueComputed
    {X : SSet.{u}} {Y : SSet.{v}}
    (M : uliftFunctor.{v, u}.obj X ⟶ uliftFunctor.{u, v}.obj Y) (x : toTop.obj X) :
    originalMixedRealization M x =
      ((toTopULiftIso.{v, u}.hom.app Y)
        (toTop.map M ((toTopULiftIso.{u, v}.inv.app X) (ULift.up x)))).down := rfl

/-- Every original mixed realization point uses precisely the original
source lift, SAME simplicial map and original target down chart. -/
theorem originalMixedRealization_apply
    {X : SSet.{u}} {Y : SSet.{v}}
    (M : uliftFunctor.{v, u}.obj X ⟶ uliftFunctor.{u, v}.obj Y) (x : toTop.obj X) :
    originalMixedRealization M x =
      ((toTopULiftIso.{v, u}.hom.app Y)
        (toTop.map M ((toTopULiftIso.{u, v}.inv.app X) (ULift.up x)))).down :=
  originalMixedRealizationValueComputed M x

end SSet

end

public section

universe u v

namespace SSet

private theorem originalRealizationDown_apply_computed (X : SSet.{u})
    (z : toTop.obj (uliftFunctor.{v, u}.obj X)) :
    originalRealizationDown.{u, v} X z = (toTopULiftIso.{u, v}.hom.app X z).down := rfl

private theorem originalRealizationUp_apply_computed (X : SSet.{u}) (z : toTop.obj X) :
    originalRealizationUp.{u, v} X z = toTopULiftIso.{u, v}.inv.app X (ULift.up z) := rfl

/-- The original down chart evaluates by its same actual realization-lift isomorphism. -/
theorem originalRealizationDown_apply (X : SSet.{u})
    (z : toTop.obj (uliftFunctor.{v, u}.obj X)) :
    originalRealizationDown.{u, v} X z = (toTopULiftIso.{u, v}.hom.app X z).down :=
  originalRealizationDown_apply_computed X z

/-- The original up chart evaluates by its same actual inverse realization-lift isomorphism. -/
theorem originalRealizationUp_apply (X : SSet.{u}) (z : toTop.obj X) :
    originalRealizationUp.{u, v} X z = toTopULiftIso.{u, v}.inv.app X (ULift.up z) :=
  originalRealizationUp_apply_computed X z

end SSet
