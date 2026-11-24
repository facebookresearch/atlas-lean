/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUniverseLift
public import Mathlib.CategoryTheory.Category.ULift
public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
public import Mathlib.Topology.Homotopy.Path

/-!
# Actual realization of object and Hom universe lifts

The original up/down category functors identify each lifted nerve with
the ordinary value lift of its original nerve. The actual realization
universe Iso then gives homeomorphisms back to the original realization,
with the original vertex retained in both directions. No category,
space, homology, or inverse witness is supplied.
-/

noncomputable section

open CategoryTheory
open scoped Simplicial

attribute [local instance] uliftCategory

universe u v w

namespace SSet

/-- Object lifting keeps every original composable-arrow chain. -/
public def nerveULiftIso (C : Type u) [Category.{v} C] :
    nerve (ULift.{w} C) ≅ uliftFunctor.{w, max u v}.obj (nerve C) :=
  NatIso.ofComponents (fun D =>
    Equiv.toIso
      { toFun := fun X => ULift.up (X ⋙ ULift.downFunctor)
        invFun := fun X => X.down ⋙ ULift.upFunctor
        left_inv := by
          intro X
          exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
            dsimp only [CategoryTheory.Functor.comp, ULift.downFunctor, ULift.upFunctor]
            change X.map f =
              eqToHom (rfl : X.obj i = X.obj i) ≫ X.map f ≫
                eqToHom (rfl : X.obj j = X.obj j)
            exact CategoryTheory.eq_conj_eqToHom (X.map f))
        right_inv := by
          intro X
          apply ULift.ext
          exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
            dsimp only [CategoryTheory.Functor.comp, ULift.upFunctor, ULift.downFunctor]
            change X.down.map f =
              eqToHom (rfl : X.down.obj i = X.down.obj i) ≫ X.down.map f ≫
                eqToHom (rfl : X.down.obj j = X.down.obj j)
            exact CategoryTheory.eq_conj_eqToHom (X.down.map f)) })
    (by intro D E f; ext X; apply ULift.ext; rfl)

/-- Hom lifting keeps every original composable-arrow chain. -/
public def nerveULiftHomIso (C : Type u) [Category.{v} C] :
    nerve (ULiftHom.{w} C) ≅ uliftFunctor.{w, max u v}.obj (nerve C) :=
  NatIso.ofComponents (fun D =>
    Equiv.toIso
      { toFun := fun X => ULift.up (X ⋙ ULiftHom.down)
        invFun := fun X => X.down ⋙ ULiftHom.up
        left_inv := by
          intro X
          exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
            dsimp only [CategoryTheory.Functor.comp, ULiftHom.down, ULiftHom.up,
              ULiftHom.objDown, ULiftHom.objUp]
            change X.map f =
              eqToHom (rfl : X.obj i = X.obj i) ≫ X.map f ≫
                eqToHom (rfl : X.obj j = X.obj j)
            exact CategoryTheory.eq_conj_eqToHom (X.map f))
        right_inv := by
          intro X
          apply ULift.ext
          exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
            dsimp only [CategoryTheory.Functor.comp, ULiftHom.up, ULiftHom.down,
              ULiftHom.objUp, ULiftHom.objDown]
            change X.down.map f =
              eqToHom (rfl : X.down.obj i = X.down.obj i) ≫ X.down.map f ≫
                eqToHom (rfl : X.down.obj j = X.down.obj j)
            exact CategoryTheory.eq_conj_eqToHom (X.down.map f)) })
    (by intro D E f; ext X; apply ULift.ext; rfl)

/-- The object-lift Iso retains the literal original vertex. -/
public theorem nerveULiftIso_hom_mk₀ (C : Type u) [Category.{v} C] (c : C) :
    ((nerveULiftIso.{u, v, w} C).hom.app (Opposite.op ⦋0⦌))
        (ComposableArrows.mk₀ (ULift.up c : ULift.{w} C)) =
      (ULift.up (ComposableArrows.mk₀ c) :
        (uliftFunctor.{w, max u v}.obj (nerve C)) _⦋0⦌) := by
  change ULift.up ((ComposableArrows.mk₀ (ULift.up c)) ⋙ ULift.downFunctor) = _
  apply congrArg ULift.up
  apply ComposableArrows.ext₀
  rfl

/-- The Hom-lift Iso retains the literal original vertex. -/
public theorem nerveULiftHomIso_hom_mk₀ (C : Type u) [Category.{v} C] (c : C) :
    ((nerveULiftHomIso.{u, v, w} C).hom.app (Opposite.op ⦋0⦌))
        (ComposableArrows.mk₀ (ULiftHom.objUp c : ULiftHom.{w} C)) =
      (ULift.up (ComposableArrows.mk₀ c) :
        (uliftFunctor.{w, max u v}.obj (nerve C)) _⦋0⦌) := by
  change ULift.up ((ComposableArrows.mk₀ (ULiftHom.objUp c)) ⋙ ULiftHom.down) = _
  apply congrArg ULift.up
  apply ComposableArrows.ext₀
  rfl

/-- The realization of the object-lifted category is homeomorphic to the
ORIGINAL realization through the actual Iso and original `ULift.down`. -/
public def realizedNerveULiftHomeomorph (C : Type u) [Category.{v} C] :
    toTop.obj (nerve (ULift.{w} C)) ≃ₜ toTop.obj (nerve C) :=
  (TopCat.homeoOfIso
    ((toTop.mapIso (nerveULiftIso.{u, v, w} C)) ≪≫
      (toTopULiftIso.{max u v, w}.app (nerve C)))).trans Homeomorph.ulift

/-- The realization of the Hom-lifted category is homeomorphic to the
ORIGINAL realization through the actual Iso and original `ULift.down`. -/
public def realizedNerveULiftHomHomeomorph (C : Type u) [Category.{v} C] :
    toTop.obj (nerve (ULiftHom.{w} C)) ≃ₜ toTop.obj (nerve C) :=
  (TopCat.homeoOfIso
    ((toTop.mapIso (nerveULiftHomIso.{u, v, w} C)) ≪≫
      (toTopULiftIso.{max u v, w}.app (nerve C)))).trans Homeomorph.ulift

/-- Every object-lifted point has the computed original carrier value. -/
public theorem realizedNerveULiftHomeomorph_apply (C : Type u) [Category.{v} C]
    (y : toTop.obj (nerve (ULift.{w} C))) :
    realizedNerveULiftHomeomorph.{u, v, w} C y =
      ((toTopULiftIso.{max u v, w}.hom.app (nerve C))
        (toTop.map (nerveULiftIso.{u, v, w} C).hom y)).down := by
  unfold realizedNerveULiftHomeomorph
  rfl

/-- Every Hom-lifted point has the computed original carrier value. -/
public theorem realizedNerveULiftHomHomeomorph_apply (C : Type u) [Category.{v} C]
    (y : toTop.obj (nerve (ULiftHom.{w} C))) :
    realizedNerveULiftHomHomeomorph.{u, v, w} C y =
      ((toTopULiftIso.{max u v, w}.hom.app (nerve C))
        (toTop.map (nerveULiftHomIso.{u, v, w} C).hom y)).down := by
  unfold realizedNerveULiftHomHomeomorph
  rfl

/-- The object-lift homeomorphism retains every ORIGINAL realized vertex. -/
public theorem realizedNerveULiftHomeomorph_vertex (C : Type u) [Category.{v} C] (c : C) :
    realizedNerveULiftHomeomorph.{u, v, w} C
        (realizedVertex (X := nerve (ULift.{w} C))
          (ComposableArrows.mk₀ (ULift.up c : ULift.{w} C))) =
      realizedVertex (X := nerve C) (ComposableArrows.mk₀ c) := by
  have hN := (realizedVertex_naturality (X := nerve (ULift.{w} C))
    (Y := uliftFunctor.{w, max u v}.obj (nerve C)) (nerveULiftIso.{u, v, w} C).hom
    (ComposableArrows.mk₀ (ULift.up c : ULift.{w} C))).symm.trans
      (congrArg (fun q => realizedVertex (X := uliftFunctor.{w, max u v}.obj (nerve C)) q)
        (nerveULiftIso_hom_mk₀.{u, v, w} C c))
  have hU := toTopULiftIso_hom_realizedVertex.{max u v, w}
    (nerve C) (ComposableArrows.mk₀ c)
  exact (realizedNerveULiftHomeomorph_apply.{u, v, w} C _).trans
    (congrArg ULift.down ((congrArg
      (toTopULiftIso.{max u v, w}.hom.app (nerve C)) hN).trans hU))

/-- The Hom-lift homeomorphism retains every ORIGINAL realized vertex. -/
public theorem realizedNerveULiftHomHomeomorph_vertex (C : Type u) [Category.{v} C] (c : C) :
    realizedNerveULiftHomHomeomorph.{u, v, w} C
        (realizedVertex (X := nerve (ULiftHom.{w} C))
          (ComposableArrows.mk₀ (ULiftHom.objUp c : ULiftHom.{w} C))) =
      realizedVertex (X := nerve C) (ComposableArrows.mk₀ c) := by
  have hN := (realizedVertex_naturality (X := nerve (ULiftHom.{w} C))
    (Y := uliftFunctor.{w, max u v}.obj (nerve C)) (nerveULiftHomIso.{u, v, w} C).hom
    (ComposableArrows.mk₀ (ULiftHom.objUp c : ULiftHom.{w} C))).symm.trans
      (congrArg (fun q => realizedVertex (X := uliftFunctor.{w, max u v}.obj (nerve C)) q)
        (nerveULiftHomIso_hom_mk₀.{u, v, w} C c))
  have hU := toTopULiftIso_hom_realizedVertex.{max u v, w}
    (nerve C) (ComposableArrows.mk₀ c)
  exact (realizedNerveULiftHomHomeomorph_apply.{u, v, w} C _).trans
    (congrArg ULift.down ((congrArg
      (toTopULiftIso.{max u v, w}.hom.app (nerve C)) hN).trans hU))

/-- Both category universe lifts have the SAME original realization. -/
public def realizedNerveLiftHomeomorph (C : Type u) [Category.{v} C] :
    toTop.obj (nerve (ULiftHom.{w} (ULift.{w} C))) ≃ₜ toTop.obj (nerve C) :=
  (realizedNerveULiftHomHomeomorph.{max u w, v, w} (ULift.{w} C)).trans
    (realizedNerveULiftHomeomorph.{u, v, w} C)

/-- The combined lift homeomorphism retains every ORIGINAL object vertex. -/
public theorem realizedNerveLiftHomeomorph_vertex (C : Type u) [Category.{v} C] (c : C) :
    realizedNerveLiftHomeomorph.{u, v, w} C
        (realizedVertex (X := nerve (ULiftHom.{w} (ULift.{w} C))) (ComposableArrows.mk₀
          (ULiftHom.objUp (ULift.up c) : ULiftHom.{w} (ULift.{w} C)))) =
      realizedVertex (X := nerve C) (ComposableArrows.mk₀ c) := by
  unfold realizedNerveLiftHomeomorph
  exact (congrArg (realizedNerveULiftHomeomorph.{u, v, w} C)
    (realizedNerveULiftHomHomeomorph_vertex.{max u w, v, w}
      (ULift.{w} C) (ULift.up c))).trans
    (realizedNerveULiftHomeomorph_vertex.{u, v, w} C c)

/-- Its actual inverse retains every ORIGINAL object vertex as well. -/
public theorem realizedNerveLiftHomeomorph_symm_vertex
    (C : Type u) [Category.{v} C] (c : C) :
    (realizedNerveLiftHomeomorph.{u, v, w} C).symm
        (realizedVertex (X := nerve C) (ComposableArrows.mk₀ c)) =
      realizedVertex (X := nerve (ULiftHom.{w} (ULift.{w} C))) (ComposableArrows.mk₀
        (ULiftHom.objUp (ULift.up c) : ULiftHom.{w} (ULift.{w} C))) := by
  have h := congrArg (realizedNerveLiftHomeomorph.{u, v, w} C).symm
    (realizedNerveLiftHomeomorph_vertex.{u, v, w} C c)
  exact h.symm.trans ((realizedNerveLiftHomeomorph.{u, v, w} C).symm_apply_apply _)

end SSet

universe uC vC uD vD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

private def liftedCategoryEquivalence (E : C ≌ D) :
    ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C) ≌
      ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D) :=
  (ULiftHomULiftCategory.equiv.{max uC vC uD vD, max uC vC uD vD, vC, uC} C).symm.trans
    (E.trans (ULiftHomULiftCategory.equiv.{max uC vC uD vD, max uC vC uD vD, vD, uD} D))

private def liftedRealizedEquivalence (E : C ≌ D) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C))))
      (SSet.toTop.obj (nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D)))) := by
  let L := liftedCategoryEquivalence E
  let f := nerveMap L.functor
  let g := nerveMap L.inverse
  have hLeft : SSet.Homotopy (f ≫ g) (𝟙 _) := by
    change SSet.Homotopy (nerveMap L.functor ≫ nerveMap L.inverse) (𝟙 _)
    rw [nerveMap_comp, ← nerveMap_id]
    exact NatTrans.nerveHomotopy L.unitInv
  have hRight : SSet.Homotopy (g ≫ f) (𝟙 _) := by
    change SSet.Homotopy (nerveMap L.inverse ≫ nerveMap L.functor) (𝟙 _)
    rw [nerveMap_comp, ← nerveMap_id]
    exact NatTrans.nerveHomotopy L.counit
  exact SSet.realizedHomotopyEquiv _ _ f g hLeft hRight

/-- A genuine category equivalence gives an ACTUAL homotopy equivalence
between its original realizations in independent object/Hom universes.
The two existing category lifts and their actual realization homeomorphisms
transport the original functor and inverse; no space/model witness is given. -/
public def realizedNerveEquivalence (E : C ≌ D) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj (nerve C))
      (SSet.toTop.obj (nerve D)) :=
  (SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD} C).symm.toHomotopyEquiv.trans
    ((liftedRealizedEquivalence E).trans
      (SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD} D).toHomotopyEquiv)

/-- The actual forward map retains the original functor at EVERY object vertex. -/
public theorem realizedNerveEquivalence_vertex (E : C ≌ D) (c : C) :
    (realizedNerveEquivalence E).toFun
        (SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ c)) =
      SSet.realizedVertex (X := nerve D) (ComposableArrows.mk₀ (E.functor.obj c)) := by
  let HC := SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD} C
  let HD := SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD} D
  let L := liftedCategoryEquivalence E
  let x : ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C) :=
    ULiftHom.objUp (ULift.up c)
  have hC := SSet.realizedNerveLiftHomeomorph_symm_vertex.{uC, vC, max uC vC uD vD} C c
  have hMiddle : (liftedRealizedEquivalence E).toFun
      (SSet.realizedVertex (X := nerve (ULiftHom.{max uC vC uD vD}
        (ULift.{max uC vC uD vD} C))) (ComposableArrows.mk₀ x)) =
    SSet.realizedVertex (X := nerve (ULiftHom.{max uC vC uD vD}
      (ULift.{max uC vC uD vD} D))) (ComposableArrows.mk₀ (L.functor.obj x)) :=
      (SSet.realizedVertex_naturality
        (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C)))
        (Y := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D)))
        (nerveMap L.functor) (ComposableArrows.mk₀ x)).symm.trans
        (congrArg (fun q => SSet.realizedVertex
          (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D))) q)
          (nerveMap_app_mk₀ L.functor x))
  have hObject : L.functor.obj x =
      (ULiftHom.objUp (ULift.up (E.functor.obj c)) :
        ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D)) := rfl
  change HD ((liftedRealizedEquivalence E).toFun
    (HC.symm (SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ c)))) = _
  exact (congrArg (fun y => HD ((liftedRealizedEquivalence E).toFun y)) hC).trans
    ((congrArg HD (hMiddle.trans (congrArg
      (fun y => SSet.realizedVertex (X := nerve (ULiftHom.{max uC vC uD vD}
        (ULift.{max uC vC uD vD} D))) (ComposableArrows.mk₀ y)) hObject))).trans
        (SSet.realizedNerveLiftHomeomorph_vertex.{uD, vD, max uC vC uD vD} D _))

/-- The actual inverse map retains the original inverse functor at EVERY vertex.
This does not assert that a separately selected point is fixed by that inverse. -/
public theorem realizedNerveEquivalence_inv_vertex (E : C ≌ D) (d : D) :
    (realizedNerveEquivalence E).invFun
        (SSet.realizedVertex (X := nerve D) (ComposableArrows.mk₀ d)) =
      SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ (E.inverse.obj d)) := by
  let HC := SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD} C
  let HD := SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD} D
  let L := liftedCategoryEquivalence E
  let y : ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D) :=
    ULiftHom.objUp (ULift.up d)
  have hD := SSet.realizedNerveLiftHomeomorph_symm_vertex.{uD, vD, max uC vC uD vD} D d
  have hMiddle : (liftedRealizedEquivalence E).invFun
      (SSet.realizedVertex (X := nerve (ULiftHom.{max uC vC uD vD}
        (ULift.{max uC vC uD vD} D))) (ComposableArrows.mk₀ y)) =
    SSet.realizedVertex (X := nerve (ULiftHom.{max uC vC uD vD}
      (ULift.{max uC vC uD vD} C))) (ComposableArrows.mk₀ (L.inverse.obj y)) :=
      (SSet.realizedVertex_naturality
        (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D)))
        (Y := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C)))
        (nerveMap L.inverse) (ComposableArrows.mk₀ y)).symm.trans
        (congrArg (fun q => SSet.realizedVertex
          (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C))) q)
          (nerveMap_app_mk₀ L.inverse y))
  have hObject : L.inverse.obj y =
      (ULiftHom.objUp (ULift.up (E.inverse.obj d)) :
        ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C)) := rfl
  change HC ((liftedRealizedEquivalence E).invFun
    (HD.symm (SSet.realizedVertex (X := nerve D) (ComposableArrows.mk₀ d)))) = _
  exact (congrArg (fun x => HC ((liftedRealizedEquivalence E).invFun x)) hD).trans
    ((congrArg HC (hMiddle.trans (congrArg
      (fun x => SSet.realizedVertex (X := nerve (ULiftHom.{max uC vC uD vD}
        (ULift.{max uC vC uD vD} C))) (ComposableArrows.mk₀ x)) hObject))).trans
        (SSet.realizedNerveLiftHomeomorph_vertex.{uC, vC, max uC vC uD vD} C _))

end CategoryTheory

end

noncomputable section

open CategoryTheory unitInterval
open scoped ContinuousMap Simplicial

universe ue ve

namespace SSet

private def intervalPathsHomotopy {a b : unitInterval} (p q : Path a b) :
    Path.Homotopy p q where
  toFun z :=
    ⟨(σ z.1 : ℝ) * (p z.2 : ℝ) + (z.1 : ℝ) * (q z.2 : ℝ),
      show (σ z.1 : ℝ) • (p z.2 : ℝ) + (z.1 : ℝ) • (q z.2 : ℝ) ∈ unitInterval from
        convex_Icc _ _ (p z.2).property (q z.2).property
          (by unit_interval) (by unit_interval) (by simp)⟩
  continuous_toFun := by fun_prop
  map_zero_left t := by apply Subtype.ext; simp
  map_one_left t := by apply Subtype.ext; simp
  prop' s t ht := by
    rcases ht with ht | ht
    · subst t
      apply Subtype.ext
      change (σ s : ℝ) * (p 0 : ℝ) + (s : ℝ) * (q 0 : ℝ) = (p 0 : ℝ)
      simp only [p.source, q.source, unitInterval.coe_symm_eq]
      ring
    · have ht' : t = 1 := Set.mem_singleton_iff.mp ht
      subst t
      apply Subtype.ext
      change (σ s : ℝ) * (p 1 : ℝ) + (s : ℝ) * (q 1 : ℝ) = (p 1 : ℝ)
      simp only [p.target, q.target, unitInterval.coe_symm_eq]
      ring

private theorem realizedDeltaOnePathsHomotopic
    {a b : toTop.obj (Δ[1] : SSet.{ue})} (p q : Path a b) : p.Homotopic q := by
  let e : toTop.obj (Δ[1] : SSet.{ue}) ≃ₜ unitInterval :=
    (TopCat.homeoOfIso SSet.stdSimplex.toTopObjIsoI).trans TopCat.I.homeomorph
  let H := intervalPathsHomotopy (p.map e.continuous_toFun) (q.map e.continuous_toFun)
  have h := Path.Homotopic.pathCast (Path.Homotopic.map (⟨H⟩ :
    (p.map e.continuous_toFun).Homotopic (q.map e.continuous_toFun))
      e.symm.toHomotopyEquiv.toFun)
    (e.symm_apply_apply a).symm (e.symm_apply_apply b).symm
  have hp : ((p.map e.continuous_toFun).map e.symm.toHomotopyEquiv.toFun.continuous).cast
      (e.symm_apply_apply a).symm (e.symm_apply_apply b).symm = p := by
    apply Path.ext
    funext t
    change e.symm (e (p t)) = p t
    exact e.symm_apply_apply (p t)
  have hq : ((q.map e.continuous_toFun).map e.symm.toHomotopyEquiv.toFun.continuous).cast
      (e.symm_apply_apply a).symm (e.symm_apply_apply b).symm = q := by
    apply Path.ext
    funext t
    change e.symm (e (q t)) = q t
    exact e.symm_apply_apply (q t)
  obtain ⟨H'⟩ := h
  exact ⟨Path.Homotopy.cast H' hp hq⟩

private def edgeValueLift {X : SSet.{ue}} {a b : X _⦋0⦌} (e : X.Edge a b) :
    (uliftFunctor.{ve, ue}.obj X).Edge (ULift.up a) (ULift.up b) where
  edge := ULift.up e.edge
  src_eq := congrArg ULift.up e.src_eq
  tgt_eq := congrArg ULift.up e.tgt_eq

private def realizationValueDown (X : SSet.{ue}) :
    C(toTop.obj (uliftFunctor.{ve, ue}.obj X), toTop.obj X) :=
  Homeomorph.ulift.toHomotopyEquiv.toFun.comp (toTopULiftIso.{ue, ve}.hom.app X).hom

private theorem realizationValueDown_vertex (X : SSet.{ue}) (x : X _⦋0⦌) :
    realizationValueDown.{ue, ve} X
        (realizedVertex (X := uliftFunctor.{ve, ue}.obj X) (ULift.up x)) = realizedVertex x := by
  change ((toTopULiftIso.{ue, ve}.hom.app X)
    (realizedVertex (X := uliftFunctor.{ve, ue}.obj X) (ULift.up x))).down =
      realizedVertex (X := X) x
  exact congrArg
    (fun z : TopCat.uliftFunctor.{ve, ue}.obj (toTop.obj X) => z.down)
    (toTopULiftIso_hom_realizedVertex.{ue, ve} X x)

private theorem realizationValueDown_naturality {X Y : SSet.{ue}} (f : X ⟶ Y)
    (z : toTop.obj (uliftFunctor.{ve, ue}.obj X)) :
    realizationValueDown.{ue, ve} Y (toTop.map (uliftFunctor.{ve, ue}.map f) z) =
      toTop.map f (realizationValueDown.{ue, ve} X z) := by
  have h := ConcreteCategory.congr_hom (toTopULiftIso.{ue, ve}.hom.naturality f) z
  change (toTopULiftIso.{ue, ve}.hom.app Y)
      (toTop.map (uliftFunctor.{ve, ue}.map f) z) =
    TopCat.uliftFunctor.{ve, ue}.map (toTop.map f)
      ((toTopULiftIso.{ue, ve}.hom.app X) z) at h
  have hd := congrArg
    (fun w : TopCat.uliftFunctor.{ve, ue}.obj (toTop.obj Y) => w.down) h
  change ((toTopULiftIso.{ue, ve}.hom.app Y)
      (toTop.map (uliftFunctor.{ve, ue}.map f) z)).down =
    toTop.map f (((toTopULiftIso.{ue, ve}.hom.app X) z).down) at hd
  exact hd

private def deltaOneIdentityEdge :
    (Δ[1] : SSet.{ue}).Edge
      ((Δ[1] : SSet.{ue}).δ 1 (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)))
      ((Δ[1] : SSet.{ue}).δ 0 (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))) where
  edge := stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)
  src_eq := rfl
  tgt_eq := rfl

private theorem liftedEdgeSimplexMapFactor {X : SSet.{ue}} {a b : X _⦋0⦌}
    (e : X.Edge a b) :
    yonedaEquiv.symm (edgeValueLift.{ue, ve} e).edge =
      yonedaEquiv.symm (edgeValueLift.{ue, ve} deltaOneIdentityEdge).edge ≫
        uliftFunctor.{ve, ue}.map (yonedaEquiv.symm e.edge) := by
  let f : (Δ[1] : SSet.{ue}) ⟶ X := yonedaEquiv.symm e.edge
  have hf : f.app (Opposite.op ⦋1⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) = e.edge := by
    calc
      f.app (Opposite.op ⦋1⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) =
          X.map (𝟙 (Opposite.op ⦋1⦌)) e.edge := by
        simpa only [f, op_id] using
          (yonedaEquiv_symm_app_objEquiv_symm e.edge (𝟙 ⦋1⦌))
      _ = e.edge := ConcreteCategory.congr_hom (X.map_id (Opposite.op ⦋1⦌)) e.edge
  rw [yonedaEquiv_symm_comp]
  apply congrArg yonedaEquiv.symm
  exact (congrArg ULift.up hf).symm

private theorem edgeLiftDown_value {X : SSet.{ue}} {a b : X _⦋0⦌}
    (e : X.Edge a b) (t : unitInterval) :
    realizationValueDown.{ue, ve} X
        (TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{ue, ve} e)) t) =
      toTop.map (yonedaEquiv.symm e.edge)
        (realizationValueDown.{ue, ve} (Δ[1] : SSet.{ue})
          (TopCat.pathEquiv (realizedEdgePath
            (edgeValueLift.{ue, ve} deltaOneIdentityEdge)) t)) := by
  let f : (Δ[1] : SSet.{ue}) ⟶ X := yonedaEquiv.symm e.edge
  have he : TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{ue, ve} e)) t =
      toTop.map (uliftFunctor.{ve, ue}.map f)
        (TopCat.pathEquiv (realizedEdgePath
          (edgeValueLift.{ue, ve} deltaOneIdentityEdge)) t) := by
    change (stdSimplex.toTopObjIsoI.inv ≫
        toTop.map (yonedaEquiv.symm (edgeValueLift.{ue, ve} e).edge))
        (TopCat.I.homeomorph.symm t) = _
    rw [liftedEdgeSimplexMapFactor, Functor.map_comp]
    rfl
  rw [he]
  exact realizationValueDown_naturality f _

private theorem edgeIdentityMapped_value {X : SSet.{ue}} {a b : X _⦋0⦌}
    (e : X.Edge a b) (t : unitInterval) :
    toTop.map (yonedaEquiv.symm e.edge)
        (TopCat.pathEquiv (realizedEdgePath deltaOneIdentityEdge) t) =
      TopCat.pathEquiv (realizedEdgePath e) t := by
  let f : (Δ[1] : SSet.{ue}) ⟶ X := yonedaEquiv.symm e.edge
  have hf : f.app (Opposite.op ⦋1⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) = e.edge := by
    calc
      f.app (Opposite.op ⦋1⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) =
          X.map (𝟙 (Opposite.op ⦋1⦌)) e.edge := by
        simpa only [f, op_id] using
          (yonedaEquiv_symm_app_objEquiv_symm e.edge (𝟙 ⦋1⦌))
      _ = e.edge := ConcreteCategory.congr_hom (X.map_id (Opposite.op ⦋1⦌)) e.edge
  have hm : yonedaEquiv.symm deltaOneIdentityEdge.edge ≫ f = yonedaEquiv.symm e.edge := by
    rw [yonedaEquiv_symm_comp]
    apply congrArg yonedaEquiv.symm
    exact hf
  change (stdSimplex.toTopObjIsoI.inv ≫ toTop.map (yonedaEquiv.symm deltaOneIdentityEdge.edge)
      ≫ toTop.map f) (TopCat.I.homeomorph.symm t) = _
  rw [← Functor.map_comp, hm]
  rfl

private theorem realizationValueDown_edge_homotopic
    {X : SSet.{ue}} {a b : X _⦋0⦌} (e : X.Edge a b) :
    Path.Homotopic
      (((TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{ue, ve} e))).map
        (realizationValueDown.{ue, ve} X).continuous).cast
          (realizationValueDown_vertex.{ue, ve} X a).symm
          (realizationValueDown_vertex.{ue, ve} X b).symm)
      (TopCat.pathEquiv (realizedEdgePath e)) := by
  let K : SSet.{ue} := Δ[1]
  let d := deltaOneIdentityEdge.{ue}
  let p : Path (realizedVertex (K.δ 1 d.edge)) (realizedVertex (K.δ 0 d.edge)) :=
    ((TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{ue, ve} d))).map
      (realizationValueDown.{ue, ve} K).continuous).cast
        (realizationValueDown_vertex.{ue, ve} K _).symm
        (realizationValueDown_vertex.{ue, ve} K _).symm
  let f : K ⟶ X := yonedaEquiv.symm e.edge
  have h := Path.Homotopic.map (realizedDeltaOnePathsHomotopic p
    (TopCat.pathEquiv (realizedEdgePath d))) (toTop.map f).hom
  have hf : f.app (Opposite.op ⦋1⦌) d.edge = e.edge := by
    change f.app (Opposite.op ⦋1⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) = e.edge
    calc
      f.app (Opposite.op ⦋1⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) =
          X.map (𝟙 (Opposite.op ⦋1⦌)) e.edge := by
        simpa only [f, op_id] using
          (yonedaEquiv_symm_app_objEquiv_symm e.edge (𝟙 ⦋1⦌))
      _ = e.edge := ConcreteCategory.congr_hom (X.map_id (Opposite.op ⦋1⦌)) e.edge
  have ha : f.app (Opposite.op ⦋0⦌) (K.δ 1 d.edge) = a := by
    have hs := (d.map f).src_eq
    change X.δ 1 (f.app (Opposite.op ⦋1⦌) d.edge) = _ at hs
    rw [hf, e.src_eq] at hs
    exact hs.symm
  have hb : f.app (Opposite.op ⦋0⦌) (K.δ 0 d.edge) = b := by
    have ht := (d.map f).tgt_eq
    change X.δ 0 (f.app (Opposite.op ⦋1⦌) d.edge) = _ at ht
    rw [hf, e.tgt_eq] at ht
    exact ht.symm
  have hra : toTop.map f (realizedVertex (K.δ 1 d.edge)) = realizedVertex a :=
    (realizedVertex_naturality f _).symm.trans (congrArg realizedVertex ha)
  have hrb : toTop.map f (realizedVertex (K.δ 0 d.edge)) = realizedVertex b :=
    (realizedVertex_naturality f _).symm.trans (congrArg realizedVertex hb)
  have hc := Path.Homotopic.pathCast h hra.symm hrb.symm
  have hp : ((p.map (toTop.map f).hom.continuous).cast hra.symm hrb.symm) =
      ((TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{ue, ve} e))).map
        (realizationValueDown.{ue, ve} X).continuous).cast
          (realizationValueDown_vertex.{ue, ve} X a).symm
          (realizationValueDown_vertex.{ue, ve} X b).symm := by
    apply Path.ext
    funext t
    exact (edgeLiftDown_value e t).symm
  have hq : (((TopCat.pathEquiv (realizedEdgePath d)).map (toTop.map f).hom.continuous).cast
      hra.symm hrb.symm) = TopCat.pathEquiv (realizedEdgePath e) := by
    apply Path.ext
    funext t
    exact edgeIdentityMapped_value e t
  obtain ⟨H⟩ := hc
  exact ⟨Path.Homotopy.cast H hp hq⟩

end SSet

end

noncomputable section

open CategoryTheory
open scoped Simplicial ContinuousMap

attribute [local instance] uliftCategory

universe uf vf wf

namespace SSet

private theorem realizedEdgePath_map_value_of_simplex
    {X Y : SSet.{uf}} (φ : X ⟶ Y) {a b : X _⦋0⦌} (e : X.Edge a b)
    {a' b' : Y _⦋0⦌} (e' : Y.Edge a' b')
    (h : φ.app (Opposite.op ⦋1⦌) e.edge = e'.edge) (t : unitInterval) :
    toTop.map φ (TopCat.pathEquiv (realizedEdgePath e) t) =
      TopCat.pathEquiv (realizedEdgePath e') t := by
  have hs : yonedaEquiv.symm e.edge ≫ φ = yonedaEquiv.symm e'.edge := by
    rw [yonedaEquiv_symm_comp, h]
  change (stdSimplex.toTopObjIsoI.inv ≫ toTop.map (yonedaEquiv.symm e.edge) ≫
    toTop.map φ) (TopCat.I.homeomorph.symm t) = _
  rw [← Functor.map_comp, hs]
  rfl

private theorem nerveULiftIso_hom_edge_simplex
    (C : Type uf) [Category.{vf} C] {x y : C} (f : x ⟶ y) :
    (nerveULiftIso.{uf, vf, wf} C).hom.app (Opposite.op ⦋1⦌)
        (nerve.edgeMk (C := ULift.{wf} C) (x := ULift.up x) (y := ULift.up y)
          (ULift.upFunctor.map f)).edge =
      (ULift.up (nerve.edgeMk (C := C) (x := x) (y := y) f).edge :
        (uliftFunctor.{wf, max uf vf}.obj (nerve C)) _⦋1⦌) := by
  change ULift.up ((ComposableArrows.mk₁ (ULift.upFunctor.map f)) ⋙
    ULift.downFunctor) = ULift.up (ComposableArrows.mk₁ f)
  apply ULift.ext
  refine ComposableArrows.ext₁ rfl rfl ?_
  simp only [Nat.reduceAdd, Functor.comp_obj, Fin.zero_eta, Fin.isValue,
    ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj, Fin.mk_one, Functor.comp_map,
    homOfLE_leOfHom, ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map,
    ULift.upFunctor_map]
  dsimp only [CategoryTheory.Functor.comp, ULift.downFunctor, ULift.upFunctor]
  change f = eqToHom (rfl : x = x) ≫ f ≫ eqToHom (rfl : y = y)
  exact CategoryTheory.eq_conj_eqToHom f

private theorem nerveULiftHomIso_hom_edge_simplex
    (C : Type uf) [Category.{vf} C] {x y : C} (f : x ⟶ y) :
    (nerveULiftHomIso.{uf, vf, wf} C).hom.app (Opposite.op ⦋1⦌)
        (nerve.edgeMk (C := ULiftHom.{wf} C)
          (x := ULiftHom.objUp x) (y := ULiftHom.objUp y)
          (ULiftHom.up.map f)).edge =
      (ULift.up (nerve.edgeMk (C := C) (x := x) (y := y) f).edge :
        (uliftFunctor.{wf, max uf vf}.obj (nerve C)) _⦋1⦌) := by
  change ULift.up ((ComposableArrows.mk₁ (ULiftHom.up.map f)) ⋙
    ULiftHom.down) = ULift.up (ComposableArrows.mk₁ f)
  apply ULift.ext
  refine ComposableArrows.ext₁ rfl rfl ?_
  simp only [Nat.reduceAdd, Functor.comp_obj, Fin.zero_eta, Fin.isValue,
    ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj, Fin.mk_one, Functor.comp_map,
    homOfLE_leOfHom, ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map,
    ULiftHom.down_map, ULiftHom.up_map_down]
  dsimp only [CategoryTheory.Functor.comp, ULiftHom.down, ULiftHom.up,
    ULiftHom.objDown, ULiftHom.objUp]
  change f = eqToHom (rfl : x = x) ≫ f ≫ eqToHom (rfl : y = y)
  exact CategoryTheory.eq_conj_eqToHom f

/-- The object-lift realization map preserves the whole original edge path
up to a homotopy with the original endpoints fixed. -/
public theorem realizedNerveULiftHomeomorph_edge_homotopic
    (C : Type uf) [Category.{vf} C] {x y : C} (f : x ⟶ y) :
    (((TopCat.pathEquiv (realizedEdgePath
        (nerve.edgeMk (C := ULift.{wf} C) (x := ULift.up x) (y := ULift.up y)
          (ULift.upFunctor.map f)))).map
        (realizedNerveULiftHomeomorph.{uf, vf, wf} C).continuous_toFun).cast
          (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C x).symm
          (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C y).symm).Homotopic
      (TopCat.pathEquiv (realizedEdgePath (nerve.edgeMk (C := C) (x := x) (y := y) f))) := by
  let e := nerve.edgeMk (C := C) (x := x) (y := y) f
  let eu := nerve.edgeMk (C := ULift.{wf} C) (x := ULift.up x) (y := ULift.up y)
    (ULift.upFunctor.map f)
  have h := realizationValueDown_edge_homotopic.{max uf vf, wf} e
  have hp :
      (((TopCat.pathEquiv (realizedEdgePath eu)).map
        (realizedNerveULiftHomeomorph.{uf, vf, wf} C).continuous_toFun).cast
          (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C x).symm
          (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C y).symm) =
      (((TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{max uf vf, wf} e))).map
        (realizationValueDown.{max uf vf, wf} (nerve C)).continuous).cast
          (realizationValueDown_vertex.{max uf vf, wf} (nerve C) _).symm
          (realizationValueDown_vertex.{max uf vf, wf} (nerve C) _).symm) := by
    apply Path.ext
    funext t
    have hv := realizedEdgePath_map_value_of_simplex
      (nerveULiftIso.{uf, vf, wf} C).hom eu (edgeValueLift.{max uf vf, wf} e)
      (nerveULiftIso_hom_edge_simplex.{uf, vf, wf} C f) t
    have hEval :
        (((TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{max uf vf, wf} e))).map
          (realizationValueDown.{max uf vf, wf} (nerve C)).continuous).cast
            (realizationValueDown_vertex.{max uf vf, wf} (nerve C) _).symm
            (realizationValueDown_vertex.{max uf vf, wf} (nerve C) _).symm) t =
          ((toTopULiftIso.{max uf vf, wf}.hom.app (nerve C))
            (TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{max uf vf, wf} e)) t)).down := by
      rfl
    exact (realizedNerveULiftHomeomorph_apply.{uf, vf, wf} C _).trans
      ((congrArg (fun z => ((toTopULiftIso.{max uf vf, wf}.hom.app (nerve C)) z).down) hv).trans
        hEval.symm)
  exact hp.symm ▸ h

/-- The Hom-lift realization map preserves the whole original edge path
up to a homotopy with the original endpoints fixed. -/
public theorem realizedNerveULiftHomHomeomorph_edge_homotopic
    (C : Type uf) [Category.{vf} C] {x y : C} (f : x ⟶ y) :
    (((TopCat.pathEquiv (realizedEdgePath
        (nerve.edgeMk (C := ULiftHom.{wf} C)
          (x := ULiftHom.objUp x) (y := ULiftHom.objUp y)
          (ULiftHom.up.map f)))).map
        (realizedNerveULiftHomHomeomorph.{uf, vf, wf} C).continuous_toFun).cast
          (realizedNerveULiftHomHomeomorph_vertex.{uf, vf, wf} C x).symm
          (realizedNerveULiftHomHomeomorph_vertex.{uf, vf, wf} C y).symm).Homotopic
      (TopCat.pathEquiv (realizedEdgePath (nerve.edgeMk (C := C) (x := x) (y := y) f))) := by
  let e := nerve.edgeMk (C := C) (x := x) (y := y) f
  let eu := nerve.edgeMk (C := ULiftHom.{wf} C)
    (x := ULiftHom.objUp x) (y := ULiftHom.objUp y) (ULiftHom.up.map f)
  have h := realizationValueDown_edge_homotopic.{max uf vf, wf} e
  have hp :
      (((TopCat.pathEquiv (realizedEdgePath eu)).map
        (realizedNerveULiftHomHomeomorph.{uf, vf, wf} C).continuous_toFun).cast
          (realizedNerveULiftHomHomeomorph_vertex.{uf, vf, wf} C x).symm
          (realizedNerveULiftHomHomeomorph_vertex.{uf, vf, wf} C y).symm) =
      (((TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{max uf vf, wf} e))).map
        (realizationValueDown.{max uf vf, wf} (nerve C)).continuous).cast
          (realizationValueDown_vertex.{max uf vf, wf} (nerve C) _).symm
          (realizationValueDown_vertex.{max uf vf, wf} (nerve C) _).symm) := by
    apply Path.ext
    funext t
    have hv := realizedEdgePath_map_value_of_simplex
      (nerveULiftHomIso.{uf, vf, wf} C).hom eu (edgeValueLift.{max uf vf, wf} e)
      (nerveULiftHomIso_hom_edge_simplex.{uf, vf, wf} C f) t
    have hEval :
        (((TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{max uf vf, wf} e))).map
          (realizationValueDown.{max uf vf, wf} (nerve C)).continuous).cast
            (realizationValueDown_vertex.{max uf vf, wf} (nerve C) _).symm
            (realizationValueDown_vertex.{max uf vf, wf} (nerve C) _).symm) t =
          ((toTopULiftIso.{max uf vf, wf}.hom.app (nerve C))
            (TopCat.pathEquiv (realizedEdgePath (edgeValueLift.{max uf vf, wf} e)) t)).down := by
      rfl
    exact (realizedNerveULiftHomHomeomorph_apply.{uf, vf, wf} C _).trans
      ((congrArg (fun z => ((toTopULiftIso.{max uf vf, wf}.hom.app (nerve C)) z).down) hv).trans
        hEval.symm)
  exact hp.symm ▸ h

/-- Both universe lifts retain the actual original edge up to a path
homotopy, with the two original vertex transports. -/
public theorem realizedNerveLiftHomeomorph_edge_homotopic
    (C : Type uf) [Category.{vf} C] {x y : C} (f : x ⟶ y) :
    (((TopCat.pathEquiv (realizedEdgePath
        (nerve.edgeMk (C := ULiftHom.{wf} (ULift.{wf} C))
          (x := ULiftHom.objUp (ULift.up x)) (y := ULiftHom.objUp (ULift.up y))
          (ULiftHom.up.map (ULift.upFunctor.map f))))).map
        (realizedNerveLiftHomeomorph.{uf, vf, wf} C).continuous_toFun).cast
          (realizedNerveLiftHomeomorph_vertex.{uf, vf, wf} C x).symm
          (realizedNerveLiftHomeomorph_vertex.{uf, vf, wf} C y).symm).Homotopic
      (TopCat.pathEquiv (realizedEdgePath (nerve.edgeMk (C := C) (x := x) (y := y) f))) := by
  let HO := realizedNerveULiftHomeomorph.{uf, vf, wf} C
  have hh := realizedNerveULiftHomHomeomorph_edge_homotopic.{max uf wf, vf, wf}
    (ULift.{wf} C) (ULift.upFunctor.map f)
  have h := (hh.map HO.toHomotopyEquiv.toFun).pathCast
    (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C x).symm
    (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C y).symm
  have hp :
      ((((TopCat.pathEquiv (realizedEdgePath
          (nerve.edgeMk (C := ULiftHom.{wf} (ULift.{wf} C))
            (x := ULiftHom.objUp (ULift.up x)) (y := ULiftHom.objUp (ULift.up y))
            (ULiftHom.up.map (ULift.upFunctor.map f))))).map
          (realizedNerveULiftHomHomeomorph.{max uf wf, vf,
            wf} (ULift.{wf} C)).continuous_toFun).cast
            (realizedNerveULiftHomHomeomorph_vertex.{max uf wf, vf, wf} (ULift.{wf} C)
              (ULift.up x)).symm
            (realizedNerveULiftHomHomeomorph_vertex.{max uf wf, vf, wf} (ULift.{wf} C)
              (ULift.up y)).symm).map HO.toHomotopyEquiv.toFun.continuous).cast
          (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C x).symm
          (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C y).symm =
      (((TopCat.pathEquiv (realizedEdgePath
          (nerve.edgeMk (C := ULiftHom.{wf} (ULift.{wf} C))
            (x := ULiftHom.objUp (ULift.up x)) (y := ULiftHom.objUp (ULift.up y))
            (ULiftHom.up.map (ULift.upFunctor.map f))))).map
          (realizedNerveLiftHomeomorph.{uf, vf, wf} C).continuous_toFun).cast
            (realizedNerveLiftHomeomorph_vertex.{uf, vf, wf} C x).symm
            (realizedNerveLiftHomeomorph_vertex.{uf, vf, wf} C y).symm) := by
    apply Path.ext
    funext t
    rfl
  have hq :
      (((TopCat.pathEquiv (realizedEdgePath
        (nerve.edgeMk (C := ULift.{wf} C) (x := ULift.up x) (y := ULift.up y)
          (ULift.upFunctor.map f)))).map HO.toHomotopyEquiv.toFun.continuous).cast
            (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C x).symm
            (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C y).symm) =
      (((TopCat.pathEquiv (realizedEdgePath
        (nerve.edgeMk (C := ULift.{wf} C) (x := ULift.up x) (y := ULift.up y)
          (ULift.upFunctor.map f)))).map HO.continuous_toFun).cast
            (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C x).symm
            (realizedNerveULiftHomeomorph_vertex.{uf, vf, wf} C y).symm) := by
    apply Path.ext
    funext t
    rfl
  obtain ⟨H⟩ := h
  refine Path.Homotopic.trans ?_
    (realizedNerveULiftHomeomorph_edge_homotopic.{uf, vf, wf} C f)
  exact ⟨Path.Homotopy.cast H hp hq⟩

/-- The inverse lift homeomorphism maps every original edge to the actual
lifted edge up to a homotopy with the derived lifted vertices fixed. -/
public theorem realizedNerveLiftHomeomorph_symm_edge_homotopic
    (C : Type uf) [Category.{vf} C] {x y : C} (f : x ⟶ y) :
    (((TopCat.pathEquiv (realizedEdgePath (nerve.edgeMk (C := C) (x := x) (y := y) f))).map
        (realizedNerveLiftHomeomorph.{uf, vf, wf} C).symm.continuous_toFun).cast
          (realizedNerveLiftHomeomorph_symm_vertex.{uf, vf, wf} C x).symm
          (realizedNerveLiftHomeomorph_symm_vertex.{uf, vf, wf} C y).symm).Homotopic
      (TopCat.pathEquiv (realizedEdgePath
        (nerve.edgeMk (C := ULiftHom.{wf} (ULift.{wf} C))
          (x := ULiftHom.objUp (ULift.up x)) (y := ULiftHom.objUp (ULift.up y))
          (ULiftHom.up.map (ULift.upFunctor.map f))))) := by
  let H := realizedNerveLiftHomeomorph.{uf, vf, wf} C
  let p := TopCat.pathEquiv (realizedEdgePath
    (nerve.edgeMk (C := ULiftHom.{wf} (ULift.{wf} C))
      (x := ULiftHom.objUp (ULift.up x)) (y := ULiftHom.objUp (ULift.up y))
      (ULiftHom.up.map (ULift.upFunctor.map f))))
  have h := ((realizedNerveLiftHomeomorph_edge_homotopic.{uf, vf, wf} C f).map
    H.symm.toHomotopyEquiv.toFun).pathCast
      (realizedNerveLiftHomeomorph_symm_vertex.{uf, vf, wf} C x).symm
      (realizedNerveLiftHomeomorph_symm_vertex.{uf, vf, wf} C y).symm
  have hp :
      ((((p.map H.continuous_toFun).cast
        (realizedNerveLiftHomeomorph_vertex.{uf, vf, wf} C x).symm
        (realizedNerveLiftHomeomorph_vertex.{uf, vf, wf} C y).symm).map
          H.symm.toHomotopyEquiv.toFun.continuous).cast
            (realizedNerveLiftHomeomorph_symm_vertex.{uf, vf, wf} C x).symm
            (realizedNerveLiftHomeomorph_symm_vertex.{uf, vf, wf} C y).symm) = p := by
    apply Path.ext
    funext t
    exact H.symm_apply_apply (p t)
  have hq :
      (((TopCat.pathEquiv (realizedEdgePath (nerve.edgeMk (C := C) (x := x) (y := y) f))).map
        H.symm.toHomotopyEquiv.toFun.continuous).cast
          (realizedNerveLiftHomeomorph_symm_vertex.{uf, vf, wf} C x).symm
          (realizedNerveLiftHomeomorph_symm_vertex.{uf, vf, wf} C y).symm) =
      (((TopCat.pathEquiv (realizedEdgePath (nerve.edgeMk (C := C) (x := x) (y := y) f))).map
        H.symm.continuous_toFun).cast
          (realizedNerveLiftHomeomorph_symm_vertex.{uf, vf, wf} C x).symm
          (realizedNerveLiftHomeomorph_symm_vertex.{uf, vf, wf} C y).symm) := by
    apply Path.ext
    funext t
    rfl
  obtain ⟨Hraw⟩ := h
  apply Path.Homotopic.symm
  exact ⟨Path.Homotopy.cast Hraw hp hq⟩

end SSet

universe uA vA uB vB

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]

/-- The actual forward realization of a category equivalence preserves the
original functor edge as a path homotopy in independent universes. -/
public theorem realizedNerveEquivalence_edge_homotopic
    (E : A ≌ B) {x y : A} (f : x ⟶ y) :
    (((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (C := A) (x := x) (y := y) f))).map
        (realizedNerveEquivalence E).toFun.continuous).cast
          (realizedNerveEquivalence_vertex E x).symm
          (realizedNerveEquivalence_vertex E y).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := B) (x := E.functor.obj x) (y := E.functor.obj y)
          (E.functor.map f)))) := by
  let HA := SSet.realizedNerveLiftHomeomorph.{uA, vA, max uA vA uB vB} A
  let HB := SSet.realizedNerveLiftHomeomorph.{uB, vB, max uA vA uB vB} B
  let L := liftedCategoryEquivalence E
  let K := liftedRealizedEquivalence E
  let M := HB.toHomotopyEquiv.toFun.comp K.toFun
  let xa : ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} A) :=
    ULiftHom.objUp (ULift.up x)
  let ya : ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} A) :=
    ULiftHom.objUp (ULift.up y)
  let xb : ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} B) :=
    ULiftHom.objUp (ULift.up (E.functor.obj x))
  let yb : ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} B) :=
    ULiftHom.objUp (ULift.up (E.functor.obj y))
  let fa : xa ⟶ ya := ULiftHom.up.map (ULift.upFunctor.map f)
  let fb : xb ⟶ yb := ULiftHom.up.map (ULift.upFunctor.map (E.functor.map f))
  let pa := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (x := xa) (y := ya) fa))
  let pb := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (x := xb) (y := yb) fb))
  have hRecipe (z : SSet.toTop.obj (nerve A)) :
      (realizedNerveEquivalence E).toFun z = M (HA.symm z) := rfl
  have hVertex (a : A) :
      M (SSet.realizedVertex (X := nerve (ULiftHom.{max uA vA uB vB}
        (ULift.{max uA vA uB vB} A)))
          (ComposableArrows.mk₀ (ULiftHom.objUp (ULift.up a)))) =
        SSet.realizedVertex (X := nerve B) (ComposableArrows.mk₀ (E.functor.obj a)) :=
    (congrArg M (SSet.realizedNerveLiftHomeomorph_symm_vertex.{uA, vA, max uA vA uB vB}
      A a)).symm.trans ((hRecipe _).symm.trans (realizedNerveEquivalence_vertex E a))
  have hArrow : L.functor.map fa = (fb : L.functor.obj xa ⟶ L.functor.obj ya) := rfl
  have hEdge : (nerveMap L.functor).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (x := xa) (y := ya) fa).edge =
      (nerve.edgeMk (x := xb) (y := yb) fb).edge := by
    have hFirst : (nerveMap L.functor).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk (x := xa) (y := ya) fa).edge =
        ComposableArrows.mk₁ (L.functor.map fa) :=
      nerveMap_app_mk₁ L.functor fa
    have hSecond : ComposableArrows.mk₁ (L.functor.map fa) =
        (nerve.edgeMk (x := xb) (y := yb) fb).edge :=
      congrArg (fun g : L.functor.obj xa ⟶ L.functor.obj ya => ComposableArrows.mk₁ g) hArrow
    exact hFirst.trans hSecond
  have hCurve (t : unitInterval) : K.toFun (pa t) = pb t := by
    have hMap : K.toFun = (SSet.toTop.map (nerveMap L.functor)).hom := rfl
    have hv := SSet.realizedEdgePath_map_value_of_simplex (nerveMap L.functor)
      (nerve.edgeMk (x := xa) (y := ya) fa) (nerve.edgeMk (x := xb) (y := yb) fb) hEdge t
    exact (congrArg
      (fun F : C(SSet.toTop.obj (nerve (ULiftHom.{max uA vA uB vB}
          (ULift.{max uA vA uB vB} A))),
        SSet.toTop.obj (nerve (ULiftHom.{max uA vA uB vB}
          (ULift.{max uA vA uB vB} B)))) => F (pa t)) hMap).trans hv
  have h := ((SSet.realizedNerveLiftHomeomorph_symm_edge_homotopic.{uA, vA,
    max uA vA uB vB} A f).map M).pathCast
    (hVertex x).symm (hVertex y).symm
  have hp :
      ((((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (C := A) (x := x) (y := y) f))).map
        HA.symm.continuous_toFun).cast
          (SSet.realizedNerveLiftHomeomorph_symm_vertex.{uA, vA, max uA vA uB vB} A x).symm
          (SSet.realizedNerveLiftHomeomorph_symm_vertex.{uA, vA, max uA vA uB vB} A y).symm).map
            M.continuous).cast (hVertex x).symm (hVertex y).symm =
      (((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (C := A) (x := x) (y := y) f))).map
        (realizedNerveEquivalence E).toFun.continuous).cast
          (realizedNerveEquivalence_vertex E x).symm (realizedNerveEquivalence_vertex E
            y).symm) := by
    apply Path.ext
    funext t
    exact (hRecipe _).symm
  have hq :
      (((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} A))
          (x := ULiftHom.objUp (ULift.up x)) (y := ULiftHom.objUp (ULift.up y))
          (ULiftHom.up.map (ULift.upFunctor.map f))))).map M.continuous).cast
            (hVertex x).symm (hVertex y).symm) =
      (((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} B))
          (x := ULiftHom.objUp (ULift.up (E.functor.obj x)))
          (y := ULiftHom.objUp (ULift.up (E.functor.obj y)))
          (ULiftHom.up.map (ULift.upFunctor.map (E.functor.map f)))))).map
            HB.continuous_toFun).cast
        (SSet.realizedNerveLiftHomeomorph_vertex.{uB, vB, max uA vA uB vB} B (E.functor.obj x)).symm
        (SSet.realizedNerveLiftHomeomorph_vertex.{uB, vB, max uA vA uB vB} B (E.functor.obj
          y)).symm) := by
    apply Path.ext
    funext t
    exact congrArg HB (hCurve t)
  obtain ⟨H⟩ := h
  refine Path.Homotopic.trans ?_
    (SSet.realizedNerveLiftHomeomorph_edge_homotopic.{uB, vB, max uA vA uB vB} B
      (E.functor.map f))
  exact ⟨Path.Homotopy.cast H hp hq⟩

/-- The actual inverse realization preserves the original inverse-functor
edge, with its derived original vertex transports. -/
public theorem realizedNerveEquivalence_inv_edge_homotopic
    (E : A ≌ B) {x y : B} (f : x ⟶ y) :
    (((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (C := B) (x := x) (y := y) f))).map
        (realizedNerveEquivalence E).invFun.continuous).cast
          (realizedNerveEquivalence_inv_vertex E x).symm
          (realizedNerveEquivalence_inv_vertex E y).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := A) (x := E.inverse.obj x) (y := E.inverse.obj y)
          (E.inverse.map f)))) := by
  let HA := SSet.realizedNerveLiftHomeomorph.{uA, vA, max uA vA uB vB} A
  let HB := SSet.realizedNerveLiftHomeomorph.{uB, vB, max uA vA uB vB} B
  let L := liftedCategoryEquivalence E
  let K := liftedRealizedEquivalence E
  let M := HA.toHomotopyEquiv.toFun.comp K.invFun
  let xb : ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} B) :=
    ULiftHom.objUp (ULift.up x)
  let yb : ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} B) :=
    ULiftHom.objUp (ULift.up y)
  let xa : ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} A) :=
    ULiftHom.objUp (ULift.up (E.inverse.obj x))
  let ya : ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} A) :=
    ULiftHom.objUp (ULift.up (E.inverse.obj y))
  let fb : xb ⟶ yb := ULiftHom.up.map (ULift.upFunctor.map f)
  let fa : xa ⟶ ya := ULiftHom.up.map (ULift.upFunctor.map (E.inverse.map f))
  let pb := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (x := xb) (y := yb) fb))
  let pa := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (x := xa) (y := ya) fa))
  have hRecipe (z : SSet.toTop.obj (nerve B)) :
      (realizedNerveEquivalence E).invFun z = M (HB.symm z) := rfl
  have hVertex (b : B) :
      M (SSet.realizedVertex (X := nerve (ULiftHom.{max uA vA uB vB}
        (ULift.{max uA vA uB vB} B)))
          (ComposableArrows.mk₀ (ULiftHom.objUp (ULift.up b)))) =
        SSet.realizedVertex (X := nerve A) (ComposableArrows.mk₀ (E.inverse.obj b)) :=
    (congrArg M (SSet.realizedNerveLiftHomeomorph_symm_vertex.{uB, vB, max uA vA uB vB}
      B b)).symm.trans ((hRecipe _).symm.trans (realizedNerveEquivalence_inv_vertex E b))
  have hArrow : L.inverse.map fb = (fa : L.inverse.obj xb ⟶ L.inverse.obj yb) := rfl
  have hEdge : (nerveMap L.inverse).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (x := xb) (y := yb) fb).edge =
      (nerve.edgeMk (x := xa) (y := ya) fa).edge := by
    have hFirst : (nerveMap L.inverse).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk (x := xb) (y := yb) fb).edge =
        ComposableArrows.mk₁ (L.inverse.map fb) :=
      nerveMap_app_mk₁ L.inverse fb
    have hSecond : ComposableArrows.mk₁ (L.inverse.map fb) =
        (nerve.edgeMk (x := xa) (y := ya) fa).edge :=
      congrArg (fun g : L.inverse.obj xb ⟶ L.inverse.obj yb => ComposableArrows.mk₁ g) hArrow
    exact hFirst.trans hSecond
  have hCurve (t : unitInterval) : K.invFun (pb t) = pa t := by
    have hMap : K.invFun = (SSet.toTop.map (nerveMap L.inverse)).hom := rfl
    have hv := SSet.realizedEdgePath_map_value_of_simplex (nerveMap L.inverse)
      (nerve.edgeMk (x := xb) (y := yb) fb) (nerve.edgeMk (x := xa) (y := ya) fa) hEdge t
    exact (congrArg
      (fun F : C(SSet.toTop.obj (nerve (ULiftHom.{max uA vA uB vB}
          (ULift.{max uA vA uB vB} B))),
        SSet.toTop.obj (nerve (ULiftHom.{max uA vA uB vB}
          (ULift.{max uA vA uB vB} A)))) => F (pb t)) hMap).trans hv
  have h := ((SSet.realizedNerveLiftHomeomorph_symm_edge_homotopic.{uB, vB,
    max uA vA uB vB} B f).map M).pathCast
    (hVertex x).symm (hVertex y).symm
  have hp :
      ((((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (C := B) (x := x) (y := y) f))).map
        HB.symm.continuous_toFun).cast
          (SSet.realizedNerveLiftHomeomorph_symm_vertex.{uB, vB, max uA vA uB vB} B x).symm
          (SSet.realizedNerveLiftHomeomorph_symm_vertex.{uB, vB, max uA vA uB vB} B y).symm).map
            M.continuous).cast (hVertex x).symm (hVertex y).symm =
      (((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (C := B) (x := x) (y := y) f))).map
        (realizedNerveEquivalence E).invFun.continuous).cast
          (realizedNerveEquivalence_inv_vertex E x).symm
            (realizedNerveEquivalence_inv_vertex E y).symm) := by
    apply Path.ext
    funext t
    exact (hRecipe _).symm
  have hq :
      (((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} B))
          (x := ULiftHom.objUp (ULift.up x)) (y := ULiftHom.objUp (ULift.up y))
          (ULiftHom.up.map (ULift.upFunctor.map f))))).map M.continuous).cast
            (hVertex x).symm (hVertex y).symm) =
      (((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} A))
          (x := ULiftHom.objUp (ULift.up (E.inverse.obj x)))
          (y := ULiftHom.objUp (ULift.up (E.inverse.obj y)))
          (ULiftHom.up.map (ULift.upFunctor.map (E.inverse.map f)))))).map
            HA.continuous_toFun).cast
        (SSet.realizedNerveLiftHomeomorph_vertex.{uA, vA, max uA vA uB vB} A (E.inverse.obj x)).symm
        (SSet.realizedNerveLiftHomeomorph_vertex.{uA, vA, max uA vA uB vB} A (E.inverse.obj
          y)).symm) := by
    apply Path.ext
    funext t
    exact congrArg HA (hCurve t)
  obtain ⟨H⟩ := h
  refine Path.Homotopic.trans ?_
    (SSet.realizedNerveLiftHomeomorph_edge_homotopic.{uA, vA, max uA vA uB vB} A
      (E.inverse.map f))
  exact ⟨Path.Homotopy.cast H hp hq⟩

end CategoryTheory

end

noncomputable section

open CategoryTheory
open scoped Simplicial

attribute [local instance] uliftCategory

universe uc vc ud vd wt

namespace SSet

variable {C : Type uc} [Category.{vc} C]

private def objectLiftEndofunctor (F : C ⥤ C) : ULift.{wt} C ⥤ ULift.{wt} C :=
  ULift.downFunctor ⋙ F ⋙ ULift.upFunctor

private def homLiftEndofunctor (F : C ⥤ C) : ULiftHom.{wt} C ⥤ ULiftHom.{wt} C :=
  ULiftHom.down ⋙ F ⋙ ULiftHom.up

private theorem nerveObjectLiftEndofunctor_naturality (F : C ⥤ C) :
    nerveMap (objectLiftEndofunctor.{uc, vc, wt} F) ≫
        (nerveULiftIso.{uc, vc, wt} C).hom =
      (nerveULiftIso.{uc, vc, wt} C).hom ≫
        uliftFunctor.{wt, max uc vc}.map (nerveMap F) := by
  ext n q
  change ULift.up ((q ⋙ objectLiftEndofunctor.{uc, vc, wt} F) ⋙ ULift.downFunctor) =
    ULift.up ((q ⋙ ULift.downFunctor) ⋙ F)
  apply ULift.ext
  exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
    dsimp only [CategoryTheory.Functor.comp, objectLiftEndofunctor,
      ULift.downFunctor, ULift.upFunctor]
    change F.map (q.map f) =
      eqToHom (rfl : F.obj (q.obj i).down = F.obj (q.obj i).down) ≫
        F.map (q.map f) ≫
          eqToHom (rfl : F.obj (q.obj j).down = F.obj (q.obj j).down)
    exact CategoryTheory.eq_conj_eqToHom (F.map (q.map f)))

private theorem nerveHomLiftEndofunctor_naturality (F : C ⥤ C) :
    nerveMap (homLiftEndofunctor.{uc, vc, wt} F) ≫
        (nerveULiftHomIso.{uc, vc, wt} C).hom =
      (nerveULiftHomIso.{uc, vc, wt} C).hom ≫
        uliftFunctor.{wt, max uc vc}.map (nerveMap F) := by
  ext n q
  change ULift.up ((q ⋙ homLiftEndofunctor.{uc, vc, wt} F) ⋙ ULiftHom.down) =
    ULift.up ((q ⋙ ULiftHom.down) ⋙ F)
  apply ULift.ext
  exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
    dsimp only [CategoryTheory.Functor.comp, homLiftEndofunctor,
      ULiftHom.down, ULiftHom.up, ULiftHom.objDown, ULiftHom.objUp]
    change F.map (q.map f).down =
      eqToHom (rfl : F.obj (q.obj i).objDown = F.obj (q.obj i).objDown) ≫
        F.map (q.map f).down ≫
          eqToHom (rfl : F.obj (q.obj j).objDown = F.obj (q.obj j).objDown)
    exact CategoryTheory.eq_conj_eqToHom (F.map (q.map f).down))

private theorem realizedObjectLiftEndofunctor_naturality (F : C ⥤ C)
    (z : toTop.obj (nerve (ULift.{wt} C))) :
    realizedNerveULiftHomeomorph.{uc, vc, wt} C
        (toTop.map (nerveMap (objectLiftEndofunctor.{uc, vc, wt} F)) z) =
      toTop.map (nerveMap F) (realizedNerveULiftHomeomorph.{uc, vc, wt} C z) := by
  rw [realizedNerveULiftHomeomorph_apply, realizedNerveULiftHomeomorph_apply]
  change realizationValueDown.{max uc vc, wt} (nerve C)
      (toTop.map (nerveULiftIso.{uc, vc, wt} C).hom
        (toTop.map (nerveMap (objectLiftEndofunctor.{uc, vc, wt} F)) z)) =
    toTop.map (nerveMap F) (realizationValueDown.{max uc vc, wt} (nerve C)
      (toTop.map (nerveULiftIso.{uc, vc, wt} C).hom z))
  have hMap :
      toTop.map (nerveULiftIso.{uc, vc, wt} C).hom
          (toTop.map (nerveMap (objectLiftEndofunctor.{uc, vc, wt} F)) z) =
        toTop.map (uliftFunctor.{wt, max uc vc}.map (nerveMap F))
          (toTop.map (nerveULiftIso.{uc, vc, wt} C).hom z) := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : nerve (ULift.{wt} C) ⟶
          uliftFunctor.{wt, max uc vc}.obj (nerve C) => toTop.map f)
        (nerveObjectLiftEndofunctor_naturality.{uc, vc, wt} F)) z
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using h
  exact (congrArg (realizationValueDown.{max uc vc, wt} (nerve C)) hMap).trans
    (realizationValueDown_naturality.{max uc vc, wt} (nerveMap F) _)

private theorem realizedHomLiftEndofunctor_naturality (F : C ⥤ C)
    (z : toTop.obj (nerve (ULiftHom.{wt} C))) :
    realizedNerveULiftHomHomeomorph.{uc, vc, wt} C
        (toTop.map (nerveMap (homLiftEndofunctor.{uc, vc, wt} F)) z) =
      toTop.map (nerveMap F) (realizedNerveULiftHomHomeomorph.{uc, vc, wt} C z) := by
  rw [realizedNerveULiftHomHomeomorph_apply, realizedNerveULiftHomHomeomorph_apply]
  change realizationValueDown.{max uc vc, wt} (nerve C)
      (toTop.map (nerveULiftHomIso.{uc, vc, wt} C).hom
        (toTop.map (nerveMap (homLiftEndofunctor.{uc, vc, wt} F)) z)) =
    toTop.map (nerveMap F) (realizationValueDown.{max uc vc, wt} (nerve C)
      (toTop.map (nerveULiftHomIso.{uc, vc, wt} C).hom z))
  have hMap :
      toTop.map (nerveULiftHomIso.{uc, vc, wt} C).hom
          (toTop.map (nerveMap (homLiftEndofunctor.{uc, vc, wt} F)) z) =
        toTop.map (uliftFunctor.{wt, max uc vc}.map (nerveMap F))
          (toTop.map (nerveULiftHomIso.{uc, vc, wt} C).hom z) := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : nerve (ULiftHom.{wt} C) ⟶
          uliftFunctor.{wt, max uc vc}.obj (nerve C) => toTop.map f)
        (nerveHomLiftEndofunctor_naturality.{uc, vc, wt} F)) z
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using h
  exact (congrArg (realizationValueDown.{max uc vc, wt} (nerve C)) hMap).trans
    (realizationValueDown_naturality.{max uc vc, wt} (nerveMap F) _)

private theorem realizedCombinedLiftEndofunctor_naturality (F : C ⥤ C)
    (z : toTop.obj (nerve (ULiftHom.{wt} (ULift.{wt} C)))) :
    realizedNerveLiftHomeomorph.{uc, vc, wt} C
        (toTop.map (nerveMap (homLiftEndofunctor.{max uc wt, vc, wt}
          (objectLiftEndofunctor.{uc, vc, wt} F))) z) =
      toTop.map (nerveMap F) (realizedNerveLiftHomeomorph.{uc, vc, wt} C z) := by
  let HO := realizedNerveULiftHomeomorph.{uc, vc, wt} C
  let HH := realizedNerveULiftHomHomeomorph.{max uc wt, vc, wt} (ULift.{wt} C)
  change HO (HH (toTop.map (nerveMap (homLiftEndofunctor.{max uc wt, vc, wt}
      (objectLiftEndofunctor.{uc, vc, wt} F))) z)) =
    toTop.map (nerveMap F) (HO (HH z))
  exact (congrArg HO
    (realizedHomLiftEndofunctor_naturality.{max uc wt, vc, wt}
      (objectLiftEndofunctor.{uc, vc, wt} F) z)).trans
    (realizedObjectLiftEndofunctor_naturality.{uc, vc, wt} F (HH z))

end SSet

namespace CategoryTheory

variable {C : Type uc} [Category.{vc} C] {D : Type ud} [Category.{vd} D]

private theorem liftedCategoryEquivalence_functor_inverse (E : C ≌ D) :
    (liftedCategoryEquivalence E).functor ⋙ (liftedCategoryEquivalence E).inverse =
      SSet.homLiftEndofunctor.{max uc (max uc vc ud vd), vc, max uc vc ud vd}
        (SSet.objectLiftEndofunctor.{uc, vc, max uc vc ud vd}
          (E.functor ⋙ E.inverse)) := by
  apply CategoryTheory.Functor.ext (fun i => rfl)

private theorem liftedCategoryEquivalence_inverse_functor (E : C ≌ D) :
    (liftedCategoryEquivalence E).inverse ⋙ (liftedCategoryEquivalence E).functor =
      SSet.homLiftEndofunctor.{max ud (max uc vc ud vd), vd, max uc vc ud vd}
        (SSet.objectLiftEndofunctor.{ud, vd, max uc vc ud vd}
          (E.inverse ⋙ E.functor)) := by
  apply CategoryTheory.Functor.ext (fun i => rfl)

private theorem realizedNerveEquivalenceInvFunCompToFunComputed (E : C ≌ D) :
    (realizedNerveEquivalence E).invFun.comp (realizedNerveEquivalence E).toFun =
      (SSet.toTop.map (nerveMap (E.functor ⋙ E.inverse))).hom := by
  ext z
  let HC := SSet.realizedNerveLiftHomeomorph.{uc, vc, max uc vc ud vd} C
  let HD := SSet.realizedNerveLiftHomeomorph.{ud, vd, max uc vc ud vd} D
  let L := liftedCategoryEquivalence E
  change HC ((liftedRealizedEquivalence E).invFun
    (HD.symm (HD ((liftedRealizedEquivalence E).toFun (HC.symm z))))) =
      SSet.toTop.map (nerveMap (E.functor ⋙ E.inverse)) z
  rw [HD.symm_apply_apply]
  have hComp : (liftedRealizedEquivalence E).invFun
      ((liftedRealizedEquivalence E).toFun (HC.symm z)) =
        SSet.toTop.map (nerveMap (L.functor ⋙ L.inverse)) (HC.symm z) := by
    change SSet.toTop.map (nerveMap L.inverse)
        (SSet.toTop.map (nerveMap L.functor) (HC.symm z)) = _
    rw [← nerveMap_comp, Functor.map_comp]
    rfl
  rw [hComp]
  have hL := liftedCategoryEquivalence_functor_inverse E
  change L.functor ⋙ L.inverse = _ at hL
  rw [hL]
  exact (SSet.realizedCombinedLiftEndofunctor_naturality.{uc, vc, max uc vc ud vd}
      (E.functor ⋙ E.inverse) (HC.symm z)).trans
      (congrArg (SSet.toTop.map (nerveMap (E.functor ⋙ E.inverse)))
        (HC.apply_symm_apply z))

/-- The whole inverse/forward composite is the realization of the original functor composite. -/
public theorem realizedNerveEquivalence_invFun_comp_toFun (E : C ≌ D) :
    (realizedNerveEquivalence E).invFun.comp (realizedNerveEquivalence E).toFun =
      (SSet.toTop.map (nerveMap (E.functor ⋙ E.inverse))).hom :=
  realizedNerveEquivalenceInvFunCompToFunComputed E

private theorem realizedNerveEquivalenceToFunCompInvFunComputed (E : C ≌ D) :
    (realizedNerveEquivalence E).toFun.comp (realizedNerveEquivalence E).invFun =
      (SSet.toTop.map (nerveMap (E.inverse ⋙ E.functor))).hom := by
  ext z
  let HC := SSet.realizedNerveLiftHomeomorph.{uc, vc, max uc vc ud vd} C
  let HD := SSet.realizedNerveLiftHomeomorph.{ud, vd, max uc vc ud vd} D
  let L := liftedCategoryEquivalence E
  change HD ((liftedRealizedEquivalence E).toFun
    (HC.symm (HC ((liftedRealizedEquivalence E).invFun (HD.symm z))))) =
      SSet.toTop.map (nerveMap (E.inverse ⋙ E.functor)) z
  rw [HC.symm_apply_apply]
  have hComp : (liftedRealizedEquivalence E).toFun
      ((liftedRealizedEquivalence E).invFun (HD.symm z)) =
        SSet.toTop.map (nerveMap (L.inverse ⋙ L.functor)) (HD.symm z) := by
    change SSet.toTop.map (nerveMap L.functor)
        (SSet.toTop.map (nerveMap L.inverse) (HD.symm z)) = _
    rw [← nerveMap_comp, Functor.map_comp]
    rfl
  rw [hComp]
  have hL := liftedCategoryEquivalence_inverse_functor E
  change L.inverse ⋙ L.functor = _ at hL
  rw [hL]
  exact (SSet.realizedCombinedLiftEndofunctor_naturality.{ud, vd, max uc vc ud vd}
      (E.inverse ⋙ E.functor) (HD.symm z)).trans
      (congrArg (SSet.toTop.map (nerveMap (E.inverse ⋙ E.functor)))
        (HD.apply_symm_apply z))

/-- The whole forward/inverse composite realizes the original inverse-functor composite. -/
public theorem realizedNerveEquivalence_toFun_comp_invFun (E : C ≌ D) :
    (realizedNerveEquivalence E).toFun.comp (realizedNerveEquivalence E).invFun =
      (SSet.toTop.map (nerveMap (E.inverse ⋙ E.functor))).hom :=
  realizedNerveEquivalenceToFunCompInvFunComputed E

end CategoryTheory

namespace SSet

section FunctorFrameNaturality

universe uFn vFn wFn

variable {A B : Type uFn} [Category.{vFn} A] [Category.{vFn} B]

private def objectLiftFrameFunctor (F : A ⥤ B) : ULift.{wFn} A ⥤ ULift.{wFn} B :=
  ULift.downFunctor ⋙ F ⋙ ULift.upFunctor

private def homLiftFrameFunctor (F : A ⥤ B) : ULiftHom.{wFn} A ⥤ ULiftHom.{wFn} B :=
  ULiftHom.down ⋙ F ⋙ ULiftHom.up

private theorem nerveObjectLiftFrame_naturality (F : A ⥤ B) :
    nerveMap (objectLiftFrameFunctor.{uFn, vFn, wFn} F) ≫
        (nerveULiftIso.{uFn, vFn, wFn} B).hom =
      (nerveULiftIso.{uFn, vFn, wFn} A).hom ≫
        uliftFunctor.{wFn, max uFn vFn}.map (nerveMap F) := by
  ext n q
  change ULift.up ((q ⋙ objectLiftFrameFunctor.{uFn, vFn, wFn} F) ⋙ ULift.downFunctor) =
    ULift.up ((q ⋙ ULift.downFunctor) ⋙ F)
  apply ULift.ext
  exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
    dsimp only [CategoryTheory.Functor.comp, objectLiftFrameFunctor,
      ULift.downFunctor, ULift.upFunctor]
    change F.map (q.map f) =
      eqToHom (rfl : F.obj (q.obj i).down = F.obj (q.obj i).down) ≫
        F.map (q.map f) ≫
          eqToHom (rfl : F.obj (q.obj j).down = F.obj (q.obj j).down)
    exact CategoryTheory.eq_conj_eqToHom (F.map (q.map f)))

private theorem nerveHomLiftFrame_naturality (F : A ⥤ B) :
    nerveMap (homLiftFrameFunctor.{uFn, vFn, wFn} F) ≫
        (nerveULiftHomIso.{uFn, vFn, wFn} B).hom =
      (nerveULiftHomIso.{uFn, vFn, wFn} A).hom ≫
        uliftFunctor.{wFn, max uFn vFn}.map (nerveMap F) := by
  ext n q
  change ULift.up ((q ⋙ homLiftFrameFunctor.{uFn, vFn, wFn} F) ⋙ ULiftHom.down) =
    ULift.up ((q ⋙ ULiftHom.down) ⋙ F)
  apply ULift.ext
  exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
    dsimp only [CategoryTheory.Functor.comp, homLiftFrameFunctor,
      ULiftHom.down, ULiftHom.up, ULiftHom.objDown, ULiftHom.objUp]
    change F.map (q.map f).down =
      eqToHom (rfl : F.obj (q.obj i).objDown = F.obj (q.obj i).objDown) ≫
        F.map (q.map f).down ≫
          eqToHom (rfl : F.obj (q.obj j).objDown = F.obj (q.obj j).objDown)
    exact CategoryTheory.eq_conj_eqToHom (F.map (q.map f).down))

private theorem realizedObjectLiftFrame_naturality (F : A ⥤ B)
    (z : toTop.obj (nerve (ULift.{wFn} A))) :
    realizedNerveULiftHomeomorph.{uFn, vFn, wFn} B
        (toTop.map (nerveMap (objectLiftFrameFunctor.{uFn, vFn, wFn} F)) z) =
      toTop.map (nerveMap F) (realizedNerveULiftHomeomorph.{uFn, vFn, wFn} A z) := by
  rw [realizedNerveULiftHomeomorph_apply, realizedNerveULiftHomeomorph_apply]
  change realizationValueDown.{max uFn vFn, wFn} (nerve B)
      (toTop.map (nerveULiftIso.{uFn, vFn, wFn} B).hom
        (toTop.map (nerveMap (objectLiftFrameFunctor.{uFn, vFn, wFn} F)) z)) =
    toTop.map (nerveMap F) (realizationValueDown.{max uFn vFn, wFn} (nerve A)
      (toTop.map (nerveULiftIso.{uFn, vFn, wFn} A).hom z))
  have hMap :
      toTop.map (nerveULiftIso.{uFn, vFn, wFn} B).hom
          (toTop.map (nerveMap (objectLiftFrameFunctor.{uFn, vFn, wFn} F)) z) =
        toTop.map (uliftFunctor.{wFn, max uFn vFn}.map (nerveMap F))
          (toTop.map (nerveULiftIso.{uFn, vFn, wFn} A).hom z) := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : nerve (ULift.{wFn} A) ⟶
          uliftFunctor.{wFn, max uFn vFn}.obj (nerve B) => toTop.map f)
        (nerveObjectLiftFrame_naturality.{uFn, vFn, wFn} F)) z
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using h
  exact (congrArg (realizationValueDown.{max uFn vFn, wFn} (nerve B)) hMap).trans
    (realizationValueDown_naturality.{max uFn vFn, wFn} (nerveMap F) _)

private theorem realizedHomLiftFrame_naturality (F : A ⥤ B)
    (z : toTop.obj (nerve (ULiftHom.{wFn} A))) :
    realizedNerveULiftHomHomeomorph.{uFn, vFn, wFn} B
        (toTop.map (nerveMap (homLiftFrameFunctor.{uFn, vFn, wFn} F)) z) =
      toTop.map (nerveMap F) (realizedNerveULiftHomHomeomorph.{uFn, vFn, wFn} A z) := by
  rw [realizedNerveULiftHomHomeomorph_apply, realizedNerveULiftHomHomeomorph_apply]
  change realizationValueDown.{max uFn vFn, wFn} (nerve B)
      (toTop.map (nerveULiftHomIso.{uFn, vFn, wFn} B).hom
        (toTop.map (nerveMap (homLiftFrameFunctor.{uFn, vFn, wFn} F)) z)) =
    toTop.map (nerveMap F) (realizationValueDown.{max uFn vFn, wFn} (nerve A)
      (toTop.map (nerveULiftHomIso.{uFn, vFn, wFn} A).hom z))
  have hMap :
      toTop.map (nerveULiftHomIso.{uFn, vFn, wFn} B).hom
          (toTop.map (nerveMap (homLiftFrameFunctor.{uFn, vFn, wFn} F)) z) =
        toTop.map (uliftFunctor.{wFn, max uFn vFn}.map (nerveMap F))
          (toTop.map (nerveULiftHomIso.{uFn, vFn, wFn} A).hom z) := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : nerve (ULiftHom.{wFn} A) ⟶
          uliftFunctor.{wFn, max uFn vFn}.obj (nerve B) => toTop.map f)
        (nerveHomLiftFrame_naturality.{uFn, vFn, wFn} F)) z
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using h
  exact (congrArg (realizationValueDown.{max uFn vFn, wFn} (nerve B)) hMap).trans
    (realizationValueDown_naturality.{max uFn vFn, wFn} (nerveMap F) _)

/-- The existing lift homeomorphisms are natural for actual functors in one category frame.
The object, Hom and lift levels remain independent; no map equation is an input. -/
public theorem realizedNerveLiftHomeomorph_functor_naturality (F : A ⥤ B)
    (z : toTop.obj (nerve (ULiftHom.{wFn} (ULift.{wFn} A)))) :
    realizedNerveLiftHomeomorph.{uFn, vFn, wFn} B
        (toTop.map (nerveMap (ULiftHom.down ⋙
          (ULift.downFunctor ⋙ F ⋙ ULift.upFunctor) ⋙ ULiftHom.up)) z) =
      toTop.map (nerveMap F) (realizedNerveLiftHomeomorph.{uFn, vFn, wFn} A z) := by
  let HO := realizedNerveULiftHomeomorph.{uFn, vFn, wFn} B
  let HH := realizedNerveULiftHomHomeomorph.{max uFn wFn, vFn, wFn} (ULift.{wFn} B)
  change HO (HH (toTop.map (nerveMap (homLiftFrameFunctor.{max uFn wFn, vFn, wFn}
      (objectLiftFrameFunctor.{uFn, vFn, wFn} F))) z)) =
    toTop.map (nerveMap F)
      (realizedNerveULiftHomeomorph.{uFn, vFn, wFn} A
        (realizedNerveULiftHomHomeomorph.{max uFn wFn, vFn, wFn} (ULift.{wFn} A) z))
  exact (congrArg HO
    (realizedHomLiftFrame_naturality.{max uFn wFn, vFn, wFn}
      (objectLiftFrameFunctor.{uFn, vFn, wFn} F) z)).trans
    (realizedObjectLiftFrame_naturality.{uFn, vFn, wFn} F
      (realizedNerveULiftHomHomeomorph.{max uFn wFn, vFn, wFn} (ULift.{wFn} A) z))

end FunctorFrameNaturality

end SSet


namespace SSet

section OriginalLiftComponentValues

universe uA vA wA

variable (C : Type uA) [Category.{vA} C]

private theorem nerveULiftIsoHomAppComputed (n : SimplexCategoryᵒᵖ)
    (q : (nerve (ULift.{wA} C)).obj n) :
    (nerveULiftIso.{uA, vA, wA} C).hom.app n q =
      (ULift.up (q ⋙ ULift.downFunctor) :
        (uliftFunctor.{wA, max uA vA}.obj (nerve C)).obj n) := rfl

/-- EVERY original object-lifted nerve chain maps to the lift of that SAME chain
followed by the ORIGINAL object-down functor. -/
public theorem nerveULiftIso_hom_app_eq (n : SimplexCategoryᵒᵖ)
    (q : (nerve (ULift.{wA} C)).obj n) :
    (nerveULiftIso.{uA, vA, wA} C).hom.app n q =
      (ULift.up (q ⋙ ULift.downFunctor) :
        (uliftFunctor.{wA, max uA vA}.obj (nerve C)).obj n) :=
  nerveULiftIsoHomAppComputed C n q

private theorem nerveULiftHomIsoHomAppComputed (n : SimplexCategoryᵒᵖ)
    (q : (nerve (ULiftHom.{wA} C)).obj n) :
    (nerveULiftHomIso.{uA, vA, wA} C).hom.app n q =
      (ULift.up (q ⋙ ULiftHom.down) :
        (uliftFunctor.{wA, max uA vA}.obj (nerve C)).obj n) := rfl

/-- EVERY original Hom-lifted nerve chain maps to the lift of that SAME chain
followed by the ORIGINAL Hom-down functor. -/
public theorem nerveULiftHomIso_hom_app_eq (n : SimplexCategoryᵒᵖ)
    (q : (nerve (ULiftHom.{wA} C)).obj n) :
    (nerveULiftHomIso.{uA, vA, wA} C).hom.app n q =
      (ULift.up (q ⋙ ULiftHom.down) :
        (uliftFunctor.{wA, max uA vA}.obj (nerve C)).obj n) :=
  nerveULiftHomIsoHomAppComputed C n q

end OriginalLiftComponentValues

end SSet

namespace SSet

section OriginalCombinedChartValues

universe uA vA wA

variable (C : Type uA) [Category.{vA} C]

private theorem realizedNerveLiftHomeomorphApplyComputed
    (x : toTop.obj (nerve (ULiftHom.{wA} (ULift.{wA} C)))) :
    realizedNerveLiftHomeomorph.{uA, vA, wA} C x =
      realizedNerveULiftHomeomorph.{uA, vA, wA} C
        (realizedNerveULiftHomHomeomorph.{max uA wA, vA, wA} (ULift.{wA} C) x) := rfl

/-- EVERY original combined lift-chart value is the ACTUAL original Hom-down
chart followed by the ACTUAL original object-down chart, in independent worlds. -/
public theorem realizedNerveLiftHomeomorph_apply
    (x : toTop.obj (nerve (ULiftHom.{wA} (ULift.{wA} C)))) :
    realizedNerveLiftHomeomorph.{uA, vA, wA} C x =
      realizedNerveULiftHomeomorph.{uA, vA, wA} C
        (realizedNerveULiftHomHomeomorph.{max uA wA, vA, wA} (ULift.{wA} C) x) :=
  realizedNerveLiftHomeomorphApplyComputed C x

end OriginalCombinedChartValues

end SSet

end


noncomputable section

open CategoryTheory
open scoped Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe uUp vUp wUp

namespace SSet

section OriginalCommonUpChart

variable {A : Type (max uUp vUp)} [Category.{vUp} A]
  {B : Type uUp} [Category.{vUp} B]

private def commonUpObjectFunctor (F : B ⥤ A) :
    ULift.{max uUp vUp wUp} B ⥤ ULift.{max uUp vUp wUp} A :=
  ULift.downFunctor ⋙ F ⋙ ULift.upFunctor

private theorem commonUpObjectNerveSquare (F : B ⥤ A) :
    nerveMap (commonUpObjectFunctor.{uUp, vUp, wUp} F) ≫
        (nerveULiftIso.{max uUp vUp, vUp, max uUp vUp wUp} A).hom =
      (nerveULiftIso.{uUp, vUp, max uUp vUp wUp} B).hom ≫
        uliftFunctor.{max uUp vUp wUp, max uUp vUp}.map
          (nerveMapCommonHomUp.{uUp, vUp, 0} F) := by
  ext n q
  change (nerveULiftIso.{max uUp vUp, vUp, max uUp vUp wUp} A).hom.app n
      ((nerveMap (commonUpObjectFunctor.{uUp, vUp, wUp} F)).app n q) =
    (uliftFunctor.{max uUp vUp wUp, max uUp vUp}.map
      (nerveMapCommonHomUp.{uUp, vUp, 0} F)).app n
      ((nerveULiftIso.{uUp, vUp, max uUp vUp wUp} B).hom.app n q)
  rw [nerveULiftIso_hom_app_eq, nerveULiftIso_hom_app_eq]
  change ULift.up ((q ⋙ commonUpObjectFunctor.{uUp, vUp, wUp} F) ⋙
      ULift.downFunctor) = ULift.up ((q ⋙ ULift.downFunctor) ⋙ F)
  apply ULift.ext
  exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
    dsimp only [CategoryTheory.Functor.comp, commonUpObjectFunctor,
      ULift.downFunctor, ULift.upFunctor]
    change F.map (q.map f) =
      eqToHom (rfl : F.obj (q.obj i).down = F.obj (q.obj i).down) ≫
        F.map (q.map f) ≫
          eqToHom (rfl : F.obj (q.obj j).down = F.obj (q.obj j).down)
    exact CategoryTheory.eq_conj_eqToHom (F.map (q.map f)))

private theorem commonUpObjectRealizationSquare (F : B ⥤ A)
    (z : toTop.obj (nerve (ULift.{max uUp vUp wUp} B))) :
    realizedNerveULiftHomeomorph.{max uUp vUp, vUp, max uUp vUp wUp} A
        (toTop.map (nerveMap (commonUpObjectFunctor.{uUp, vUp, wUp} F)) z) =
      toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F)
        (realizedNerveULiftHomeomorph.{uUp, vUp, max uUp vUp wUp} B z) := by
  rw [realizedNerveULiftHomeomorph_apply, realizedNerveULiftHomeomorph_apply]
  change realizationValueDown.{max uUp vUp, max uUp vUp wUp} (nerve A)
      (toTop.map (nerveULiftIso.{max uUp vUp, vUp, max uUp vUp wUp} A).hom
        (toTop.map (nerveMap (commonUpObjectFunctor.{uUp, vUp, wUp} F)) z)) =
    toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F)
      (realizationValueDown.{max uUp vUp, max uUp vUp wUp} (nerve B)
        (toTop.map (nerveULiftIso.{uUp, vUp, max uUp vUp wUp} B).hom z))
  have hNerve := commonUpObjectNerveSquare.{uUp, vUp, wUp} F
  have hTop :
      toTop.map (nerveMap (commonUpObjectFunctor.{uUp, vUp, wUp} F)) ≫
          toTop.map (nerveULiftIso.{max uUp vUp, vUp, max uUp vUp wUp} A).hom =
        toTop.map (nerveULiftIso.{uUp, vUp, max uUp vUp wUp} B).hom ≫
          toTop.map (uliftFunctor.{max uUp vUp wUp, max uUp vUp}.map
            (nerveMapCommonHomUp.{uUp, vUp, 0} F)) :=
    (toTop.map_comp _ _).symm.trans ((toTop.congr_map hNerve).trans (toTop.map_comp _ _))
  have hPoint :
      toTop.map (nerveULiftIso.{max uUp vUp, vUp, max uUp vUp wUp} A).hom
          (toTop.map (nerveMap (commonUpObjectFunctor.{uUp, vUp, wUp} F)) z) =
        toTop.map (uliftFunctor.{max uUp vUp wUp, max uUp vUp}.map
          (nerveMapCommonHomUp.{uUp, vUp, 0} F))
          (toTop.map (nerveULiftIso.{uUp, vUp, max uUp vUp wUp} B).hom z) :=
    (TopCat.comp_app _ _ z).symm.trans
      ((ConcreteCategory.congr_hom hTop z).trans (TopCat.comp_app _ _ z))
  exact (congrArg
    (realizationValueDown.{max uUp vUp, max uUp vUp wUp} (nerve A)) hPoint).trans
      (realizationValueDown_naturality.{max uUp vUp, max uUp vUp wUp}
        (nerveMapCommonHomUp.{uUp, vUp, 0} F) _)

private theorem commonUpCombinedChartComputed (F : B ⥤ A)
    (z : toTop.obj (nerve
      (ULiftHom.{max uUp vUp wUp} (ULift.{max uUp vUp wUp} B)))) :
    realizedNerveLiftHomeomorph.{max uUp vUp, vUp, max uUp vUp wUp} A
        (toTop.map (nerveMap (ULiftHom.down ⋙
          (ULift.downFunctor ⋙ F ⋙ ULift.upFunctor) ⋙ ULiftHom.up)) z) =
      toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F)
        (realizedNerveLiftHomeomorph.{uUp, vUp, max uUp vUp wUp} B z) := by
  rw [realizedNerveLiftHomeomorph_apply, realizedNerveLiftHomeomorph_apply]
  let F0 := commonUpObjectFunctor.{uUp, vUp, wUp} F
  have hHom :=
    realizedHomLiftFrame_naturality.{max uUp vUp wUp, vUp, max uUp vUp wUp} F0 z
  change realizedNerveULiftHomeomorph.{max uUp vUp, vUp, max uUp vUp wUp} A
      (realizedNerveULiftHomHomeomorph.{max uUp vUp wUp, vUp, max uUp vUp wUp}
        (ULift.{max uUp vUp wUp} A)
        (toTop.map (nerveMap (homLiftFrameFunctor F0)) z)) =
    toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F)
      (realizedNerveULiftHomeomorph.{uUp, vUp, max uUp vUp wUp} B
        (realizedNerveULiftHomHomeomorph.{max uUp vUp wUp, vUp, max uUp vUp wUp}
          (ULift.{max uUp vUp wUp} B) z))
  exact (congrArg
    (realizedNerveULiftHomeomorph.{max uUp vUp, vUp, max uUp vUp wUp} A) hHom).trans
      (commonUpObjectRealizationSquare.{uUp, vUp, wUp} F _)

/-- The SAME actual upward object-level functor commutes with both original
lift charts on EVERY original point in any larger canonical working envelope. -/
public theorem realizedNerveLiftHomeomorph_commonUpFunctor_naturality (F : B ⥤ A)
    (z : toTop.obj (nerve
      (ULiftHom.{max uUp vUp wUp} (ULift.{max uUp vUp wUp} B)))) :
    realizedNerveLiftHomeomorph.{max uUp vUp, vUp, max uUp vUp wUp} A
        (toTop.map (nerveMap (ULiftHom.down ⋙
          (ULift.downFunctor ⋙ F ⋙ ULift.upFunctor) ⋙ ULiftHom.up)) z) =
      toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F)
        (realizedNerveLiftHomeomorph.{uUp, vUp, max uUp vUp wUp} B z) :=
  commonUpCombinedChartComputed F z

end OriginalCommonUpChart

end SSet

end


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe u v w

namespace SSet

private theorem originalRealizedSimplexMapComputed
    {X Y : SSet.{u}} (φ : X ⟶ Y) (n : SimplexCategory) (σ : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    toTop.map φ (toTop.map (yonedaEquiv.symm σ)
        ((toTopSimplex.{u}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{u}.obj n))) =
      toTop.map (yonedaEquiv.symm (φ.app (op n) σ))
        ((toTopSimplex.{u}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{u}.obj n)) := by
  let y : SimplexCategory.toTop.{u}.obj n := ULift.up t
  let z : toTop.obj (stdSimplex.{u}.obj n) := (toTopSimplex.{u}.inv.app n) y
  exact (TopCat.comp_app (toTop.map (yonedaEquiv.symm σ)) (toTop.map φ) z).symm.trans
    ((ConcreteCategory.congr_hom
      (toTop.map_comp (yonedaEquiv.symm σ) φ).symm z).trans
      (congrArg (fun f : stdSimplex.{u}.obj n ⟶ Y => toTop.map f z)
        (yonedaEquiv_symm_comp σ φ)))

private theorem originalRealizationValueDownSimplexComputed
    (X : SSet.{u}) (n : SimplexCategory) (σ : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizationValueDown.{u, w} X
        (toTop.map (yonedaEquiv.symm
          (ULift.up σ : (uliftFunctor.{w, u}.obj X).obj (op n)))
          ((toTopSimplex.{max u w}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max u w}.obj n))) =
      toTop.map (yonedaEquiv.symm σ) ((toTopSimplex.{u}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{u}.obj n)) := by
  let J : stdSimplex.{max u w}.obj n ⟶
      uliftFunctor.{w, u}.obj (stdSimplex.{u}.obj n) :=
    { app Δ := ↾fun a => ULift.up (ULift.up a.down)
      naturality := by intro Δ Γ f; ext a; rfl }
  let g : stdSimplex.{u}.obj n ⟶ X := yonedaEquiv.symm σ
  let y : SimplexCategory.toTop.{max u w}.obj n := ULift.up t
  let z := toTop.map J ((toTopSimplex.{max u w}.inv.app n) y)
  have hJ : J ≫ uliftFunctor.{w, u}.map g =
      yonedaEquiv.symm (ULift.up σ : (uliftFunctor.{w, u}.obj X).obj (op n)) := by
    ext Δ a
    rfl
  have hLift :
      toTop.map (yonedaEquiv.symm
          (ULift.up σ : (uliftFunctor.{w, u}.obj X).obj (op n)))
        ((toTopSimplex.{max u w}.inv.app n) y) =
      toTop.map (uliftFunctor.{w, u}.map g) z := by
    calc
      _ = toTop.map (J ≫ uliftFunctor.{w, u}.map g)
          ((toTopSimplex.{max u w}.inv.app n) y) :=
        congrArg (fun f : stdSimplex.{max u w}.obj n ⟶ uliftFunctor.{w, u}.obj X =>
          toTop.map f ((toTopSimplex.{max u w}.inv.app n) y)) hJ.symm
      _ = (toTop.map J ≫ toTop.map (uliftFunctor.{w, u}.map g))
          ((toTopSimplex.{max u w}.inv.app n) y) :=
        ConcreteCategory.congr_hom (toTop.map_comp J (uliftFunctor.{w, u}.map g))
          ((toTopSimplex.{max u w}.inv.app n) y)
      _ = toTop.map (uliftFunctor.{w, u}.map g) z :=
        TopCat.comp_app _ _ _
  have hStandard : realizationValueDown.{u, w} (stdSimplex.{u}.obj n) z =
      (toTopSimplex.{u}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{u}.obj n) := by
    change ((toTopULiftIso.{u, w}.hom.app (stdSimplex.{u}.obj n)) z).down = _
    have h := toTopULiftIso_hom_simplexValue.{u, w} n t
    change (toTopULiftIso.{u, w}.hom.app (stdSimplex.{u}.obj n)) z =
      (ULift.up ((toTopSimplex.{u}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{u}.obj n)) :
        TopCat.uliftFunctor.{w, u}.obj (toTop.obj (stdSimplex.{u}.obj n))) at h
    exact congrArg
      (fun q : TopCat.uliftFunctor.{w, u}.obj (toTop.obj (stdSimplex.{u}.obj n)) => q.down) h
  exact (congrArg (realizationValueDown.{u, w} X) hLift).trans
    ((realizationValueDown_naturality.{u, w} g z).trans
      (congrArg (toTop.map g) hStandard))

private theorem originalObjectLiftSimplexChartComputed
    (C : Type u) [Category.{v} C] (n : SimplexCategory) (σ : (nerve C).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizedNerveULiftHomeomorph.{u, v, w} C
        (toTop.map (yonedaEquiv.symm
          (σ ⋙ (ULift.upFunctor : C ⥤ ULift.{w} C)))
          ((toTopSimplex.{max u v w}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max u v w}.obj n))) =
      toTop.map (yonedaEquiv.symm σ) ((toTopSimplex.{max u v}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{max u v}.obj n)) := by
  let σO : (nerve (ULift.{w} C)).obj (op n) := σ ⋙ ULift.upFunctor
  let y : SimplexCategory.toTop.{max u v w}.obj n := ULift.up t
  let z := toTop.map (yonedaEquiv.symm σO) ((toTopSimplex.{max u v w}.inv.app n) y)
  have hChain : σO ⋙ (ULift.downFunctor : ULift.{w} C ⥤ C) = σ := by
    exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
      change σ.map f = eqToHom (rfl : σ.obj i = σ.obj i) ≫ σ.map f ≫
        eqToHom (rfl : σ.obj j = σ.obj j)
      exact CategoryTheory.eq_conj_eqToHom (σ.map f))
  have hNerve : (nerveULiftIso.{u, v, w} C).hom.app (op n) σO =
      (ULift.up σ : (uliftFunctor.{w, max u v}.obj (nerve C)).obj (op n)) :=
    (nerveULiftIso_hom_app_eq.{u, v, w} C (op n) σO).trans (congrArg ULift.up hChain)
  have hPoint : toTop.map (nerveULiftIso.{u, v, w} C).hom z =
      toTop.map (yonedaEquiv.symm
          (ULift.up σ : (uliftFunctor.{w, max u v}.obj (nerve C)).obj (op n)))
        ((toTopSimplex.{max u v w}.inv.app n) y) :=
    (originalRealizedSimplexMapComputed.{max u v w}
      (nerveULiftIso.{u, v, w} C).hom n σO t).trans
      (congrArg (fun q : (uliftFunctor.{w, max u v}.obj (nerve C)).obj (op n) =>
        toTop.map (yonedaEquiv.symm q) ((toTopSimplex.{max u v w}.inv.app n) y)) hNerve)
  have hChart : realizedNerveULiftHomeomorph.{u, v, w} C z =
      realizationValueDown.{max u v, w} (nerve C)
        (toTop.map (nerveULiftIso.{u, v, w} C).hom z) :=
    realizedNerveULiftHomeomorph_apply.{u, v, w} C z
  exact hChart.trans
    ((congrArg (realizationValueDown.{max u v, w} (nerve C)) hPoint).trans
      (originalRealizationValueDownSimplexComputed.{max u v, w} (nerve C) n σ t))

private theorem originalHomLiftSimplexChartComputed
    (C : Type u) [Category.{v} C] (n : SimplexCategory) (σ : (nerve C).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizedNerveULiftHomHomeomorph.{u, v, w} C
        (toTop.map (yonedaEquiv.symm
          (σ ⋙ (ULiftHom.up : C ⥤ ULiftHom.{w} C)))
          ((toTopSimplex.{max u v w}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max u v w}.obj n))) =
      toTop.map (yonedaEquiv.symm σ) ((toTopSimplex.{max u v}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{max u v}.obj n)) := by
  let σH : (nerve (ULiftHom.{w} C)).obj (op n) := σ ⋙ ULiftHom.up
  let y : SimplexCategory.toTop.{max u v w}.obj n := ULift.up t
  let z := toTop.map (yonedaEquiv.symm σH) ((toTopSimplex.{max u v w}.inv.app n) y)
  have hChain : σH ⋙ (ULiftHom.down : ULiftHom.{w} C ⥤ C) = σ := by
    exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
      change σ.map f = eqToHom (rfl : σ.obj i = σ.obj i) ≫ σ.map f ≫
        eqToHom (rfl : σ.obj j = σ.obj j)
      exact CategoryTheory.eq_conj_eqToHom (σ.map f))
  have hNerve : (nerveULiftHomIso.{u, v, w} C).hom.app (op n) σH =
      (ULift.up σ : (uliftFunctor.{w, max u v}.obj (nerve C)).obj (op n)) :=
    (nerveULiftHomIso_hom_app_eq.{u, v, w} C (op n) σH).trans (congrArg ULift.up hChain)
  have hPoint : toTop.map (nerveULiftHomIso.{u, v, w} C).hom z =
      toTop.map (yonedaEquiv.symm
          (ULift.up σ : (uliftFunctor.{w, max u v}.obj (nerve C)).obj (op n)))
        ((toTopSimplex.{max u v w}.inv.app n) y) :=
    (originalRealizedSimplexMapComputed.{max u v w}
      (nerveULiftHomIso.{u, v, w} C).hom n σH t).trans
      (congrArg (fun q : (uliftFunctor.{w, max u v}.obj (nerve C)).obj (op n) =>
        toTop.map (yonedaEquiv.symm q) ((toTopSimplex.{max u v w}.inv.app n) y)) hNerve)
  have hChart : realizedNerveULiftHomHomeomorph.{u, v, w} C z =
      realizationValueDown.{max u v, w} (nerve C)
        (toTop.map (nerveULiftHomIso.{u, v, w} C).hom z) :=
    realizedNerveULiftHomHomeomorph_apply.{u, v, w} C z
  exact hChart.trans
    ((congrArg (realizationValueDown.{max u v, w} (nerve C)) hPoint).trans
      (originalRealizationValueDownSimplexComputed.{max u v, w} (nerve C) n σ t))

private theorem originalCombinedLiftSimplexChartComputed
    (C : Type u) [Category.{v} C] (n : SimplexCategory) (σ : (nerve C).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizedNerveLiftHomeomorph.{u, v, w} C
        (toTop.map (yonedaEquiv.symm
          (σ ⋙ (ULiftHomULiftCategory.equiv.{w, w, v, u} C).functor))
          ((toTopSimplex.{max u v w}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max u v w}.obj n))) =
      toTop.map (yonedaEquiv.symm σ) ((toTopSimplex.{max u v}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{max u v}.obj n)) := by
  let σO : (nerve (ULift.{w} C)).obj (op n) := σ ⋙ ULift.upFunctor
  let σH : (nerve (ULiftHom.{w} (ULift.{w} C))).obj (op n) := σO ⋙ ULiftHom.up
  let y : SimplexCategory.toTop.{max u v w}.obj n := ULift.up t
  let z := toTop.map (yonedaEquiv.symm σH) ((toTopSimplex.{max u v w}.inv.app n) y)
  have hHom : realizedNerveULiftHomHomeomorph.{max u w, v, w} (ULift.{w} C) z =
      toTop.map (yonedaEquiv.symm σO) ((toTopSimplex.{max u v w}.inv.app n) y) :=
    originalHomLiftSimplexChartComputed.{max u w, v, w} (ULift.{w} C) n σO t
  have hObject : realizedNerveULiftHomeomorph.{u, v, w} C
      (toTop.map (yonedaEquiv.symm σO) ((toTopSimplex.{max u v w}.inv.app n) y)) =
      toTop.map (yonedaEquiv.symm σ) ((toTopSimplex.{max u v}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{max u v}.obj n)) :=
    originalObjectLiftSimplexChartComputed.{u, v, w} C n σ t
  change realizedNerveLiftHomeomorph.{u, v, w} C z = _
  exact (realizedNerveLiftHomeomorph_apply.{u, v, w} C z).trans
    ((congrArg (realizedNerveULiftHomeomorph.{u, v, w} C) hHom).trans hObject)

/-- The SAME original combined chart keeps every canonical lifted chain and
its actual barycentric point in three independent object, Hom and lift worlds. -/
public theorem realizedNerveLiftHomeomorph_simplexValue
    (C : Type u) [Category.{v} C] (n : SimplexCategory) (σ : (nerve C).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizedNerveLiftHomeomorph.{u, v, w} C
        (toTop.map (yonedaEquiv.symm
          (σ ⋙ (ULiftHomULiftCategory.equiv.{w, w, v, u} C).functor))
          ((toTopSimplex.{max u v w}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max u v w}.obj n))) =
      toTop.map (yonedaEquiv.symm σ) ((toTopSimplex.{max u v}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{max u v}.obj n)) :=
  originalCombinedLiftSimplexChartComputed C n σ t

end SSet

end

noncomputable section

attribute [local instance] CategoryTheory.uliftCategory

universe uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom

namespace CategoryTheory

variable {C : Type uEquivSourceObj} [Category.{uEquivSourceHom} C]
  {D : Type uEquivTargetObj} [Category.{uEquivTargetHom} D]

private theorem realizedNerveEquivalenceToFunRecipeComputed (E : C ≌ D) :
    (realizedNerveEquivalence E).toFun =
      (SSet.realizedNerveLiftHomeomorph.{
        uEquivTargetObj, uEquivTargetHom,
          max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom}
        D).toHomotopyEquiv.toFun.comp
        ((SSet.toTop.map (nerveMap
          ((ULiftHomULiftCategory.equiv.{
            max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom,
              max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom,
              uEquivSourceHom, uEquivSourceObj} C).inverse ⋙ E.functor ⋙
            (ULiftHomULiftCategory.equiv.{
              max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom,
                max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom,
                uEquivTargetHom, uEquivTargetObj} D).functor))).hom.comp
          (SSet.realizedNerveLiftHomeomorph.{
            uEquivSourceObj, uEquivSourceHom,
              max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom}
            C).symm.toHomotopyEquiv.toFun) := by
  apply ContinuousMap.ext
  intro x
  let HC := SSet.realizedNerveLiftHomeomorph.{
    uEquivSourceObj, uEquivSourceHom,
      max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom} C
  let HD := SSet.realizedNerveLiftHomeomorph.{
    uEquivTargetObj, uEquivTargetHom,
      max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom} D
  let L := liftedCategoryEquivalence E
  change HD ((liftedRealizedEquivalence E).toFun (HC.symm x)) =
    HD (SSet.toTop.map (nerveMap L.functor) (HC.symm x))
  have hMiddle : (liftedRealizedEquivalence E).toFun (HC.symm x) =
      SSet.toTop.map (nerveMap L.functor) (HC.symm x) := by
    change (⇑(liftedRealizedEquivalence E)) (HC.symm x) = _
    dsimp only [liftedRealizedEquivalence]
    exact congrFun (SSet.coe_realizedHomotopyEquiv _ _ _ _ _ _) (HC.symm x)
  exact congrArg HD hMiddle

/-- The whole forward map of the SAME original mixed-world equivalence has
its actual default lifted recipe, retaining all four category worlds and choices. -/
public theorem realizedNerveEquivalence_toFun_recipe (E : C ≌ D) :
    (realizedNerveEquivalence E).toFun =
      (SSet.realizedNerveLiftHomeomorph.{
        uEquivTargetObj, uEquivTargetHom,
          max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom}
        D).toHomotopyEquiv.toFun.comp
        ((SSet.toTop.map (nerveMap
          ((ULiftHomULiftCategory.equiv.{
            max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom,
              max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom,
              uEquivSourceHom, uEquivSourceObj} C).inverse ⋙ E.functor ⋙
            (ULiftHomULiftCategory.equiv.{
              max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom,
                max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom,
                uEquivTargetHom, uEquivTargetObj} D).functor))).hom.comp
          (SSet.realizedNerveLiftHomeomorph.{
            uEquivSourceObj, uEquivSourceHom,
              max uEquivSourceObj uEquivSourceHom uEquivTargetObj uEquivTargetHom}
            C).symm.toHomotopyEquiv.toFun) :=
  realizedNerveEquivalenceToFunRecipeComputed E

end CategoryTheory

end


noncomputable section

attribute [local instance] CategoryTheory.uliftCategory

namespace CategoryTheory

private theorem realizedNerveEquivalenceInvFunRecipeComputed.{uInvSourceObj, uInvSourceHom,
  uInvTargetObj, uInvTargetHom}
    {C : Type uInvSourceObj} [Category.{uInvSourceHom} C]
    {D : Type uInvTargetObj} [Category.{uInvTargetHom} D] (E : C ≌ D) :
    (realizedNerveEquivalence E).invFun =
      (SSet.realizedNerveLiftHomeomorph.{uInvSourceObj, uInvSourceHom, max uInvSourceObj
        uInvSourceHom uInvTargetObj uInvTargetHom}
        C).toHomotopyEquiv.toFun.comp
        ((SSet.toTop.map (nerveMap
          ((ULiftHomULiftCategory.equiv.{max uInvSourceObj uInvSourceHom uInvTargetObj
            uInvTargetHom, max uInvSourceObj uInvSourceHom uInvTargetObj uInvTargetHom,
            uInvTargetHom, uInvTargetObj}
            D).inverse ⋙ E.inverse ⋙
              (ULiftHomULiftCategory.equiv.{max uInvSourceObj uInvSourceHom uInvTargetObj
                uInvTargetHom, max uInvSourceObj uInvSourceHom uInvTargetObj uInvTargetHom,
                uInvSourceHom, uInvSourceObj}
                C).functor))).hom.comp
          (SSet.realizedNerveLiftHomeomorph.{uInvTargetObj, uInvTargetHom, max uInvSourceObj
            uInvSourceHom uInvTargetObj uInvTargetHom}
            D).symm.toHomotopyEquiv.toFun) := by
  apply ContinuousMap.ext
  intro x
  let HC := SSet.realizedNerveLiftHomeomorph.{uInvSourceObj, uInvSourceHom, max uInvSourceObj
    uInvSourceHom uInvTargetObj uInvTargetHom} C
  let HD := SSet.realizedNerveLiftHomeomorph.{uInvTargetObj, uInvTargetHom, max uInvSourceObj
    uInvSourceHom uInvTargetObj uInvTargetHom} D
  let L := liftedCategoryEquivalence E
  change HC ((liftedRealizedEquivalence E).invFun (HD.symm x)) =
    HC (SSet.toTop.map (nerveMap L.inverse) (HD.symm x))
  have hMiddle : (liftedRealizedEquivalence E).invFun (HD.symm x) =
      SSet.toTop.map (nerveMap L.inverse) (HD.symm x) := by
    change (⇑(liftedRealizedEquivalence E).symm) (HD.symm x) = _
    dsimp only [liftedRealizedEquivalence]
    exact congrFun (SSet.coe_symm_realizedHomotopyEquiv _ _ _ _ _ _) (HD.symm x)
  exact congrArg HC hMiddle

/-- The whole inverse field of the SAME original mixed-world realization
    equivalence has its actual inverse-functor recipe and original charts. -/
public theorem realizedNerveEquivalence_invFun_recipe.{uInvSourceObj, uInvSourceHom,
  uInvTargetObj, uInvTargetHom}
    {C : Type uInvSourceObj} [Category.{uInvSourceHom} C]
    {D : Type uInvTargetObj} [Category.{uInvTargetHom} D] (E : C ≌ D) :
    (realizedNerveEquivalence E).invFun =
      (SSet.realizedNerveLiftHomeomorph.{uInvSourceObj, uInvSourceHom, max uInvSourceObj
        uInvSourceHom uInvTargetObj uInvTargetHom}
        C).toHomotopyEquiv.toFun.comp
        ((SSet.toTop.map (nerveMap
          ((ULiftHomULiftCategory.equiv.{max uInvSourceObj uInvSourceHom uInvTargetObj
            uInvTargetHom, max uInvSourceObj uInvSourceHom uInvTargetObj uInvTargetHom,
            uInvTargetHom, uInvTargetObj}
            D).inverse ⋙ E.inverse ⋙
              (ULiftHomULiftCategory.equiv.{max uInvSourceObj uInvSourceHom uInvTargetObj
                uInvTargetHom, max uInvSourceObj uInvSourceHom uInvTargetObj uInvTargetHom,
                uInvSourceHom, uInvSourceObj}
                C).functor))).hom.comp
          (SSet.realizedNerveLiftHomeomorph.{uInvTargetObj, uInvTargetHom, max uInvSourceObj
            uInvSourceHom uInvTargetObj uInvTargetHom}
            D).symm.toHomotopyEquiv.toFun) :=
  realizedNerveEquivalenceInvFunRecipeComputed E

end CategoryTheory

end
