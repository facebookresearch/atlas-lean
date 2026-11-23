/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveHomotopy
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import Mathlib.Topology.Homotopy.Path
public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMapPrecomp

/-!
# Realization of nerve homotopies at objects

Evaluating the realized homotopy induced by a natural transformation at a
realized object gives the realized edge of the corresponding component.  The
proof exposes the required pointwise inverse formula for the realization
product comparison with the simplicial interval.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet

/-- Constant simplicial map from the interval at a chosen vertex. -/
noncomputable def intervalConstVertex
    {X : SSet.{u}} (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    (Δ[1] : SSet.{u}) ⟶ X :=
  IsTerminal.from SSet.stdSimplex.isTerminalObj₀ (Δ[1] : SSet.{u}) ≫
    SSet.const x

private theorem toTop_map_intervalConstVertex
    {X : SSet.{u}} (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    SSet.toTop.map (intervalConstVertex x) =
      TopCat.const (SSet.realizedVertex x) := by
  unfold intervalConstVertex
  rw [Functor.map_comp]
  apply TopCat.hom_ext
  ext s
  change SSet.toTop.map (SSet.const x)
      (SSet.toTop.map
        (IsTerminal.from SSet.stdSimplex.isTerminalObj₀
          (Δ[1] : SSet.{u})) s) = _
  change _ = SSet.realizedVertex x
  rw [SSet.realizedVertex_eq_const]
  exact congrArg (SSet.toTop.map (SSet.const x))
    (Subsingleton.elim _ _)

/-- Inverse to the realization product comparison with the simplicial
interval in the second factor. -/
noncomputable def prodComparisonToTopInvInterval (X : SSet.{u}) :
    SSet.toTop.obj X ⨯ SSet.toTop.obj (Δ[1] : SSet.{u}) ⟶
      SSet.toTop.obj (X ⨯ (Δ[1] : SSet.{u})) := by
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap (Δ[1] : SSet.{u}) X
  exact inv (Limits.prodComparison SSet.toTop X (Δ[1] : SSet.{u}))

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise inverse-product formula for a realized vertex and an interval
point. -/
theorem prodComparison_toTop_inv_constVertex_apply
    (X : SSet.{u})
    (x : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (s : SSet.toTop.obj (Δ[1] : SSet.{u})) :
    prodComparisonToTopInvInterval X
        (Limits.prod.lift (TopCat.const (SSet.realizedVertex x))
          (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u}))) s) =
      SSet.toTop.map
        (Limits.prod.lift (intervalConstVertex x)
          (𝟙 (Δ[1] : SSet.{u}))) s := by
  let c := Limits.prodComparison SSet.toTop X (Δ[1] : SSet.{u})
  let pair := Limits.prod.lift (TopCat.const (SSet.realizedVertex x))
    (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u})))
  let k := Limits.prod.lift (intervalConstVertex x)
    (𝟙 (Δ[1] : SSet.{u}))
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let _ : IsIso c :=
    SSet.isIso_prodComparison_swap (Δ[1] : SSet.{u}) X
  apply (ConcreteCategory.bijective_of_isIso c).1
  have hInv : c (prodComparisonToTopInvInterval X (pair s)) = pair s := by
    unfold prodComparisonToTopInvInterval
    simpa only [ConcreteCategory.comp_apply, CategoryTheory.id_apply] using
      ConcreteCategory.congr_hom (IsIso.inv_hom_id c) (pair s)
  rw [hInv]
  have hMap : SSet.toTop.map k ≫ c = pair := by
    apply Limits.prod.hom_ext
    · rw [Category.assoc, Limits.prodComparison_fst,
        ← Functor.map_comp, Limits.prod.lift_fst,
        Limits.prod.lift_fst, toTop_map_intervalConstVertex]
    · rw [Category.assoc, Limits.prodComparison_snd,
        ← Functor.map_comp, Limits.prod.lift_snd,
        Limits.prod.lift_snd]
      exact SSet.toTop.map_id _
  exact (ConcreteCategory.congr_hom hMap s).symm

/-- The inverse realization-product comparison on a realized vertex and the
identity interval is the realization of the corresponding simplicial
cylinder. -/
theorem prod_lift_constVertex_prodComparisonToTopInvInterval
    (X : SSet.{u})
    (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    Limits.prod.lift (TopCat.const (SSet.realizedVertex x))
        (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u}))) ≫
        prodComparisonToTopInvInterval X =
      SSet.toTop.map
        (Limits.prod.lift (intervalConstVertex x)
          (𝟙 (Δ[1] : SSet.{u}))) := by
  apply TopCat.hom_ext
  ext s
  change prodComparisonToTopInvInterval X
      (Limits.prod.lift (TopCat.const (SSet.realizedVertex x))
        (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u}))) s) = _
  exact prodComparison_toTop_inv_constVertex_apply X x s

private theorem interval_realizedVertex_front
    (X : SSet.{u})
    (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    Limits.prod.lift (𝟙 TopCat.I.{u})
        (TopCat.const (SSet.realizedVertex x)) ≫
        (Limits.prod.braiding TopCat.I.{u}
          (SSet.toTop.obj X)).hom ≫
        Limits.prod.map (𝟙 (SSet.toTop.obj X))
          SSet.stdSimplex.toTopObjIsoI.inv =
      SSet.stdSimplex.toTopObjIsoI.inv ≫
        Limits.prod.lift (TopCat.const (SSet.realizedVertex x))
          (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u}))) := by
  apply Limits.prod.hom_ext
  · simp only [Limits.prod.braiding_hom, Limits.prod.lift_map,
      Category.comp_id, Limits.prod.comp_lift, Limits.limit.lift_π,
      Limits.BinaryFan.mk_pt, Limits.BinaryFan.mk_snd,
      Limits.limit.lift_π_assoc, Limits.pair_obj_left,
      Limits.BinaryFan.mk_fst, Category.id_comp]
    ext t
    rfl
  · simp

private theorem tensorLeftIsoProd_inv_fst (X Y : SSet.{u}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app Y ≫
        CartesianMonoidalCategory.fst X Y =
      Limits.prod.fst := by
  exact IsLimit.conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (Limits.limit.isLimit _) ⟨WalkingPair.left⟩

private theorem tensorLeftIsoProd_inv_snd (X Y : SSet.{u}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app Y ≫
        CartesianMonoidalCategory.snd X Y =
      Limits.prod.snd := by
  exact IsLimit.conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (Limits.limit.isLimit _) ⟨WalkingPair.right⟩

set_option backward.isDefEq.respectTransparency false in
private theorem prod_lift_tensorLeftIsoProd_inv
    {T X Y : SSet.{u}} (f : T ⟶ X) (g : T ⟶ Y) :
    Limits.prod.lift f g ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app Y =
      CartesianMonoidalCategory.lift f g := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tensorLeftIsoProd_inv_fst,
      Limits.prod.lift_fst, CartesianMonoidalCategory.lift_fst]
  · rw [Category.assoc, tensorLeftIsoProd_inv_snd,
      Limits.prod.lift_snd, CartesianMonoidalCategory.lift_snd]

private theorem yonedaEquiv_lift
    {X Y : SSet.{u}} {n : SimplexCategory}
    (f : SSet.stdSimplex.obj n ⟶ X)
    (g : SSet.stdSimplex.obj n ⟶ Y) :
    SSet.yonedaEquiv (CartesianMonoidalCategory.lift f g) =
      (SSet.yonedaEquiv f, SSet.yonedaEquiv g) := by
  apply Prod.ext
  · change SSet.yonedaEquiv
      (CartesianMonoidalCategory.lift f g ≫
        CartesianMonoidalCategory.fst X Y) = _
    rw [CartesianMonoidalCategory.lift_fst]
  · change SSet.yonedaEquiv
      (CartesianMonoidalCategory.lift f g ≫
        CartesianMonoidalCategory.snd X Y) = _
    rw [CartesianMonoidalCategory.lift_snd]

end SSet

namespace CategoryTheory
namespace NatTrans

set_option backward.isDefEq.respectTransparency false in
/-- The constant-object/identity-interval cylinder for a natural
transformation is the Yoneda map of its component edge. -/
theorem nerveHomotopyMap_component
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C) :
    Limits.prod.lift
        (SSet.intervalConstVertex (ComposableArrows.mk₀ c))
        (𝟙 (Δ[1] : SSet.{u})) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd (nerve C)).inv.app
          (Δ[1] : SSet.{u}) ≫
        nerveHomotopyMap alpha =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (alpha.app c)) := by
  rw [← Category.assoc, SSet.prod_lift_tensorLeftIsoProd_inv]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change (nerveHomotopyMap alpha).app
      (op (SimplexCategory.mk 1))
      (SSet.yonedaEquiv (CartesianMonoidalCategory.lift
        (SSet.intervalConstVertex (ComposableArrows.mk₀ c))
        (𝟙 (Δ[1] : SSet.{u})))) =
    ComposableArrows.mk₁ (alpha.app c)
  rw [SSet.yonedaEquiv_lift]
  rw [show SSet.intervalConstVertex (ComposableArrows.mk₀ c) =
      (SSet.const (X := (Δ[1] : SSet.{u}))
        (Y := nerve C) (ComposableArrows.mk₀ c)) by
    unfold SSet.intervalConstVertex
    rw [SSet.comp_const]]
  have hconst :
      SSet.yonedaEquiv
          (SSet.const (X := (Δ[1] : SSet.{u}))
            (Y := nerve C) (ComposableArrows.mk₀ c)) =
        (Functor.const (Fin 2)).obj c := by
    apply Functor.hext
    · intro i
      rfl
    · intro i j f
      apply heq_of_eq
      change 𝟙 c = 𝟙 c
      rfl
  rw [hconst]
  change ((nerveCylinderFunctor alpha).mapComposableArrows 1).obj
      (((Functor.const (Fin 2)).obj c).prod'
        (SSet.stdSimplex.asOrderHom
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))).toFunctor) =
    ComposableArrows.mk₁ (alpha.app c)
  have hinterval :
      (SSet.stdSimplex.asOrderHom
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))).toFunctor =
        𝟭 (Fin 2) := by
    apply Functor.hext
    · intro i
      rfl
    · intro i j f
      apply heq_of_eq
      rfl
  rw [hinterval]
  apply Functor.hext
  · intro i
    fin_cases i <;> rfl
  · intro i j f
    fin_cases i
    · fin_cases j
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]
    · fin_cases j
      · exfalso
        have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom f
        omega
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]

end NatTrans
end CategoryTheory

namespace SSet

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the realized nerve homotopy of a natural transformation to a
realized object gives the realized path of the component edge. -/
theorem realizeHomotopyMap_nerveHomotopy_vertex
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C) :
    Limits.prod.lift (𝟙 TopCat.I.{u})
        (TopCat.const
          (SSet.realizedVertex (ComposableArrows.mk₀ c))) ≫
        SSet.realizeHomotopyMap (nerve C) (nerve D)
          (nerveMap F) (nerveMap G)
          (CategoryTheory.NatTrans.nerveHomotopy alpha) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom := by
  let X : SSet.{u} := nerve C
  let x : X.obj (Opposite.op (SimplexCategory.mk 0)) :=
    ComposableArrows.mk₀ c
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap _ _
  let bridge : ((Limits.prod.functor.obj X).obj
      (Δ[1] : SSet.{u})) ≅ (X ⨯ (Δ[1] : SSet.{u})) :=
    Iso.refl _
  rw [SSet.realizedEdgePath_hom]
  change
    Limits.prod.lift (𝟙 TopCat.I.{u})
        (TopCat.const (SSet.realizedVertex x)) ≫
        (Limits.prod.braiding TopCat.I.{u}
          (SSet.toTop.obj X)).hom ≫
        Limits.prod.map (𝟙 (SSet.toTop.obj X))
          SSet.stdSimplex.toTopObjIsoI.inv ≫
        (asIso (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{u}))).inv ≫
        SSet.toTop.map bridge.inv ≫
        SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{u})) ≫
        SSet.toTop.map
          (CategoryTheory.NatTrans.nerveHomotopy alpha).h =
      SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            (ComposableArrows.mk₁ (alpha.app c)))
  have hInv :
      (asIso (Limits.prodComparison SSet.toTop
        X (Δ[1] : SSet.{u}))).inv =
        SSet.prodComparisonToTopInvInterval X := by
    rw [CategoryTheory.asIso_inv]
    apply (cancel_mono (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{u}))).mp
    simp [SSet.prodComparisonToTopInvInterval]
  slice_lhs 1 3 =>
    rw [SSet.interval_realizedVertex_front X x]
  rw [hInv]
  slice_lhs 2 3 =>
    rw [SSet.prod_lift_constVertex_prodComparisonToTopInvInterval X x]
  have hBridge : bridge.inv = 𝟙 _ := by
    rfl
  rw [hBridge]
  simp only [Category.comp_id, ← Functor.map_comp,
    Category.assoc]
  dsimp [X, x]
  change
    SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map
          (Limits.prod.lift
              (SSet.intervalConstVertex (ComposableArrows.mk₀ c))
              (𝟙 (Δ[1] : SSet.{u})) ≫
            (CartesianMonoidalCategory.tensorLeftIsoProd
              (nerve C)).inv.app (Δ[1] : SSet.{u}) ≫
            CategoryTheory.NatTrans.nerveHomotopyMap alpha) =
      SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            (ComposableArrows.mk₁ (alpha.app c)))
  rw [CategoryTheory.NatTrans.nerveHomotopyMap_component]

/-- Pointwise form of
`realizeHomotopyMap_nerveHomotopy_vertex`, expressed through the ordinary
product carrier of the chosen topological product. -/
theorem realizeHomotopyMap_nerveHomotopy_vertex_apply
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C)
    (t : TopCat.I.{u}) :
    SSet.realizeHomotopyMap (nerve C) (nerve D)
        (nerveMap F) (nerveMap G)
        (CategoryTheory.NatTrans.nerveHomotopy alpha)
        ((TopCat.prodIsoProd TopCat.I.{u}
          (SSet.toTop.obj (nerve C))).inv
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c))) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom t := by
  have hPoint :
      (TopCat.prodIsoProd TopCat.I.{u}
        (SSet.toTop.obj (nerve C))).inv
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
        Limits.prod.lift (𝟙 TopCat.I.{u})
          (TopCat.const
            (SSet.realizedVertex (ComposableArrows.mk₀ c))) t := by
    apply Limits.Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · change ((TopCat.prodIsoProd TopCat.I.{u}
          (SSet.toTop.obj (nerve C))).inv ≫ Limits.prod.fst)
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
        (Limits.prod.lift (𝟙 TopCat.I.{u})
          (TopCat.const
            (SSet.realizedVertex (ComposableArrows.mk₀ c)) :
              TopCat.I.{u} ⟶ SSet.toTop.obj (nerve C)) ≫
            Limits.prod.fst) t
      rw [TopCat.prodIsoProd_inv_fst, Limits.prod.lift_fst]
      rfl
    · change ((TopCat.prodIsoProd TopCat.I.{u}
          (SSet.toTop.obj (nerve C))).inv ≫ Limits.prod.snd)
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
        (Limits.prod.lift (𝟙 TopCat.I.{u})
          (TopCat.const
            (SSet.realizedVertex (ComposableArrows.mk₀ c)) :
              TopCat.I.{u} ⟶ SSet.toTop.obj (nerve C)) ≫
            Limits.prod.snd) t
      rw [TopCat.prodIsoProd_inv_snd, Limits.prod.lift_snd]
      rfl
  rw [hPoint]
  exact ConcreteCategory.congr_hom
    (SSet.realizeHomotopyMap_nerveHomotopy_vertex alpha c) t

/-- A realized nerve map carries the realized object vertex to the realized
vertex of its image. -/
theorem nerveMap_realizedVertex
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (c : C) :
    SSet.toTop.map (nerveMap F)
        (SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      SSet.realizedVertex (ComposableArrows.mk₀ (F.obj c)) := by
  simpa only [CategoryTheory.nerveMap_app_mk₀] using
    (SSet.realizedVertex_naturality
      (CategoryTheory.nerveMap F) (ComposableArrows.mk₀ c)).symm

/-- Evaluating the realized nerve homotopy of a natural transformation at
an object is the realized component edge, with only the endpoint transports
forced by vertex naturality. -/
theorem realizeHomotopy_nerveHomotopy_evalAt
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C) :
    (SSet.realizeHomotopy (nerve C) (nerve D)
        (nerveMap F) (nerveMap G)
        (CategoryTheory.NatTrans.nerveHomotopy alpha)).evalAt
          (SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      (TopCat.pathEquiv
        (SSet.realizedEdgePath
          (CategoryTheory.nerve.edgeMk (alpha.app c)))).cast
        (SSet.nerveMap_realizedVertex F c)
        (SSet.nerveMap_realizedVertex G c) := by
  apply Path.ext
  funext t
  change
    SSet.realizeHomotopyMap (nerve C) (nerve D)
        (nerveMap F) (nerveMap G)
        (CategoryTheory.NatTrans.nerveHomotopy alpha)
        ((TopCat.prodIsoProd TopCat.I.{u}
          (SSet.toTop.obj (nerve C))).inv
          (TopCat.I.homeomorph.symm t,
            SSet.realizedVertex (ComposableArrows.mk₀ c))) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom
          (TopCat.I.homeomorph.symm t)
  exact SSet.realizeHomotopyMap_nerveHomotopy_vertex_apply
    alpha c (TopCat.I.homeomorph.symm t)

end SSet

end

@[expose] public section NativeStationaryVertex

universe uObj vObj wHom

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped Simplicial MonoidalCategory

namespace SSet

variable {A : Type (max uObj vObj)} [Category.{max vObj wHom} A]
  {B : Type uObj} [Category.{max vObj wHom} B] {F G : A ⥤ B}

/-- An equality component keeps the entire realized native cylinder fixed at its source vertex. -/
theorem realizeHomotopyMap_nerveHomotopyCommonHom_stationary_vertex
    (alpha : F ⟶ G) (c : A) (h : F.obj c = G.obj c)
    (halpha : alpha.app c = eqToHom h) :
    Limits.prod.map (𝟙 TopCat.I.{max uObj vObj wHom})
        (SSet.toTop.map
          (SSet.const (ComposableArrows.mk₀ c) :
            (Δ[0] : SSet.{max uObj vObj wHom}) ⟶ nerve A)) ≫
        SSet.realizeHomotopyMap (nerve A) (nerve B)
          (nerveMapCommonHom.{uObj, vObj, wHom} F)
          (nerveMapCommonHom.{uObj, vObj, wHom} G)
          (NatTrans.nerveHomotopyCommonHom.{uObj, vObj, wHom} alpha) =
      Limits.prod.snd ≫ SSet.toTop.map
        ((SSet.const (ComposableArrows.mk₀ c) :
          (Δ[0] : SSet.{max uObj vObj wHom}) ⟶ nerve A) ≫
            nerveMapCommonHom.{uObj, vObj, wHom} F) := by
  let k : (Δ[0] : SSet.{max uObj vObj wHom}) ⟶ nerve A :=
    SSet.const (ComposableArrows.mk₀ c)
  let H : SSet.Homotopy (nerveMapCommonHom.{uObj, vObj, wHom} F)
      (nerveMapCommonHom.{uObj, vObj, wHom} G) :=
    NatTrans.nerveHomotopyCommonHom.{uObj, vObj, wHom} alpha
  have hk (Delta : SimplexCategoryᵒᵖ)
      (x : (Δ[0] : SSet.{max uObj vObj wHom}).obj Delta) :
      k.app Delta x = (Functor.const (Fin (Delta.unop.len + 1))).obj c := by
    apply Functor.hext
    · intro i
      rfl
    · intro i j f
      apply heq_of_eq
      change 𝟙 c = 𝟙 c
      rfl
  have hstat : (H.precomp k).h =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{max uObj vObj wHom})
        (Δ[1] : SSet.{max uObj vObj wHom}) ≫
          (k ≫ nerveMapCommonHom.{uObj, vObj, wHom} F) := by
    rw [Homotopy.precomp_h]
    ext Delta x
    change (NatTrans.nerveHomotopyMapCommonHom.{uObj, vObj, wHom} alpha).app Delta
        ⟨k.app Delta x.1, x.2⟩ =
      (nerveMapCommonHom.{uObj, vObj, wHom} F).app Delta (k.app Delta x.1)
    rw [hk]
    exact NatTrans.nerveHomotopyMapCommonHom_const_apply_of_app_eqToHom
      alpha c h halpha x.2
  exact (SSet.realizeHomotopyMap_precomp H k).trans
    (SSet.realizeHomotopyMap_of_h_eq_fst (H.precomp k) hstat)

/-- Every point of the interval has the actual constant image of an equality component. -/
theorem realizeHomotopyMap_nerveHomotopyCommonHom_const_vertex_apply
    (alpha : F ⟶ G) (c : A) (h : F.obj c = G.obj c)
    (halpha : alpha.app c = eqToHom h) (t : TopCat.I.{max uObj vObj wHom}) :
    SSet.realizeHomotopyMap (nerve A) (nerve B)
        (nerveMapCommonHom.{uObj, vObj, wHom} F)
        (nerveMapCommonHom.{uObj, vObj, wHom} G)
        (NatTrans.nerveHomotopyCommonHom.{uObj, vObj, wHom} alpha)
        ((TopCat.prodIsoProd TopCat.I.{max uObj vObj wHom}
          (SSet.toTop.obj (nerve A : SSet.{max uObj vObj wHom}))).inv
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c))) =
      SSet.realizedVertex (ComposableArrows.mk₀ (F.obj c)) := by
  let k : (Δ[0] : SSet.{max uObj vObj wHom}) ⟶ nerve A :=
    SSet.const (ComposableArrows.mk₀ c)
  let H : SSet.Homotopy (nerveMapCommonHom.{uObj, vObj, wHom} F)
      (nerveMapCommonHom.{uObj, vObj, wHom} G) :=
    NatTrans.nerveHomotopyCommonHom.{uObj, vObj, wHom} alpha
  let P0 : TopCat.{max uObj vObj wHom} :=
    SSet.toTop.obj (Δ[0] : SSet.{max uObj vObj wHom})
  let p0 : ↥(TopCat.I.{max uObj vObj wHom} ⨯ P0 : TopCat.{max uObj vObj wHom}) :=
    (TopCat.prodIsoProd TopCat.I P0).inv (t, default)
  have hk : SSet.toTop.map k (default : P0) =
      SSet.realizedVertex (ComposableArrows.mk₀ c) := by
    change SSet.toTop.map
        (SSet.const (ComposableArrows.mk₀ c) :
          (Δ[0] : SSet.{max uObj vObj wHom}) ⟶ (nerve A : SSet.{max uObj vObj wHom}))
        (default : SSet.toTop.obj (Δ[0] : SSet.{max uObj vObj wHom})) =
      SSet.realizedVertex (X := (nerve A : SSet.{max uObj vObj wHom}))
        (ComposableArrows.mk₀ c)
    exact (SSet.realizedVertex_eq_const
      (X := (nerve A : SSet.{max uObj vObj wHom}))
      (ComposableArrows.mk₀ c)).symm
  have hp : (Limits.prod.map (𝟙 TopCat.I.{max uObj vObj wHom})
      (SSet.toTop.map k)) p0 =
      (TopCat.prodIsoProd TopCat.I (SSet.toTop.obj (nerve A))).inv
        (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) := by
    change (Limits.prod.map (𝟙 TopCat.I.{max uObj vObj wHom})
      (SSet.toTop.map k)) ((TopCat.prodIsoProd TopCat.I P0).inv (t, default)) = _
    rw [TopCat.prodMap_prodIso_inv_apply]
    exact congrArg (fun x =>
      (TopCat.prodIsoProd TopCat.I (SSet.toTop.obj (nerve A))).inv (t, x)) hk
  have hsnd : (Limits.prod.snd : TopCat.I.{max uObj vObj wHom} ⨯ P0 ⟶ P0) p0 =
      (default : P0) :=
    ConcreteCategory.congr_hom (TopCat.prodIsoProd_inv_snd TopCat.I P0) (t, default)
  have hstat := ConcreteCategory.congr_hom
    (realizeHomotopyMap_nerveHomotopyCommonHom_stationary_vertex alpha c h halpha) p0
  change SSet.realizeHomotopyMap (nerve A) (nerve B)
      (nerveMapCommonHom.{uObj, vObj, wHom} F)
      (nerveMapCommonHom.{uObj, vObj, wHom} G) H
      ((Limits.prod.map (𝟙 TopCat.I.{max uObj vObj wHom}) (SSet.toTop.map k)) p0) =
    SSet.toTop.map (k ≫ nerveMapCommonHom.{uObj, vObj, wHom} F)
      ((Limits.prod.snd : TopCat.I.{max uObj vObj wHom} ⨯ P0 ⟶ P0) p0) at hstat
  rw [hp, hsnd] at hstat
  calc
    SSet.realizeHomotopyMap (nerve A) (nerve B)
        (nerveMapCommonHom.{uObj, vObj, wHom} F)
        (nerveMapCommonHom.{uObj, vObj, wHom} G) H
        ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj (nerve A))).inv
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c))) =
        SSet.toTop.map (k ≫ nerveMapCommonHom.{uObj, vObj, wHom} F) default := hstat
    _ = SSet.toTop.map (nerveMapCommonHom.{uObj, vObj, wHom} F)
        (SSet.toTop.map k default) :=
      ConcreteCategory.congr_hom
        (SSet.toTop.map_comp k (nerveMapCommonHom.{uObj, vObj, wHom} F)) default
    _ = SSet.toTop.map (nerveMapCommonHom.{uObj, vObj, wHom} F)
        (SSet.realizedVertex (ComposableArrows.mk₀ c)) :=
      congrArg (SSet.toTop.map (nerveMapCommonHom.{uObj, vObj, wHom} F)) hk
    _ = SSet.realizedVertex (ComposableArrows.mk₀ (F.obj c)) := by
      have hz : (nerveMapCommonHom.{uObj, vObj, wHom} F).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ c) = ComposableArrows.mk₀ (F.obj c) :=
        ComposableArrows.ext₀ rfl
      have hv := (SSet.realizedVertex_naturality
        (nerveMapCommonHom.{uObj, vObj, wHom} F) (ComposableArrows.mk₀ c)).symm
      rw [hz] at hv
      exact hv

/-- The ordinary realized native homotopy fixes the source vertex for every time. -/
theorem realizeHomotopy_nerveHomotopyCommonHom_const_vertex_apply
    (alpha : F ⟶ G) (c : A) (h : F.obj c = G.obj c)
    (halpha : alpha.app c = eqToHom h) (t : unitInterval) :
    SSet.realizeHomotopy (nerve A) (nerve B)
        (nerveMapCommonHom.{uObj, vObj, wHom} F)
        (nerveMapCommonHom.{uObj, vObj, wHom} G)
        (NatTrans.nerveHomotopyCommonHom.{uObj, vObj, wHom} alpha)
        (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      SSet.realizedVertex (ComposableArrows.mk₀ (F.obj c)) := by
  change SSet.realizeHomotopyMap (nerve A) (nerve B)
      (nerveMapCommonHom.{uObj, vObj, wHom} F)
      (nerveMapCommonHom.{uObj, vObj, wHom} G)
      (NatTrans.nerveHomotopyCommonHom.{uObj, vObj, wHom} alpha)
      ((TopCat.prodIsoProd TopCat.I (SSet.toTop.obj (nerve A))).inv
        (TopCat.I.homeomorph.symm t, SSet.realizedVertex (ComposableArrows.mk₀ c))) = _
  exact realizeHomotopyMap_nerveHomotopyCommonHom_const_vertex_apply
    alpha c h halpha (TopCat.I.homeomorph.symm t)

end SSet

end NativeStationaryVertex


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped Simplicial

universe uNerveObj vNerveHom

namespace CategoryTheory.NatTrans

public theorem nerveHomotopyMap_component_polymorphic
    {C D : Type uNerveObj} [Category.{vNerveHom} C] [Category.{vNerveHom} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C) :
    Limits.prod.lift
        (SSet.intervalConstVertex (ComposableArrows.mk₀ c))
        (𝟙 (Δ[1] : SSet.{max uNerveObj vNerveHom})) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd (nerve C)).inv.app
          (Δ[1] : SSet.{max uNerveObj vNerveHom}) ≫
        nerveHomotopyMap alpha =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (alpha.app c)) := by
  let x₀ : (nerve C) _⦋0⦌ := ComposableArrows.mk₀ c
  let e₁ : (nerve D) _⦋1⦌ := ComposableArrows.mk₁ (alpha.app c)
  change Limits.prod.lift (SSet.intervalConstVertex x₀)
      (𝟙 (Δ[1] : SSet.{max uNerveObj vNerveHom})) ≫
      (CartesianMonoidalCategory.tensorLeftIsoProd (nerve C)).inv.app
        (Δ[1] : SSet.{max uNerveObj vNerveHom}) ≫ nerveHomotopyMap alpha =
    SSet.yonedaEquiv.symm e₁
  rw [← Category.assoc, SSet.prod_lift_tensorLeftIsoProd_inv]
  apply SSet.yonedaEquiv.injective
  have hYoneda : SSet.yonedaEquiv (SSet.yonedaEquiv.symm e₁) = e₁ :=
    SSet.yonedaEquiv.apply_symm_apply e₁
  rw [hYoneda]
  change (nerveHomotopyMap alpha).app
      (op (SimplexCategory.mk 1))
      (SSet.yonedaEquiv (CartesianMonoidalCategory.lift
        (SSet.intervalConstVertex (x₀))
        (𝟙 (Δ[1] : SSet.{max uNerveObj vNerveHom})))) =
    ComposableArrows.mk₁ (alpha.app c)
  rw [SSet.yonedaEquiv_lift]
  rw [show SSet.intervalConstVertex (x₀) =
      (SSet.const (X := (Δ[1] : SSet.{max uNerveObj vNerveHom}))
        (Y := nerve C) (x₀)) by
    unfold SSet.intervalConstVertex
    rw [SSet.comp_const]]
  have hconst :
      SSet.yonedaEquiv
          (SSet.const (X := (Δ[1] : SSet.{max uNerveObj vNerveHom}))
            (Y := nerve C) (x₀)) =
        (Functor.const (Fin 2)).obj c := by
    apply Functor.hext
    · intro i
      rfl
    · intro i j f
      apply heq_of_eq
      change 𝟙 c = 𝟙 c
      rfl
  rw [hconst]
  change ((nerveCylinderFunctor alpha).mapComposableArrows 1).obj
      (((Functor.const (Fin 2)).obj c).prod'
        (SSet.stdSimplex.asOrderHom
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max uNerveObj vNerveHom})))).toFunctor) =
    ComposableArrows.mk₁ (alpha.app c)
  have hinterval :
      (SSet.stdSimplex.asOrderHom
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max uNerveObj vNerveHom})))).toFunctor =
        𝟭 (Fin 2) := by
    apply Functor.hext
    · intro i
      rfl
    · intro i j f
      apply heq_of_eq
      rfl
  rw [hinterval]
  apply Functor.hext
  · intro i
    fin_cases i <;> rfl
  · intro i j f
    fin_cases i
    · fin_cases j
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]
    · fin_cases j
      · exfalso
        have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom f
        omega
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]

end CategoryTheory.NatTrans

namespace SSet

public theorem realizeHomotopyMap_nerveHomotopy_vertex_polymorphic
    {C D : Type uNerveObj} [Category.{vNerveHom} C] [Category.{vNerveHom} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C) :
    Limits.prod.lift (𝟙 TopCat.I.{max uNerveObj vNerveHom})
        (TopCat.const
          (SSet.realizedVertex (ComposableArrows.mk₀ c))) ≫
        SSet.realizeHomotopyMap (nerve C) (nerve D)
          (nerveMap F) (nerveMap G)
          (CategoryTheory.NatTrans.nerveHomotopy alpha) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom := by
  let X : SSet.{max uNerveObj vNerveHom} := nerve C
  let x : X.obj (Opposite.op (SimplexCategory.mk 0)) :=
    ComposableArrows.mk₀ c
  let e : (nerve D) _⦋1⦌ := ComposableArrows.mk₁ (alpha.app c)
  have hEdgeHom :
      (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk (alpha.app c))).hom =
        SSet.stdSimplex.toTopObjIsoI.inv ≫
          SSet.toTop.map (SSet.yonedaEquiv.symm e) :=
    SSet.realizedEdgePath_hom (CategoryTheory.nerve.edgeMk (alpha.app c))
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{max uNerveObj vNerveHom}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{max uNerveObj vNerveHom})) :=
    SSet.isIso_prodComparison_swap _ _
  let bridge : ((Limits.prod.functor.obj X).obj
      (Δ[1] : SSet.{max uNerveObj vNerveHom})) ≅ (X ⨯ (Δ[1] : SSet.{max uNerveObj vNerveHom})) :=
    Iso.refl _
  change Limits.prod.lift (𝟙 TopCat.I.{max uNerveObj vNerveHom})
      (TopCat.const (SSet.realizedVertex (X := X) x)) ≫
      SSet.realizeHomotopyMap X (nerve D) (nerveMap F) (nerveMap G)
        (CategoryTheory.NatTrans.nerveHomotopy alpha) =
    (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk (alpha.app c))).hom
  refine Eq.trans
    (b := SSet.stdSimplex.toTopObjIsoI.inv ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm e)) ?_ hEdgeHom.symm
  change
    Limits.prod.lift (𝟙 TopCat.I.{max uNerveObj vNerveHom})
        (TopCat.const (SSet.realizedVertex x)) ≫
        (Limits.prod.braiding TopCat.I.{max uNerveObj vNerveHom}
          (SSet.toTop.obj X)).hom ≫
        Limits.prod.map (𝟙 (SSet.toTop.obj X))
          SSet.stdSimplex.toTopObjIsoI.inv ≫
        (asIso (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{max uNerveObj vNerveHom}))).inv ≫
        SSet.toTop.map bridge.inv ≫
        SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max uNerveObj vNerveHom})) ≫
        SSet.toTop.map
          (CategoryTheory.NatTrans.nerveHomotopy alpha).h =
      SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            e)
  have hInv :
      (asIso (Limits.prodComparison SSet.toTop
        X (Δ[1] : SSet.{max uNerveObj vNerveHom}))).inv =
        SSet.prodComparisonToTopInvInterval X := by
    rw [CategoryTheory.asIso_inv]
    apply (cancel_mono (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{max uNerveObj vNerveHom}))).mp
    simp [SSet.prodComparisonToTopInvInterval]
  slice_lhs 1 3 =>
    rw [SSet.interval_realizedVertex_front X x]
  rw [hInv]
  slice_lhs 2 3 =>
    rw [SSet.prod_lift_constVertex_prodComparisonToTopInvInterval X x]
  have hBridge : bridge.inv = 𝟙 _ := by
    rfl
  rw [hBridge]
  simp only [Category.comp_id, ← Functor.map_comp,
    Category.assoc]
  change
    SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map
          (Limits.prod.lift
              (SSet.intervalConstVertex x)
              (𝟙 (Δ[1] : SSet.{max uNerveObj vNerveHom})) ≫
            (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
              (Δ[1] : SSet.{max uNerveObj vNerveHom}) ≫
            CategoryTheory.NatTrans.nerveHomotopyMap alpha) =
      SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            e)
  have hComponent :
      Limits.prod.lift (SSet.intervalConstVertex x)
          (𝟙 (Δ[1] : SSet.{max uNerveObj vNerveHom})) ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max uNerveObj vNerveHom}) ≫
          CategoryTheory.NatTrans.nerveHomotopyMap alpha =
        SSet.yonedaEquiv.symm e :=
    CategoryTheory.NatTrans.nerveHomotopyMap_component_polymorphic alpha c
  exact congrArg (fun f : (Δ[1] : SSet.{max uNerveObj vNerveHom}) ⟶ nerve D =>
    SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map f) hComponent

public theorem realizeHomotopyMap_nerveHomotopy_vertex_apply_polymorphic
    {C D : Type uNerveObj} [Category.{vNerveHom} C] [Category.{vNerveHom} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C)
    (t : TopCat.I.{max uNerveObj vNerveHom}) :
    SSet.realizeHomotopyMap (nerve C) (nerve D)
        (nerveMap F) (nerveMap G)
        (CategoryTheory.NatTrans.nerveHomotopy alpha)
        ((TopCat.prodIsoProd TopCat.I.{max uNerveObj vNerveHom}
          (SSet.toTop.obj (nerve C))).inv
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c))) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom t := by
  have hPoint :
      (TopCat.prodIsoProd TopCat.I.{max uNerveObj vNerveHom}
        (SSet.toTop.obj (nerve C))).inv
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
        Limits.prod.lift (𝟙 TopCat.I.{max uNerveObj vNerveHom})
          (TopCat.const
            (SSet.realizedVertex (ComposableArrows.mk₀ c))) t := by
    apply Limits.Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · change ((TopCat.prodIsoProd TopCat.I.{max uNerveObj vNerveHom}
          (SSet.toTop.obj (nerve C))).inv ≫ Limits.prod.fst)
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
        (Limits.prod.lift (𝟙 TopCat.I.{max uNerveObj vNerveHom})
          (TopCat.const
            (SSet.realizedVertex (ComposableArrows.mk₀ c)) :
              TopCat.I.{max uNerveObj vNerveHom} ⟶ SSet.toTop.obj (nerve C)) ≫
            Limits.prod.fst) t
      rw [TopCat.prodIsoProd_inv_fst, Limits.prod.lift_fst]
      rfl
    · change ((TopCat.prodIsoProd TopCat.I.{max uNerveObj vNerveHom}
          (SSet.toTop.obj (nerve C))).inv ≫ Limits.prod.snd)
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
        (Limits.prod.lift (𝟙 TopCat.I.{max uNerveObj vNerveHom})
          (TopCat.const
            (SSet.realizedVertex (ComposableArrows.mk₀ c)) :
              TopCat.I.{max uNerveObj vNerveHom} ⟶ SSet.toTop.obj (nerve C)) ≫
            Limits.prod.snd) t
      rw [TopCat.prodIsoProd_inv_snd, Limits.prod.lift_snd]
      rfl
  rw [hPoint]
  exact ConcreteCategory.congr_hom
    (SSet.realizeHomotopyMap_nerveHomotopy_vertex_polymorphic alpha c) t

public theorem nerveMap_realizedVertex_polymorphic
    {C D : Type uNerveObj} [Category.{vNerveHom} C] [Category.{vNerveHom} D]
    (F : C ⥤ D) (c : C) :
    SSet.toTop.map (nerveMap F)
        (SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      SSet.realizedVertex (ComposableArrows.mk₀ (F.obj c)) := by
  simpa only [CategoryTheory.nerveMap_app_mk₀] using
    (SSet.realizedVertex_naturality
      (CategoryTheory.nerveMap F) (ComposableArrows.mk₀ c)).symm

public theorem realizeHomotopy_nerveHomotopy_evalAt_polymorphic
    {C D : Type uNerveObj} [Category.{vNerveHom} C] [Category.{vNerveHom} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C) :
    (SSet.realizeHomotopy (nerve C) (nerve D)
        (nerveMap F) (nerveMap G)
        (CategoryTheory.NatTrans.nerveHomotopy alpha)).evalAt
          (SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      (TopCat.pathEquiv
        (SSet.realizedEdgePath
          (CategoryTheory.nerve.edgeMk (alpha.app c)))).cast
        (SSet.nerveMap_realizedVertex_polymorphic F c)
        (SSet.nerveMap_realizedVertex_polymorphic G c) := by
  apply _root_.Path.ext
  funext t
  change
    SSet.realizeHomotopyMap (nerve C) (nerve D)
        (nerveMap F) (nerveMap G)
        (CategoryTheory.NatTrans.nerveHomotopy alpha)
        ((TopCat.prodIsoProd TopCat.I.{max uNerveObj vNerveHom}
          (SSet.toTop.obj (nerve C))).inv
          (TopCat.I.homeomorph.symm t,
            SSet.realizedVertex (ComposableArrows.mk₀ c))) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom
          (TopCat.I.homeomorph.symm t)
  exact SSet.realizeHomotopyMap_nerveHomotopy_vertex_apply_polymorphic
    alpha c (TopCat.I.homeomorph.symm t)

end SSet

end


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial

universe u

namespace SSet

private theorem originalRealizedIntervalCylinderComputed
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (q : (Δ[1] : SSet.{u}) ⟶ Y)
    (h : H.h = CartesianMonoidalCategory.snd X (Δ[1] : SSet.{u}) ≫ q) :
    realizeHomotopyMap X Y f g H =
      (prod.fst : TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ TopCat.I.{u}) ≫
        SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map q := by
  let U : SSet.{u} := Δ[1]
  let c := prodComparison SSet.toTop X U
  let front := (prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
    prod.map (𝟙 (SSet.toTop.obj X)) SSet.stdSimplex.toTopObjIsoI.inv
  let tc := (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app U
  let _ : IsIso (prodComparison SSet.toTop U X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let _ : IsIso c := SSet.isIso_prodComparison_swap U X
  have hTensor : SSet.toTop.map tc ≫
      SSet.toTop.map (CartesianMonoidalCategory.snd X U) = SSet.toTop.map (prod.snd : X ⨯ U ⟶ U) :=
    (SSet.toTop.map_comp tc (CartesianMonoidalCategory.snd X U)).symm.trans
      (congrArg SSet.toTop.map (tensorLeftIsoProd_inv_snd X U))
  have hComparison : (asIso c).inv ≫ SSet.toTop.map (prod.snd : X ⨯ U ⟶ U) =
      (prod.snd : SSet.toTop.obj X ⨯ SSet.toTop.obj U ⟶ SSet.toTop.obj U) := by
    apply (cancel_epi c).mp
    exact ((asIso c).hom_inv_id_assoc (SSet.toTop.map (prod.snd : X ⨯ U ⟶ U))).trans
      (prodComparison_snd SSet.toTop X U).symm
  have hFront : front ≫ prod.snd =
      (prod.fst : TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ TopCat.I.{u}) ≫ SSet.stdSimplex.toTopObjIsoI.inv := by
    dsimp only [front]
    rw [Category.assoc, prod.map_snd, ← Category.assoc, prod.braiding_hom, prod.lift_snd]
  have hMap : SSet.toTop.map H.h =
      SSet.toTop.map (CartesianMonoidalCategory.snd X U) ≫ SSet.toTop.map q :=
    (congrArg SSet.toTop.map h).trans
      (SSet.toTop.map_comp (CartesianMonoidalCategory.snd X U) q)
  have hFormula : realizeHomotopyMap X Y f g H =
      front ≫ (asIso c).inv ≫ SSet.toTop.map tc ≫ SSet.toTop.map H.h := by
    have hIdentity : SSet.toTop.map (𝟙 (X ⨯ U)) =
        𝟙 (SSet.toTop.obj (X ⨯ U)) := SSet.toTop.map_id (X ⨯ U)
    have hIdentityComp : SSet.toTop.map (𝟙 (X ⨯ U)) ≫
        SSet.toTop.map tc ≫ SSet.toTop.map H.h =
          SSet.toTop.map tc ≫ SSet.toTop.map H.h :=
      (congrArg (fun m => m ≫ SSet.toTop.map tc ≫ SSet.toTop.map H.h) hIdentity).trans
        (Category.id_comp (SSet.toTop.map tc ≫ SSet.toTop.map H.h))
    dsimp only [realizeHomotopyMap]
    change front ≫ (asIso c).inv ≫ SSet.toTop.map (𝟙 (X ⨯ U)) ≫
        SSet.toTop.map tc ≫ SSet.toTop.map H.h =
      front ≫ (asIso c).inv ≫ SSet.toTop.map tc ≫ SSet.toTop.map H.h
    exact congrArg (fun m => front ≫ (asIso c).inv ≫ m) hIdentityComp
  calc
    realizeHomotopyMap X Y f g H =
        front ≫ (asIso c).inv ≫ SSet.toTop.map tc ≫ SSet.toTop.map H.h := hFormula
    _ = front ≫ (asIso c).inv ≫ SSet.toTop.map tc ≫
        (SSet.toTop.map (CartesianMonoidalCategory.snd X U) ≫ SSet.toTop.map q) :=
      congrArg (fun m => front ≫ (asIso c).inv ≫ SSet.toTop.map tc ≫ m) hMap
    _ = front ≫ ((asIso c).inv ≫
        (SSet.toTop.map tc ≫ SSet.toTop.map (CartesianMonoidalCategory.snd X U))) ≫
          SSet.toTop.map q := by simp only [Category.assoc]
    _ = front ≫ ((asIso c).inv ≫ SSet.toTop.map (prod.snd : X ⨯ U ⟶ U)) ≫ SSet.toTop.map q :=
      congrArg (fun m => front ≫ ((asIso c).inv ≫ m) ≫ SSet.toTop.map q) hTensor
    _ = front ≫ prod.snd ≫ SSet.toTop.map q :=
      congrArg (fun m => front ≫ m ≫ SSet.toTop.map q) hComparison
    _ = (prod.fst : TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ TopCat.I.{u}) ≫
        SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map q :=
      (congrArg (fun m => m ≫ SSet.toTop.map q) hFront).trans
        (Category.assoc _ _ _)

/-- A whole interval-factor cylinder realizes to the same interval path uniformly over its source. -/
public theorem realizeHomotopyMap_interval_factor
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (q : (Δ[1] : SSet.{u}) ⟶ Y)
    (h : H.h = CartesianMonoidalCategory.snd X (Δ[1] : SSet.{u}) ≫ q) :
    realizeHomotopyMap X Y f g H =
      (prod.fst : TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ TopCat.I.{u}) ≫
        SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map q :=
  originalRealizedIntervalCylinderComputed H q h

end SSet

end


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial Topology
open scoped Simplicial ContinuousMap CategoryTheory.Prod CategoryTheory.MonoidalCategory

universe uUpObj vUpObj wUpHom

namespace CategoryTheory.NatTrans

/-- The original upward cylinder on a constant original vertex is the
original component edge, on the whole interval simplex. -/
public theorem nerveHomotopyMapCommonHomUp_component
    {C : Type uUpObj} [Category.{max vUpObj wUpHom} C]
    {D : Type (max uUpObj vUpObj)} [Category.{max vUpObj wUpHom} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C) :
    Limits.prod.lift
        (SSet.intervalConstVertex (ComposableArrows.mk₀ c))
        (𝟙 (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd (nerve C)).inv.app
          (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}) ≫
        nerveHomotopyMapCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (alpha.app c)) := by
  let x₀ : (nerve C) _⦋0⦌ := ComposableArrows.mk₀ c
  let e₁ : (nerve D) _⦋1⦌ := ComposableArrows.mk₁ (alpha.app c)
  change Limits.prod.lift (SSet.intervalConstVertex x₀)
      (𝟙 (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})) ≫
      (CartesianMonoidalCategory.tensorLeftIsoProd (nerve C)).inv.app
        (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}) ≫ nerveHomotopyMapCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha =
    SSet.yonedaEquiv.symm e₁
  rw [← Category.assoc, SSet.prod_lift_tensorLeftIsoProd_inv]
  apply SSet.yonedaEquiv.injective
  have hYoneda : SSet.yonedaEquiv (SSet.yonedaEquiv.symm e₁) = e₁ :=
    SSet.yonedaEquiv.apply_symm_apply e₁
  rw [hYoneda]
  change (nerveHomotopyMapCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha).app
      (op (SimplexCategory.mk 1))
      (SSet.yonedaEquiv (CartesianMonoidalCategory.lift
        (SSet.intervalConstVertex (x₀))
        (𝟙 (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})))) =
    ComposableArrows.mk₁ (alpha.app c)
  rw [SSet.yonedaEquiv_lift]
  rw [show SSet.intervalConstVertex (x₀) =
      (SSet.const (X := (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}))
        (Y := nerve C) (x₀)) by
    unfold SSet.intervalConstVertex
    rw [SSet.comp_const]]
  have hconst :
      SSet.yonedaEquiv
          (SSet.const (X := (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}))
            (Y := nerve C) (x₀)) =
        (Functor.const (Fin 2)).obj c := by
    apply Functor.hext
    · intro i
      rfl
    · intro i j f
      apply heq_of_eq
      change 𝟙 c = 𝟙 c
      rfl
  rw [hconst]
  change ((nerveCylinderFunctor alpha).mapComposableArrows 1).obj
      (((Functor.const (Fin 2)).obj c).prod'
        (SSet.stdSimplex.asOrderHom
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})))).toFunctor) =
    ComposableArrows.mk₁ (alpha.app c)
  have hinterval :
      (SSet.stdSimplex.asOrderHom
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})))).toFunctor =
        𝟭 (Fin 2) := by
    apply Functor.hext
    · intro i
      rfl
    · intro i j f
      apply heq_of_eq
      rfl
  rw [hinterval]
  apply Functor.hext
  · intro i
    fin_cases i <;> rfl
  · intro i j f
    fin_cases i
    · fin_cases j
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]
    · fin_cases j
      · exfalso
        have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom f
        omega
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]


end CategoryTheory.NatTrans

namespace SSet

/-- The whole realized upward cylinder at an original vertex is its
original component-edge map, with the actual interval carrier. -/
public theorem realizeHomotopyMap_nerveHomotopyCommonHomUp_vertex
    {C : Type uUpObj} [Category.{max vUpObj wUpHom} C]
    {D : Type (max uUpObj vUpObj)} [Category.{max vUpObj wUpHom} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C) :
    Limits.prod.lift (𝟙 TopCat.I.{max uUpObj vUpObj wUpHom})
        (TopCat.const
          (SSet.realizedVertex (ComposableArrows.mk₀ c))) ≫
        SSet.realizeHomotopyMap (nerve C) (nerve D)
          (nerveMapCommonHomUp.{uUpObj, vUpObj, wUpHom} F) (nerveMapCommonHomUp.{uUpObj, vUpObj, wUpHom} G)
          (CategoryTheory.NatTrans.nerveHomotopyCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom := by
  let X : SSet.{max uUpObj vUpObj wUpHom} := nerve C
  let x : X.obj (Opposite.op (SimplexCategory.mk 0)) :=
    ComposableArrows.mk₀ c
  let e : (nerve D) _⦋1⦌ := ComposableArrows.mk₁ (alpha.app c)
  have hEdgeHom :
      (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk (alpha.app c))).hom =
        SSet.stdSimplex.toTopObjIsoI.inv ≫
          SSet.toTop.map (SSet.yonedaEquiv.symm e) :=
    SSet.realizedEdgePath_hom (CategoryTheory.nerve.edgeMk (alpha.app c))
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})) :=
    SSet.isIso_prodComparison_swap _ _
  let bridge : ((Limits.prod.functor.obj X).obj
      (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})) ≅ (X ⨯ (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})) :=
    Iso.refl _
  change Limits.prod.lift (𝟙 TopCat.I.{max uUpObj vUpObj wUpHom})
      (TopCat.const (SSet.realizedVertex (X := X) x)) ≫
      SSet.realizeHomotopyMap X (nerve D) (nerveMapCommonHomUp.{uUpObj, vUpObj, wUpHom} F)
          (nerveMapCommonHomUp.{uUpObj, vUpObj, wUpHom} G)
        (CategoryTheory.NatTrans.nerveHomotopyCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha) =
    (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk (alpha.app c))).hom
  refine Eq.trans
    (b := SSet.stdSimplex.toTopObjIsoI.inv ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm e)) ?_ hEdgeHom.symm
  change
    Limits.prod.lift (𝟙 TopCat.I.{max uUpObj vUpObj wUpHom})
        (TopCat.const (SSet.realizedVertex x)) ≫
        (Limits.prod.braiding TopCat.I.{max uUpObj vUpObj wUpHom}
          (SSet.toTop.obj X)).hom ≫
        Limits.prod.map (𝟙 (SSet.toTop.obj X))
          SSet.stdSimplex.toTopObjIsoI.inv ≫
        (asIso (Limits.prodComparison SSet.toTop
          X (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}))).inv ≫
        SSet.toTop.map bridge.inv ≫
        SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})) ≫
        SSet.toTop.map
          (CategoryTheory.NatTrans.nerveHomotopyCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha).h =
      SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            e)
  have hInv :
      (asIso (Limits.prodComparison SSet.toTop
        X (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}))).inv =
        SSet.prodComparisonToTopInvInterval X := by
    rw [CategoryTheory.asIso_inv]
    apply (cancel_mono (Limits.prodComparison SSet.toTop
      X (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}))).mp
    simp [SSet.prodComparisonToTopInvInterval]
  slice_lhs 1 3 =>
    rw [SSet.interval_realizedVertex_front X x]
  rw [hInv]
  slice_lhs 2 3 =>
    rw [SSet.prod_lift_constVertex_prodComparisonToTopInvInterval X x]
  have hBridge : bridge.inv = 𝟙 _ := by
    rfl
  rw [hBridge]
  simp only [Category.comp_id, ← Functor.map_comp,
    Category.assoc]
  change
    SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map
          (Limits.prod.lift
              (SSet.intervalConstVertex x)
              (𝟙 (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})) ≫
            (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
              (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}) ≫
            CategoryTheory.NatTrans.nerveHomotopyMapCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha) =
      SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            e)
  have hComponent :
      Limits.prod.lift (SSet.intervalConstVertex x)
          (𝟙 (Δ[1] : SSet.{max uUpObj vUpObj wUpHom})) ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}) ≫
          CategoryTheory.NatTrans.nerveHomotopyMapCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha =
        SSet.yonedaEquiv.symm e :=
    CategoryTheory.NatTrans.nerveHomotopyMapCommonHomUp_component alpha c
  exact congrArg (fun f : (Δ[1] : SSet.{max uUpObj vUpObj wUpHom}) ⟶ nerve D =>
    SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map f) hComponent

/-- The original product-carrier coordinates retain every point of the
whole upward component-edge map. -/
public theorem realizeHomotopyMap_nerveHomotopyCommonHomUp_vertex_apply
    {C : Type uUpObj} [Category.{max vUpObj wUpHom} C]
    {D : Type (max uUpObj vUpObj)} [Category.{max vUpObj wUpHom} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C)
    (t : TopCat.I.{max uUpObj vUpObj wUpHom}) :
    SSet.realizeHomotopyMap (nerve C) (nerve D)
        (nerveMapCommonHomUp.{uUpObj, vUpObj, wUpHom} F) (nerveMapCommonHomUp.{uUpObj, vUpObj, wUpHom} G)
        (CategoryTheory.NatTrans.nerveHomotopyCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha)
        ((TopCat.prodIsoProd TopCat.I.{max uUpObj vUpObj wUpHom}
          (SSet.toTop.obj (nerve C))).inv
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c))) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom t := by
  have hPoint :
      (TopCat.prodIsoProd TopCat.I.{max uUpObj vUpObj wUpHom}
        (SSet.toTop.obj (nerve C))).inv
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
        Limits.prod.lift (𝟙 TopCat.I.{max uUpObj vUpObj wUpHom})
          (TopCat.const
            (SSet.realizedVertex (ComposableArrows.mk₀ c))) t := by
    apply Limits.Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · change ((TopCat.prodIsoProd TopCat.I.{max uUpObj vUpObj wUpHom}
          (SSet.toTop.obj (nerve C))).inv ≫ Limits.prod.fst)
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
        (Limits.prod.lift (𝟙 TopCat.I.{max uUpObj vUpObj wUpHom})
          (TopCat.const
            (SSet.realizedVertex (ComposableArrows.mk₀ c)) :
              TopCat.I.{max uUpObj vUpObj wUpHom} ⟶ SSet.toTop.obj (nerve C)) ≫
            Limits.prod.fst) t
      rw [TopCat.prodIsoProd_inv_fst, Limits.prod.lift_fst]
      rfl
    · change ((TopCat.prodIsoProd TopCat.I.{max uUpObj vUpObj wUpHom}
          (SSet.toTop.obj (nerve C))).inv ≫ Limits.prod.snd)
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
        (Limits.prod.lift (𝟙 TopCat.I.{max uUpObj vUpObj wUpHom})
          (TopCat.const
            (SSet.realizedVertex (ComposableArrows.mk₀ c)) :
              TopCat.I.{max uUpObj vUpObj wUpHom} ⟶ SSet.toTop.obj (nerve C)) ≫
            Limits.prod.snd) t
      rw [TopCat.prodIsoProd_inv_snd, Limits.prod.lift_snd]
      rfl
  rw [hPoint]
  exact ConcreteCategory.congr_hom
    (SSet.realizeHomotopyMap_nerveHomotopyCommonHomUp_vertex alpha c) t


/-- At every ordinary interval time, the original upward realization
family at the original vertex is the same original component edge. -/
public theorem realizeHomotopy_nerveHomotopyCommonHomUp_vertex_apply
    {C : Type uUpObj} [Category.{max vUpObj wUpHom} C]
    {D : Type (max uUpObj vUpObj)} [Category.{max vUpObj wUpHom} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C) (t : unitInterval) :
    (SSet.realizeHomotopy (nerve C) (nerve D)
      (nerveMapCommonHomUp.{uUpObj, vUpObj, wUpHom} F)
      (nerveMapCommonHomUp.{uUpObj, vUpObj, wUpHom} G)
      (CategoryTheory.NatTrans.nerveHomotopyCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha)).toContinuousMap
        (t, SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      TopCat.pathEquiv (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))) t := by
  change
    SSet.realizeHomotopyMap (nerve C) (nerve D)
      (nerveMapCommonHomUp.{uUpObj, vUpObj, wUpHom} F)
      (nerveMapCommonHomUp.{uUpObj, vUpObj, wUpHom} G)
      (CategoryTheory.NatTrans.nerveHomotopyCommonHomUp.{uUpObj, vUpObj, wUpHom} alpha)
      ((TopCat.prodIsoProd TopCat.I.{max uUpObj vUpObj wUpHom}
        (SSet.toTop.obj (nerve C))).inv
          (TopCat.I.homeomorph.{max uUpObj vUpObj wUpHom}.symm t,
            SSet.realizedVertex (ComposableArrows.mk₀ c))) =
      (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk (alpha.app c))).hom
        (TopCat.I.homeomorph.{max uUpObj vUpObj wUpHom}.symm t)
  exact SSet.realizeHomotopyMap_nerveHomotopyCommonHomUp_vertex_apply
    alpha c (TopCat.I.homeomorph.{max uUpObj vUpObj wUpHom}.symm t)

end SSet

end
