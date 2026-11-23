/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanTerminalWeightRows
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import MathlibExt.CategoryTheory.CategoryBar.NerveNaturality
public import MathlibExt.CategoryTheory.CategoryBar.RightUnitBridge
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Fixed rows of the Bousfield--Kan bar of the point diagram

For a small category `D`, this file compares each fixed inner row of the
Bousfield--Kan bar of the constant point-valued diagram with `nerve D`,
assembles those rows into a curried natural isomorphism and its diagonal
comparison, and proves indexing-functor naturality.  It stops before any
realization, weak-equivalence, or Quillen-Theorem-A claim.

The indexing category has object universe `u` and morphism universe `v`.
Point coefficients, weighted rows, and nerves have their native value universe
`max u v`. Indexing-functor naturality uses a common object universe and a
common morphism universe for the source and target categories.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

open scoped Simplicial

namespace SSet

universe u v w

/-- The constant point-valued simplicial-set diagram. -/
def bkPointDiagram (D : Type u) [Category.{v} D] : D ⥤ SSet.{max u v} :=
  (Functor.const D).obj (Δ[0] : SSet.{max u v})

/-- The unique simplex of `Δ[0]` in an arbitrary degree. -/
def deltaZeroSimplex (a : SimplexCategoryᵒᵖ) :
    (Δ[0] : SSet.{w}).obj a :=
  SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.const a.unop (SimplexCategory.mk 0) 0)

/-- Constant point coefficient in the native value universe of the diagram. -/
def bkPointUnitCoeff (D : Type u) [Category.{v} D] : D ⥤ Type (max u v) :=
  (Functor.const D).obj (ULift.{max u v} PUnit)

/-- In a fixed inner degree, the coefficient of the point diagram is
canonically the unit coefficient of simplicial replacement. -/
noncomputable def pointDegreeCoefficientIso
    (D : Type u) [Category.{v} D] (a : SimplexCategoryᵒᵖ) :
    wbarDegreeCoefficient (bkPointDiagram D) a ≅
      bkPointUnitCoeff D :=
  NatIso.ofComponents
    (fun _ => by
      change (Δ[0] : SSet.{max u v}).obj a ≅ ULift.{max u v} PUnit
      exact Equiv.toIso
        { toFun := fun _ => ULift.up PUnit.unit
          invFun := fun _ => deltaZeroSimplex a
          left_inv := fun x => by
            apply SSet.stdSimplex.objEquiv.injective
            exact Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _ })
    (by
      intro _d _d' _f
      ext x
      change (_ : ULift.{max u v} PUnit) = _
      exact Subsingleton.elim _ _)

/-- Change of inner degree on an evaluated coefficient diagram. -/
def wbarDegreeCoefficientMap
    {J : Type u} [Category.{v} J] (E : J ⥤ SSet.{max u v})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    wbarDegreeCoefficient E a ⟶ wbarDegreeCoefficient E b where
  app j := (E.obj j).map f
  naturality _j _k g := ((E.map g).naturality f).symm

/-- The point-coefficient comparison is natural in the inner degree. -/
theorem pointDegreeCoefficientIso_naturality
    (D : Type u) [Category.{v} D]
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    wbarDegreeCoefficientMap (bkPointDiagram D) f ≫
        (pointDegreeCoefficientIso D b).hom =
      (pointDegreeCoefficientIso D a).hom := by
  apply NatTrans.ext
  funext d
  ext x
  change (_ : ULift.{max u v} PUnit) = _
  exact Subsingleton.elim _ _

/-- Simplicial replacement respects the point-coefficient isomorphism. -/
noncomputable def pointReplacementIso
    (D : Type u) [Category.{v} D] (a : SimplexCategoryᵒᵖ) :
    CategoryBar.simplicialReplacement
        (wbarDegreeCoefficient (bkPointDiagram D) a) ≅
      CategoryBar.simplicialReplacement (bkPointUnitCoeff D) where
  hom := CategoryBar.replMap (pointDegreeCoefficientIso D a).hom
  inv := CategoryBar.replMap (pointDegreeCoefficientIso D a).inv
  hom_inv_id := by
    rw [CategoryBar.replMap_comp, Iso.hom_inv_id,
      CategoryBar.replMap_id]
  inv_hom_id := by
    rw [CategoryBar.replMap_comp, Iso.inv_hom_id,
      CategoryBar.replMap_id]

/-- Section of the elements projection for the native point coefficient. -/
noncomputable def bkPointUnitElementsSection
    (D : Type u) [Category.{v} D] :
    D ⥤ (bkPointUnitCoeff D).Elements where
  obj X := (bkPointUnitCoeff D).elementsMk X (ULift.up PUnit.unit)
  map {X Y} f := Functor.Elements.homMk f (by
    have hSub : Subsingleton ((bkPointUnitCoeff D).obj Y) := by
      change Subsingleton (ULift.{max u v} PUnit)
      infer_instance
    exact @Subsingleton.elim _ hSub _ _)
  map_id X := by
    apply Functor.Elements.hom_ext
    rfl
  map_comp f g := by
    apply Functor.Elements.hom_ext
    rfl

/-- Degreewise equivalence from composable arrows in the elements category
of the native point coefficient to composable arrows in the base category. -/
noncomputable def bkPointUnitElementsNerveEquiv
    (D : Type u) [Category.{v} D] (n : ℕ) :
    ComposableArrows (bkPointUnitCoeff D).Elements n ≃
      ComposableArrows D n where
  toFun G := ((Functor.Elements.π (bkPointUnitCoeff D)).mapComposableArrows n).obj G
  invFun F := ((bkPointUnitElementsSection D).mapComposableArrows n).obj F
  left_inv G := by
    have h_obj : ∀ i : Fin (n + 1),
        ((((Functor.Elements.π (bkPointUnitCoeff D)).mapComposableArrows n).obj G ⋙
          bkPointUnitElementsSection D).obj i) = G.obj i := fun i => by
      exact Functor.Elements.ext _ _ rfl (by
        have hSub : Subsingleton
            ((bkPointUnitCoeff D).obj (G.obj i).obj) := by
          change Subsingleton (ULift.{max u v} PUnit)
          infer_instance
        exact @Subsingleton.elim _ hSub _ _)
    refine ComposableArrows.ext h_obj (fun i hi => ?_)
    apply Functor.Elements.hom_ext
    have hEq : ∀ {x y : (bkPointUnitCoeff D).Elements} (h : x = y),
        (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
      intro x y h
      cases h
      rfl
    rw [Functor.Elements.comp_hom, Functor.Elements.comp_hom, hEq, hEq]
    change (G.map _).hom = 𝟙 _ ≫ (G.map _).hom ≫ 𝟙 _
    simp
  right_inv F := by
    have h_obj : ∀ i : Fin (n + 1),
        (((bkPointUnitElementsSection D).mapComposableArrows n).obj F ⋙
          Functor.Elements.π (bkPointUnitCoeff D)).obj i = F.obj i := fun _ => rfl
    refine ComposableArrows.ext h_obj (fun i hi => ?_)
    change F.map _ = 𝟙 _ ≫ F.map _ ≫ 𝟙 _
    simp

/-- Nerve-level comparison from the native point coefficient's elements
category to the indexing category. -/
noncomputable def bkPointUnitElementsNerveIso
    (D : Type u) [Category.{v} D] :
    nerve (bkPointUnitCoeff D).Elements ≅ nerve D :=
  NatIso.ofComponents
    (fun Δ => (bkPointUnitElementsNerveEquiv D Δ.unop.len).toIso) (by
      intro Δ₁ Δ₂ f
      ext X
      rfl)

/-- Simplicial replacement of the native point coefficient is the nerve of
the indexing category. -/
noncomputable def bkPointReplacementNerveIso
    (D : Type u) [Category.{v} D] :
    CategoryBar.simplicialReplacement (bkPointUnitCoeff D) ≅ nerve D :=
  (CategoryBar.replNerveSimplicialIso (bkPointUnitCoeff D)).trans
    (bkPointUnitElementsNerveIso D)

/-- The replacement comparison is natural in the inner degree. -/
theorem pointReplacementIso_naturality
    (D : Type u) [Category.{v} D]
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    CategoryBar.replMap
        (wbarDegreeCoefficientMap (bkPointDiagram D) f) ≫
        (pointReplacementIso D b).hom =
      (pointReplacementIso D a).hom := by
  unfold pointReplacementIso
  rw [CategoryBar.replMap_comp, pointDegreeCoefficientIso_naturality]

/-- Every fixed inner row of the constant-point weighted bar is canonically
the nerve of the indexing category. -/
noncomputable def pointRowIso
    (D : Type u) [Category.{v} D] (a : SimplexCategoryᵒᵖ) :
    wbarRow (bkPointDiagram D) a ≅ nerve D :=
  (terminalWeightRowIso (bkPointDiagram D) a).trans
    ((pointReplacementIso D a).trans (bkPointReplacementNerveIso D))

/-- Change of fixed inner degree in a weighted-bar row. -/
noncomputable def wbarInnerMap
    {J : Type u} [Category.{v} J] (E : J ⥤ SSet.{max u v})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    wbarRow E a ⟶ wbarRow E b :=
  SimplicialObject.Data.toSimplicialNatTrans
    (SimplicialObject.Data.evalObjMap
      (StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) E) f)

@[simp]
theorem wbarInnerMap_app_mk
    {J : Type u} [Category.{v} J] (E : J ⥤ SSet.{max u v})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) (n : ℕ) :
    (wbarInnerMap E f).app (Opposite.op (SimplexCategory.mk n)) =
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit J) E n).map f :=
  rfl

/-- The inner-degree map is natural on every explicit weighted-row
inclusion. -/
theorem wbarRowIncl_inner_naturality
    {J : Type u} [Category.{v} J] (E : J ⥤ SSet.{max u v})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    wbarRowIncl E a n p ≫
        (wbarInnerMap E f).app (Opposite.op (SimplexCategory.mk n)) =
      (E.obj p.1.left).map f ≫ wbarRowIncl E b n p := by
  rw [wbarRowIncl_eq_wbarIncl_app, wbarRowIncl_eq_wbarIncl_app,
    wbarInnerMap_app_mk]
  exact ((StrictOrdinaryWeightedBar.wbarIncl
    (CategoryBar.replUnit J) E n p).naturality f).symm

/-- The replacement inclusion is natural in the inner degree. -/
theorem terminalWeightReplIncl_inner_naturality
    {J : Type u} [Category.{v} J] (E : J ⥤ SSet.{max u v})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    terminalWeightReplIncl E a n p ≫
        (CategoryBar.replMap (wbarDegreeCoefficientMap E f)).app
          (Opposite.op (SimplexCategory.mk n)) =
      (E.obj p.1.left).map f ≫ terminalWeightReplIncl E b n p := by
  rw [CategoryBar.replMap_app_mk]
  ext x
  rfl

private theorem wbarRow_hom_ext_inner
    {J : Type u} [Category.{v} J] (E : J ⥤ SSet.{max u v})
    (a : SimplexCategoryᵒᵖ) (n : ℕ) {P : Type (max u v)}
    {f g : (wbarRowData E a).obj n ⟶ P}
    (h : ∀ p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n,
      wbarRowIncl E a n p ≫ f = wbarRowIncl E a n p ≫ g) :
    f = g := by
  let e := Limits.sigmaObjIso
    (fun p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n => E.obj p.1.left) a
  have hfg : e.inv ≫ f = e.inv ≫ g := by
    apply Limits.Sigma.hom_ext
    intro p
    have hι : Limits.Sigma.ι
          (fun p : StrictOrdinaryWeightedBar.WIdx J
            (CategoryBar.replUnit J) n => (E.obj p.1.left).obj a) p ≫
        e.inv = wbarRowIncl E a n p := by
      dsimp only [e]
      exact (Limits.ι_comp_sigmaObjIso_inv _ _ p).trans
        (wbarRowIncl_eq_wbarIncl_app E a n p).symm
    calc
      Limits.Sigma.ι
            (fun p : StrictOrdinaryWeightedBar.WIdx J
              (CategoryBar.replUnit J) n => (E.obj p.1.left).obj a) p ≫
          (e.inv ≫ f) =
        (Limits.Sigma.ι
            (fun p : StrictOrdinaryWeightedBar.WIdx J
              (CategoryBar.replUnit J) n => (E.obj p.1.left).obj a) p ≫
          e.inv) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = wbarRowIncl E a n p ≫ f := congrArg (· ≫ f) hι
      _ = wbarRowIncl E a n p ≫ g := h p
      _ = (Limits.Sigma.ι
            (fun p : StrictOrdinaryWeightedBar.WIdx J
              (CategoryBar.replUnit J) n => (E.obj p.1.left).obj a) p ≫
          e.inv) ≫ g := congrArg (· ≫ g) hι.symm
      _ = Limits.Sigma.ι
            (fun p : StrictOrdinaryWeightedBar.WIdx J
              (CategoryBar.replUnit J) n => (E.obj p.1.left).obj a) p ≫
          (e.inv ≫ g) :=
        Category.assoc _ _ _
  exact (cancel_epi e.inv).mp hfg

/-- The terminal-weight row comparison is natural in the fixed inner
degree. -/
theorem terminalWeightRowIso_inner_naturality
    {J : Type u} [Category.{v} J] (E : J ⥤ SSet.{max u v})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    wbarInnerMap E f ≫ (terminalWeightRowIso E b).hom =
      (terminalWeightRowIso E a).hom ≫
        CategoryBar.replMap (wbarDegreeCoefficientMap E f) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  simp only [NatTrans.comp_app, terminalWeightRowIso_hom_app_mk]
  apply wbarRow_hom_ext_inner E a n
  intro p
  have hLeft :
      wbarRowIncl E a n p ≫
          ((wbarInnerMap E f).app (Opposite.op (SimplexCategory.mk n)) ≫
            (terminalWeightRowDegreeIso E b n).hom) =
        (E.obj p.1.left).map f ≫ terminalWeightReplIncl E b n p := by
    calc
      _ = (wbarRowIncl E a n p ≫
            (wbarInnerMap E f).app (Opposite.op (SimplexCategory.mk n))) ≫
          (terminalWeightRowDegreeIso E b n).hom :=
        (Category.assoc _ _ _).symm
      _ = ((E.obj p.1.left).map f ≫ wbarRowIncl E b n p) ≫
          (terminalWeightRowDegreeIso E b n).hom :=
        congrArg (· ≫ (terminalWeightRowDegreeIso E b n).hom)
          (wbarRowIncl_inner_naturality E f n p)
      _ = (E.obj p.1.left).map f ≫ terminalWeightReplIncl E b n p := by
        rw [Category.assoc, terminalWeightRowDegreeIso_hom_rowIncl]
  have hRight :
      wbarRowIncl E a n p ≫
          ((terminalWeightRowDegreeIso E a n).hom ≫
            (CategoryBar.replMap (wbarDegreeCoefficientMap E f)).app
              (Opposite.op (SimplexCategory.mk n))) =
        terminalWeightReplIncl E a n p ≫
          (CategoryBar.replMap (wbarDegreeCoefficientMap E f)).app
            (Opposite.op (SimplexCategory.mk n)) := by
    calc
      _ = (wbarRowIncl E a n p ≫
            (terminalWeightRowDegreeIso E a n).hom) ≫
          (CategoryBar.replMap (wbarDegreeCoefficientMap E f)).app
            (Opposite.op (SimplexCategory.mk n)) :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ (CategoryBar.replMap
        (wbarDegreeCoefficientMap E f)).app
          (Opposite.op (SimplexCategory.mk n)))
        (terminalWeightRowDegreeIso_hom_rowIncl E a n p)
  exact hLeft.trans
    ((terminalWeightReplIncl_inner_naturality E f n p).symm.trans hRight.symm)

/-- The fixed-inner point-row identification is natural in the inner
degree. -/
theorem pointRowIso_inner_naturality
    (D : Type u) [Category.{v} D]
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    wbarInnerMap (bkPointDiagram D) f ≫ (pointRowIso D b).hom =
      (pointRowIso D a).hom := by
  change wbarInnerMap (bkPointDiagram D) f ≫
      ((terminalWeightRowIso (bkPointDiagram D) b).hom ≫
        ((pointReplacementIso D b).hom ≫
          (bkPointReplacementNerveIso D).hom)) =
    (terminalWeightRowIso (bkPointDiagram D) a).hom ≫
      ((pointReplacementIso D a).hom ≫
        (bkPointReplacementNerveIso D).hom)
  calc
    _ = (wbarInnerMap (bkPointDiagram D) f ≫
          (terminalWeightRowIso (bkPointDiagram D) b).hom) ≫
        ((pointReplacementIso D b).hom ≫
          (bkPointReplacementNerveIso D).hom) :=
      (Category.assoc _ _ _).symm
    _ = ((terminalWeightRowIso (bkPointDiagram D) a).hom ≫
          CategoryBar.replMap
            (wbarDegreeCoefficientMap (bkPointDiagram D) f)) ≫
        ((pointReplacementIso D b).hom ≫
          (bkPointReplacementNerveIso D).hom) :=
      congrArg (· ≫ ((pointReplacementIso D b).hom ≫
        (bkPointReplacementNerveIso D).hom))
        (terminalWeightRowIso_inner_naturality
          (bkPointDiagram D) f)
    _ = (terminalWeightRowIso (bkPointDiagram D) a).hom ≫
        (CategoryBar.replMap
            (wbarDegreeCoefficientMap (bkPointDiagram D) f) ≫
          ((pointReplacementIso D b).hom ≫
            (bkPointReplacementNerveIso D).hom)) :=
      Category.assoc _ _ _
    _ = (terminalWeightRowIso (bkPointDiagram D) a).hom ≫
        ((CategoryBar.replMap
            (wbarDegreeCoefficientMap (bkPointDiagram D) f) ≫
              (pointReplacementIso D b).hom) ≫
          (bkPointReplacementNerveIso D).hom) :=
      congrArg ((terminalWeightRowIso (bkPointDiagram D) a).hom ≫ ·)
        (Category.assoc _ _ _).symm
    _ = (terminalWeightRowIso (bkPointDiagram D) a).hom ≫
        ((pointReplacementIso D a).hom ≫
          (bkPointReplacementNerveIso D).hom) :=
      congrArg ((terminalWeightRowIso (bkPointDiagram D) a).hom ≫ ·)
        (congrArg (· ≫ (bkPointReplacementNerveIso D).hom)
          (pointReplacementIso_naturality D f))

/-- Fixed weighted-bar rows, functorial in the inner simplicial degree. -/
noncomputable def wbarRowFunctor
    {J : Type u} [Category.{v} J] (E : J ⥤ SSet.{max u v}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  SimplicialObject.Data.curryObj
      (StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) E) ⋙
    SimplicialObject.Data.toSimplicialFunctor (C := Type (max u v))

@[simp]
theorem wbarRowFunctor_obj
    {J : Type u} [Category.{v} J] (E : J ⥤ SSet.{max u v})
    (a : SimplexCategoryᵒᵖ) :
    (wbarRowFunctor E).obj a = wbarRow E a :=
  rfl

@[simp]
theorem wbarRowFunctor_map
    {J : Type u} [Category.{v} J] (E : J ⥤ SSet.{max u v})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (wbarRowFunctor E).map f = wbarInnerMap E f :=
  rfl

/-- The family of fixed-row comparisons identifies the inner simplicial
direction of the point-weighted bar with the constant functor on `nerve D`.

This is a curried bisimplicial comparison only; no diagonal or realization
conclusion is asserted. -/
noncomputable def pointRowNatIso
    (D : Type u) [Category.{v} D] :
    wbarRowFunctor (bkPointDiagram D) ≅
      (Functor.const SimplexCategoryᵒᵖ).obj (nerve D) :=
  NatIso.ofComponents (pointRowIso D) (by
    intro a b f
    change wbarInnerMap (bkPointDiagram D) f ≫ (pointRowIso D b).hom =
      (pointRowIso D a).hom ≫ 𝟙 (nerve D)
    rw [Category.comp_id]
    exact pointRowIso_inner_naturality D f)

/-- The Bousfield--Kan carrier of the constant point diagram is canonically
isomorphic to the nerve of its indexing category.

This is the categorical diagonal of `pointRowNatIso`.  It is an isomorphism
of simplicial sets and makes no realization or weak-equivalence claim. -/
noncomputable def bkPointIsoNerve
    (D : Type u) [Category.{v} D] :
    bkHocolim (bkPointDiagram D) ≅ nerve D :=
  NatIso.ofComponents
    (fun a => ((pointRowNatIso D).app a).app a) (by
      intro a b f
      have hOuter :
          ((StrictOrdinaryWeightedBar.wbarSimplicial
            (CategoryBar.replUnit D) (bkPointDiagram D)).map f).app b =
            (wbarRow (bkPointDiagram D) b).map f := by
        change
          ((StrictOrdinaryWeightedBar.wbarData
                (CategoryBar.replUnit D) (bkPointDiagram D)).toSimplicialObject ⋙
              (evaluation SimplexCategoryᵒᵖ (Type (max u v))).obj b).map f =
            (((SimplicialObject.Data.evalFunctor b).obj
              (StrictOrdinaryWeightedBar.wbarData
                (CategoryBar.replUnit D)
                (bkPointDiagram D))).toSimplicialObject).map f
        exact SimplicialObject.Data.evalToSimplicial_map_eq
          (StrictOrdinaryWeightedBar.wbarData
            (CategoryBar.replUnit D) (bkPointDiagram D)) b f.unop
      have hDiag : (bkHocolim (bkPointDiagram D)).map f =
          (wbarInnerMap (bkPointDiagram D) f).app a ≫
            (wbarRow (bkPointDiagram D) b).map f := by
        unfold bkHocolim
        rw [simplicialDiagonalFunctor_obj_map]
        change (wbarInnerMap (bkPointDiagram D) f).app a ≫
            ((StrictOrdinaryWeightedBar.wbarSimplicial
              (CategoryBar.replUnit D) (bkPointDiagram D)).map f).app b = _
        rw [hOuter]
        rfl
      rw [hDiag]
      change ((wbarInnerMap (bkPointDiagram D) f).app a ≫
            (wbarRow (bkPointDiagram D) b).map f) ≫
          (pointRowIso D b).hom.app b =
        (pointRowIso D a).hom.app a ≫ (nerve D).map f
      have hOuter := (pointRowIso D b).hom.naturality f
      have hInner := congr_app (pointRowIso_inner_naturality D f) a
      change (wbarInnerMap (bkPointDiagram D) f).app a ≫
          (pointRowIso D b).hom.app a =
        (pointRowIso D a).hom.app a at hInner
      calc
        _ = (wbarInnerMap (bkPointDiagram D) f).app a ≫
            ((wbarRow (bkPointDiagram D) b).map f ≫
              (pointRowIso D b).hom.app b) := Category.assoc _ _ _
        _ = (wbarInnerMap (bkPointDiagram D) f).app a ≫
            ((pointRowIso D b).hom.app a ≫ (nerve D).map f) :=
          congrArg ((wbarInnerMap (bkPointDiagram D) f).app a ≫ ·) hOuter
        _ = ((wbarInnerMap (bkPointDiagram D) f).app a ≫
              (pointRowIso D b).hom.app a) ≫ (nerve D).map f :=
          (Category.assoc _ _ _).symm
        _ = (pointRowIso D a).hom.app a ≫ (nerve D).map f :=
          congrArg (· ≫ (nerve D).map f) hInner)

section IndexFunctor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Identity comparison between native point coefficients under an indexing
functor. -/
def bkPointUnitIdxL (F : C ⥤ D) :
    bkPointUnitCoeff C ⟶ F ⋙ bkPointUnitCoeff D where
  app _ := 𝟙 _
  naturality := by
    intro X Y f
    rfl

/-- The replacement-to-unit-bar comparison commutes with an indexing
functor. -/
theorem replUnitBarSimplicial_indexNaturality (F : C ⥤ D) :
    CategoryBar.replIdxMapSSet F (CategoryBar.unitIdxL F) ≫
        (CategoryBar.replUnitBarSimplicialIso D).hom =
      (CategoryBar.replUnitBarSimplicialIso C).hom ≫
        CategoryBar.categoryBarIdxMap F (CategoryBar.unitIdxR F)
          (CategoryBar.unitIdxL F) := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  obtain ⟨s, l, r⟩ := x
  rfl

/-- The replacement-to-nerve route for unit coefficients is natural under
an indexing functor. -/
theorem pointReplacementNerve_indexNaturality (F : C ⥤ D) :
    CategoryBar.replIdxMapSSet F (bkPointUnitIdxL F) ≫
        (bkPointReplacementNerveIso D).hom =
      (bkPointReplacementNerveIso C).hom ≫
        nerveMap F := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  obtain ⟨s, l, r⟩ := x
  rfl

/-- The fixed-row map induced by an indexing functor, constructed through
the landed simplicial-replacement index map. -/
noncomputable def pointRowIndexMap (F : C ⥤ D)
    (a : SimplexCategoryᵒᵖ) :
    wbarRow (bkPointDiagram C) a ⟶ wbarRow (bkPointDiagram D) a :=
  (terminalWeightRowIso (bkPointDiagram C) a).hom ≫
    (pointReplacementIso C a).hom ≫
      CategoryBar.replIdxMapSSet F (bkPointUnitIdxL F) ≫
        (pointReplacementIso D a).inv ≫
          (terminalWeightRowIso (bkPointDiagram D) a).inv

/-- The fixed-row indexing map agrees with `nerveMap F` through the point-row
comparisons. -/
theorem pointRowIndexMap_comp_pointRowIso (F : C ⥤ D)
    (a : SimplexCategoryᵒᵖ) :
    pointRowIndexMap F a ≫ (pointRowIso D a).hom =
      (pointRowIso C a).hom ≫ nerveMap F := by
  simp only [pointRowIndexMap, pointRowIso, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg
    (fun q => (terminalWeightRowIso (bkPointDiagram C) a).hom ≫
      (pointReplacementIso C a).hom ≫ q)
    (pointReplacementNerve_indexNaturality F)

/-- The fixed-row indexing maps are natural in the inner simplicial degree. -/
theorem pointRowIndexMap_inner_naturality (F : C ⥤ D)
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    wbarInnerMap (bkPointDiagram C) f ≫ pointRowIndexMap F b =
      pointRowIndexMap F a ≫ wbarInnerMap (bkPointDiagram D) f := by
  apply (cancel_mono (pointRowIso D b).hom).mp
  calc
    (wbarInnerMap (bkPointDiagram C) f ≫ pointRowIndexMap F b) ≫
          (pointRowIso D b).hom =
        wbarInnerMap (bkPointDiagram C) f ≫
          (pointRowIndexMap F b ≫ (pointRowIso D b).hom) :=
      Category.assoc _ _ _
    _ = wbarInnerMap (bkPointDiagram C) f ≫
        ((pointRowIso C b).hom ≫ nerveMap F) :=
      congrArg (wbarInnerMap (bkPointDiagram C) f ≫ ·)
        (pointRowIndexMap_comp_pointRowIso F b)
    _ = (wbarInnerMap (bkPointDiagram C) f ≫
          (pointRowIso C b).hom) ≫ nerveMap F :=
      (Category.assoc _ _ _).symm
    _ = (pointRowIso C a).hom ≫ nerveMap F :=
      congrArg (· ≫ nerveMap F) (pointRowIso_inner_naturality C f)
    _ = pointRowIndexMap F a ≫ (pointRowIso D a).hom :=
      (pointRowIndexMap_comp_pointRowIso F a).symm
    _ = pointRowIndexMap F a ≫
        (wbarInnerMap (bkPointDiagram D) f ≫ (pointRowIso D b).hom) :=
      congrArg (pointRowIndexMap F a ≫ ·)
        (pointRowIso_inner_naturality D f).symm
    _ = (pointRowIndexMap F a ≫
          wbarInnerMap (bkPointDiagram D) f) ≫
        (pointRowIso D b).hom := (Category.assoc _ _ _).symm

/-- The fixed-row indexing maps assembled in the inner simplicial direction. -/
noncomputable def pointRowIndexNatTrans (F : C ⥤ D) :
    wbarRowFunctor (bkPointDiagram C) ⟶
      wbarRowFunctor (bkPointDiagram D) :=
  (pointRowNatIso C).hom ≫
    (Functor.const SimplexCategoryᵒᵖ).map (nerveMap F) ≫
      (pointRowNatIso D).inv

@[simp]
theorem pointRowIndexNatTrans_app (F : C ⥤ D)
    (a : SimplexCategoryᵒᵖ) :
    (pointRowIndexNatTrans F).app a = pointRowIndexMap F a := by
  unfold pointRowIndexNatTrans
  rw [NatTrans.comp_app, NatTrans.comp_app]
  apply (cancel_mono (pointRowIso D a).hom).mp
  change (((pointRowIso C a).hom ≫ nerveMap F) ≫
        (pointRowIso D a).inv) ≫ (pointRowIso D a).hom =
    pointRowIndexMap F a ≫ (pointRowIso D a).hom
  calc
    _ = (pointRowIso C a).hom ≫ nerveMap F := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = pointRowIndexMap F a ≫ (pointRowIso D a).hom :=
      (pointRowIndexMap_comp_pointRowIso F a).symm

/-- Diagonal component of the fixed-row indexing square. -/
theorem pointRowIndexMap_app_comp_bkPointIso (F : C ⥤ D)
    (a : SimplexCategoryᵒᵖ) :
    (pointRowIndexMap F a).app a ≫ (bkPointIsoNerve D).hom.app a =
      (bkPointIsoNerve C).hom.app a ≫ (nerveMap F).app a := by
  have h := congr_app (pointRowIndexMap_comp_pointRowIso F a) a
  change (pointRowIndexMap F a).app a ≫
      (pointRowIso D a).hom.app a =
    (pointRowIso C a).hom.app a ≫ (nerveMap F).app a at h
  exact h

/-- Map of point-diagram Bousfield--Kan carriers induced by an indexing
functor.  It is transported from `nerveMap F` across the canonical
BK-to-nerve isomorphisms. -/
noncomputable def bkPointIndexMap (F : C ⥤ D) :
    bkHocolim (bkPointDiagram C) ⟶ bkHocolim (bkPointDiagram D) :=
  (bkPointIsoNerve C).hom ≫ nerveMap F ≫ (bkPointIsoNerve D).inv

/-- The point-diagram BK indexing map is exactly `nerveMap F` through the
canonical BK-to-nerve comparisons. -/
theorem bkPointIndexMap_comp_bkPointIso (F : C ⥤ D) :
    bkPointIndexMap F ≫ (bkPointIsoNerve D).hom =
      (bkPointIsoNerve C).hom ≫ nerveMap F := by
  unfold bkPointIndexMap
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The transported BK indexing map has the diagonal component of the direct
row-level `replIdxMapSSet` construction. -/
@[simp]
theorem bkPointIndexMap_app (F : C ⥤ D) (a : SimplexCategoryᵒᵖ) :
    (bkPointIndexMap F).app a = (pointRowIndexMap F a).app a := by
  apply (cancel_mono ((bkPointIsoNerve D).hom.app a)).mp
  have hTransport := congr_app (bkPointIndexMap_comp_bkPointIso F) a
  change (bkPointIndexMap F).app a ≫ (bkPointIsoNerve D).hom.app a =
    (bkPointIsoNerve C).hom.app a ≫ (nerveMap F).app a at hTransport
  exact hTransport.trans (pointRowIndexMap_app_comp_bkPointIso F a).symm

end IndexFunctor

end SSet

end
