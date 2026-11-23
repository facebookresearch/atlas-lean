/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpaceFundamentalGroup
public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpaceTelescopeConnected
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveUnit

/-!
# Stable labels on the finite-`BGL` telescope

A morphism in the Grothendieck telescope from stage `n` to stage `m` has a
fiber label in `GLₘ(R)ᵒᵖ`.  Sending that label through the `m`th stable
inclusion defines a functor from the telescope to the one-object category of
`StableGL(R)ᵒᵖ`.  The composition proof uses the finite-to-stable cocone
equation, with heterogeneous equality removing only the dependent endpoint
transport introduced by `Grothendieck`.

Taking nerves and then the simplicial fundamental-groupoid universal
property gives the forward map from the groupoid completion of the telescope
to stable `GL`.

This file deliberately does not claim that the forward functor is an
equivalence.  Constructing and verifying its filtered-colimit inverse is the
next algebraic gate; the later homology/plus comparison is a separate gate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe w u

namespace AlgebraicKTheory
namespace StableGL

/-- Send a telescope morphism to its stable finite-stage label. -/
noncomputable def finiteBGLTelescopeToStableCategory
    (R : Type u) [Semiring R] :
    FiniteBGLTelescopeCategory R ⥤ ClassifyingCategory R where
  obj _ := SingleObj.star (StableGL R)ᵐᵒᵖ
  map {X Y} f :=
    (finiteToStableCategoryMap R Y.base).toFunctor.map f.fiber
  map_id X := by
    change (finiteToStableCategoryMap R X.base).toFunctor.map
        (Grothendieck.Hom.fiber (𝟙 X)) = 𝟙 _
    rw [Grothendieck.id_fiber, eqToHom_map, eqToHom_refl]
  map_comp {X Y Z} f g := by
    change (finiteToStableCategoryMap R Z.base).toFunctor.map
        (Grothendieck.Hom.fiber (f ≫ g)) =
      (finiteToStableCategoryMap R Y.base).toFunctor.map f.fiber ≫
        (finiteToStableCategoryMap R Z.base).toFunctor.map g.fiber
    rw [Grothendieck.comp_fiber,
      (finiteToStableCategoryMap R Z.base).toFunctor.map_comp,
      (finiteToStableCategoryMap R Z.base).toFunctor.map_comp,
      eqToHom_map, eqToHom_refl, Category.id_comp]
    have hNat := congrArg Cat.Hom.toFunctor
      (finiteToStableCategoryMap_naturality R g.base)
    have hMap := Functor.congr_hom hNat f.fiber
    let hX := Functor.congr_obj hNat
      (((finiteClassifyingCategoryDiagram R).map
        f.base).toFunctor.obj X.fiber)
    let hY := Functor.congr_obj hNat Y.fiber
    have hMapHeq : HEq
        (((finiteClassifyingCategoryDiagram R).map g.base ≫
          finiteToStableCategoryMap R Z.base).toFunctor.map f.fiber)
        ((finiteToStableCategoryMap R Y.base).toFunctor.map f.fiber) :=
      (CategoryTheory.conj_eqToHom_iff_heq _ _ hX hY).1 hMap
    have hMapHeq' : HEq
        ((finiteToStableCategoryMap R Z.base).toFunctor.map
          (((finiteClassifyingCategoryDiagram R).map
            g.base).toFunctor.map f.fiber))
        ((finiteToStableCategoryMap R Y.base).toFunctor.map f.fiber) :=
      hMapHeq
    rw [eq_of_heq hMapHeq']
    rfl

/-- Simplicial nerve map induced by stable finite-stage labels. -/
noncomputable def finiteBGLTelescopeNerveToStableNerve
    (R : Type u) [Semiring R] :
    finiteBGLTelescopeNerve R ⟶ classifyingNerve R :=
  CategoryTheory.nerveMap (finiteBGLTelescopeToStableCategory R)

/-- Canonical CGWH map from the finite-`BGL` telescope to stable `BGL`. -/
noncomputable def finiteBGLTelescopeToBGL
    (R : Type u) [Semiring R] :
    finiteBGLTelescope.{w} R ⟶ BGL.{w} R :=
  CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
    (finiteBGLTelescopeToStableCategory R).toCatHom

/-- The telescope-to-stable-`BGL` map as a strictly pointed CGWH map. -/
noncomputable def pointedFiniteBGLTelescopeToBGL
    (R : Type u) [Semiring R] :
    pointedFiniteBGLTelescope.{w} R ⟶ pointedBGL.{w} R :=
  Under.homMk (finiteBGLTelescopeToBGL.{w} R) (by
    exact CategoryTheory.classifyingSpaceCGWH_basepointMap_naturality
      (finiteBGLTelescopeToStableCategory R)
      (finiteBGLTelescopeBaseObject R))

/-- Basepoint of the ordinary realization of the finite-`BGL` telescope. -/
noncomputable def ordinaryFiniteBGLTelescopeBasepoint
    (R : Type u) [Semiring R] :
    ordinaryFiniteBGLTelescope R :=
  SSet.realizedVertex (finiteBGLTelescopeBaseVertex R)

/-- Ordinary-realization form of the telescope-to-stable-`BGL` map. -/
noncomputable def ordinaryFiniteBGLTelescopeToBGL
    (R : Type u) [Semiring R] :
    ordinaryFiniteBGLTelescope R ⟶ ordinaryBGL R :=
  SSet.toTop.map (finiteBGLTelescopeNerveToStableNerve R)

set_option backward.isDefEq.respectTransparency false in
/-- The simplicial comparison sends the selected telescope vertex to the
stable classifying vertex. -/
theorem finiteBGLTelescopeNerveToStableNerve_baseVertex
    (R : Type u) [Semiring R] :
    (finiteBGLTelescopeNerveToStableNerve R).app (op ⦋0⦌)
        (finiteBGLTelescopeBaseVertex R) =
      classifyingVertex R := by
  unfold finiteBGLTelescopeNerveToStableNerve
    finiteBGLTelescopeBaseVertex finiteBGLTelescopeVertex
    classifyingVertex
  have hVertex : CategoryTheory.nerveEquiv.symm
      (finiteBGLTelescopeBaseObject R) =
        ComposableArrows.mk₀ (finiteBGLTelescopeBaseObject R) := rfl
  rw [hVertex, CategoryTheory.nerveMap_app_mk₀]
  rfl

/-- The ordinary telescope comparison preserves the selected basepoint. -/
theorem ordinaryFiniteBGLTelescopeToBGL_basepoint
    (R : Type u) [Semiring R] :
    ordinaryFiniteBGLTelescopeToBGL R
        (ordinaryFiniteBGLTelescopeBasepoint R) =
      ordinaryBGLBasepoint R := by
  calc
    ordinaryFiniteBGLTelescopeToBGL R
        (ordinaryFiniteBGLTelescopeBasepoint R) =
        SSet.realizedVertex
          ((finiteBGLTelescopeNerveToStableNerve R).app (op ⦋0⦌)
            (finiteBGLTelescopeBaseVertex R)) :=
      (SSet.realizedVertex_naturality
        (finiteBGLTelescopeNerveToStableNerve R)
        (finiteBGLTelescopeBaseVertex R)).symm
    _ = ordinaryBGLBasepoint R := by
      rw [finiteBGLTelescopeNerveToStableNerve_baseVertex]
      rfl

/-- Homomorphism on ordinary fundamental groups induced by the canonical
telescope comparison. -/
noncomputable def ordinaryFiniteBGLTelescopeFundamentalMap
    (R : Type u) [Semiring R] :
    FundamentalGroup (ordinaryFiniteBGLTelescope R)
        (ordinaryFiniteBGLTelescopeBasepoint R) →*
      FundamentalGroup (ordinaryBGL R)
        (ordinaryBGLBasepoint R) :=
  FundamentalGroup.mapOfEq
    (ordinaryFiniteBGLTelescopeToBGL R).hom
    (ordinaryFiniteBGLTelescopeToBGL_basepoint R)

/-- Forward functor from the groupoid completion of the telescope nerve to
the stable-`GL` one-object groupoid. -/
noncomputable def finiteBGLTelescopeFundamentalGroupoidToStable
    (R : Type u) [Semiring R] :
    SSet.FundamentalGroupoid (finiteBGLTelescopeNerve R) ⥤
      ClassifyingCategory R :=
  SSet.FundamentalGroupoid.desc
    (fun x => CategoryTheory.nerveEquiv
      ((finiteBGLTelescopeNerveToStableNerve R).app _ x))
    (fun e => CategoryTheory.nerve.homEquiv
      (e.map (finiteBGLTelescopeNerveToStableNerve R)))
    (fun h => CategoryTheory.nerve.homEquiv_comp
      (h.map (finiteBGLTelescopeNerveToStableNerve R)))

@[simp]
theorem finiteBGLTelescopeFundamentalGroupoidToStable_obj_mk
    (R : Type u) [Semiring R]
    (x : (finiteBGLTelescopeNerve R).obj (Opposite.op ⦋0⦌)) :
    (finiteBGLTelescopeFundamentalGroupoidToStable R).obj
        (SSet.FundamentalGroupoid.mk x) =
      CategoryTheory.nerveEquiv
        ((finiteBGLTelescopeNerveToStableNerve R).app _ x) :=
  rfl

@[simp]
theorem finiteBGLTelescopeFundamentalGroupoidToStable_map_homMk
    (R : Type u) [Semiring R]
    {x y : (finiteBGLTelescopeNerve R).obj (Opposite.op ⦋0⦌)}
    (e : (finiteBGLTelescopeNerve R).Edge x y) :
    (finiteBGLTelescopeFundamentalGroupoidToStable R).map
        (SSet.FundamentalGroupoid.homMk e) =
      CategoryTheory.nerve.homEquiv
        (e.map (finiteBGLTelescopeNerveToStableNerve R)) :=
  SSet.FundamentalGroupoid.desc_map_homMk
    (fun x => CategoryTheory.nerveEquiv
      ((finiteBGLTelescopeNerveToStableNerve R).app _ x))
    (fun e => CategoryTheory.nerve.homEquiv
      (e.map (finiteBGLTelescopeNerveToStableNerve R)))
    (fun h => CategoryTheory.nerve.homEquiv_comp
      (h.map (finiteBGLTelescopeNerveToStableNerve R))) e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a categorical nerve edge, the forward groupoid functor is the
stable-label functor itself. -/
theorem finiteBGLTelescopeFundamentalGroupoidToStable_map_categoryNerveUnit
    (R : Type u) [Semiring R]
    {X Y : FiniteBGLTelescopeCategory R} (f : X ⟶ Y) :
    (finiteBGLTelescopeFundamentalGroupoidToStable R).map
        ((SSet.categoryNerveUnit
          (FiniteBGLTelescopeCategory R)).map f) =
      (finiteBGLTelescopeToStableCategory R).map f := by
  rw [SSet.categoryNerveUnit_map,
    finiteBGLTelescopeFundamentalGroupoidToStable_map_homMk]
  exact CategoryTheory.nerve.homEquiv_edgeMk_map_nerveMap
    f (finiteBGLTelescopeToStableCategory R)

/-- The forward groupoid functor sends the selected telescope base object to
the unique stable-`GL` object. -/
theorem finiteBGLTelescopeFundamentalGroupoidToStable_obj_base
    (R : Type u) [Semiring R] :
    (finiteBGLTelescopeFundamentalGroupoidToStable R).obj
        (SSet.FundamentalGroupoid.mk
          (finiteBGLTelescopeBaseVertex R)) =
      SingleObj.star (StableGL R)ᵐᵒᵖ := by
  rw [finiteBGLTelescopeFundamentalGroupoidToStable_obj_mk]
  have hVertex : CategoryTheory.nerveEquiv.symm
      (finiteBGLTelescopeBaseObject R) =
        ComposableArrows.mk₀ (finiteBGLTelescopeBaseObject R) := rfl
  change CategoryTheory.nerveEquiv
      ((CategoryTheory.nerveMap
        (finiteBGLTelescopeToStableCategory R)).app (op ⦋0⦌)
          (CategoryTheory.nerveEquiv.symm
            (finiteBGLTelescopeBaseObject R))) = _
  rw [hVertex]
  rw [CategoryTheory.nerveMap_app_mk₀]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The equality isomorphism identifying the image of the telescope base
with the stable one-object category acts trivially by conjugation. -/
theorem finiteBGLTelescopeFundamentalGroupoidToStable_base_conj
    (R : Type u) [Semiring R]
    (g : CategoryTheory.End
      (SingleObj.star (StableGL R)ᵐᵒᵖ)) :
    (eqToIso
      (finiteBGLTelescopeFundamentalGroupoidToStable_obj_base R)).conj g =
        g := by
  apply End.ext
  rw [Iso.conj_apply_asHom]
  rw [eqToIso.inv, eqToIso.hom,
    classifyingCategory_eqToHom R]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Forward homomorphism from the based endomorphism group of the telescope
fundamental groupoid to the opposite stable general linear group. -/
noncomputable def finiteBGLTelescopeFundamentalToStableOpposite
    (R : Type u) [Semiring R] :
    CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (finiteBGLTelescopeBaseVertex R)) →*
      (StableGL R)ᵐᵒᵖ :=
  (SingleObj.toEnd ((StableGL R)ᵐᵒᵖ)).symm.toMonoidHom.comp
    ((eqToIso
      (finiteBGLTelescopeFundamentalGroupoidToStable_obj_base R)).conj.toMonoidHom.comp
        ((finiteBGLTelescopeFundamentalGroupoidToStable R).mapEnd
          (SSet.FundamentalGroupoid.mk
            (finiteBGLTelescopeBaseVertex R))))

/-- Forward homomorphism with the deliberate opposite convention removed by
inversion. -/
noncomputable def finiteBGLTelescopeFundamentalToStable
    (R : Type u) [Semiring R] :
    CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (finiteBGLTelescopeBaseVertex R)) →*
      StableGL R :=
  (MulEquiv.inv' (StableGL R)).symm.toMonoidHom.comp
    (finiteBGLTelescopeFundamentalToStableOpposite R)

/-- Conjugate an arbitrary telescope fundamental-groupoid morphism to the
selected basepoint using the canonical paths to its endpoints. -/
noncomputable def finiteBGLTelescopeBasedNormalize
    (R : Type u) [Semiring R]
    {x y : SSet.FundamentalGroupoid
      (finiteBGLTelescopeNerve R)}
    (q : x ⟶ y) :
    CategoryTheory.End
      (SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeBaseVertex R)) :=
  End.of ((finiteBGLTelescopeBaseIsoToVertex R x.pt).hom ≫ q ≫
    (finiteBGLTelescopeBaseIsoToVertex R y.pt).inv)

/-- Based normalization turns groupoid composition into composition of based
loops. -/
theorem finiteBGLTelescopeBasedNormalize_comp
    (R : Type u) [Semiring R]
    {x y z : SSet.FundamentalGroupoid
      (finiteBGLTelescopeNerve R)}
    (q : x ⟶ y) (r : y ⟶ z) :
    finiteBGLTelescopeBasedNormalize R (q ≫ r) =
      finiteBGLTelescopeBasedNormalize R r *
        finiteBGLTelescopeBasedNormalize R q := by
  apply End.ext
  simp only [End.mul_asHom, finiteBGLTelescopeBasedNormalize, Category.assoc]
  rw [Iso.inv_hom_id_assoc]

/-- Based normalization commutes with groupoid inversion. -/
theorem finiteBGLTelescopeBasedNormalize_inv
    (R : Type u) [Semiring R]
    {x y : SSet.FundamentalGroupoid
      (finiteBGLTelescopeNerve R)}
    (q : x ⟶ y) :
    finiteBGLTelescopeBasedNormalize R (CategoryTheory.inv q) =
      (finiteBGLTelescopeBasedNormalize R q)⁻¹ := by
  apply End.ext
  change (finiteBGLTelescopeBasedNormalize R (CategoryTheory.inv q)).asHom =
    Groupoid.inv ((finiteBGLTelescopeBasedNormalize R q).asHom)
  rw [Groupoid.inv_eq_inv]
  simp only [finiteBGLTelescopeBasedNormalize,
    IsIso.inv_comp, Category.assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- At a represented category object, the arbitrary-target base isomorphism
has the nerve-unit image of the canonical base morphism as its forward map. -/
theorem finiteBGLTelescopeBaseIsoToVertex_hom_vertex
    (R : Type u) [Semiring R]
    (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeBaseIsoToVertex R
      (CategoryTheory.nerveEquiv.symm X)).hom =
        (SSet.categoryNerveUnit
          (FiniteBGLTelescopeCategory R)).map
            (finiteBGLTelescopeBaseTo R X) := by
  unfold finiteBGLTelescopeBaseIsoToVertex
    finiteBGLTelescopeBaseHomToVertex
    finiteBGLTelescopeBaseEdgeToVertex
  rw [SSet.categoryNerveUnit_map]
  cat_disch

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse arbitrary-target base path is the groupoid inverse of the
nerve-unit image. -/
theorem finiteBGLTelescopeBaseIsoToVertex_inv_vertex
    (R : Type u) [Semiring R]
    (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeBaseIsoToVertex R
      (CategoryTheory.nerveEquiv.symm X)).inv =
        Groupoid.inv
          ((SSet.categoryNerveUnit
            (FiniteBGLTelescopeCategory R)).map
              (finiteBGLTelescopeBaseTo R X)) := by
  rw [Groupoid.inv_eq_inv]
  rw [← finiteBGLTelescopeBaseIsoToVertex_hom_vertex R X]
  rfl

/-- Regard the fiber label of a telescope morphism as an endomorphism of its
target object. -/
noncomputable def finiteBGLTelescopeTargetLabelHom
    (R : Type u) [Semiring R]
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    Y ⟶ Y where
  base := 𝟙 Y.base
  fiber := show
    (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.flexible false in
/-- A telescope morphism factors, after the canonical path to its source, as
the canonical path to its target followed by its fiber label. -/
theorem finiteBGLTelescopeBaseTo_comp_eq_baseTo_comp_targetLabel
    (R : Type u) [Semiring R]
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    finiteBGLTelescopeBaseTo R X ≫ a =
      finiteBGLTelescopeBaseTo R Y ≫
        finiteBGLTelescopeTargetLabelHom R a := by
  let hbase :
      (finiteBGLTelescopeBaseTo R X ≫ a).base =
        (finiteBGLTelescopeBaseTo R Y ≫
          finiteBGLTelescopeTargetLabelHom R a).base :=
    Subsingleton.elim _ _
  apply Grothendieck.ext _ _ hbase
  cases hbase
  rw [Grothendieck.comp_fiber, Grothendieck.comp_fiber]
  unfold finiteBGLTelescopeBaseTo
  unfold finiteBGLTelescopeTargetLabelHom
  rw [finiteClassifyingCategoryDiagram_eqToHom R (n := Y.base)]
  simp
  let φ : Matrix.GeneralLinearGroup (Fin X.base) R →*
      Matrix.GeneralLinearGroup (Fin Y.base) R := by
    simpa only [finiteGLDiagram_obj_obj_of] using
      ((finiteGLDiagram.obj (SemiRingCat.of R)).map a.base).hom
  have hφone : φ 1 = 1 := φ.map_one
  change
    (((show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber) *
      MulOpposite.op (φ 1)) * 1) * 1 =
      ((show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber) * 1) * 1
  simp only [hφone, MulOpposite.op_one, mul_one]

/-- The based loop obtained directly from a categorical telescope
morphism. -/
noncomputable def finiteBGLTelescopeCategoryBasedLoop
    (R : Type u) [Semiring R]
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    CategoryTheory.End
      (SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeBaseVertex R)) :=
  End.of ((SSet.categoryNerveUnit
      (FiniteBGLTelescopeCategory R)).map
        (finiteBGLTelescopeBaseTo R X) ≫
    (SSet.categoryNerveUnit
      (FiniteBGLTelescopeCategory R)).map a ≫
    Groupoid.inv
      ((SSet.categoryNerveUnit
        (FiniteBGLTelescopeCategory R)).map
          (finiteBGLTelescopeBaseTo R Y)))

/-- The same based loop, formed from the fiber-label endomorphism at the
target. -/
noncomputable def finiteBGLTelescopeTargetLabelBasedLoop
    (R : Type u) [Semiring R]
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    CategoryTheory.End
      (SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeBaseVertex R)) :=
  End.of ((SSet.categoryNerveUnit
      (FiniteBGLTelescopeCategory R)).map
        (finiteBGLTelescopeBaseTo R Y) ≫
    (SSet.categoryNerveUnit
      (FiniteBGLTelescopeCategory R)).map
        (finiteBGLTelescopeTargetLabelHom R a) ≫
    Groupoid.inv
      ((SSet.categoryNerveUnit
        (FiniteBGLTelescopeCategory R)).map
          (finiteBGLTelescopeBaseTo R Y)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Categorical factorization identifies the direct based loop with the
target-label based loop. -/
theorem finiteBGLTelescopeCategoryBasedLoop_eq_targetLabel
    (R : Type u) [Semiring R]
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    finiteBGLTelescopeCategoryBasedLoop R a =
      finiteBGLTelescopeTargetLabelBasedLoop R a := by
  apply End.ext
  unfold finiteBGLTelescopeCategoryBasedLoop
    finiteBGLTelescopeTargetLabelBasedLoop
  rw [← Category.assoc,
    ← Functor.map_comp,
    finiteBGLTelescopeBaseTo_comp_eq_baseTo_comp_targetLabel,
    Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On an edge generator of the telescope nerve, arbitrary-endpoint based
normalization is the categorical based loop of the represented morphism. -/
theorem finiteBGLTelescopeBasedNormalize_homMk
    (R : Type u) [Semiring R]
    {x y : (finiteBGLTelescopeNerve R).obj (op ⦋0⦌)}
    (e : (finiteBGLTelescopeNerve R).Edge x y) :
    finiteBGLTelescopeBasedNormalize R
        (SSet.FundamentalGroupoid.homMk e) =
      finiteBGLTelescopeCategoryBasedLoop R
        (CategoryTheory.nerve.homEquiv e) := by
  obtain ⟨X, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective x
  obtain ⟨Y, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective y
  obtain ⟨a, rfl⟩ := CategoryTheory.nerve.edgeMk_surjective e
  have hX := CategoryTheory.nerveEquiv.apply_symm_apply X
  have hY := CategoryTheory.nerveEquiv.apply_symm_apply Y
  cases hX
  cases hY
  apply End.ext
  unfold finiteBGLTelescopeBasedNormalize
    finiteBGLTelescopeCategoryBasedLoop
  dsimp only [SSet.FundamentalGroupoid.mk]
  rw [finiteBGLTelescopeBaseIsoToVertex_hom_vertex,
    finiteBGLTelescopeBaseIsoToVertex_inv_vertex,
    CategoryTheory.nerve.homEquiv_edgeMk,
    SSet.categoryNerveUnit_map]
  simp only [SSet.categoryNerveUnit_map]
  cat_disch

/-- The telescope object obtained by including the unique object of the
`n`th finite classifying category. -/
abbrev finiteBGLTelescopeStageObject
    (R : Type u) [Semiring R] (n : ℕ) :
    FiniteBGLTelescopeCategory R :=
  ⟨n, SingleObj.star
    (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ⟩

@[simp]
theorem finiteBGLTelescopeStageObject_base
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteBGLTelescopeStageObject R n).base = n :=
  rfl

/-- Every telescope object is equal to the canonical object at its base
stage. -/
theorem finiteBGLTelescopeStageObject_eq
    (R : Type u) [Semiring R]
    (X : FiniteBGLTelescopeCategory R) :
    finiteBGLTelescopeStageObject R X.base = X := by
  cases X with
  | mk n x =>
      congr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- At a canonical stage object, the target-label endomorphism is the fiber
inclusion of the raw label. -/
theorem finiteBGLTelescopeTargetLabelHom_at_stage
    (R : Type u) [Semiring R]
    {X : FiniteBGLTelescopeCategory R} {m : ℕ}
    (a : X ⟶ finiteBGLTelescopeStageObject R m) :
    finiteBGLTelescopeTargetLabelHom R a =
      (finiteBGLTelescopeFiberInclusion R m).map
        (show (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from
          a.fiber) := by
  let hbase :
      (finiteBGLTelescopeTargetLabelHom R a).base =
        ((finiteBGLTelescopeFiberInclusion R m).map
          (show (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from
            a.fiber)).base :=
    Subsingleton.elim _ _
  apply Grothendieck.ext _ _ hbase
  cases hbase
  unfold finiteBGLTelescopeTargetLabelHom
  unfold finiteBGLTelescopeFiberInclusion
  rw [Grothendieck.ι_map]

/-- Canonical categorical morphism from the selected zeroth-stage object to
the explicit `n`th-stage object. -/
noncomputable def finiteBGLTelescopeBaseToStageCategoryHom
    (R : Type u) [Semiring R] (n : ℕ) :
    finiteBGLTelescopeBaseObject R ⟶
      finiteBGLTelescopeStageObject R n where
  base := homOfLE (Nat.zero_le n)
  fiber := 𝟙 _

@[simp]
theorem finiteBGLTelescopeBaseToStageCategoryHom_base
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteBGLTelescopeBaseToStageCategoryHom R n).base =
      homOfLE (Nat.zero_le n) :=
  rfl

@[simp]
theorem finiteBGLTelescopeBaseToStageCategoryHom_fiber
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteBGLTelescopeBaseToStageCategoryHom R n).fiber =
      𝟙 (((finiteClassifyingCategoryDiagram R).map
        (homOfLE (Nat.zero_le n))).toFunctor.obj
          (finiteBGLTelescopeBaseObject R).fiber) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.flexible false in
/-- The general canonical base morphism agrees with the explicit
finite-stage specialization. -/
theorem finiteBGLTelescopeBaseTo_stage
    (R : Type u) [Semiring R] (n : ℕ) :
    finiteBGLTelescopeBaseTo R
        (finiteBGLTelescopeStageObject R n) =
      finiteBGLTelescopeBaseToStageCategoryHom R n := by
  let hbase :
      (finiteBGLTelescopeBaseTo R
        (finiteBGLTelescopeStageObject R n)).base =
      (finiteBGLTelescopeBaseToStageCategoryHom R n).base :=
    Subsingleton.elim _ _
  apply Grothendieck.ext _ _ hbase
  cases hbase
  unfold finiteBGLTelescopeBaseTo
  rw [finiteBGLTelescopeBaseToStageCategoryHom_fiber]
  rw [finiteClassifyingCategoryDiagram_eqToHom R (n := n)]
  simp
  change (1 : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) * 1 = 1
  exact mul_one 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.flexible false in
/-- The canonical base-to-zero-stage morphism is the identity. -/
theorem finiteBGLTelescopeBaseToStageCategoryHom_zero
    (R : Type u) [Semiring R] :
    finiteBGLTelescopeBaseToStageCategoryHom R 0 =
      𝟙 (finiteBGLTelescopeBaseObject R) := by
  let hbase :
      (finiteBGLTelescopeBaseToStageCategoryHom R 0).base =
        Grothendieck.Hom.base
          (𝟙 (finiteBGLTelescopeBaseObject R)) :=
    Subsingleton.elim _ _
  apply Grothendieck.ext _ _ hbase
  cases hbase
  rw [finiteBGLTelescopeBaseToStageCategoryHom_fiber,
    Grothendieck.id_fiber]
  rw [finiteClassifyingCategoryDiagram_eqToHom R (n := 0)]
  simp

/-- The general canonical base morphism is the identity at the selected base
object. -/
theorem finiteBGLTelescopeBaseTo_baseObject
    (R : Type u) [Semiring R] :
    finiteBGLTelescopeBaseTo R
        (finiteBGLTelescopeBaseObject R) =
      𝟙 (finiteBGLTelescopeBaseObject R) := by
  rw [finiteBGLTelescopeBaseTo_stage,
    finiteBGLTelescopeBaseToStageCategoryHom_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The arbitrary-vertex base isomorphism is the identity at the selected
base vertex. -/
theorem finiteBGLTelescopeBaseIsoToVertex_hom_base
    (R : Type u) [Semiring R] :
    (finiteBGLTelescopeBaseIsoToVertex R
      (finiteBGLTelescopeBaseVertex R)).hom =
        𝟙 (SSet.FundamentalGroupoid.mk
          (finiteBGLTelescopeBaseVertex R)) := by
  unfold finiteBGLTelescopeBaseVertex
    finiteBGLTelescopeVertex
  rw [finiteBGLTelescopeBaseIsoToVertex_hom_vertex]
  rw [finiteBGLTelescopeBaseTo_baseObject]
  exact (SSet.categoryNerveUnit
    (FiniteBGLTelescopeCategory R)).map_id
      (finiteBGLTelescopeBaseObject R)

/-- The inverse of the arbitrary-vertex base isomorphism is also the
identity at the selected base vertex. -/
theorem finiteBGLTelescopeBaseIsoToVertex_inv_base
    (R : Type u) [Semiring R] :
    (finiteBGLTelescopeBaseIsoToVertex R
      (finiteBGLTelescopeBaseVertex R)).inv =
        𝟙 (SSet.FundamentalGroupoid.mk
          (finiteBGLTelescopeBaseVertex R)) := by
  have h := Iso.hom_inv_id
    (finiteBGLTelescopeBaseIsoToVertex R
      (finiteBGLTelescopeBaseVertex R))
  rw [finiteBGLTelescopeBaseIsoToVertex_hom_base,
    Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Based normalization is the identity on endomorphisms of the selected
base vertex. -/
theorem finiteBGLTelescopeBasedNormalize_base
    (R : Type u) [Semiring R]
    (q : CategoryTheory.End
      (SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeBaseVertex R))) :
    finiteBGLTelescopeBasedNormalize R q.asHom = q := by
  apply End.ext
  unfold finiteBGLTelescopeBasedNormalize
  dsimp only [SSet.FundamentalGroupoid.mk]
  rw [finiteBGLTelescopeBaseIsoToVertex_hom_base,
    finiteBGLTelescopeBaseIsoToVertex_inv_base]
  calc
    𝟙 _ ≫ q.asHom ≫ 𝟙 _ = q.asHom ≫ 𝟙 _ := Category.id_comp _
    _ = q.asHom := Category.comp_id _

/-- The telescope vertex represented by the included `n`th-stage object. -/
noncomputable def finiteBGLTelescopeStageVertex
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteBGLTelescopeNerve R).obj (op ⦋0⦌) :=
  CategoryTheory.nerveEquiv.symm
    (finiteBGLTelescopeStageObject R n)

/-- Canonical edge from the telescope base vertex to the included `n`th
stage vertex. -/
noncomputable def finiteBGLTelescopeBaseToStageEdge
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteBGLTelescopeNerve R).Edge
      (finiteBGLTelescopeBaseVertex R)
      (finiteBGLTelescopeStageVertex R n) :=
  CategoryTheory.nerve.edgeMk
    (finiteBGLTelescopeBaseToStageCategoryHom R n)

/-- Telescope morphism induced by an indexing transition between two finite
stages. -/
noncomputable def finiteBGLTelescopeStageTransition
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    finiteBGLTelescopeStageObject R n ⟶
      finiteBGLTelescopeStageObject R m :=
  (finiteBGLTelescopeFiberTransition R f).app
    (SingleObj.star
      (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)

@[simp]
theorem finiteBGLTelescopeStageTransition_base
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    (finiteBGLTelescopeStageTransition R f).base = f :=
  rfl

@[simp]
theorem finiteBGLTelescopeStageTransition_fiber
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    (finiteBGLTelescopeStageTransition R f).fiber =
      𝟙 (((finiteClassifyingCategoryDiagram R).map f).toFunctor.obj
        (SingleObj.star
          (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.flexible false in
/-- The canonical base-to-stage morphisms commute strictly with every stage
transition. -/
theorem finiteBGLTelescopeBaseToStage_comp_transition
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    finiteBGLTelescopeBaseToStageCategoryHom R n ≫
        finiteBGLTelescopeStageTransition R f =
      finiteBGLTelescopeBaseToStageCategoryHom R m := by
  let hbase :
      (finiteBGLTelescopeBaseToStageCategoryHom R n ≫
        finiteBGLTelescopeStageTransition R f).base =
      (finiteBGLTelescopeBaseToStageCategoryHom R m).base :=
    Subsingleton.elim _ _
  apply Grothendieck.ext _ _ hbase
  cases hbase
  rw [Grothendieck.comp_fiber]
  simp only [finiteBGLTelescopeStageObject_base,
    finiteBGLTelescopeStageTransition_base,
    finiteBGLTelescopeStageTransition_fiber,
    finiteBGLTelescopeBaseToStageCategoryHom_fiber]
  rw [finiteClassifyingCategoryDiagram_eqToHom R (n := m)]
  simp
  change
    (MulOpposite.op
      (((finiteGLDiagram.obj (SemiRingCat.of R)).map f).hom
        (1 : Matrix.GeneralLinearGroup (Fin n) R)) * 1) * 1 =
      (1 : (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ)
  simp only [map_one, MulOpposite.op_one, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Stable labels send every canonical base-to-stage morphism to the
identity. -/
theorem finiteBGLTelescopeToStableCategory_map_baseToStage
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteBGLTelescopeToStableCategory R).map
        (finiteBGLTelescopeBaseToStageCategoryHom R n) =
      𝟙 (SingleObj.star (StableGL R)ᵐᵒᵖ) := by
  change (finiteToStableCategoryMap R n).toFunctor.map
      (finiteBGLTelescopeBaseToStageCategoryHom R n).fiber = 𝟙 _
  rw [finiteBGLTelescopeBaseToStageCategoryHom_fiber,
    finiteBGLTelescopeBaseToStageCategoryHom_base]
  rw [finiteClassifyingCategoryDiagram_id_as_one R]
  change MulOpposite.op
      ((StableGL.inclusion n).app (SemiRingCat.of R) 1) =
    (1 : (StableGL R)ᵐᵒᵖ)
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Stable labeling after a finite-stage fiber inclusion is the original
finite-to-stable functor on morphisms. -/
theorem finiteBGLTelescopeToStableCategory_map_fiberInclusion
    (R : Type u) [Semiring R] (n : ℕ)
    {X Y : (finiteClassifyingCategoryDiagram R).obj n}
    (g : X ⟶ Y) :
    (finiteBGLTelescopeToStableCategory R).map
        ((finiteBGLTelescopeFiberInclusion R n).map g) =
      (finiteToStableCategoryMap R n).toFunctor.map g := by
  change (finiteToStableCategoryMap R n).toFunctor.map
      ((finiteBGLTelescopeFiberInclusion R n).map g).fiber =
    (finiteToStableCategoryMap R n).toFunctor.map g
  unfold finiteBGLTelescopeFiberInclusion
  rw [Grothendieck.ι_map]
  rw [(finiteToStableCategoryMap R n).toFunctor.map_comp]
  rw [eqToHom_map, classifyingCategory_eqToHom R]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On the `n`th finite fiber, the telescope stable-label functor equals the
original finite-to-stable functor. -/
theorem finiteBGLTelescopeFiberInclusionCompStable_eq
    (R : Type u) [Semiring R] (n : ℕ) :
    finiteBGLTelescopeFiberInclusion R n ⋙
        finiteBGLTelescopeToStableCategory R =
      (finiteToStableCategoryMap R n).toFunctor := by
  let hObj : ∀ X,
      (finiteBGLTelescopeFiberInclusion R n ⋙
        finiteBGLTelescopeToStableCategory R).obj X =
      (finiteToStableCategoryMap R n).toFunctor.obj X := fun _ => rfl
  refine CategoryTheory.Functor.ext hObj ?_
  intro X Y g
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (hObj X) (hObj Y)).2
  exact heq_of_eq
    (finiteBGLTelescopeToStableCategory_map_fiberInclusion R n g)

/-- Natural-isomorphism form of the finite-fiber stable-label comparison. -/
noncomputable def finiteBGLTelescopeFiberInclusionCompStableIso
    (R : Type u) [Semiring R] (n : ℕ) :
    finiteBGLTelescopeFiberInclusion R n ⋙
        finiteBGLTelescopeToStableCategory R ≅
      (finiteToStableCategoryMap R n).toFunctor :=
  eqToIso (finiteBGLTelescopeFiberInclusionCompStable_eq R n)

/-- Every finite-stage map to stable `BGL` factors strictly through the
realized categorical telescope. -/
theorem finiteBGLToTelescope_comp_toBGL
    (R : Type u) [Semiring R] (n : ℕ) :
    finiteBGLToTelescope.{w} R n ≫
        finiteBGLTelescopeToBGL.{w} R =
      finiteBGLToBGL.{w} R n := by
  change CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
        (finiteBGLTelescopeFiberInclusion R n).toCatHom ≫
      CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
        (finiteBGLTelescopeToStableCategory R).toCatHom =
    CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map
      (finiteToStableCategoryMap R n)
  rw [← CategoryTheory.classifyingSpaceCGWH.map_comp]
  apply congrArg
    (CategoryTheory.classifyingSpaceCGWH.{w, u, 0}.map)
  apply Cat.Hom.ext
  exact finiteBGLTelescopeFiberInclusionCompStable_eq R n

/-- A finite-stage label commutes with an indexing transition after applying
the corresponding stabilization map. -/
theorem finiteBGLTelescopeStageLabel_naturality
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m)
    (g : CategoryTheory.End
      (SingleObj.star
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) :
    (finiteBGLTelescopeFiberInclusion R n).map g.asHom ≫
        finiteBGLTelescopeStageTransition R f =
      finiteBGLTelescopeStageTransition R f ≫
        (finiteBGLTelescopeFiberInclusion R m).map
          (((finiteClassifyingCategoryDiagram R).map f).toFunctor.map g.asHom) :=
  (finiteBGLTelescopeFiberTransition R f).naturality g.asHom

/-- The base-to-stage edge as a morphism in the telescope fundamental
groupoid. -/
noncomputable def finiteBGLTelescopeBaseToStageHom
    (R : Type u) [Semiring R] (n : ℕ) :
    SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeBaseVertex R) ⟶
      SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeStageVertex R n) :=
  SSet.FundamentalGroupoid.homMk
    (finiteBGLTelescopeBaseToStageEdge R n)

/-- The canonical base-to-stage isomorphism in the groupoid completion. -/
noncomputable def finiteBGLTelescopeBaseToStageIso
    (R : Type u) [Semiring R] (n : ℕ) :
    SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeBaseVertex R) ≅
      SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeStageVertex R n) :=
  asIso (finiteBGLTelescopeBaseToStageHom R n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The forward groupoid functor sends the canonical base-to-stage path to
the identity stable label. -/
theorem finiteBGLTelescopeFundamentalGroupoidToStable_map_baseToStageIso_hom
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteBGLTelescopeFundamentalGroupoidToStable R).map
        (finiteBGLTelescopeBaseToStageIso R n).hom =
      𝟙 (SingleObj.star (StableGL R)ᵐᵒᵖ) := by
  change (finiteBGLTelescopeFundamentalGroupoidToStable R).map
      ((SSet.categoryNerveUnit
        (FiniteBGLTelescopeCategory R)).map
          (finiteBGLTelescopeBaseToStageCategoryHom R n)) = _
  rw [finiteBGLTelescopeFundamentalGroupoidToStable_map_categoryNerveUnit,
    finiteBGLTelescopeToStableCategory_map_baseToStage]

/-- The inverse base path also has identity stable label. -/
theorem finiteBGLTelescopeFundamentalGroupoidToStable_map_baseToStageIso_inv
    (R : Type u) [Semiring R] (n : ℕ) :
    (finiteBGLTelescopeFundamentalGroupoidToStable R).map
        (finiteBGLTelescopeBaseToStageIso R n).inv =
      𝟙 (SingleObj.star (StableGL R)ᵐᵒᵖ) := by
  have h := Functor.map_hom_inv'
    (finiteBGLTelescopeFundamentalGroupoidToStable R)
    (finiteBGLTelescopeBaseToStageIso R n)
  rw [finiteBGLTelescopeFundamentalGroupoidToStable_map_baseToStageIso_hom] at h
  simpa only [classifyingCategory_comp_as_mul,
    classifyingCategory_id_as_one, mul_one] using h

/-- Include the `n`th finite one-object groupoid into the fundamental
groupoid of the telescope nerve. -/
noncomputable def finiteBGLTelescopeStageFundamentalFunctor
    (R : Type u) [Semiring R] (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
      SSet.FundamentalGroupoid (finiteBGLTelescopeNerve R) :=
  finiteBGLTelescopeFiberInclusion R n ⋙
    SSet.categoryNerveUnit (FiniteBGLTelescopeCategory R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a finite-stage loop, the forward groupoid functor is the original
finite-to-stable classifying functor. -/
theorem finiteBGLTelescopeFundamentalGroupoidToStable_map_stage
    (R : Type u) [Semiring R] (n : ℕ)
    (g : CategoryTheory.End
      (SingleObj.star
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) :
    (finiteBGLTelescopeFundamentalGroupoidToStable R).map
        ((finiteBGLTelescopeStageFundamentalFunctor R n).map g.asHom) =
      (finiteToStableCategoryMap R n).toFunctor.map g.asHom := by
  change (finiteBGLTelescopeFundamentalGroupoidToStable R).map
      ((SSet.categoryNerveUnit
        (FiniteBGLTelescopeCategory R)).map
          ((finiteBGLTelescopeFiberInclusion R n).map g.asHom)) = _
  rw [finiteBGLTelescopeFundamentalGroupoidToStable_map_categoryNerveUnit]
  change (finiteToStableCategoryMap R n).toFunctor.map
      ((finiteBGLTelescopeFiberInclusion R n).map g.asHom).fiber =
    (finiteToStableCategoryMap R n).toFunctor.map g.asHom
  unfold finiteBGLTelescopeFiberInclusion
  rw [Grothendieck.ι_map]
  rw [(finiteToStableCategoryMap R n).toFunctor.map_comp]
  rw [eqToHom_map, classifyingCategory_eqToHom R]
  exact Category.id_comp _

/-- A finite-stage matrix gives a based loop by including it at stage `n`
and conjugating along the canonical base-to-stage isomorphism. -/
noncomputable def finiteBGLTelescopeStageLoopHom
    (R : Type u) [Semiring R] (n : ℕ) :
    (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ →*
      CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (finiteBGLTelescopeBaseVertex R)) :=
  (finiteBGLTelescopeBaseToStageIso R n).symm.conj.toMonoidHom.comp
    (((finiteBGLTelescopeStageFundamentalFunctor R n).mapEnd
      (SingleObj.star
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).comp
      (SingleObj.toEnd ((Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).toMonoidHom)

/-- Finite-stage loop map as conjugation by the canonical base-to-stage
path. -/
theorem finiteBGLTelescopeStageLoopHom_apply
    (R : Type u) [Semiring R] (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    finiteBGLTelescopeStageLoopHom R n g =
      End.of ((finiteBGLTelescopeBaseToStageIso R n).hom ≫
        (finiteBGLTelescopeStageFundamentalFunctor R n).map g ≫
          (finiteBGLTelescopeBaseToStageIso R n).inv) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For a morphism whose target is a canonical stage object, the
target-label based loop is the finite-stage loop of its raw fiber label. -/
theorem finiteBGLTelescopeTargetLabelBasedLoop_at_stage
    (R : Type u) [Semiring R]
    {X : FiniteBGLTelescopeCategory R} {m : ℕ}
    (a : X ⟶ finiteBGLTelescopeStageObject R m) :
    finiteBGLTelescopeTargetLabelBasedLoop R a =
      finiteBGLTelescopeStageLoopHom R m
        (show (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ from
          a.fiber) := by
  apply End.ext
  unfold finiteBGLTelescopeTargetLabelBasedLoop
  rw [finiteBGLTelescopeBaseTo_stage,
    finiteBGLTelescopeTargetLabelHom_at_stage,
    finiteBGLTelescopeStageLoopHom_apply]
  unfold finiteBGLTelescopeBaseToStageIso
    finiteBGLTelescopeBaseToStageHom
    finiteBGLTelescopeStageFundamentalFunctor
  rw [Groupoid.inv_eq_inv]
  rfl

/-- In the groupoid completion, the base-to-`n` path followed by a stage
transition is the base-to-`m` path. -/
theorem finiteBGLTelescopeBaseToStageIso_hom_comp_transition
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    (finiteBGLTelescopeBaseToStageIso R n).hom ≫
        (SSet.categoryNerveUnit
          (FiniteBGLTelescopeCategory R)).map
            (finiteBGLTelescopeStageTransition R f) =
      (finiteBGLTelescopeBaseToStageIso R m).hom := by
  change (SSet.categoryNerveUnit
      (FiniteBGLTelescopeCategory R)).map
        (finiteBGLTelescopeBaseToStageCategoryHom R n) ≫
      (SSet.categoryNerveUnit
        (FiniteBGLTelescopeCategory R)).map
          (finiteBGLTelescopeStageTransition R f) =
    (SSet.categoryNerveUnit
      (FiniteBGLTelescopeCategory R)).map
        (finiteBGLTelescopeBaseToStageCategoryHom R m)
  rw [← Functor.map_comp,
    finiteBGLTelescopeBaseToStage_comp_transition]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse base paths satisfy the equivalent transition identity. -/
theorem finiteBGLTelescopeStageTransition_comp_baseToStageIso_inv
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m) :
    (SSet.categoryNerveUnit
        (FiniteBGLTelescopeCategory R)).map
          (finiteBGLTelescopeStageTransition R f) ≫
        (finiteBGLTelescopeBaseToStageIso R m).inv =
      (finiteBGLTelescopeBaseToStageIso R n).inv := by
  rw [← cancel_epi (finiteBGLTelescopeBaseToStageIso R n).hom]
  rw [← Category.assoc,
    finiteBGLTelescopeBaseToStageIso_hom_comp_transition,
    Iso.hom_inv_id, Iso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Stage loops commute with the groupoid image of a stabilization
transition. -/
theorem finiteBGLTelescopeStageFundamentalFunctor_map_naturality
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m)
    (g : CategoryTheory.End
      (SingleObj.star
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) :
    (finiteBGLTelescopeStageFundamentalFunctor R n).map g.asHom ≫
        (SSet.categoryNerveUnit
          (FiniteBGLTelescopeCategory R)).map
            (finiteBGLTelescopeStageTransition R f) =
      (SSet.categoryNerveUnit
          (FiniteBGLTelescopeCategory R)).map
            (finiteBGLTelescopeStageTransition R f) ≫
        (finiteBGLTelescopeStageFundamentalFunctor R m).map
          (((finiteClassifyingCategoryDiagram R).map f).toFunctor.map g.asHom) := by
  change (SSet.categoryNerveUnit
      (FiniteBGLTelescopeCategory R)).map
        ((finiteBGLTelescopeFiberInclusion R n).map g.asHom) ≫
      (SSet.categoryNerveUnit
        (FiniteBGLTelescopeCategory R)).map
          (finiteBGLTelescopeStageTransition R f) =
    (SSet.categoryNerveUnit
        (FiniteBGLTelescopeCategory R)).map
          (finiteBGLTelescopeStageTransition R f) ≫
      (SSet.categoryNerveUnit
        (FiniteBGLTelescopeCategory R)).map
          ((finiteBGLTelescopeFiberInclusion R m).map
            (((finiteClassifyingCategoryDiagram R).map f).toFunctor.map g.asHom))
  rw [← Functor.map_comp, ← Functor.map_comp,
    finiteBGLTelescopeStageLabel_naturality R f g]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The based finite-stage loop homomorphisms are compatible with every
stabilization transition. -/
theorem finiteBGLTelescopeStageLoopHom_naturality
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m)
    (g : CategoryTheory.End
      (SingleObj.star
        (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) :
    finiteBGLTelescopeStageLoopHom R n g.asHom =
      finiteBGLTelescopeStageLoopHom R m
        (((finiteClassifyingCategoryDiagram R).map f).toFunctor.map g.asHom) := by
  apply End.ext
  rw [finiteBGLTelescopeStageLoopHom_apply,
    finiteBGLTelescopeStageLoopHom_apply]
  let s := (SSet.categoryNerveUnit
    (FiniteBGLTelescopeCategory R)).map
      (finiteBGLTelescopeStageTransition R f)
  have hbase :
      (finiteBGLTelescopeBaseToStageIso R n).hom ≫ s =
        (finiteBGLTelescopeBaseToStageIso R m).hom :=
    finiteBGLTelescopeBaseToStageIso_hom_comp_transition R f
  have hinv :
      s ≫ (finiteBGLTelescopeBaseToStageIso R m).inv =
        (finiteBGLTelescopeBaseToStageIso R n).inv :=
    finiteBGLTelescopeStageTransition_comp_baseToStageIso_inv R f
  have hlabel :
      (finiteBGLTelescopeStageFundamentalFunctor R n).map g.asHom ≫ s =
        s ≫ (finiteBGLTelescopeStageFundamentalFunctor R m).map
          (((finiteClassifyingCategoryDiagram R).map f).toFunctor.map g.asHom) :=
    finiteBGLTelescopeStageFundamentalFunctor_map_naturality R f g
  rw [← hinv]
  rw [← Category.assoc
    ((finiteBGLTelescopeStageFundamentalFunctor R n).map g.asHom)
    s (finiteBGLTelescopeBaseToStageIso R m).inv]
  rw [hlabel]
  rw [Category.assoc s
    ((finiteBGLTelescopeStageFundamentalFunctor R m).map
      (((finiteClassifyingCategoryDiagram R).map f).toFunctor.map g.asHom))
    (finiteBGLTelescopeBaseToStageIso R m).inv]
  rw [← Category.assoc
    (finiteBGLTelescopeBaseToStageIso R n).hom s]
  rw [hbase]

/-- Finite-stage based loops with the opposite convention removed, so a
matrix `g` is represented by the edge labelled `op g⁻¹`. -/
noncomputable def finiteBGLTelescopeNormalizedStageLoopHom
    (R : Type u) [Semiring R] (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) R →*
      CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (finiteBGLTelescopeBaseVertex R)) :=
  (finiteBGLTelescopeStageLoopHom R n).comp
    (MulEquiv.inv'
      (Matrix.GeneralLinearGroup (Fin n) R)).toMonoidHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every target-label based loop is a normalized finite-stage loop, with
matrix given by the inverse of the underlying opposite fiber label. -/
theorem finiteBGLTelescopeTargetLabelBasedLoop_eq_normalizedStage
    (R : Type u) [Semiring R]
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    finiteBGLTelescopeTargetLabelBasedLoop R a =
      finiteBGLTelescopeNormalizedStageLoopHom R Y.base
        (MulOpposite.unop
          (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from
            a.fiber))⁻¹ := by
  let hY := finiteBGLTelescopeStageObject_eq R Y
  cases hY
  rw [finiteBGLTelescopeTargetLabelBasedLoop_at_stage]
  change finiteBGLTelescopeStageLoopHom R Y.base
      (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from
        a.fiber) =
    finiteBGLTelescopeStageLoopHom R Y.base
      (MulOpposite.op
        ((MulOpposite.unop
          (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from
            a.fiber))⁻¹)⁻¹)
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The forward stable-label map sends a normalized finite-stage loop to the
corresponding inverse stable label in the opposite group. -/
@[simp↓]
theorem finiteBGLTelescopeFundamentalToStableOpposite_normalizedStage
    (R : Type u) [Semiring R] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteBGLTelescopeFundamentalToStableOpposite R
        (finiteBGLTelescopeNormalizedStageLoopHom R n g) =
      MulOpposite.op (StableGL.of g)⁻¹ := by
  apply (SingleObj.toEnd ((StableGL R)ᵐᵒᵖ)).injective
  change (eqToIso
      (finiteBGLTelescopeFundamentalGroupoidToStable_obj_base R)).conj
        ((finiteBGLTelescopeFundamentalGroupoidToStable R).mapEnd
          (SSet.FundamentalGroupoid.mk
            (finiteBGLTelescopeBaseVertex R))
          (finiteBGLTelescopeStageLoopHom R n
            (MulOpposite.op g⁻¹))) =
    End.of (MulOpposite.op (StableGL.of g)⁻¹)
  rw [finiteBGLTelescopeFundamentalGroupoidToStable_base_conj]
  apply End.ext
  change (finiteBGLTelescopeFundamentalGroupoidToStable R).map
      ((finiteBGLTelescopeStageLoopHom R n (MulOpposite.op g⁻¹)).asHom) =
    MulOpposite.op (StableGL.of g)⁻¹
  rw [finiteBGLTelescopeStageLoopHom_apply]
  rw [Functor.map_comp, Functor.map_comp]
  rw [finiteBGLTelescopeFundamentalGroupoidToStable_map_baseToStageIso_hom,
    finiteBGLTelescopeFundamentalGroupoidToStable_map_stage R n
      (End.of (MulOpposite.op g⁻¹)),
    finiteBGLTelescopeFundamentalGroupoidToStable_map_baseToStageIso_inv]
  have hNormalized := congrArg
    (fun z : End (SingleObj.star (StableGL R)ᵐᵒᵖ) => z.asHom)
    (finiteToStableCategoryMap_map_normalized g)
  change (finiteToStableCategoryMap R n).toFunctor.map (MulOpposite.op g⁻¹) =
    MulOpposite.op (StableGL.of g)⁻¹ at hNormalized
  rw [hNormalized]
  simp only [classifyingCategory_comp_as_mul,
    classifyingCategory_id_as_one, mul_one, one_mul]

/-- After removing the opposite convention, a normalized finite-stage loop
maps to its stable matrix class. -/
theorem finiteBGLTelescopeFundamentalToStable_normalizedStage
    (R : Type u) [Semiring R] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteBGLTelescopeFundamentalToStable R
        (finiteBGLTelescopeNormalizedStageLoopHom R n g) =
      StableGL.of g := by
  change (MulEquiv.inv' (StableGL R)).symm
      (finiteBGLTelescopeFundamentalToStableOpposite R
        (finiteBGLTelescopeNormalizedStageLoopHom R n g)) = _
  rw [finiteBGLTelescopeFundamentalToStableOpposite_normalizedStage]
  simp only [MulEquiv.inv'_symm_apply, Function.comp_apply,
    MulOpposite.unop_op, inv_inv]

/-- The normalized finite-stage loop homomorphisms form a cocone on the
finite general-linear stabilization diagram. -/
theorem finiteBGLTelescopeNormalizedStageLoopHom_naturality
    (R : Type u) [Semiring R] {n m : ℕ} (f : n ⟶ m)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteBGLTelescopeNormalizedStageLoopHom R n g =
      finiteBGLTelescopeNormalizedStageLoopHom R m
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map f g) := by
  change finiteBGLTelescopeStageLoopHom R n
      (MulOpposite.op g⁻¹) =
    finiteBGLTelescopeStageLoopHom R m
      (MulOpposite.op
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map f g)⁻¹)
  rw [finiteBGLTelescopeStageLoopHom_naturality R f
    (End.of (MulOpposite.op g⁻¹))]
  congr 1
  change MulOpposite.op
      ((finiteGLDiagram.obj (SemiRingCat.of R)).map f g⁻¹) =
    MulOpposite.op
      ((finiteGLDiagram.obj (SemiRingCat.of R)).map f g)⁻¹
  exact congrArg MulOpposite.op
    ((ConcreteCategory.hom
      ((finiteGLDiagram.obj (SemiRingCat.of R)).map f)).map_inv g)

/-- The normalized finite-stage loop homomorphisms as a cocone in
`GrpCat`. -/
noncomputable def finiteBGLTelescopeFundamentalCocone
    (R : Type u) [Semiring R] :
    Limits.Cocone (finiteGLDiagram.obj (SemiRingCat.of R)) where
  pt := GrpCat.of
    (CategoryTheory.End
      (SSet.FundamentalGroupoid.mk
        (finiteBGLTelescopeBaseVertex R)))
  ι :=
    { app := fun n => GrpCat.ofHom
        (finiteBGLTelescopeNormalizedStageLoopHom R n)
      naturality := fun {n m} f => by
        apply GrpCat.hom_ext
        apply MonoidHom.ext
        intro g
        change finiteBGLTelescopeNormalizedStageLoopHom R m
            ((finiteGLDiagram.obj (SemiRingCat.of R)).map f g) =
          finiteBGLTelescopeNormalizedStageLoopHom R n g
        exact (finiteBGLTelescopeNormalizedStageLoopHom_naturality
          R f g).symm }

/-- Universal map from the stable general linear group to the based
fundamental group of the finite-`BGL` telescope. -/
noncomputable def finiteBGLTelescopeStableToFundamentalGrpCatHom
    (R : Type u) [Semiring R] :
    StableGL.functor.obj (SemiRingCat.of R) ⟶
      (finiteBGLTelescopeFundamentalCocone R).pt :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit
    (F := finiteGLDiagram.obj (SemiRingCat.of R))).desc
      (finiteBGLTelescopeFundamentalCocone R)

/-- Underlying homomorphism from `StableGL(R)` to the based telescope
fundamental group. -/
noncomputable def finiteBGLTelescopeStableToFundamental
    (R : Type u) [Semiring R] :
    StableGL R →*
      CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (finiteBGLTelescopeBaseVertex R)) :=
  (finiteBGLTelescopeStableToFundamentalGrpCatHom R).hom

/-- Formula for the universal inverse candidate on a finite stable
representative. -/
theorem finiteBGLTelescopeStableToFundamental_of
    (R : Type u) [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteBGLTelescopeStableToFundamental R (StableGL.of g) =
      finiteBGLTelescopeNormalizedStageLoopHom R n g := by
  have hfac :=
    (GrpCat.FilteredColimits.colimitCoconeIsColimit
      (F := finiteGLDiagram.obj (SemiRingCat.of R))).fac
        (finiteBGLTelescopeFundamentalCocone R) n
  exact ConcreteCategory.congr_hom hfac g

/-- The two comparison homomorphisms compose to the identity on every based
loop coming from a categorical telescope morphism. -/
theorem finiteBGLTelescopeStableToFundamental_fundamentalToStable_categoryBasedLoop
    (R : Type u) [Semiring R]
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    finiteBGLTelescopeStableToFundamental R
        (finiteBGLTelescopeFundamentalToStable R
          (finiteBGLTelescopeCategoryBasedLoop R a)) =
      finiteBGLTelescopeCategoryBasedLoop R a := by
  rw [finiteBGLTelescopeCategoryBasedLoop_eq_targetLabel,
    finiteBGLTelescopeTargetLabelBasedLoop_eq_normalizedStage,
    finiteBGLTelescopeFundamentalToStable_normalizedStage,
    finiteBGLTelescopeStableToFundamental_of]

/-- The comparison composite fixes the based normalization of every nerve
edge generator. -/
theorem finiteBGLTelescopeStableToFundamental_fundamentalToStable_homMk
    (R : Type u) [Semiring R]
    {x y : (finiteBGLTelescopeNerve R).obj (op ⦋0⦌)}
    (e : (finiteBGLTelescopeNerve R).Edge x y) :
    finiteBGLTelescopeStableToFundamental R
        (finiteBGLTelescopeFundamentalToStable R
          (finiteBGLTelescopeBasedNormalize R
            (SSet.FundamentalGroupoid.homMk e))) =
      finiteBGLTelescopeBasedNormalize R
        (SSet.FundamentalGroupoid.homMk e) := by
  rw [finiteBGLTelescopeBasedNormalize_homMk,
    finiteBGLTelescopeStableToFundamental_fundamentalToStable_categoryBasedLoop]

/-- The comparison composite fixes the based normalization of every
fundamental-groupoid morphism. -/
theorem finiteBGLTelescopeStableToFundamental_fundamentalToStable_normalize
    (R : Type u) [Semiring R]
    {x y : SSet.FundamentalGroupoid
      (finiteBGLTelescopeNerve R)} (q : x ⟶ y) :
    finiteBGLTelescopeStableToFundamental R
        (finiteBGLTelescopeFundamentalToStable R
          (finiteBGLTelescopeBasedNormalize R q)) =
      finiteBGLTelescopeBasedNormalize R q := by
  induction q using SSet.FundamentalGroupoid.hom_rec with
  | homMk e =>
      exact finiteBGLTelescopeStableToFundamental_fundamentalToStable_homMk
        R e
  | inv q hq =>
      rw [finiteBGLTelescopeBasedNormalize_inv]
      rw [map_inv, map_inv, hq]
  | comp q r hq hr =>
      rw [finiteBGLTelescopeBasedNormalize_comp]
      rw [map_mul, map_mul, hq, hr]

/-- The colimit-induced map is a left inverse to the forward stable-label
map on the based telescope fundamental group. -/
theorem finiteBGLTelescopeStableToFundamental_comp_fundamentalToStable
    (R : Type u) [Semiring R] :
    (finiteBGLTelescopeStableToFundamental R).comp
        (finiteBGLTelescopeFundamentalToStable R) =
      MonoidHom.id
        (CategoryTheory.End
          (SSet.FundamentalGroupoid.mk
            (finiteBGLTelescopeBaseVertex R))) := by
  apply MonoidHom.ext
  intro q
  change finiteBGLTelescopeStableToFundamental R
      (finiteBGLTelescopeFundamentalToStable R q) = q
  have h :=
    finiteBGLTelescopeStableToFundamental_fundamentalToStable_normalize
      R q.asHom
  rw [finiteBGLTelescopeBasedNormalize_base] at h
  exact h

/-- The forward map is a left inverse to the colimit-induced map from
`StableGL`. -/
theorem finiteBGLTelescopeFundamentalToStable_comp_stableToFundamental
    (R : Type u) [Semiring R] :
    (finiteBGLTelescopeFundamentalToStable R).comp
        (finiteBGLTelescopeStableToFundamental R) =
      MonoidHom.id (StableGL R) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨n, g, hg⟩ := StableGL.exists_finite_rep x
  rw [← hg, MonoidHom.comp_apply,
    finiteBGLTelescopeStableToFundamental_of,
    finiteBGLTelescopeFundamentalToStable_normalizedStage]
  rfl

/-- Canonical multiplicative equivalence between the fundamental group of
the finite-`BGL` categorical telescope and `StableGL(R)`. -/
noncomputable def finiteBGLTelescopeFundamentalMulEquiv
    (R : Type u) [Semiring R] :
    CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (finiteBGLTelescopeBaseVertex R)) ≃*
      StableGL R where
  toFun := finiteBGLTelescopeFundamentalToStable R
  invFun := finiteBGLTelescopeStableToFundamental R
  left_inv q := by
    have h := congrArg
      (fun φ : CategoryTheory.End
          (SSet.FundamentalGroupoid.mk
            (finiteBGLTelescopeBaseVertex R)) →*
            CategoryTheory.End
              (SSet.FundamentalGroupoid.mk
                (finiteBGLTelescopeBaseVertex R)) => φ q)
      (finiteBGLTelescopeStableToFundamental_comp_fundamentalToStable R)
    simpa using h
  right_inv g := by
    have h := congrArg
      (fun φ : StableGL R →* StableGL R => φ g)
      (finiteBGLTelescopeFundamentalToStable_comp_stableToFundamental R)
    simpa using h
  map_mul' x y :=
    (finiteBGLTelescopeFundamentalToStable R).map_mul x y

/-- The ordinary topological fundamental group of the finite-`BGL`
categorical telescope is canonically `StableGL(R)`. -/
noncomputable def ordinaryFiniteBGLTelescopeFundamentalMulEquiv
    (R : Type u) [Semiring R] :
    FundamentalGroup (ordinaryFiniteBGLTelescope R)
        (ordinaryFiniteBGLTelescopeBasepoint R) ≃*
      StableGL R :=
  (SSet.realizationFundamentalGroupoidFunctorEndMulEquiv
    (finiteBGLTelescopeNerve R)
    (finiteBGLTelescopeBaseVertex R)).symm.trans
      (finiteBGLTelescopeFundamentalMulEquiv R)

end StableGL
end AlgebraicKTheory

end
