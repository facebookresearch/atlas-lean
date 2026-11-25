/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
Original authors: @junekim623, Muse
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.CategoryTheory.Sites.Over
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits

/-!
# Restriction and local-surjectivity toolkit for sheaves of modules

General-site helpers shared by the finite-type, coherence, and finite-presentation
developments. Every declaration is stated over an independent site
(`{D : Type w} [Category.{v₂} D]`, coefficients in `AddCommGrpCat.{u}`) so it also
applies on slice categories and iterated slices without extra hypotheses.

Contents:

* `locallySurjective_of_epi` / `epi_of_locallySurjective`: an epi of sheaves of
  modules is locally surjective on underlying presheaves, and conversely.
* `locallySurjective_over` / `epi_over_of_epi`: both directions are preserved by
  restriction to a slice (`overFunctor`), with no binary-product hypothesis.
* `locallySurjective_overMap` / `epi_overMap_of_epi`: the same along an arrow of
  the base site (`overMap`), without pullbacks.
* `overOverEquivalence`: the iterated-slice equivalence
  `SheafOfModules (S.over Y.left) ≌ SheafOfModules ((S.over X).over Y)`.
* `preservesKernel_overFunctor`: restriction to a slice preserves
  kernels (commutation iso is Mathlib's `PreservesKernel.iso`).
* `mapCokernelPiOverIsColimit`: restriction to a slice sends a cokernel
  projection to a cokernel projection.
* `mapCokernelPiOverMapIsColimit` /
  `preservesColimit_parallelPair_overMap`: restriction along a base arrow
  sends cokernel projections to cokernel projections (hence preserves the
  colimit of a `parallelPair` cokernel diagram), without pullbacks.
* `Presentation.mapOfPreserves` / `Presentation.mapOfPreserves_isFinite`: transport a
  presentation along a colimit-preserving functor; a transported finite
  presentation is finite.
* `LocalGeneratorsData.IsFiniteType.shrink`: finiteness descends through
  `LocalGeneratorsData.shrink`.
* `transported_section_eval`: sections of transported generators evaluate as
  restrictions of the original sections.
-/

@[expose] public section

universe u w v₂ w' v₂'

open _root_.CategoryTheory CategoryTheory Limits

namespace SheafOfModules

/-- An epi of sheaves of modules is locally surjective on underlying
presheaves. The forgetful functor `toSheaf` preserves colimits
(`preservesColimitsOfShape_toSheaf`), hence epis, and for abelian sheaves
epi is local surjectivity (`Sheaf.isLocallySurjective_iff_epi'`). -/
lemma locallySurjective_of_epi {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} S}
    (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf S.obj).map f.val) := by
  have : PreservesColimitsOfShape WalkingSpan (SheafOfModules.toSheaf S) :=
    preservesColimitsOfShape_toSheaf
  have : (SheafOfModules.toSheaf S).PreservesEpimorphisms :=
    preservesEpimorphisms_of_preservesColimitsOfShape _
  have hepi : Epi ((SheafOfModules.toSheaf S).map f) := inferInstance
  exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
    ((SheafOfModules.toSheaf S).map f)).mpr hepi

/-- A locally surjective morphism of sheaves of modules is an epimorphism,
without using sheafification. -/
lemma epi_of_locallySurjective {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    {A B : SheafOfModules.{u} S} (g : A ⟶ B)
    (h : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf S.obj).map g.val)) : Epi g := by
  let _ : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf S).map g) := h
  have hg : Epi ((SheafOfModules.toSheaf S).map g) := inferInstance
  exact (SheafOfModules.toSheaf S).epi_of_epi_map hg

/-- Local surjectivity is preserved by restriction to a slice.
Given a cover trivializing a section over the base, the same data works over
the slice, using that covers of the slice are detected on the base. -/
lemma locallySurjective_over {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {R : Sheaf K RingCat.{u}}
    {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (h : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf R.obj).map f.val))
    (X : D) :
    Presheaf.IsLocallySurjective (K.over X)
      ((PresheafOfModules.toPresheaf (R.over X).obj).map
        ((_root_.SheafOfModules.overFunctor R X).map f).val) := by
  have := h
  exact Presheaf.isLocallySurjective_whisker (K.over X) K (Over.forget X)
    ((PresheafOfModules.toPresheaf R.obj).map f.val)

/-- Restriction to a slice preserves epis, with no binary-product hypothesis:
combine the two directions above. The site and module universes are independent
so this helper also applies on iterated slices. -/
lemma epi_over_of_epi {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} S} (f : M ⟶ N) [Epi f] (X : D) :
    Epi ((_root_.SheafOfModules.overFunctor S X).map f) := by
  apply epi_of_locallySurjective
  apply locallySurjective_over
  exact locallySurjective_of_epi f

/-- Local surjectivity is preserved by `overMap` along an arrow of the base
site. This mirrors `locallySurjective_over` (which handles `overFunctor`,
i.e. pushforward along `Over.forget`); here we push forward along `Over.map g`.
Both are `Presheaf.isLocallySurjective_whisker` for the cocontinuous
`Over.forget` / `Over.map` functors. -/
lemma locallySurjective_overMap {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    {Y : D} {M N : SheafOfModules.{u} (S.over Y)} (f : M ⟶ N)
    (h : Presheaf.IsLocallySurjective (K.over Y)
      ((PresheafOfModules.toPresheaf (S.over Y).obj).map f.val))
    {X : D} (g : X ⟶ Y) :
    Presheaf.IsLocallySurjective (K.over X)
      ((PresheafOfModules.toPresheaf (S.over X).obj).map
        ((_root_.SheafOfModules.overMap S g).map f).val) := by
  have := h
  exact Presheaf.isLocallySurjective_whisker (K.over X) (K.over Y) (Over.map g)
    ((PresheafOfModules.toPresheaf (S.over Y).obj).map f.val)

/-- Restriction along a base arrow preserves epis without pullbacks. -/
lemma epi_overMap_of_epi {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [∀ X : D, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X : D, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {Y : D} {M N : SheafOfModules.{u} (S.over Y)} (f : M ⟶ N) [Epi f]
    {X : D} (g : X ⟶ Y) :
    Epi ((_root_.SheafOfModules.overMap S g).map f) := by
  apply epi_of_locallySurjective
  apply locallySurjective_overMap
  exact locallySurjective_of_epi f

/-- Restriction to a slice is additive; zero preservation follows from
Mathlib's `Functor.preservesZeroMorphisms_of_additive`. This shared instance
supplies the `Additive` (hence `PreservesZeroMorphisms`) facts at the
`overFunctor` use sites, which are `inferInstance` calls. -/
instance overFunctor_additive {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} (S : Sheaf K RingCat.{u}) (X : D) :
    (_root_.SheafOfModules.overFunctor S X).Additive where
  map_add := by
    intro A B f g
    ext Y y
    rfl

/-- Restriction along a base arrow is additive; zero preservation follows from
Mathlib's `Functor.preservesZeroMorphisms_of_additive`. This shared instance
supplies the `Additive` facts at the `overMap` use sites, which are
`inferInstance` calls (two use sites keep a `.{u}` ascription, with an
`inferInstance` proof, for universe pinning: `Coherent.lean` and the
`MathlibExtTest` transport client). -/
instance overMap_additive {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} (S : Sheaf K RingCat.{u}) {X Y : D} (f : X ⟶ Y) :
    (_root_.SheafOfModules.overMap S f).Additive where
  map_add := by
    intro A B g h
    ext U x
    rfl

/-- Restriction to a slice preserves the kernel of a specified map. -/
instance preservesKernel_overFunctor {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    {M N : SheafOfModules.{u} S} (φ : M ⟶ N) (X : D) :
    PreservesLimit (parallelPair φ 0) (_root_.SheafOfModules.overFunctor S X) := by
  have hA : PreservesLimit (parallelPair φ 0)
      (_root_.SheafOfModules.overFunctor S X ⋙ SheafOfModules.forget (S.over X)) := by
    constructor
    intro c hc
    refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits
      (F := parallelPair φ 0 ⋙ _root_.SheafOfModules.overFunctor S X ⋙
        SheafOfModules.forget (S.over X))
      (((_root_.SheafOfModules.overFunctor S X ⋙
        SheafOfModules.forget (S.over X)).mapCone c)) (fun U' => ?_)⟩
    change IsLimit ((SheafOfModules.forget S ⋙
      PresheafOfModules.evaluation S.obj ((Over.forget X).op.obj U') ⋙
        ModuleCat.restrictScalars (RingHom.id _)).mapCone c)
    exact isLimitOfPreserves _ hc
  have hB : ReflectsLimit (parallelPair φ 0 ⋙ _root_.SheafOfModules.overFunctor S X)
      (SheafOfModules.forget (S.over X)) := inferInstance
  exact preservesLimit_of_reflects_of_preserves (_root_.SheafOfModules.overFunctor S X)
    (SheafOfModules.forget (S.over X))

/-- Doubly restricted sheaves `(M.over X).over Y` identify with
`M.over Y.left` through `Over.iteratedSliceEquiv` and the identity ring maps. -/
noncomputable abbrev overOverEquivalence {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    {X : D} (Y : Over X) :
    SheafOfModules.{u} (S.over Y.left) ≌
      SheafOfModules.{u} ((S.over X).over Y) :=
  _root_.SheafOfModules.pushforwardPushforwardEquivalence
    (Over.iteratedSliceEquiv Y)
    (S := (S.over X).over Y) (R := S.over Y.left)
    (𝟙 _) (𝟙 _) (by ext : 2; exact S.1.map_id _) (by ext : 2; exact S.1.map_id _)

/-- Shared cokernel step for `mapCokernelPiOverIsColimit` and
`mapCokernelPiOverMapIsColimit`: an epi- and kernel-preserving additive
functor sends a cokernel projection to a cokernel projection, via exactness
of the mapped kernel/cokernel sequences. -/
noncomputable def isColimitMapCokernelPiOfEpiOfKernel
    {D₁ : Type w} [Category.{v₂} D₁]
    {K₁ : GrothendieckTopology D₁} {S₁ : Sheaf K₁ RingCat.{u}}
    [HasSheafify K₁ AddCommGrpCat.{u}]
    [K₁.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D₂ : Type w'} [Category.{v₂'} D₂]
    {K₂ : GrothendieckTopology D₂} {S₂ : Sheaf K₂ RingCat.{u}}
    [HasSheafify K₂ AddCommGrpCat.{u}]
    [K₂.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} S₁ ⥤ SheafOfModules.{u} S₂) [F.Additive]
    (hepi : F.PreservesEpimorphisms)
    (hker : ∀ {A B : SheafOfModules.{u} S₁} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) F)
    {M N : SheafOfModules.{u} S₁} (φ : M ⟶ N) :
    IsColimit (CokernelCofork.ofπ (F.map (Limits.cokernel.π φ))
      (show F.map φ ≫ F.map (Limits.cokernel.π φ) = 0 by
        rw [← F.map_comp, Limits.cokernel.condition, Functor.map_zero])) := by
  haveI : Functor.PreservesZeroMorphisms F := inferInstance
  haveI : F.PreservesEpimorphisms := hepi
  haveI : ∀ {A B : SheafOfModules.{u} S₁} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) F := fun f => hker f
  haveI : F.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels F
  haveI : PreservesColimit (parallelPair φ 0) F :=
    Functor.PreservesHomology.preservesCokernel F φ
  exact isColimitOfHasCokernelOfPreservesColimit F φ


/-- Deprecated alias for `isColimitMapCokernelPiOfEpiOfKernel`. -/
@[deprecated isColimitMapCokernelPiOfEpiOfKernel (since := "2026-10-29"),
  nolint defsWithUnderscore]
alias isColimit_mapCokernelPi_of_epi_of_kernel := isColimitMapCokernelPiOfEpiOfKernel


/-- Restricting a cokernel projection to a slice remains a cokernel projection. -/
noncomputable def mapCokernelPiOverIsColimit
    {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X : D, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X : D, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} S} (φ : M ⟶ N) (X : D) :
    IsColimit (CokernelCofork.ofπ
      ((_root_.SheafOfModules.overFunctor S X).map (Limits.cokernel.π φ))
      (show (_root_.SheafOfModules.overFunctor S X).map φ ≫
          (_root_.SheafOfModules.overFunctor S X).map (Limits.cokernel.π φ) = 0 by
        rw [← (_root_.SheafOfModules.overFunctor S X).map_comp, Limits.cokernel.condition]
        ext U'
        rfl)) := by
  exact isColimitMapCokernelPiOfEpiOfKernel
    (_root_.SheafOfModules.overFunctor S X)
    ⟨by
      intro A B f hf
      exact epi_over_of_epi f X⟩
    (fun f => preservesKernel_overFunctor f X) φ

/-- Finiteness descends through `LocalGeneratorsData.shrink`: since the shrunk
generators are a subfamily of the original ones, finiteness is inherited
pointwise. -/
theorem LocalGeneratorsData.IsFiniteType.shrink {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [∀ X : D, HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X : D, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} S} (q : M.LocalGeneratorsData)
    (hq : q.IsFiniteType) :
    q.shrink.IsFiniteType where
  isFiniteType i := hq.isFiniteType (i.2.choose)

/-- Sections of transported generators evaluate as restrictions of the original
sections. -/
lemma transported_section_eval {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [∀ X : D, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X : D, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {Y V : D} {M : SheafOfModules.{u} S}
    (G : (M.over Y).GeneratingSections) (q : V ⟶ Y) [HasPullbacks D]
    (k : G.I) (U' : (Over V)ᵒᵖ) :
    (((G.map (_root_.SheafOfModules.overMap S q)
      (_root_.SheafOfModules.overMapUnitIso q).symm).ofEpi
      ((_root_.SheafOfModules.overFunctorMap S q).app M).hom).s k).eval U'
      = (G.s k).eval (Opposite.op (Over.mk (U'.unop.hom ≫ q))) := by
  have key : SheafOfModules.ιFree (R := S.over V) k ≫
        G.mapFreeHom (_root_.SheafOfModules.overMap S q)
          (_root_.SheafOfModules.overMapUnitIso q).symm
      = (_root_.SheafOfModules.overMap S q).map (SheafOfModules.ιFree k ≫ G.π) := by
    unfold SheafOfModules.GeneratingSections.mapFreeHom
    rw [← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom,
      Category.assoc, ← Functor.map_comp, SheafOfModules.overMapUnitIso]
    change (Iso.refl (_root_.SheafOfModules.unit (S.over V))).symm.hom ≫ _ = _
    exact Category.id_comp _
  have h2 : ((_root_.SheafOfModules.overMap S q).obj (M.over Y)).unitHomEquiv.symm
        ((G.map (_root_.SheafOfModules.overMap S q)
          (_root_.SheafOfModules.overMapUnitIso q).symm).s k)
      = (_root_.SheafOfModules.overMap S q).map (SheafOfModules.ιFree k ≫ G.π) := by
    have e1 : (G.map (_root_.SheafOfModules.overMap S q)
      (_root_.SheafOfModules.overMapUnitIso q).symm).s k
        = ((_root_.SheafOfModules.overMap S q).obj (M.over Y)).freeHomEquiv
          (G.mapFreeHom (_root_.SheafOfModules.overMap S q)
            (_root_.SheafOfModules.overMapUnitIso q).symm) k := rfl
    rw [e1, show ((_root_.SheafOfModules.overMap S q).obj (M.over Y)).freeHomEquiv
        (G.mapFreeHom (_root_.SheafOfModules.overMap S q)
          (_root_.SheafOfModules.overMapUnitIso q).symm) k
        = ((_root_.SheafOfModules.overMap S q).obj (M.over Y)).unitHomEquiv
          (SheafOfModules.ιFree k ≫ G.mapFreeHom (_root_.SheafOfModules.overMap S q)
            (_root_.SheafOfModules.overMapUnitIso q).symm) from rfl,
      Equiv.symm_apply_apply, key]
  have hmapsec : (G.map (_root_.SheafOfModules.overMap S q)
    (_root_.SheafOfModules.overMapUnitIso q).symm).s k
      = ((_root_.SheafOfModules.overMap S q).obj (M.over Y)).unitHomEquiv
        ((_root_.SheafOfModules.overMap S q).map (SheafOfModules.ιFree k ≫ G.π)) := by
    have h3 := congrArg ((_root_.SheafOfModules.overMap S q).obj (M.over Y)).unitHomEquiv h2
    rwa [Equiv.apply_symm_apply] at h3
  have hsymm : SheafOfModules.ιFree (R := S.over Y) k ≫ G.π
      = (M.over Y).unitHomEquiv.symm (G.s k) := by
    have h := SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
      (M := M.over Y) (f := G.π) (i := k)
    simpa using h.symm
  -- Unfold the outer layers: `ofEpi` and the restriction iso are transparent.
  have hunfold : (((G.map (_root_.SheafOfModules.overMap S q)
    (_root_.SheafOfModules.overMapUnitIso q).symm).ofEpi
      ((_root_.SheafOfModules.overFunctorMap S q).app M).hom).s k).eval U'
      = (((_root_.SheafOfModules.overMap S q).map ((M.over Y).unitHomEquiv.symm (G.s k))).val.app
        U' (1 : (S.over V).obj.obj U')) := by
    change (((_root_.SheafOfModules.overFunctorMap S q).app M).hom.val.app U'
      (((G.map (_root_.SheafOfModules.overMap S q)
        (_root_.SheafOfModules.overMapUnitIso q).symm).s k).eval U')) = _
    rw [hmapsec]
    change (((_root_.SheafOfModules.overFunctorMap S q).app M).hom.val.app U'
      ((((_root_.SheafOfModules.overMap S q).map (SheafOfModules.ιFree k ≫ G.π)).val.app) U'
        (1 : (S.over V).obj.obj U'))) = _
    rw [hsymm]
    rfl
  rw [hunfold]
  change ((((M.over Y).unitHomEquiv.symm (G.s k))).val.app
    ((Over.map q).op.obj U') (1 : (S.over V).obj.obj U'))
    = (G.s k).eval (Opposite.op (Over.mk (U'.unop.hom ≫ q)))
  have hss : (M.over Y).unitHomEquiv ((M.over Y).unitHomEquiv.symm (G.s k))
      = G.s k := Equiv.apply_symm_apply _ _
  have hco := SheafOfModules.unitHomEquiv_apply_coe (M := M.over Y)
    ((M.over Y).unitHomEquiv.symm (G.s k)) ((Over.map q).op.obj U')
  rw [hss] at hco
  exact hco.symm

/-- Restricting a cokernel projection along a base arrow remains a cokernel
projection. -/
noncomputable def mapCokernelPiOverMapIsColimit
    {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [∀ X : D, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X : D, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {Y : D} {M N : SheafOfModules.{u} (S.over Y)} (φ : M ⟶ N)
    {X : D} (g : X ⟶ Y) :
    IsColimit (CokernelCofork.ofπ
      ((_root_.SheafOfModules.overMap S g).map (Limits.cokernel.π φ))
      (show (_root_.SheafOfModules.overMap S g).map φ ≫
          (_root_.SheafOfModules.overMap S g).map (Limits.cokernel.π φ) = 0 by
        rw [← (_root_.SheafOfModules.overMap S g).map_comp, Limits.cokernel.condition]
        ext U'
        rfl)) := by
  exact isColimitMapCokernelPiOfEpiOfKernel
    (_root_.SheafOfModules.overMap S g)
    ⟨by
      intro A B f hf
      exact epi_overMap_of_epi f g⟩
    (fun {A B} f => by
      have hA : PreservesLimit (parallelPair f 0)
          (_root_.SheafOfModules.overMap S g ⋙
            SheafOfModules.forget (S.over X)) := by
        constructor
        intro c hc
        refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits
          (F := parallelPair f 0 ⋙ _root_.SheafOfModules.overMap S g ⋙
            SheafOfModules.forget (S.over X))
          (((_root_.SheafOfModules.overMap S g ⋙
            SheafOfModules.forget (S.over X)).mapCone c)) (fun U' => ?_)⟩
        change IsLimit ((SheafOfModules.forget (S.over Y) ⋙
          PresheafOfModules.evaluation (S.over Y).obj ((Over.map g).op.obj U') ⋙
            ModuleCat.restrictScalars (RingHom.id _)).mapCone c)
        exact isLimitOfPreserves _ hc
      have hB : ReflectsLimit
          (parallelPair f 0 ⋙ _root_.SheafOfModules.overMap S g)
          (SheafOfModules.forget (S.over X)) := inferInstance
      exact preservesLimit_of_reflects_of_preserves
        (_root_.SheafOfModules.overMap S g)
        (SheafOfModules.forget (S.over X))) φ

/-- Restriction along a base arrow preserves the colimit of a `parallelPair`
cokernel diagram. -/
lemma preservesColimit_parallelPair_overMap
    {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [∀ X : D, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X : D, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {Y : D} {M N : SheafOfModules.{u} (S.over Y)} (φ : M ⟶ N)
    {X : D} (g : X ⟶ Y) :
    PreservesColimit (parallelPair φ 0) (_root_.SheafOfModules.overMap S g) := by
  have hcolim : IsColimit
      (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ)) :=
    cokernelIsCokernel φ
  have hmap : IsColimit (CokernelCofork.ofπ ((_root_.SheafOfModules.overMap S g).map (cokernel.π φ))
      (show (_root_.SheafOfModules.overMap S g).map φ ≫
          (_root_.SheafOfModules.overMap S g).map (Limits.cokernel.π φ) = 0 by
        rw [← (_root_.SheafOfModules.overMap S g).map_comp, cokernel.condition]
        ext U'
        rfl)) :=
    mapCokernelPiOverMapIsColimit φ g
  have hmapCocone : IsColimit ((_root_.SheafOfModules.overMap S g).mapCocone
      (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ))) :=
    (CokernelCofork.isColimitMapCoconeEquiv _ _).symm hmap
  exact preservesColimit_of_preserves_colimit_cocone hcolim hmapCocone

/-- Transport a presentation along a colimit-preserving functor: the image of
the generator epi, with relations transported through the free comparison
isos. Needs only shape-colimit preservation for the two discrete index types
plus preservation of the single relation colimit. This cannot use Mathlib's
`Presentation.map`, which needs `PreservesColimitsOfSize.{u, u}` (whose
derivation needs `HasPullbacks`, absent at the call site). -/
noncomputable def Presentation.mapOfPreserves
    {D₁ : Type w} [Category.{v₂} D₁]
    {K₁ : GrothendieckTopology D₁} {S₁ : Sheaf K₁ RingCat.{u}}
    [HasSheafify K₁ AddCommGrpCat.{u}]
    [K₁.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D₂ : Type w'} [Category.{v₂'} D₂]
    {K₂ : GrothendieckTopology D₂} {S₂ : Sheaf K₂ RingCat.{u}}
    [HasSheafify K₂ AddCommGrpCat.{u}]
    [K₂.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} S₁} (P : M.Presentation)
    (F : SheafOfModules.{u} S₁ ⥤ SheafOfModules.{u} S₂)
    [F.Additive]
    [PreservesColimitsOfShape (Discrete P.relations.I) F]
    [PreservesColimitsOfShape (Discrete P.generators.I) F]
    (η : _root_.SheafOfModules.unit S₂ ≅ F.obj (_root_.SheafOfModules.unit S₁))
    (hF : PreservesColimit
      (parallelPair ((_root_.SheafOfModules.freeHomEquiv _).symm
        P.relations.s ≫ kernel.ι P.generators.π) 0) F) :
    (F.obj M).Presentation := by
  letI : F.PreservesZeroMorphisms := inferInstance
  let eR := _root_.SheafOfModules.mapFreeIso F P.relations.I η
  let eG := _root_.SheafOfModules.mapFreeIso F P.generators.I η
  let d := eR.hom ≫ F.map ((_root_.SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
    kernel.ι P.generators.π) ≫ eG.inv
  let g := eG.hom ≫ F.map P.generators.π
  have hdg : d ≫ g = 0 := by
    dsimp [d, g]
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← F.map_comp]
    have hz : ((_root_.SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
        kernel.ι P.generators.π) ≫ P.generators.π = 0 := by simp
    rw [hz, F.map_zero]
    exact comp_zero
  refine _root_.SheafOfModules.presentationOfIsCokernelFree d g hdg ?_
  let Kp := parallelPair ((_root_.SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
    kernel.ι P.generators.π) 0
  haveI : PreservesColimit Kp F := hF
  refine IsColimit.equivOfNatIsoOfIso
    (parallelPairIsoMk eR.symm eG.symm
      (by simp [d]) (by simp)) _ _ ?_ (isColimitOfPreserves F P.isColimit)
  exact (Cocone.ext (Iso.refl _) <| by rintro (_ | _)
    <;> simp [d, g, ← Functor.map_comp])

/-- A transported finite presentation is finite. -/
instance Presentation.mapOfPreserves_isFinite
    {D₁ : Type w} [Category.{v₂} D₁]
    {K₁ : GrothendieckTopology D₁} {S₁ : Sheaf K₁ RingCat.{u}}
    [HasSheafify K₁ AddCommGrpCat.{u}]
    [K₁.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {D₂ : Type w'} [Category.{v₂'} D₂]
    {K₂ : GrothendieckTopology D₂} {S₂ : Sheaf K₂ RingCat.{u}}
    [HasSheafify K₂ AddCommGrpCat.{u}]
    [K₂.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} S₁} (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} S₁ ⥤ SheafOfModules.{u} S₂)
    [F.Additive]
    [PreservesColimitsOfShape (Discrete P.relations.I) F]
    [PreservesColimitsOfShape (Discrete P.generators.I) F]
    (η : _root_.SheafOfModules.unit S₂ ≅ F.obj (_root_.SheafOfModules.unit S₁))
    (hF : PreservesColimit
      (parallelPair ((_root_.SheafOfModules.freeHomEquiv _).symm
        P.relations.s ≫ kernel.ι P.generators.π) 0) F) :
    (P.mapOfPreserves F η hF).IsFinite where
  isFiniteType_generators := by
    exact ⟨inferInstanceAs (Finite P.generators.I)⟩
  isFiniteType_relations := by
    exact ⟨inferInstanceAs (Finite P.relations.I)⟩

end SheafOfModules

end
