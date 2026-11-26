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
# Slice restriction and local surjectivity of module sheaves

Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`. A morphism of module sheaves is locally
surjective when every target section lifts on a covering sieve. Local surjectivity implies
epimorphy; the converse holds with additive sheafification and the locally-bijective
comparison on `K`.

Restriction to a slice and restriction along a base arrow preserve local surjectivity. These
functors are additive and preserve kernels; with additive sheafification and the
locally-bijective comparison on the base and slice sites, they preserve epimorphisms and
cokernel projections. Direct and iterated slice module categories have a canonical
equivalence.

A module-sheaf presentation can be transported by an additive functor preserving its two
generator coproducts, its relation cokernel diagram, and the unit sheaf. Finite presentations
remain finite. The site and module-carrier universes are independent.
-/

@[expose] public section

universe u w v₂ w' v₂'

open _root_.CategoryTheory CategoryTheory Limits

namespace SheafOfModules

/-- Let `D : Type w` have morphism universe `v₂`, `K` a Grothendieck topology, and `S : Sheaf K
RingCat.{u}`. Assume additive sheafification of `AddCommGrpCat.{u}`-valued presheaves and
`K.WEqualsLocallyBijective AddCommGrpCat.{u}`. For `f : M → N` between module sheaves of
carrier universe `u`, epimorphy of `f` implies local surjectivity of its underlying additive
presheaf morphism on `K`. -/
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

/-- Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`. For `g : A → B` between module sheaves of
carrier universe `u`, if every target section locally lifts through the underlying additive
presheaf morphism, then `g` is an epimorphism. The local-lifting hypothesis is
`Presheaf.IsLocallySurjective K ((PresheafOfModules.toPresheaf S.obj).map g.val)`. -/
lemma epi_of_locallySurjective {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    {A B : SheafOfModules.{u} S} (g : A ⟶ B)
    (h : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf S.obj).map g.val)) : Epi g := by
  let _ : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf S).map g) := h
  have hg : Epi ((SheafOfModules.toSheaf S).map g) := inferInstance
  exact (SheafOfModules.toSheaf S).epi_of_epi_map hg

/-- On a ringed site `(D,K,R)`, let `f : M → N` be a module-sheaf morphism whose underlying
additive presheaf map is locally surjective. For `X∈D`, the map `(SheafOfModules.overFunctor R
X).map f : M.over X → N.over X` is locally surjective on `K.over X`. -/
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

/-- Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`. Assume additive sheafification and the
locally-bijective comparison on `K`. For an epimorphism `f : M → N` of module sheaves of
carrier universe `u` and `X∈D`, `(SheafOfModules.overFunctor S X).map f` is an epimorphism
over `S.over X`. -/
lemma epi_over_of_epi {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} S} (f : M ⟶ N) [Epi f] (X : D) :
    Epi ((_root_.SheafOfModules.overFunctor S X).map f) := by
  apply epi_of_locallySurjective
  apply locallySurjective_over
  exact locallySurjective_of_epi f

/-- Let `(D,K)` be a site, `S` a ring sheaf, `g : X → Y`, and `f : M → N` a module-sheaf morphism
over `S.over Y`. If its underlying additive presheaf map is locally surjective on `K.over Y`,
then `(SheafOfModules.overMap S g).map f` is locally surjective on `K.over X`. -/
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

/-- Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`. Assume additive sheafification and the
locally-bijective comparison on every `K.over X`. For `g : X → Y` and an epimorphism `f : M →
N` between module sheaves over `S.over Y`, the restricted morphism `(SheafOfModules.overMap S
g).map f` is an epimorphism over `S.over X`. -/
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

/-- For a site `(D,K)`, a ring sheaf `S : Sheaf K RingCat.{u}`, and `X∈D`, the functor
`SheafOfModules.overFunctor S X` is additive: for module-sheaf morphisms `f,g` with the same
source and target, it sends `f+g` to the sum of their restrictions. In particular, it
preserves the zero morphism. -/
instance overFunctor_additive {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} (S : Sheaf K RingCat.{u}) (X : D) :
    (_root_.SheafOfModules.overFunctor S X).Additive where
  map_add := by
    intro A B f g
    ext Y y
    rfl

/-- For a site `(D,K)`, a ring sheaf `S : Sheaf K RingCat.{u}`, and `f : X → Y`, the functor
`SheafOfModules.overMap S f` from module sheaves over `S.over Y` to those over `S.over X` is
additive. It preserves sums of morphisms and the zero morphism. -/
instance overMap_additive {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} (S : Sheaf K RingCat.{u}) {X Y : D} (f : X ⟶ Y) :
    (_root_.SheafOfModules.overMap S f).Additive where
  map_add := by
    intro A B g h
    ext U x
    rfl

/-- On a site `(D,K)` with `S : Sheaf K RingCat.{u}`, let `φ : M → N` be a morphism of module
sheaves of carrier universe `u`. For `X∈D`, the functor `SheafOfModules.overFunctor S X`
preserves the limit of `parallelPair φ 0`, hence preserves the kernel of `φ`. -/
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

/-- Let `D : Type w` have morphism universe `v₂`, `K` a Grothendieck topology, `S : Sheaf K
RingCat.{u}`, `X∈D`, and `Y∈Over X`. The canonical slice equivalence induces
`SheafOfModules.{u}(S.over Y.left) ≌ SheafOfModules.{u}((S.over X).over Y)`, using the
identity coefficient-ring maps on the identified base objects. -/
noncomputable abbrev overOverEquivalence {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    {X : D} (Y : Over X) :
    SheafOfModules.{u} (S.over Y.left) ≌
      SheafOfModules.{u} ((S.over X).over Y) :=
  _root_.SheafOfModules.pushforwardPushforwardEquivalence
    (Over.iteratedSliceEquiv Y)
    (S := (S.over X).over Y) (R := S.over Y.left)
    (𝟙 _) (𝟙 _) (by ext : 2; exact S.1.map_id _) (by ext : 2; exact S.1.map_id _)

/-- Let `(D₁,K₁,S₁)` and `(D₂,K₂,S₂)` be ringed sites, with rings and module carriers in universe
`u`, and additive sheafification with the locally-bijective comparison on both sites. Suppose
an additive functor `F : SheafOfModules S₁ → SheafOfModules S₂` preserves epimorphisms and the
limits of every `parallelPair f 0`. For any `φ : M → N`, the cofork with point `F(coker φ)`
and projection `F(cokernel.π φ)` is a colimit cofork of `F(φ)` and zero. -/
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


/-- Let two ringed sites have additive sheafification and the locally-bijective comparison at a
common module universe `u`. For an additive functor `F` between their module-sheaf categories,
assume preservation of epimorphisms and every kernel limit `parallelPair f 0`. Then for each
morphism `φ`, the image `F(cokernel.π φ)` exhibits `F(coker φ)` as a cokernel of `F(φ)`, with
relation `F(φ) ≫ F(cokernel.π φ)=0`. -/
@[deprecated isColimitMapCokernelPiOfEpiOfKernel (since := "2026-10-29"),
  nolint defsWithUnderscore]
alias isColimit_mapCokernelPi_of_epi_of_kernel := isColimitMapCokernelPiOfEpiOfKernel


/-- Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`. Assume additive sheafification and the
locally-bijective comparison on `K` and all `K.over X`. For `φ : M → N` between module sheaves
of carrier universe `u` and `X∈D`, set `F=SheafOfModules.overFunctor S X`. The cofork with
point `F(coker φ)` and projection `F(cokernel.π φ)` is a colimit cofork of `F(φ)` and zero. -/
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

/-- Let `(D,K)` be a site, `S : Sheaf K RingCat.{u}`, and assume weak additive sheafification and
the locally-bijective comparison on every slice `K.over X`. For a module sheaf `M` and local
generator data `q`, if every chart's generating family is finite (`q.IsFiniteType`), then
`q.shrink.IsFiniteType`. Each shrunk chart uses a selected generating family from `q`. -/
theorem LocalGeneratorsData.IsFiniteType.shrink {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [∀ X : D, HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X : D, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} S} (q : M.LocalGeneratorsData)
    (hq : q.IsFiniteType) :
    q.shrink.IsFiniteType where
  isFiniteType i := hq.isFiniteType (i.2.choose)

/-- Let `(D,K)` be a site with pullbacks, `S : Sheaf K RingCat.{u}`, and additive sheafification
with the locally-bijective comparison on all slices. For a module sheaf `M`, a generating
family `G` of `M.over Y`, and `q : V → Y`, transport `G` along `overMap S q` and the canonical
comparison to `M.over V`. For `k∈G.I` and `U'∈(Over V)ᵒᵖ`, its generator value equals `(G.s
k).eval (op (Over.mk (U'.unop.hom ≫ q)))`: the source section evaluated on the composite arrow
to `Y`. -/
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

/-- Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`, with additive sheafification and the
locally-bijective comparison on every slice. For `g : X → Y` and `φ : M → N` over `S.over Y`,
put `F=SheafOfModules.overMap S g`. The image `F(cokernel.π φ)` is a colimit cofork projection
for `F(φ)` and zero, with point `F(coker φ)`. -/
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

/-- Let `(D,K)` be a site and `S : Sheaf K RingCat.{u}`. Assume additive sheafification and the
locally-bijective comparison on every slice `K.over X`. For `g : X → Y` and `φ : M → N`
between module sheaves over `S.over Y`, the functor `SheafOfModules.overMap S g` preserves the
colimit of `parallelPair φ 0`, hence the cokernel of `φ`. -/
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

/-- Let `(D₁,K₁,S₁)` and `(D₂,K₂,S₂)` be ringed sites with rings/modules in universe `u`, and
additive sheafification with the locally-bijective comparison on both sites. Let `P` present a
module sheaf `M`, with generator set `I_G`, relation set `I_R`, and relation map `r :
free(I_R) → free(I_G)` equal to the relation-generating map followed by `kernel.ι
P.generators.π`. For an additive functor `F`, assume preservation of `Discrete I_G`- and
`Discrete I_R`-colimits and of `parallelPair r 0`, and give `η : unit S₂ ≅ F(unit S₁)`. Then
`P.mapOfPreserves F η hF` is a presentation of `F(M)` with the transported generator and
relation families. -/
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

/-- Let two ringed sites have additive sheafification and the locally-bijective comparison at
module universe `u`. Suppose `P` is a presentation of `M` whose generator and relation index
sets are finite. Let `F` be additive, preserve the coproducts indexed by both sets and the
cokernel diagram of the relation map `r : free(I_R) → free(I_G)`, and let `η : unit S₂ ≅
F(unit S₁)`. Then `(P.mapOfPreserves F η hF).IsFinite`: the presentation of `F(M)` has finite
generator and relation families. -/
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
