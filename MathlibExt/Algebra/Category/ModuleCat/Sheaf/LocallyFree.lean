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

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import MathlibExt.CategoryTheory.Sites.CoversTop

/-!
# Locally free of fixed rank — general ringed site

Fixed-rank locally free sheaves of modules over a general ringed site, and
their closure properties (biproducts, pullbacks, tensors).

When `M` is locally free of rank `n`, it is in particular locally free
(`IsLocallyFree`), but the converse is not true: `IsLocallyFree` permits
arbitrary and locally varying ranks, potentially infinite bases.
Hence fixed-rank and arbitrary APIs are kept separately.
-/

@[expose] public section

universe u v₁ u₁

open _root_.CategoryTheory CategoryTheory Limits MonoidalCategory
open scoped _root_.AddCommGrpCat AddCommGrpCat

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

namespace LocalGeneratorsData

/-- Ranked local-freeness data: local generator data that is locally free and
whose charts all have finite rank `n`. Bundles the data form of
`IsLocallyFreeOfRank` for sites where the rank must be witnessed
chart by chart. -/
class _root_.SheafOfModules.LocalGeneratorsData.IsLocallyFreeOfRankData {M : SheafOfModules.{u} R}
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M) (n : ℕ) : Prop where
  isLocallyFreeData : q.IsLocallyFreeData
  rank_eq : ∀ i, Nonempty ((q.generators i).I ≃ Fin n)

end LocalGeneratorsData

/-- Local freeness with a generating family of uniform finite cardinality.
Such a rank need not be unique, for example on an empty site or over the zero ring. -/
class IsLocallyFreeOfRank (M : SheafOfModules.{u} R) (n : semiOutParam ℕ) : Prop where
  exists_isLocallyFreeOfRankData :
    ∃ q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M,
      LocalGeneratorsData.IsLocallyFreeOfRankData q n

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Fixed-rank local freeness yields unranked local freeness, by typeclass
search as well as by explicit application. There is no reverse instance, so
no loop. -/
instance (priority := 100) isLocallyFree_of_isLocallyFreeOfRank
    {M : SheafOfModules.{u} R}
    {n : ℕ} [IsLocallyFreeOfRank (R := R) M n] :
    _root_.SheafOfModules.IsLocallyFree (R := R) M := by
  obtain ⟨q, hq⟩ :=
      (inferInstance : IsLocallyFreeOfRank (R := R) M n).exists_isLocallyFreeOfRankData
  exact ⟨q, hq.isLocallyFreeData⟩

-- Fixed-rank pullback closure (unit and biproduct closure live in `LocallyFreeRank`).

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Comma cover: given a `K`-cover `X` of the source site and a continuous final
functor `F`, the family of objects of `C` equipped with a map into some
`F.obj (X i)` covers the top in `J`. The image family `F.obj ∘ X` does not cover
in general; the comma refinement is what carries pullback data.

This is distinct from `CategoryTheory.GrothendieckTopology.CoversTop.overComma`
(in `MathlibExt.CategoryTheory.Sites.CoversTop`): that lemma refines a cover of
the *same* site over a slice object, while this one transports a cover along a
*change of site* (`F : C' ⥤ C`), producing the pullback-chart cover. -/
private theorem coversTop_comma {C' : Type u} [Category.{v₁} C']
    {K : GrothendieckTopology C'} {F : C' ⥤ C}
    [Functor.IsContinuous F K J] [F.Final]
    {I : Type*} {X : I → C'} (hX : K.CoversTop X) :
    J.CoversTop (fun p : (i : I) × Over (F.obj (X i)) ↦ p.2.left) := by
  intro W
  have hne : Nonempty (StructuredArrow W F) := inferInstance
  obtain ⟨obj⟩ := hne
  have hpush : (Sieve.ofObjects X obj.right).functorPushforward F ∈
      J (F.obj obj.right) :=
    (CoverPreserving.of_isContinuous F K J).cover_preserve (hX obj.right)
  refine J.superset_covering ?_ (J.pullback_stable obj.hom hpush)
  intro Z g hg
  simp only [Sieve.pullback_arrows, Presieve.pullback_iff] at hg
  obtain ⟨Y, u, hu, v, heq⟩ := hg
  rw [Sieve.mem_ofObjects_iff] at v
  obtain ⟨i, ⟨w⟩⟩ := v
  simp only [Sieve.mem_ofObjects_iff]
  exact ⟨⟨i, Over.mk (hu ≫ F.map w)⟩, ⟨𝟙 Z⟩⟩

/-- Ring map over `X` inducing the fiber pullback functor
`SheafOfModules (S.over X) ⥤ SheafOfModules (R.over (F.obj X))`.
It is the pushforward of `φ` along `Over.forget X`, reindexed along
`Over.post F ⋙ Over.forget = Over.forget ⋙ F`. -/
noncomputable def overRingHom {C' : Type u} [Category.{v₁} C']
    {K : GrothendieckTopology C'} {S : Sheaf K RingCat.{u}}
    {F : C' ⥤ C} [Functor.IsContinuous F K J]
    [∀ (X : C'), Functor.IsContinuous (Over.post (X := X) F)
      (K.over X) (J.over (F.obj X))]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K J).obj R) (X : C') :
    S.over X ⟶ ((Over.post (X := X) F).sheafPushforwardContinuous RingCat.{u}
      (K.over X) (J.over (F.obj X))).obj (R.over (F.obj X)) :=
  ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Coproduct and biproduct rank formulas are given in
`MathlibExt.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank`. -/
theorem isLocallyFreeOfRank_pullback
    [HasPullbacks C]
    {C' : Type u} [Category.{v₁} C']
    {K : GrothendieckTopology C'}
    {S : Sheaf K RingCat.{u}}
    [∀ (X : C'), HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ (X : C'), (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F : C' ⥤ C} [Functor.IsContinuous F K J] [F.Final]
    [∀ (X : C'), Functor.IsContinuous (Over.post (X := X) F)
      (K.over X) (J.over (F.obj X))]
    [∀ (X : C'), (Over.post (X := X) F).Final]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    [(_root_.SheafOfModules.pushforward φ).IsRightAdjoint]
    [∀ (X : C'), (_root_.SheafOfModules.pushforward (overRingHom φ X)).IsRightAdjoint]
    {M : SheafOfModules.{u} S} {n : ℕ} [IsLocallyFreeOfRank (R := S) M n]
    (hbeck : ∀ (X : C'), (_root_.SheafOfModules.pullback (overRingHom φ X)).obj (M.over X) ≅
      ((_root_.SheafOfModules.pullback φ).obj M).over (F.obj X)) :
    IsLocallyFreeOfRank (R := R) ((_root_.SheafOfModules.pullback φ).obj M) n := by
  obtain ⟨q, hq⟩ :=
    (inferInstance : IsLocallyFreeOfRank (R := S) M n).exists_isLocallyFreeOfRankData
  have := hq.isLocallyFreeData
  have hIso : ∀ i, IsIso (q.generators i).π := fun i ↦ inferInstance
  have hcover : J.CoversTop
      (fun p : (i : q.I) × Over (F.obj (q.X i)) ↦ p.2.left) :=
    coversTop_comma (F := F) q.coversTop
  have piece : ∀ p : (i : q.I) × Over (F.obj (q.X i)),
      ∃ G : (((_root_.SheafOfModules.pullback φ).obj M).over p.2.left).GeneratingSections,
        IsIso G.π ∧ Nonempty (G.I ≃ Fin n) := by
    intro p
    obtain ⟨i, Y⟩ := p
    have := hIso i
    -- Transfer along the fiber pullback, then restrict along `Y.hom` via `overMap`.
    let ψ : S.over (q.X i) ⟶
        ((Over.post (X := q.X i) F).sheafPushforwardContinuous RingCat.{u}
          (K.over (q.X i)) (J.over (F.obj (q.X i)))).obj
          (R.over (F.obj (q.X i))) :=
      overRingHom φ (q.X i)
    let H : SheafOfModules (S.over (q.X i)) ⥤ SheafOfModules (R.over Y.left) :=
      (_root_.SheafOfModules.pullback ψ) ⋙ (_root_.SheafOfModules.overMap R Y.hom)
    have uψ : (_root_.SheafOfModules.pullback ψ).obj (_root_.SheafOfModules.unit (S.over (q.X i))) ≅
        _root_.SheafOfModules.unit (R.over (F.obj (q.X i))) :=
      asIso (_root_.SheafOfModules.pullbackObjUnitToUnit ψ)
    let ηH : _root_.SheafOfModules.unit (R.over Y.left) ≅
        H.obj (_root_.SheafOfModules.unit (S.over (q.X i))) :=
      (_root_.SheafOfModules.overMapUnitIso Y.hom).symm.trans
          ((_root_.SheafOfModules.overMap R Y.hom).mapIso uψ.symm)
    let G' : (H.obj (M.over (q.X i))).GeneratingSections :=
      (q.generators i).map H ηH
    -- Beck–Chevalley comparison plus restriction along `Y.hom`.
    let e : H.obj (M.over (q.X i)) ≅ ((_root_.SheafOfModules.pullback φ).obj M).over Y.left :=
      (_root_.SheafOfModules.overMap R Y.hom).mapIso (hbeck (q.X i)) ≪≫
          (_root_.SheafOfModules.overFunctorMap R Y.hom).app _
    let G'' := G'.ofEpi e.hom
    have hG : IsIso G''.π := by
      rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
      exact (asIso G'.π ≪≫ e).isIso_hom
    exact ⟨G'', hG, hq.rank_eq i⟩
  choose gen hgen using piece
  have hfree : (((⟨_, _, hcover, gen⟩ :
    _root_.SheafOfModules.LocalGeneratorsData
      ((_root_.SheafOfModules.pullback φ).obj M))).IsLocallyFreeData) :=
    ⟨fun p ↦ (hgen p).1⟩
  have hshrink : ((⟨_, _, hcover, gen⟩ :
    _root_.SheafOfModules.LocalGeneratorsData
      ((_root_.SheafOfModules.pullback φ).obj M)).shrink).IsLocallyFreeData :=
    inferInstance
  refine ⟨((⟨_, _, hcover, gen⟩ :
      _root_.SheafOfModules.LocalGeneratorsData
        ((_root_.SheafOfModules.pullback φ).obj M))).shrink,
    ⟨hshrink, fun s ↦ (hgen s.2.choose).2⟩⟩

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem isLocallyFree_pullback
    [HasPullbacks C]
    {C' : Type u} [Category.{v₁} C']
    {K : GrothendieckTopology C'}
    {S : Sheaf K RingCat.{u}}
    [∀ (X : C'), HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ (X : C'), (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F : C' ⥤ C} [Functor.IsContinuous F K J] [F.Final]
    [∀ (X : C'), Functor.IsContinuous (Over.post (X := X) F)
      (K.over X) (J.over (F.obj X))]
    [∀ (X : C'), (Over.post (X := X) F).Final]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    [(_root_.SheafOfModules.pushforward φ).IsRightAdjoint]
    [∀ (X : C'), (_root_.SheafOfModules.pushforward (overRingHom φ X)).IsRightAdjoint]
    {M : SheafOfModules.{u} S} [_root_.SheafOfModules.IsLocallyFree (R := S) M]
    (hbeck : ∀ (X : C'), (_root_.SheafOfModules.pullback (overRingHom φ X)).obj (M.over X) ≅
      ((_root_.SheafOfModules.pullback φ).obj M).over (F.obj X)) :
    _root_.SheafOfModules.IsLocallyFree (R := R) ((_root_.SheafOfModules.pullback φ).obj M) := by
  obtain ⟨q, hq⟩ :=
      (inferInstance : _root_.SheafOfModules.IsLocallyFree (R := S) M).exists_isLocallyFreeData
  have := hq
  have hIso : ∀ i, IsIso (q.generators i).π := fun i ↦ inferInstance
  have hcover : J.CoversTop
      (fun p : (i : q.I) × Over (F.obj (q.X i)) ↦ p.2.left) :=
    coversTop_comma (F := F) q.coversTop
  have piece : ∀ p : (i : q.I) × Over (F.obj (q.X i)),
      ∃ G : (((_root_.SheafOfModules.pullback φ).obj M).over p.2.left).GeneratingSections,
        IsIso G.π := by
    intro p
    obtain ⟨i, Y⟩ := p
    have := hIso i
    let ψ : S.over (q.X i) ⟶
        ((Over.post (X := q.X i) F).sheafPushforwardContinuous RingCat.{u}
          (K.over (q.X i)) (J.over (F.obj (q.X i)))).obj
          (R.over (F.obj (q.X i))) :=
      overRingHom φ (q.X i)
    let H : SheafOfModules (S.over (q.X i)) ⥤ SheafOfModules (R.over Y.left) :=
      (_root_.SheafOfModules.pullback ψ) ⋙ (_root_.SheafOfModules.overMap R Y.hom)
    have uψ : (_root_.SheafOfModules.pullback ψ).obj (_root_.SheafOfModules.unit (S.over (q.X i))) ≅
        _root_.SheafOfModules.unit (R.over (F.obj (q.X i))) :=
      asIso (_root_.SheafOfModules.pullbackObjUnitToUnit ψ)
    let ηH : _root_.SheafOfModules.unit (R.over Y.left) ≅
        H.obj (_root_.SheafOfModules.unit (S.over (q.X i))) :=
      (_root_.SheafOfModules.overMapUnitIso Y.hom).symm.trans
          ((_root_.SheafOfModules.overMap R Y.hom).mapIso uψ.symm)
    let G' : (H.obj (M.over (q.X i))).GeneratingSections :=
      (q.generators i).map H ηH
    let e : H.obj (M.over (q.X i)) ≅ ((_root_.SheafOfModules.pullback φ).obj M).over Y.left :=
      (_root_.SheafOfModules.overMap R Y.hom).mapIso (hbeck (q.X i)) ≪≫
          (_root_.SheafOfModules.overFunctorMap R Y.hom).app _
    let G'' := G'.ofEpi e.hom
    have hG : IsIso G''.π := by
      rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
      exact (asIso G'.π ≪≫ e).isIso_hom
    exact ⟨G'', hG⟩
  choose gen hgen using piece
  have hfree : (((⟨_, _, hcover, gen⟩ :
      _root_.SheafOfModules.LocalGeneratorsData
          ((_root_.SheafOfModules.pullback φ).obj M))).IsLocallyFreeData) :=
    ⟨fun p ↦ hgen p⟩
  have hshrink : (((⟨_, _, hcover, gen⟩ :
    _root_.SheafOfModules.LocalGeneratorsData
      ((_root_.SheafOfModules.pullback φ).obj M))).shrink).IsLocallyFreeData :=
    inferInstance
  exact ⟨(⟨_, _, hcover, gen⟩ :
    _root_.SheafOfModules.LocalGeneratorsData
      ((_root_.SheafOfModules.pullback φ).obj M)).shrink, hshrink⟩

/-! ### Tensor products over a commutative ring structure sheaf -/

section Tensor

-- NOTE: the site universes here are pinned to the coefficient universe
-- (`C₀ : Type u`, `Category.{u}`). Generalizing to `Type*`/`Category*` was
-- attempted and reverted: the section's Mathlib inputs (`tensorUnitIso`,
-- `sheafificationCommId`, `HasSheafCompose`, the `monoidalCategory`
-- instance) require the site to live in the same universes as the
-- coefficients.
variable {C₀ : Type u} [Category.{u} C₀] {J₀ : GrothendieckTopology C₀}
  (R₀ : Sheaf J₀ CommRingCat.{u})
  [(J₀.W (A := Ab.{u})).IsMonoidal] [J₀.WEqualsLocallyBijective Ab.{u}]
  [HasSheafify J₀ Ab.{u}]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ (X : C₀),
    (J₀.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ (X : C₀), HasSheafify (J₀.over X) Ab.{u}]
  [∀ (X : C₀), (J₀.over X).WEqualsLocallyBijective Ab.{u}]
  [∀ (X : C₀) (Y : Over X), HasWeakSheafify ((J₀.over X).over Y) Ab.{u}]
  [∀ (X : C₀) (Y : Over X),
    ((J₀.over X).over Y).WEqualsLocallyBijective Ab.{u}]
  [HasPullbacks C₀] [HasBinaryProducts C₀]

attribute [local instance] SheafOfModules.monoidalCategory

variable (U : C₀)

namespace RestrictSheafification

/-- Every sheaf of modules is the sheafification of its underlying presheaf of modules. -/
noncomputable abbrev counitIso
    (A : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) :
    (PresheafOfModules.sheafificationCommId R₀).obj
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).obj A) ≅ A :=
  asIso ((PresheafOfModules.sheafificationAdjunction
    (Sheaf.commRingCatForget₂Id R₀)).counit.app A)

omit [(J₀.W (A := Ab.{u})).IsMonoidal]
  [∀ (X : C₀), (J₀.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ (X : C₀), HasSheafify (J₀.over X) Ab.{u}]
  [∀ (X : C₀), (J₀.over X).WEqualsLocallyBijective Ab.{u}]
  [∀ (X : C₀) (Y : Over X), HasWeakSheafify ((J₀.over X).over Y) Ab.{u}]
  [∀ (X : C₀) (Y : Over X),
    ((J₀.over X).over Y).WEqualsLocallyBijective Ab.{u}]
  [HasPullbacks C₀] [HasBinaryProducts C₀] in
/-- Inverse-counit naturality: `f ≫ inv B' = inv B ≫ L.map (R.map f)`.
Kept for `sheafTensor_whisker_eq_of_presheaf_tensorHom` below. -/
lemma counitIso_inv_naturality
    (B B' : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) (f : B ⟶ B') :
    f ≫ (counitIso R₀ B').inv =
      (counitIso R₀ B).inv ≫ (PresheafOfModules.sheafificationCommId R₀).map
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).map f) := by
  simp [counitIso, ← Functor.comp_map,
    ← (PresheafOfModules.sheafificationAdjunction
      (Sheaf.commRingCatForget₂Id R₀)).counit_naturality_assoc]

end RestrictSheafification

namespace TensorHelpers

/-- The sheafification counit isomorphism after restriction of coefficients. -/
noncomputable abbrev counitIso
    (A : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) :
    (PresheafOfModules.sheafificationCommId R₀).obj
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).obj A) ≅ A :=
  RestrictSheafification.counitIso R₀ A

/-- The tensor comparison for restriction to a slice site. -/
noncomputable abbrev resTensorIso
    (A B : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) :
    (RestrictSheafification.restrictSheaf R₀ U).obj (A ⊗ B) ≅
      (RestrictSheafification.restrictSheaf R₀ U).obj A ⊗
        (RestrictSheafification.restrictSheaf R₀ U).obj B :=
  RestrictSheafification.ofTensorIso R₀ U A B

end TensorHelpers


omit [∀ (X : C₀) (Y : Over X),
    HasWeakSheafify ((J₀.over X).over Y) Ab.{u}]
  [∀ (X : C₀) (Y : Over X),
    ((J₀.over X).over Y).WEqualsLocallyBijective Ab.{u}]
  [HasPullbacks C₀] [HasBinaryProducts C₀] in
/-- Right-whisker naturality of `RestrictSheafification.ofTensorIso`: oplax `δ`-naturality. -/
theorem resTensorIso_naturality_right
    (A B B' : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) (f : B ⟶ B') :
    ((RestrictSheafification.restrictSheaf R₀ U).map (whiskerLeft A f)) ≫
      (RestrictSheafification.ofTensorIso R₀ U A B').hom =
      (RestrictSheafification.ofTensorIso R₀ U A B).hom ≫
        whiskerLeft ((RestrictSheafification.restrictSheaf R₀ U).obj A)
            ((RestrictSheafification.restrictSheaf R₀ U).map f) :=
  (Functor.OplaxMonoidal.δ_natural_right
    (RestrictSheafification.restrictSheaf R₀ U) A f).symm

omit [∀ (X : C₀) (Y : Over X),
    HasWeakSheafify ((J₀.over X).over Y) Ab.{u}]
  [∀ (X : C₀) (Y : Over X),
    ((J₀.over X).over Y).WEqualsLocallyBijective Ab.{u}]
  [HasPullbacks C₀] [HasBinaryProducts C₀] in
/-- Left-whisker naturality of `RestrictSheafification.ofTensorIso`: oplax `δ`-naturality. -/
theorem resTensorIso_naturality_left
    (A A' B : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) (f : A ⟶ A') :
    ((RestrictSheafification.restrictSheaf R₀ U).map (whiskerRight f B)) ≫
      (RestrictSheafification.ofTensorIso R₀ U A' B).hom =
      (RestrictSheafification.ofTensorIso R₀ U A B).hom ≫
        whiskerRight ((RestrictSheafification.restrictSheaf R₀ U).map f)
            ((RestrictSheafification.restrictSheaf R₀ U).obj B) :=
  (Functor.OplaxMonoidal.δ_natural_left
    (RestrictSheafification.restrictSheaf R₀ U) f B).symm

omit [∀ (X : C₀),
    (J₀.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ (X : C₀), HasSheafify (J₀.over X) Ab.{u}]
  [∀ (X : C₀), (J₀.over X).WEqualsLocallyBijective Ab.{u}]
  [∀ (X : C₀) (Y : Over X), HasWeakSheafify ((J₀.over X).over Y) Ab.{u}]
  [∀ (X : C₀) (Y : Over X),
    ((J₀.over X).over Y).WEqualsLocallyBijective Ab.{u}]
  [HasPullbacks C₀] [HasBinaryProducts C₀] in
theorem sheafTensor_whisker_eq_of_presheaf_tensorHom
    (A B : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀))
    (psi : A ⟶ A) (phi : B ⟶ B)
    (h : PresheafOfModulesOfCommRing.Monoidal.tensorHom
        (𝟙 ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).obj A))
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).map phi) =
      PresheafOfModulesOfCommRing.Monoidal.tensorHom
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).map psi)
        (𝟙 ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).obj B))) :
    whiskerLeft A phi = psi ▷ B := by
  -- Sheafification presentation of the sheaf tensor, mirroring
  -- `RestrictSheafification.ofTensorIso`.
  let L := PresheafOfModules.sheafificationCommId R₀
  let Q : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀) ⥤
      PresheafOfModules.{u} (R₀.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
    _root_.SheafOfModules.forget _ ⋙
        PresheafOfModules.restrictScalars (Sheaf.commRingCatForget₂Id R₀)
  let iAB : A ⊗ B ≅ L.obj (Q.obj A ⊗ Q.obj B) :=
    tensorIso (RestrictSheafification.counitIso R₀ A).symm
        (RestrictSheafification.counitIso R₀ B).symm ≪≫
      Localization.Monoidal.μ L
        (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _) _ _
  have hCinvPhiE : phi ≫ (RestrictSheafification.counitIso R₀ B).inv =
      (RestrictSheafification.counitIso R₀ B).inv ≫ (PresheafOfModules.sheafificationCommId R₀).map
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).map phi) :=
    RestrictSheafification.counitIso_inv_naturality R₀ B B phi
  have hCinvPsiE : psi ≫ (RestrictSheafification.counitIso R₀ A).inv =
      (RestrictSheafification.counitIso R₀ A).inv ≫ (PresheafOfModules.sheafificationCommId R₀).map
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).map psi) :=
    RestrictSheafification.counitIso_inv_naturality R₀ A A psi
  have hTensorCPhiE : whiskerLeft A phi ≫
        (tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom =
        (tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
          whiskerLeft ((PresheafOfModules.sheafificationCommId R₀).obj
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj A))
            ((PresheafOfModules.sheafificationCommId R₀).map
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map phi)) := by
    calc whiskerLeft A phi ≫
            (tensorIso (RestrictSheafification.counitIso R₀ A).symm
                (RestrictSheafification.counitIso R₀ B).symm).hom
        _ = whiskerLeft A phi ≫
            ((RestrictSheafification.counitIso R₀ A).symm.hom ⊗ₘ
                (RestrictSheafification.counitIso R₀ B).symm.hom) := by
          rw [MonoidalCategory.tensorIso_hom]
        _ = whiskerLeft A phi ≫
            ((RestrictSheafification.counitIso R₀ A).inv ⊗ₘ
                (RestrictSheafification.counitIso R₀ B).inv) := by
          rw [Iso.symm_hom, Iso.symm_hom]
        _ = (𝟙 A ⊗ₘ phi) ≫
            ((RestrictSheafification.counitIso R₀ A).inv ⊗ₘ
                (RestrictSheafification.counitIso R₀ B).inv) := by
          rw [← MonoidalCategory.id_tensorHom]
        _ = (𝟙 A ≫ (RestrictSheafification.counitIso R₀ A).inv) ⊗ₘ
            (phi ≫ (RestrictSheafification.counitIso R₀ B).inv) := by
          rw [MonoidalCategory.tensorHom_comp_tensorHom]
        _ = (RestrictSheafification.counitIso R₀ A).inv ⊗ₘ
            (phi ≫ (RestrictSheafification.counitIso R₀ B).inv) := by
          rw [Category.id_comp]
        _ = (RestrictSheafification.counitIso R₀ A).inv ⊗ₘ
            ((RestrictSheafification.counitIso R₀ B).inv ≫
                (PresheafOfModules.sheafificationCommId R₀).map
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map phi)) := by
          rw [hCinvPhiE]
        _ = ((RestrictSheafification.counitIso R₀ A).inv ≫ 𝟙 _) ⊗ₘ
            ((RestrictSheafification.counitIso R₀ B).inv ≫
                (PresheafOfModules.sheafificationCommId R₀).map
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map phi)) := by
          rw [Category.comp_id]
        _ = ((RestrictSheafification.counitIso R₀ A).inv ⊗ₘ
            (RestrictSheafification.counitIso R₀ B).inv) ≫
            (𝟙 _ ⊗ₘ (PresheafOfModules.sheafificationCommId R₀).map
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map phi)) := by
          rw [MonoidalCategory.tensorHom_comp_tensorHom]
        _ = ((RestrictSheafification.counitIso R₀ A).inv ⊗ₘ
            (RestrictSheafification.counitIso R₀ B).inv) ≫
            whiskerLeft ((PresheafOfModules.sheafificationCommId R₀).obj
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A))
              ((PresheafOfModules.sheafificationCommId R₀).map
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).map phi)) := by
          rw [MonoidalCategory.id_tensorHom]
        _ = (tensorIso (RestrictSheafification.counitIso R₀ A).symm
              (RestrictSheafification.counitIso R₀ B).symm).hom ≫
            whiskerLeft ((PresheafOfModules.sheafificationCommId R₀).obj
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A))
              ((PresheafOfModules.sheafificationCommId R₀).map
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).map phi)) := by
          rw [MonoidalCategory.tensorIso_hom, Iso.symm_hom, Iso.symm_hom]
  have hTensorCPsiE : (psi ▷ B) ≫
        (tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom =
        (tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
          ((PresheafOfModules.sheafificationCommId R₀).map
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
            (PresheafOfModules.sheafificationCommId R₀).obj
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)) := by
    calc (psi ▷ B) ≫
            (tensorIso (RestrictSheafification.counitIso R₀ A).symm
                (RestrictSheafification.counitIso R₀ B).symm).hom
        _ = (psi ▷ B) ≫
            ((RestrictSheafification.counitIso R₀ A).symm.hom ⊗ₘ
                (RestrictSheafification.counitIso R₀ B).symm.hom) := by
          rw [MonoidalCategory.tensorIso_hom]
        _ = (psi ▷ B) ≫
            ((RestrictSheafification.counitIso R₀ A).inv ⊗ₘ
                (RestrictSheafification.counitIso R₀ B).inv) := by
          rw [Iso.symm_hom, Iso.symm_hom]
        _ = (psi ⊗ₘ 𝟙 B) ≫
            ((RestrictSheafification.counitIso R₀ A).inv ⊗ₘ
                (RestrictSheafification.counitIso R₀ B).inv) := by
          rw [← MonoidalCategory.tensorHom_id]
        _ = (psi ≫ (RestrictSheafification.counitIso R₀ A).inv) ⊗ₘ
            (𝟙 B ≫ (RestrictSheafification.counitIso R₀ B).inv) := by
          rw [MonoidalCategory.tensorHom_comp_tensorHom]
        _ = (psi ≫ (RestrictSheafification.counitIso R₀ A).inv) ⊗ₘ
            (RestrictSheafification.counitIso R₀ B).inv := by
          rw [Category.id_comp]
        _ = ((RestrictSheafification.counitIso R₀ A).inv ≫
            (PresheafOfModules.sheafificationCommId R₀).map
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map psi)) ⊗ₘ
            (RestrictSheafification.counitIso R₀ B).inv := by
          rw [hCinvPsiE]
        _ = ((RestrictSheafification.counitIso R₀ A).inv ≫
            (PresheafOfModules.sheafificationCommId R₀).map
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map psi)) ⊗ₘ
            ((RestrictSheafification.counitIso R₀ B).inv ≫ 𝟙 _) := by
          rw [Category.comp_id]
        _ = ((RestrictSheafification.counitIso R₀ A).inv ⊗ₘ
            (RestrictSheafification.counitIso R₀ B).inv) ≫
            ((PresheafOfModules.sheafificationCommId R₀).map
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map psi) ⊗ₘ 𝟙 _) := by
          rw [← MonoidalCategory.tensorHom_comp_tensorHom]
        _ = ((RestrictSheafification.counitIso R₀ A).inv ⊗ₘ
            (RestrictSheafification.counitIso R₀ B).inv) ≫
            ((PresheafOfModules.sheafificationCommId R₀).map
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
              (PresheafOfModules.sheafificationCommId R₀).obj
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B)) := by
          rw [MonoidalCategory.tensorHom_id]
        _ = (tensorIso (RestrictSheafification.counitIso R₀ A).symm
              (RestrictSheafification.counitIso R₀ B).symm).hom ≫
            ((PresheafOfModules.sheafificationCommId R₀).map
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
              (PresheafOfModules.sheafificationCommId R₀).obj
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B)) := by
          rw [MonoidalCategory.tensorIso_hom, Iso.symm_hom, Iso.symm_hom]
  have hMuPhiE := Localization.Monoidal.μ_natural_right
    (PresheafOfModules.sheafificationCommId R₀)
    (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
    ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
      (Sheaf.commRingCatForget₂Id R₀)).obj A)
    ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
      (Sheaf.commRingCatForget₂Id R₀)).map phi)
  have hMuPsiE := Localization.Monoidal.μ_natural_left
    (PresheafOfModules.sheafificationCommId R₀)
    (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
    ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
      (Sheaf.commRingCatForget₂Id R₀)).map psi)
    ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
      (Sheaf.commRingCatForget₂Id R₀)).obj B)
  have hBridgePhiE : ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (Sheaf.commRingCatForget₂Id R₀)).obj A) ◁
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).map phi) =
        PresheafOfModulesOfCommRing.Monoidal.tensorHom
          (𝟙 ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).obj A))
          ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).map phi) :=
    (MonoidalCategory.id_tensorHom _ _).symm
  have hBridgePsiE : ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).obj B) =
        PresheafOfModulesOfCommRing.Monoidal.tensorHom
          ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).map psi)
          (𝟙 ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).obj B)) :=
    (MonoidalCategory.tensorHom_id _ _).symm
  have hLeftE : whiskerLeft A phi ≫
        ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
            (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj A)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) =
        ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
            (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj A)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) ≫
          (PresheafOfModules.sheafificationCommId R₀).map
            (PresheafOfModulesOfCommRing.Monoidal.tensorHom
              (𝟙 ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A))
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map phi)) := by
    calc whiskerLeft A phi ≫
            ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
                (RestrictSheafification.counitIso R₀ B).symm).hom ≫
              (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
                (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj A)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom)
        _ = (whiskerLeft A phi ≫
              (tensorIso (RestrictSheafification.counitIso R₀ A).symm
                  (RestrictSheafification.counitIso R₀ B).symm).hom) ≫
            (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom :=
          (Category.assoc _ _ _).symm
        _ = ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
              whiskerLeft ((Localization.Monoidal.toMonoidalCategory
                  (PresheafOfModules.sheafificationCommId R₀)
                  (J₀.W.inverseImage (PresheafOfModules.toPresheaf _))
                  (Iso.refl _)).obj
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj A))
                ((Localization.Monoidal.toMonoidalCategory
                  (PresheafOfModules.sheafificationCommId R₀)
                  (J₀.W.inverseImage (PresheafOfModules.toPresheaf _))
                  (Iso.refl _)).map
                  ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                    (Sheaf.commRingCatForget₂Id R₀)).map phi))) ≫
            (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom := by
          rw [hTensorCPhiE]
          rfl
        _ = (tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
            ((Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom ≫
              (Localization.Monoidal.toMonoidalCategory
                (PresheafOfModules.sheafificationCommId R₀)
                (J₀.W.inverseImage (PresheafOfModules.toPresheaf _))
                (Iso.refl _)).map
                (((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj A) ◁
                  ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                    (Sheaf.commRingCatForget₂Id R₀)).map phi))) := by
          have hPrefPhi := congrArg
            (fun q => (tensorIso (RestrictSheafification.counitIso R₀ A).symm
              (RestrictSheafification.counitIso R₀ B).symm).hom ≫ q) hMuPhiE
          exact (Category.assoc _ _ _).trans hPrefPhi
        _ = ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
              (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
                (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj A)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) ≫
            (Localization.Monoidal.toMonoidalCategory
              (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _))
              (Iso.refl _)).map
              (((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A) ◁
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).map phi)) :=
          (Category.assoc _ _ _).symm
        _ = ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
              (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
                (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj A)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) ≫
            (Localization.Monoidal.toMonoidalCategory
              (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _))
              (Iso.refl _)).map
              (PresheafOfModulesOfCommRing.Monoidal.tensorHom
                (𝟙 ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj A))
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).map phi)) := by
          rw [hBridgePhiE]
  have hRightE : (psi ▷ B) ≫
        ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
            (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj A)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) =
        ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
            (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj A)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) ≫
          (PresheafOfModules.sheafificationCommId R₀).map
            (PresheafOfModulesOfCommRing.Monoidal.tensorHom
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map psi)
              (𝟙 ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B))) := by
    have hMuPsiE' : ((((PresheafOfModules.sheafificationCommId R₀).map
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).map psi)) ▷
            ((PresheafOfModules.sheafificationCommId R₀).obj
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B))) ≫
        (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
          (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
          ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).obj A)
          ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) =
        ((Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
          (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
          ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).obj A)
          ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom ≫
        (PresheafOfModules.sheafificationCommId R₀).map
          (((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj B))) := hMuPsiE
    have hStepPsi : ((((tensorIso (RestrictSheafification.counitIso R₀ A).symm
          (RestrictSheafification.counitIso R₀ B).symm).hom ≫
          (((PresheafOfModules.sheafificationCommId R₀).map
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).map psi)) ▷
            ((PresheafOfModules.sheafificationCommId R₀).obj
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)))) ≫
        (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
          (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
          ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).obj A)
          ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) =
        ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
          ((Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
            (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj A)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom ≫
            (PresheafOfModules.sheafificationCommId R₀).map
              (((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B))))) := by
      have hPrefPsi := congrArg
        (fun q => (tensorIso (RestrictSheafification.counitIso R₀ A).symm
          (RestrictSheafification.counitIso R₀ B).symm).hom ≫ q) hMuPsiE'
      exact (Category.assoc _ _ _).trans hPrefPsi
    have cPsiAssoc : (psi ▷ B) ≫
            ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
                (RestrictSheafification.counitIso R₀ B).symm).hom ≫
              (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
                (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj A)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) =
          (((psi ▷ B) ≫
              (tensorIso (RestrictSheafification.counitIso R₀ A).symm
                  (RestrictSheafification.counitIso R₀ B).symm).hom) ≫
            (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) :=
      (Category.assoc _ _ _).symm
    have cPsiTensor : (((psi ▷ B) ≫
              (tensorIso (RestrictSheafification.counitIso R₀ A).symm
                  (RestrictSheafification.counitIso R₀ B).symm).hom) ≫
            (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) =
          (((tensorIso (RestrictSheafification.counitIso R₀ A).symm
              (RestrictSheafification.counitIso R₀ B).symm).hom ≫
              ((PresheafOfModules.sheafificationCommId R₀).map
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
                (PresheafOfModules.sheafificationCommId R₀).obj
                  ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                    (Sheaf.commRingCatForget₂Id R₀)).obj B))) ≫
            (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) := by
      rw [hTensorCPsiE]
    have cPsiStep : (((tensorIso (RestrictSheafification.counitIso R₀ A).symm
        (RestrictSheafification.counitIso R₀ B).symm).hom ≫
              ((PresheafOfModules.sheafificationCommId R₀).map
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
                (PresheafOfModules.sheafificationCommId R₀).obj
                  ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                    (Sheaf.commRingCatForget₂Id R₀)).obj B))) ≫
            (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) =
          ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
              (RestrictSheafification.counitIso R₀ B).symm).hom ≫
            ((Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom ≫
              (PresheafOfModules.sheafificationCommId R₀).map
                (((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
                  ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                    (Sheaf.commRingCatForget₂Id R₀)).obj B)))) :=
      hStepPsi
    have cPsiReassoc : ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
        (RestrictSheafification.counitIso R₀ B).symm).hom ≫
            ((Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
              (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj A)
              ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom ≫
              (PresheafOfModules.sheafificationCommId R₀).map
                (((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
                  ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                    (Sheaf.commRingCatForget₂Id R₀)).obj B)))) =
          (((tensorIso (RestrictSheafification.counitIso R₀ A).symm
              (RestrictSheafification.counitIso R₀ B).symm).hom ≫
              (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
                (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj A)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) ≫
            (PresheafOfModules.sheafificationCommId R₀).map
              (((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B))) :=
      (Category.assoc _ _ _).symm
    have cPsiBridge : (((tensorIso (RestrictSheafification.counitIso R₀ A).symm
        (RestrictSheafification.counitIso R₀ B).symm).hom ≫
              (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
                (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj A)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) ≫
            (PresheafOfModules.sheafificationCommId R₀).map
              (((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                (Sheaf.commRingCatForget₂Id R₀)).map psi) ▷
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B))) =
          (((tensorIso (RestrictSheafification.counitIso R₀ A).symm
              (RestrictSheafification.counitIso R₀ B).symm).hom ≫
              (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
                (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj A)
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) ≫
            (PresheafOfModules.sheafificationCommId R₀).map
              (PresheafOfModulesOfCommRing.Monoidal.tensorHom
                ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).map psi)
                (𝟙 ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
                  (Sheaf.commRingCatForget₂Id R₀)).obj B)))) := by
      rw [hBridgePsiE]
    exact cPsiAssoc.trans (cPsiTensor.trans (cPsiStep.trans (cPsiReassoc.trans cPsiBridge)))
  have hMapped := congrArg (PresheafOfModules.sheafificationCommId R₀).map h
  have key : whiskerLeft A phi ≫
        ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
            (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj A)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) =
        (psi ▷ B) ≫
        ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
            (RestrictSheafification.counitIso R₀ B).symm).hom ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
            (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj A)
            ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
              (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) := by
    have hL := hLeftE
    have hM := congrArg (fun q =>
      ((tensorIso (RestrictSheafification.counitIso R₀ A).symm
          (RestrictSheafification.counitIso R₀ B).symm).hom ≫
        (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
          (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
          ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).obj A)
          ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) ≫ q) hMapped
    have hR := hRightE
    exact hL.trans (hM.trans hR.symm)
  have : IsIso (tensorIso (RestrictSheafification.counitIso R₀ A).symm
      (RestrictSheafification.counitIso R₀ B).symm).hom := Iso.isIso_hom _
  have : IsIso (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
      (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
      ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (Sheaf.commRingCatForget₂Id R₀)).obj A)
      ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom := Iso.isIso_hom _
  have keyAssoc : ((whiskerLeft A phi ≫
      (tensorIso (RestrictSheafification.counitIso R₀ A).symm
          (RestrictSheafification.counitIso R₀ B).symm).hom) ≫
      (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
        (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).obj A)
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) =
      (((psi ▷ B) ≫
      (tensorIso (RestrictSheafification.counitIso R₀ A).symm
          (RestrictSheafification.counitIso R₀ B).symm).hom) ≫
      (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R₀)
        (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).obj A)
        ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom) :=
    (Category.assoc _ _ _).trans (key.trans (Category.assoc _ _ _).symm)
  have keyMu := (cancel_mono (Localization.Monoidal.μ
      (PresheafOfModules.sheafificationCommId R₀)
      (J₀.W.inverseImage (PresheafOfModules.toPresheaf _)) (Iso.refl _)
      ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (Sheaf.commRingCatForget₂Id R₀)).obj A)
      ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (Sheaf.commRingCatForget₂Id R₀)).obj B)).hom).mp keyAssoc
  have keyMuAssoc : (whiskerLeft A phi ≫
      (tensorIso (RestrictSheafification.counitIso R₀ A).symm
          (RestrictSheafification.counitIso R₀ B).symm).hom) =
      ((psi ▷ B) ≫
      (tensorIso (RestrictSheafification.counitIso R₀ A).symm
          (RestrictSheafification.counitIso R₀ B).symm).hom) :=
    keyMu
  exact (cancel_mono (tensorIso (RestrictSheafification.counitIso R₀ A).symm
    (RestrictSheafification.counitIso R₀ B).symm).hom).mp keyMuAssoc

/-- If two sheaves of modules restrict to free sheaves over `U`, so does their tensor product. -/
noncomputable def overTensorFreeIso
    (A B : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀))
    {I K : Type u}
    (eA : A.over U ≅ _root_.SheafOfModules.free
      (R := ((sheafCompose J₀
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀).over U) I)
    (eB : B.over U ≅ _root_.SheafOfModules.free
      (R := ((sheafCompose J₀
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀).over U) K) :
    (A ⊗ B).over U ≅ _root_.SheafOfModules.free
      (R := ((sheafCompose J₀
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀).over U) (I × K) :=
  letI : MonoidalCategory (SheafOfModules.{u}
      (((sheafCompose J₀
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀).over U)) :=
    monoidalCategory (R₀.over U)
  RestrictSheafification.ofTensorIso R₀ U A B ≪≫ tensorIso eA eB ≪≫
    _root_.SheafOfModules.freeTensorIso (R₀.over U) I K

/-- Free-ness of a restriction is inherited along a map of base objects. -/
noncomputable def overFreeIsoOfMap {S : Sheaf J₀ RingCat.{u}}
    (A : SheafOfModules.{u} S) {V W : C₀} (f : V ⟶ W) (I : Type u)
    (e : A.over W ≅ _root_.SheafOfModules.free (R := S.over W) I) :
    A.over V ≅ _root_.SheafOfModules.free (R := S.over V) I :=
  ((_root_.SheafOfModules.overFunctorMap S f).app A).symm ≪≫
    (_root_.SheafOfModules.overMap S f).mapIso e ≪≫
    (_root_.SheafOfModules.mapFreeIso (_root_.SheafOfModules.overMap S f) I
        (_root_.SheafOfModules.overMapUnitIso f).symm).symm

omit [∀ (X : C₀) (Y : Over X),
    HasWeakSheafify ((J₀.over X).over Y) Ab.{u}]
  [∀ (X : C₀) (Y : Over X),
    ((J₀.over X).over Y).WEqualsLocallyBijective Ab.{u}] in
/-- The tensor product of locally free sheaves of fixed ranks has product rank. -/
theorem isLocallyFreeOfRank_tensor
    {A B : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)}
    {m n : ℕ}
    [IsLocallyFreeOfRank
      (R := (sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀) A m]
    [IsLocallyFreeOfRank
      (R := (sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀) B n] :
    IsLocallyFreeOfRank
      (R := (sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)
      (A ⊗ B) (m * n) := by
  have hinstA : IsLocallyFreeOfRank
    (R := (sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀) A m :=
    inferInstance
  have hinstB : IsLocallyFreeOfRank
    (R := (sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀) B n :=
    inferInstance
  obtain ⟨qA, hqA⟩ := hinstA.exists_isLocallyFreeOfRankData
  obtain ⟨qB, hqB⟩ := hinstB.exists_isLocallyFreeOfRankData
  have := hqA.isLocallyFreeData
  have := hqB.isLocallyFreeData
  have hcover := CategoryTheory.GrothendieckTopology.CoversTop.prod
    qA.coversTop qB.coversTop
  have piece : ∀ p : qA.I × qB.I,
      ∃ G : ((A ⊗ B : SheafOfModules.{u}
          ((sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)).over
          (Limits.prod (qA.X p.1) (qB.X p.2))).GeneratingSections,
        IsIso G.π ∧ Nonempty (G.I ≃ Fin (m * n)) := by
    intro p
    have : IsIso (qA.generators p.1).π := inferInstance
    have : IsIso (qB.generators p.2).π := inferInstance
    have e := overTensorFreeIso R₀ (Limits.prod (qA.X p.1) (qB.X p.2)) A B
      (overFreeIsoOfMap A Limits.prod.fst _ (asIso (qA.generators p.1).π).symm)
      (overFreeIsoOfMap B Limits.prod.snd _ (asIso (qB.generators p.2).π).symm)
    refine ⟨(_root_.SheafOfModules.free.generatingSections _).ofEpi e.inv, ?_,
      ⟨(Equiv.prodCongr (hqA.rank_eq p.1).some
        (hqB.rank_eq p.2).some).trans finProdFinEquiv⟩⟩
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
    exact (asIso (_root_.SheafOfModules.free.generatingSections _).π ≪≫ e.symm).isIso_hom
  choose gen hgen using piece
  have hfree : (⟨qA.I × qB.I, fun p ↦ Limits.prod (qA.X p.1) (qB.X p.2),
      hcover, gen⟩ : _root_.SheafOfModules.LocalGeneratorsData.{u} (A ⊗ B)).IsLocallyFreeData :=
    ⟨fun p ↦ (hgen p).1⟩
  exact ⟨⟨qA.I × qB.I, fun p ↦ Limits.prod (qA.X p.1) (qB.X p.2),
      hcover, gen⟩, ⟨hfree, fun p ↦ (hgen p).2⟩⟩

omit [∀ (X : C₀) (Y : Over X), HasWeakSheafify ((J₀.over X).over Y) Ab.{u}]
  [∀ (X : C₀) (Y : Over X),
    ((J₀.over X).over Y).WEqualsLocallyBijective Ab.{u}] in
/-- The tensor product of two locally free sheaves of modules is locally free. -/
theorem isLocallyFree_tensor
    {A B : SheafOfModules.{u} ((sheafCompose J₀
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)}
    [_root_.SheafOfModules.IsLocallyFree
      (R := (sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀) A]
    [_root_.SheafOfModules.IsLocallyFree
      (R := (sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀) B] :
    _root_.SheafOfModules.IsLocallyFree
      (R := (sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)
      (A ⊗ B) := by
  have hinstA : _root_.SheafOfModules.IsLocallyFree
    (R := (sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀) A :=
    inferInstance
  have hinstB : _root_.SheafOfModules.IsLocallyFree
    (R := (sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀) B :=
    inferInstance
  obtain ⟨qA, hqA⟩ := hinstA.exists_isLocallyFreeData
  obtain ⟨qB, hqB⟩ := hinstB.exists_isLocallyFreeData
  have := hqA
  have := hqB
  have hcover := CategoryTheory.GrothendieckTopology.CoversTop.prod
    qA.coversTop qB.coversTop
  have piece : ∀ p : qA.I × qB.I,
      ∃ G : ((A ⊗ B : SheafOfModules.{u}
          ((sheafCompose J₀ (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)).over
          (Limits.prod (qA.X p.1) (qB.X p.2))).GeneratingSections,
        IsIso G.π := by
    intro p
    have : IsIso (qA.generators p.1).π := inferInstance
    have : IsIso (qB.generators p.2).π := inferInstance
    have e := overTensorFreeIso R₀ (Limits.prod (qA.X p.1) (qB.X p.2)) A B
      (overFreeIsoOfMap A Limits.prod.fst _ (asIso (qA.generators p.1).π).symm)
      (overFreeIsoOfMap B Limits.prod.snd _ (asIso (qB.generators p.2).π).symm)
    refine ⟨(_root_.SheafOfModules.free.generatingSections _).ofEpi e.inv, ?_⟩
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
    exact (asIso (_root_.SheafOfModules.free.generatingSections _).π ≪≫ e.symm).isIso_hom
  choose gen hgen using piece
  have hfree : (⟨qA.I × qB.I, fun p ↦ Limits.prod (qA.X p.1) (qB.X p.2),
      hcover, gen⟩ : _root_.SheafOfModules.LocalGeneratorsData.{u} (A ⊗ B)).IsLocallyFreeData :=
    ⟨fun p ↦ hgen p⟩
  exact ⟨⟨qA.I × qB.I, fun p ↦ Limits.prod (qA.X p.1) (qB.X p.2),
    hcover, gen⟩, hfree⟩

end Tensor

end SheafOfModules

end
