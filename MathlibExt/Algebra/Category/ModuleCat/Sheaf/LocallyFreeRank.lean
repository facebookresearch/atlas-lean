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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.ULift
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.Basic.Unique
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.Colimits
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.OverLocalSurjective
public import MathlibExt.CategoryTheory.Sites.CoversTop

/-!
# Finite-rank locally free sheaves

Finite free sheaves are locally free of the cardinality of their basis.
Local freeness and fixed rank are preserved by isomorphisms. A free sheaf
on a unique index type is the tensor unit, of rank one; the free sheaf on
an empty index type has rank zero.

Pullback of a finite free sheaf along a final continuous map of ringed
sites preserves its rank. Generating sections restrict to slice sites and
glue over covers. Finite rank therefore glues over covers and is preserved
by restriction to a slice. Finite coproducts and biproducts have the sum of
the ranks of their summands.

These constructions support locally free presentations of coherent sheaves
on quasi-projective schemes (Hartshorne II.5.18).
-/

@[expose] public section

universe u v₁ u₁ v₂ u₂ wD vD wI wI₁ wI₂

open _root_.CategoryTheory CategoryTheory Limits

private theorem functorMapIsIso
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    (F : A ⥤ B) {X Y : A} (f : X ⟶ Y) [IsIso f] : IsIso (F.map f) := by
  infer_instance

private theorem categoricalIdentityIsIso
    {A : Type u₁} [Category.{v₁} A] (X : A) : IsIso (𝟙 X) := by
  infer_instance

-- Public coproduct types need public colimit evidence. Register the
-- universe-pinned discrete-colimit theorem only in this consumer.
attribute [local instance] SheafOfModules.hasColimitsOfShape_discrete

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [HasBinaryProducts C]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

omit [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{u}] in
/-- A finite free sheaf is locally free of rank `Fintype.card I`, witnessed
by the local generator data of its tautological generating sections. -/
theorem isLocallyFreeOfRank_free (I : Type u) [Fintype I] :
    IsLocallyFreeOfRank (R := R) (_root_.SheafOfModules.free (R := R) I) (Fintype.card I) := by
  let q := (_root_.SheafOfModules.free.generatingSections (R := R) I).localGeneratorsData
  have hq : q.IsLocallyFreeData := inferInstance
  refine IsLocallyFreeOfRank.mk ⟨q, hq, ?_⟩
  intro i
  exact ⟨Fintype.equivFin I⟩

omit [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{u}] in
/-- The free sheaf on `ULift (Fin n)` is locally free of rank `n`. -/
theorem isLocallyFreeOfRank_free_fin (n : ℕ) :
    IsLocallyFreeOfRank (R := R) (_root_.SheafOfModules.free (R := R) (ULift.{u} (Fin n))) n := by
  have hcard : Fintype.card (ULift.{u} (Fin n)) = n := by
    rw [Fintype.card_congr Equiv.ulift, Fintype.card_fin]
  have h := isLocallyFreeOfRank_free (R := R) (ULift.{u} (Fin n))
  rwa [hcard] at h

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasBinaryProducts C] in
/-- Finite rank is preserved under isomorphism: transport the local
generator data along the restriction of the iso to each cover member. -/
theorem isLocallyFreeOfRank_of_iso {M N : SheafOfModules.{u} R} {n : ℕ}
    (e : M ≅ N) [hM : IsLocallyFreeOfRank (R := R) M n] :
    IsLocallyFreeOfRank (R := R) N n := by
  obtain ⟨q, hq⟩ := hM.exists_isLocallyFreeOfRankData
  let q' : _root_.SheafOfModules.LocalGeneratorsData.{u₁} N :=
    { I := q.I, X := q.X, coversTop := q.coversTop,
      generators := fun i => (q.generators i).ofEpi
        (((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom) }
  have hfree : q'.IsLocallyFreeData := ⟨fun i => by
    change IsIso (((q.generators i).ofEpi
      (((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom)).π)
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
    exact IsIso.comp_isIso' (hq.isLocallyFreeData.isIso i) (Iso.isIso_hom _)⟩
  exact IsLocallyFreeOfRank.mk ⟨q', hfree, fun i => hq.rank_eq i⟩

/-- The free sheaf on a unique index type is the unit sheaf: a coproduct
over a singleton index is the single summand. -/
noncomputable def freeUniqueIso (I : Type u) [Unique I] :
    _root_.SheafOfModules.free (R := R) I ≅ _root_.SheafOfModules.unit (R := R) :=
  coproductUniqueIso (fun _ : I => _root_.SheafOfModules.unit (R := R))

/-- The unit sheaf is locally free of rank one, via the free sheaf on
`ULift (Fin 1)`. This is the single rank-one unit lemma (replacing the
split-epi argument formerly in `Sheaf/LocallyFree.lean`). -/
theorem isLocallyFreeOfRank_unit :
    IsLocallyFreeOfRank (R := R) (_root_.SheafOfModules.unit (R := R)) 1 := by
  have h1 := isLocallyFreeOfRank_free_fin (R := R) (n := 1)
  exact isLocallyFreeOfRank_of_iso (freeUniqueIso (R := R) (ULift.{u} (Fin 1)))
    (hM := h1)

section PullbackFree

variable {C' : Type u₂} [Category.{v₂} C'] {K : GrothendieckTopology C'}
  {S : Sheaf K RingCat.{u}}
  [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C' ⥤ C} [Functor.IsContinuous F K J] [F.Final]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K J).obj R)
  [(_root_.SheafOfModules.pushforward φ).IsRightAdjoint]

/-- The pullback of a finite free sheaf along a final continuous map of
ringed sites is locally free of rank `Fintype.card I`. -/
theorem isLocallyFreeOfRank_pullback_free (I : Type u) [Fintype I] :
    IsLocallyFreeOfRank (R := R)
      ((_root_.SheafOfModules.pullback φ).obj (_root_.SheafOfModules.free (R := S) I))
      (Fintype.card I) := by
  have h := isLocallyFreeOfRank_free (R := R) I
  exact isLocallyFreeOfRank_of_iso (_root_.SheafOfModules.pullbackObjFreeIso φ I).symm (hM := h)

end PullbackFree

/-- A binary coproduct of finite free sheaves is locally free of additive
rank, via `freeSumIso`. -/
theorem isLocallyFreeOfRank_coprod_free (I J : Type u) [Fintype I]
    [Fintype J] :
    IsLocallyFreeOfRank (R := R)
      (_root_.SheafOfModules.free (R := R) I ⨿ _root_.SheafOfModules.free (R := R) J)
      (Fintype.card I + Fintype.card J) := by
  have h := isLocallyFreeOfRank_free (R := R) (I ⊕ J)
  rw [Fintype.card_sum] at h
  exact isLocallyFreeOfRank_of_iso (_root_.SheafOfModules.freeSumIso (R := R) I J).symm (hM := h)

/-- The coproduct of the free sheaves on `ULift (Fin m)` and
`ULift (Fin n)` is locally free of rank `m + n`. -/
theorem isLocallyFreeOfRank_coprod_free_fin (m n : ℕ) :
    IsLocallyFreeOfRank (R := R)
      (_root_.SheafOfModules.free (R := R) (ULift.{u} (Fin m)) ⨿
        _root_.SheafOfModules.free (R := R) (ULift.{u} (Fin n))) (m + n) := by
  have h := isLocallyFreeOfRank_coprod_free (R := R) (ULift.{u} (Fin m))
    (ULift.{u} (Fin n))
  have hm : Fintype.card (ULift.{u} (Fin m)) = m := by
    rw [Fintype.card_congr Equiv.ulift, Fintype.card_fin]
  have hn : Fintype.card (ULift.{u} (Fin n)) = n := by
    rw [Fintype.card_congr Equiv.ulift, Fintype.card_fin]
  rwa [hm, hn] at h

omit [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{u}] in
/-- The free sheaf on `ULift Empty` is locally free of rank zero. -/
theorem isLocallyFreeOfRank_free_ulift_empty :
    IsLocallyFreeOfRank (R := R) (_root_.SheafOfModules.free (R := R) (ULift.{u} Empty)) 0 := by
  have h := isLocallyFreeOfRank_free (R := R) (ULift.{u} Empty)
  have hcard : Fintype.card (ULift.{u} Empty) = 0 := by
    rw [Fintype.card_congr Equiv.ulift, Fintype.card_empty]
  rwa [hcard] at h

section Bind

variable [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

section BindEquivGeneral

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}}

/-- The comparison equivalence identifying doubly restricted module
sheaves `(M.over X).over Y` with singly restricted ones
`M.over Y.left`, via the iterated slice equivalence. Stated over an
arbitrary site since restriction-stability arguments apply it at
every slice. -/
noncomputable abbrev _root_.SheafOfModules.LocalGeneratorsData.bindEquiv {X : C'} (Y : Over X) :
    SheafOfModules (S.over Y.left) ≌ SheafOfModules ((S.over X).over Y) :=
  _root_.SheafOfModules.overOverEquivalence (S := S) Y

/-- The unit sheaf is preserved definitionally by the inverse of
`LocalGeneratorsData.bindEquiv`, but stated with syntactic sides so that
transported terms stay well-typed at reducible transparency. -/
noncomputable def _root_.SheafOfModules.LocalGeneratorsData.bindEquivUnitIso {X : C'} (Y : Over X) :
    _root_.SheafOfModules.unit (S.over Y.left) ≅
      (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv (S := S) Y).inverse.obj
        (_root_.SheafOfModules.unit ((S.over X).over Y)) :=
  eqToIso (show _root_.SheafOfModules.unit (S.over Y.left) =
    (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv (S := S) Y).inverse.obj
      (_root_.SheafOfModules.unit ((S.over X).over Y)) from rfl)

end BindEquivGeneral

/-- Transport doubly restricted generating sections to singly restricted
ones along `LocalGeneratorsData.bindEquiv`. -/
noncomputable def _root_.SheafOfModules.LocalGeneratorsData.bindGenerators {X : C}
    {M : SheafOfModules.{u} R} (Y : Over X)
    (G : ((M.over X).over Y).GeneratingSections) :
    (M.over Y.left).GeneratingSections :=
  (G.map (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).inverse
    (_root_.SheafOfModules.LocalGeneratorsData.bindEquivUnitIso Y)).ofEpi
    ((_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).fullyFaithfulFunctor.preimageIso
      (by exact (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).counitIso.app
            ((M.over X).over Y))).hom

/-- Given a cover `X` and local generator data for each restriction
`M.over (X i)`, glue them into local generator data for `M` itself,
following `SheafOfModules.QuasicoherentData.bind`. -/
noncomputable def _root_.SheafOfModules.LocalGeneratorsData.bind (M : SheafOfModules.{u} R)
    {I : Type u₁} (X : I → C) (hX : J.CoversTop X)
    (D : Π i, _root_.SheafOfModules.LocalGeneratorsData.{max u₁ v₁} (M.over (X i))) :
    _root_.SheafOfModules.LocalGeneratorsData.{max u₁ v₁} M where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i ↦ (D i).coversTop)
  generators i :=
    _root_.SheafOfModules.LocalGeneratorsData.bindGenerators ((D i.1).X i.2)
        ((D i.1).generators i.2)

/-- Glued generator data preserves the locally-free property: the
transported comparison map is a composite of isomorphisms. -/
instance LocalGeneratorsData.bind_isLocallyFreeData
    (M : SheafOfModules.{u} R) {I : Type u₁} (X : I → C)
    (hX : J.CoversTop X)
    (D : Π i, _root_.SheafOfModules.LocalGeneratorsData.{max u₁ v₁} (M.over (X i)))
    [hD : ∀ i, (D i).IsLocallyFreeData] :
    (_root_.SheafOfModules.LocalGeneratorsData.bind M X hX D).IsLocallyFreeData where
  isIso i := by
    obtain ⟨i1, i2⟩ := i
    change IsIso ((_root_.SheafOfModules.LocalGeneratorsData.bindGenerators ((D i1).X i2)
      ((D i1).generators i2)).π)
    dsimp only [_root_.SheafOfModules.LocalGeneratorsData.bindGenerators]
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
    refine IsIso.comp_isIso' ?_ (Iso.isIso_hom _)
    rw [_root_.SheafOfModules.GeneratingSections.map_π_eq]
    refine IsIso.comp_isIso' (Iso.isIso_hom _) ?_
    have := (hD i1).isIso i2
    infer_instance

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasBinaryProducts C] in
/-- Finite rank glues over a cover: if every restriction `M.over (X i)`
carries rank-`n` local generator data, so does `M`. The glued data is
shrunk back into the site universe. -/
theorem IsLocallyFreeOfRank.of_coversTop (M : SheafOfModules.{u} R)
    {n : ℕ} {I : Type u₁} (X : I → C) (hX : J.CoversTop X)
    (D : Π i, _root_.SheafOfModules.LocalGeneratorsData.{max u₁ v₁} (M.over (X i)))
    [hD : ∀ i, LocalGeneratorsData.IsLocallyFreeOfRankData (D i) n] :
    IsLocallyFreeOfRank (R := R) M n := by
  have : ∀ i, (D i).IsLocallyFreeData := fun i ↦ (hD i).isLocallyFreeData
  have hshrink :
      ((_root_.SheafOfModules.LocalGeneratorsData.bind M X hX D).shrink).IsLocallyFreeData :=
    inferInstance
  refine IsLocallyFreeOfRank.mk
    ⟨(_root_.SheafOfModules.LocalGeneratorsData.bind M X hX D).shrink,
      hshrink, ?_⟩
  · intro i
    exact (hD (i.2.choose).1).rank_eq (i.2.choose).2

end Bind

end SheafOfModules

namespace CategoryTheory.Limits

variable {D : Type wD} [Category.{vD} D]

/-- A coproduct over a sum index type splits as a binary coproduct of
the two constituent coproducts, via `Cofan.combPairIsColimit`. -/
noncomputable def coproductSumIso {ι₁ : Type wI₁} {ι₂ : Type wI₂}
    {f₁ : ι₁ → D} {f₂ : ι₂ → D} [_root_.CategoryTheory.Limits.HasCoproduct f₁]
    [_root_.CategoryTheory.Limits.HasCoproduct f₂]
    [_root_.CategoryTheory.Limits.HasCoproduct (Sum.elim f₁ f₂)]
    [_root_.CategoryTheory.Limits.HasBinaryCoproduct (∐ f₁) (∐ f₂)] :
    ∐ (Sum.elim f₁ f₂) ≅ (∐ f₁) ⨿ (∐ f₂) :=
  _root_.CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso
      (_root_.CategoryTheory.Limits.coproductIsCoproduct _)
    (_root_.CategoryTheory.Limits.Cofan.combPairIsColimit
        (_root_.CategoryTheory.Limits.coproductIsCoproduct f₁)
      (_root_.CategoryTheory.Limits.coproductIsCoproduct f₂)
          (_root_.CategoryTheory.Limits.coprodIsCoprod (∐ f₁) (∐ f₂)))

/-- A coproduct over an empty index type is initial: the diagram is
empty, so the colimit cocone is colimiting iff its point is initial. -/
noncomputable def isInitialCoproductOfIsEmpty {ι : Type wI} [IsEmpty ι]
    (f : ι → D) [_root_.CategoryTheory.Limits.HasCoproduct f] :
    _root_.CategoryTheory.Limits.IsInitial (∐ f) :=
  (_root_.CategoryTheory.Limits.isColimitEquivIsInitialOfIsEmpty D
    (colimit.cocone (_root_.CategoryTheory.Discrete.functor f)))
    (colimit.isColimit _)

end CategoryTheory.Limits

namespace SheafOfModules

section Biprod

variable [HasPullbacks C]

/-- Restriction to a slice site is a left adjoint. -/
instance overFunctorIsLeftAdjoint (X : C) :
    (_root_.SheafOfModules.overFunctor R X : SheafOfModules.{u} R ⥤
      SheafOfModules.{u} (R.over X)).IsLeftAdjoint := by
  unfold _root_.SheafOfModules.overFunctor
  infer_instance

/-- Restriction to an over category preserves binary coproduct pairs. -/
instance overFunctorPreservesColimitPair (X : C)
    (M N : SheafOfModules.{u} R) :
    PreservesColimit (pair M N) (_root_.SheafOfModules.overFunctor R X) := by
  have : PreservesColimitsOfSize.{u, u} (_root_.SheafOfModules.overFunctor R X) :=
    (Adjunction.ofIsLeftAdjoint
      (_root_.SheafOfModules.overFunctor R X)).leftAdjoint_preservesColimits
  infer_instance

omit [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}] in
/-- Restrict generating sections along a morphism of the site. -/
noncomputable def _root_.SheafOfModules.GeneratingSections.overRestrict
    {M : SheafOfModules.{u} R} {X Y : C} (f : X ⟶ Y)
    (G : (M.over Y).GeneratingSections) :
    (M.over X).GeneratingSections :=
  (G.map (_root_.SheafOfModules.overMap R f)
      (_root_.SheafOfModules.overMapUnitIso (R := R) f).symm).ofEpi
    ((_root_.SheafOfModules.overFunctorMap R f).app M).hom

omit [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}] in
/-- Restriction preserves the locally-free property. -/
instance GeneratingSections.isIso_π_overRestrict
    {M : SheafOfModules.{u} R} {X Y : C} {f : X ⟶ Y}
    {G : (M.over Y).GeneratingSections}
    [IsIso G.π] : IsIso (GeneratingSections.overRestrict f G).π := by
  unfold _root_.SheafOfModules.GeneratingSections.overRestrict
  rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
  refine IsIso.comp_isIso' ?_ (Iso.isIso_hom _)
  rw [_root_.SheafOfModules.GeneratingSections.map_π_eq]
  exact IsIso.comp_isIso' (Iso.isIso_hom _)
    (functorMapIsIso (_root_.SheafOfModules.overMap R f) G.π)

omit [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}] in
/-- Restriction preserves finite generating families. -/
instance GeneratingSections.isFiniteType_overRestrict
    {M : SheafOfModules.{u} R} {X Y : C} {f : X ⟶ Y}
    {G : (M.over Y).GeneratingSections}
    [G.IsFiniteType] : (GeneratingSections.overRestrict f G).IsFiniteType := by
  unfold _root_.SheafOfModules.GeneratingSections.overRestrict
  infer_instance

section CoprodGenerators

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {R' : Sheaf J' RingCat.{u}}
  [HasWeakSheafify J' AddCommGrpCat.{u}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The sum of two iso-generating families along a binary coproduct,
indexed by the sum of the index types. -/
noncomputable def _root_.SheafOfModules.GeneratingSections.coprod {M N : SheafOfModules.{u} R'}
    [_root_.CategoryTheory.Limits.HasBinaryCoproduct M N] (G : M.GeneratingSections)
    (H : N.GeneratingSections) [IsIso G.π] [IsIso H.π] :
    (M ⨿ N).GeneratingSections :=
  (_root_.SheafOfModules.free.generatingSections (R := R') (G.I ⊕ H.I)).ofEpi
    ((_root_.SheafOfModules.freeSumIso (R := R') G.I H.I).symm ≪≫
      coprod.mapIso (asIso G.π) (asIso H.π)).hom

/-- The summed generators still present an isomorphism. -/
instance _root_.SheafOfModules.GeneratingSections.isIso_π_coprod {M N : SheafOfModules.{u} R'}
    [_root_.CategoryTheory.Limits.HasBinaryCoproduct M N] {G : M.GeneratingSections}
    {H : N.GeneratingSections} [IsIso G.π] [IsIso H.π] :
    IsIso (GeneratingSections.coprod G H).π := by
  unfold _root_.SheafOfModules.GeneratingSections.coprod
  rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
  refine IsIso.comp_isIso' ?_ (Iso.isIso_hom _)
  rw [_root_.SheafOfModules.free.generatingSections_π]
  exact categoricalIdentityIsIso (_root_.SheafOfModules.free (R := R') (G.I ⊕ H.I))

end CoprodGenerators

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A binary coproduct of finite-rank locally free sheaves is locally
free of additive rank, via the product cover and restriction of the
given generator data along the product projections. -/
theorem isLocallyFreeOfRank_coprod {M N : SheafOfModules.{u} R}
    [_root_.CategoryTheory.Limits.HasBinaryCoproduct M N] {m n : ℕ}
    [IsLocallyFreeOfRank (R := R) M m]
    [IsLocallyFreeOfRank (R := R) N n] :
    IsLocallyFreeOfRank (R := R) (M ⨿ N) (m + n) := by
  obtain ⟨qM, hqM⟩ :=
    IsLocallyFreeOfRank.exists_isLocallyFreeOfRankData (M := M) (n := m)
  obtain ⟨qN, hqN⟩ :=
    IsLocallyFreeOfRank.exists_isLocallyFreeOfRankData (M := N) (n := n)
  have := hqM.isLocallyFreeData
  have := hqN.isLocallyFreeData
  let q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} (M ⨿ N) :=
    { I := qM.I × qN.I,
      X := fun p ↦ qM.X p.1 ⨯ qN.X p.2,
      coversTop := CategoryTheory.GrothendieckTopology.CoversTop.prod qM.coversTop qN.coversTop,
      generators := fun p ↦
        (GeneratingSections.coprod
            (GeneratingSections.overRestrict
              (prod.fst : qM.X p.1 ⨯ qN.X p.2 ⟶ qM.X p.1)
              (qM.generators p.1))
            (GeneratingSections.overRestrict
              (prod.snd : qM.X p.1 ⨯ qN.X p.2 ⟶ qN.X p.2)
              (qN.generators p.2))).ofEpi
          (PreservesColimitPair.iso
            (_root_.SheafOfModules.overFunctor R (qM.X p.1 ⨯ qN.X p.2)) M N).hom }
  have hfree : q.IsLocallyFreeData := ⟨fun p => by
    change IsIso (((_root_.SheafOfModules.GeneratingSections.coprod _ _).ofEpi _).π)
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
    refine IsIso.comp_isIso' ?_ (Iso.isIso_hom _)
    refine _root_.SheafOfModules.GeneratingSections.isIso_π_coprod⟩
  have hrank : ∀ p : qM.I × qN.I, Nonempty (((qM.generators p.1).I ⊕
      (qN.generators p.2).I) ≃ Fin (m + n)) := fun p => by
    obtain ⟨eM⟩ := hqM.rank_eq p.1
    obtain ⟨eN⟩ := hqN.rank_eq p.2
    exact ⟨(eM.sumCongr eN).trans finSumFinEquiv⟩
  exact IsLocallyFreeOfRank.mk ⟨q, hfree, hrank⟩

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A binary biproduct of finite-rank locally free sheaves is locally
free of additive rank, via the coproduct closure and `biprod.isoCoprod`.
This is the single ranked biproduct lemma (replacing the two `piece`
constructions formerly in `Sheaf/LocallyFree.lean`). -/
theorem isLocallyFreeOfRank_biprod
    {M N : SheafOfModules.{u} R} [HasBinaryBiproduct M N] {m n : ℕ}
    [IsLocallyFreeOfRank (R := R) M m]
    [IsLocallyFreeOfRank (R := R) N n] :
    IsLocallyFreeOfRank (R := R) (M ⊞ N) (m + n) := by
  have h := isLocallyFreeOfRank_coprod
    (R := R) (M := M) (N := N) (m := m) (n := n)
  exact isLocallyFreeOfRank_of_iso
    (biprod.isoCoprod M N).symm (hM := h)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}] [HasBinaryProducts C]
  [HasPullbacks C] in
/-- Unranked local freeness is preserved under isomorphism: transport the
local generator data along the restriction of the iso to each cover
member. -/
theorem IsLocallyFree.of_iso {M N : SheafOfModules.{u} R}
    (e : M ≅ N) [hM : _root_.SheafOfModules.IsLocallyFree (R := R) M] :
    _root_.SheafOfModules.IsLocallyFree (R := R) N := by
  obtain ⟨q, hq⟩ := hM.exists_isLocallyFreeData
  let q' : _root_.SheafOfModules.LocalGeneratorsData.{u₁} N :=
    { I := q.I, X := q.X, coversTop := q.coversTop,
      generators := fun i => (q.generators i).ofEpi
        (((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom) }
  refine ⟨q', ?_⟩
  constructor
  intro i
  change IsIso (((q.generators i).ofEpi
    (((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom)).π)
  rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
  exact IsIso.comp_isIso' (hq.isIso i) (Iso.isIso_hom _)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A binary coproduct of locally free sheaves is locally free, via the
product cover and restriction of the given generator data along the
product projections (the unranked shadow of `isLocallyFreeOfRank_coprod`,
sharing its `coprod`/`overRestrict` pipeline). -/
theorem isLocallyFree_coprod {M N : SheafOfModules.{u} R}
    [_root_.CategoryTheory.Limits.HasBinaryCoproduct M N]
    [_root_.SheafOfModules.IsLocallyFree (R := R) M]
    [_root_.SheafOfModules.IsLocallyFree (R := R) N] :
    _root_.SheafOfModules.IsLocallyFree (R := R) (M ⨿ N) := by
  obtain ⟨qM, hqM⟩ :=
    (inferInstance : _root_.SheafOfModules.IsLocallyFree (R := R) M).exists_isLocallyFreeData
  obtain ⟨qN, hqN⟩ :=
    (inferInstance : _root_.SheafOfModules.IsLocallyFree (R := R) N).exists_isLocallyFreeData
  have := hqM
  have := hqN
  let q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} (M ⨿ N) :=
    { I := qM.I × qN.I,
      X := fun p ↦ qM.X p.1 ⨯ qN.X p.2,
      coversTop := CategoryTheory.GrothendieckTopology.CoversTop.prod qM.coversTop qN.coversTop,
      generators := fun p ↦
        (GeneratingSections.coprod
            (GeneratingSections.overRestrict
              (prod.fst : qM.X p.1 ⨯ qN.X p.2 ⟶ qM.X p.1)
              (qM.generators p.1))
            (GeneratingSections.overRestrict
              (prod.snd : qM.X p.1 ⨯ qN.X p.2 ⟶ qN.X p.2)
              (qN.generators p.2))).ofEpi
          (PreservesColimitPair.iso
            (_root_.SheafOfModules.overFunctor R (qM.X p.1 ⨯ qN.X p.2)) M N).hom }
  refine ⟨q, ?_⟩
  constructor
  intro p
  change IsIso (((_root_.SheafOfModules.GeneratingSections.coprod _ _).ofEpi _).π)
  rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
  refine IsIso.comp_isIso' ?_ (Iso.isIso_hom _)
  refine _root_.SheafOfModules.GeneratingSections.isIso_π_coprod

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A binary biproduct of locally free sheaves is locally free, via the
coproduct closure and `biprod.isoCoprod`. This is the single unranked
biproduct lemma (replacing the `piece` construction formerly in
`Sheaf/LocallyFree.lean`). -/
theorem isLocallyFree_biprod
    {M N : SheafOfModules.{u} R} [HasBinaryBiproduct M N]
    [_root_.SheafOfModules.IsLocallyFree (R := R) M]
    [_root_.SheafOfModules.IsLocallyFree (R := R) N] :
    _root_.SheafOfModules.IsLocallyFree (R := R) (M ⊞ N) := by
  have h := isLocallyFree_coprod (R := R) (M := M) (N := N)
  exact IsLocallyFree.of_iso (biprod.isoCoprod M N).symm (hM := h)

end Biprod

section Over

variable [HasPullbacks C]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The forward unit comparison for `LocalGeneratorsData.bindEquiv`,
lifting the unit sheaf across the iterated-slice equivalence. -/
noncomputable def _root_.SheafOfModules.LocalGeneratorsData.bindEquivUnitIsoForward {X : C}
    (Y : Over X) :
    _root_.SheafOfModules.unit ((R.over X).over Y) ≅
      (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).functor.obj
        (_root_.SheafOfModules.unit (R.over Y.left)) :=
  eqToIso (show _root_.SheafOfModules.unit ((R.over X).over Y) =
    (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).functor.obj
      (_root_.SheafOfModules.unit (R.over Y.left)) from rfl)

/-- Lift generating sections across the iterated-slice equivalence:
from `M.over Y.left` to `(M.over X).over Y`. This is the forward
direction of `LocalGeneratorsData.bindGenerators`. -/
noncomputable def _root_.SheafOfModules.LocalGeneratorsData.bindGeneratorsForward {X : C}
    {M : SheafOfModules.{u} R} (Y : Over X)
    (G : (M.over Y.left).GeneratingSections) :
    ((M.over X).over Y).GeneratingSections :=
  (G.map (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).functor
    (_root_.SheafOfModules.LocalGeneratorsData.bindEquivUnitIsoForward Y)).ofEpi
    (((_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).functor.mapIso
      (((_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).fullyFaithfulFunctor.preimageIso
        (by exact (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).counitIso.app
              ((M.over X).over Y))).symm) ≪≫
      (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).counitIso.app
        ((M.over X).over Y)).hom)

/-- Forward transport preserves the locally-free property. -/
instance _root_.SheafOfModules.LocalGeneratorsData.isIso_π_bindGeneratorsForward {X : C}
    {M : SheafOfModules.{u} R} {Y : Over X}
    {G : (M.over Y.left).GeneratingSections} [IsIso G.π] :
    IsIso ((_root_.SheafOfModules.LocalGeneratorsData.bindGeneratorsForward Y G).π) := by
  unfold _root_.SheafOfModules.LocalGeneratorsData.bindGeneratorsForward
  rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
  refine IsIso.comp_isIso' ?_ (Iso.isIso_hom _)
  rw [_root_.SheafOfModules.GeneratingSections.map_π_eq]
  exact IsIso.comp_isIso' (Iso.isIso_hom _)
    (functorMapIsIso (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).functor G.π)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasBinaryProducts C] in
/-- Restriction to a slice preserves finite rank: over the comma cover,
each comma object carries the given generators restricted along its
span and lifted across the iterated-slice equivalence. -/
theorem isLocallyFreeOfRank_over {M : SheafOfModules.{u} R} {n : ℕ}
    [IsLocallyFreeOfRank (R := R) M n] (X₀ : C) :
    IsLocallyFreeOfRank (R := R.over X₀) (M.over X₀) n := by
  obtain ⟨q, hq⟩ :=
    IsLocallyFreeOfRank.exists_isLocallyFreeOfRankData (M := M) (n := n)
  have := hq.isLocallyFreeData
  let q' : _root_.SheafOfModules.LocalGeneratorsData.{max u₁ v₁} (M.over X₀) :=
    { I := (i : q.I) × (Z : C) × (Z ⟶ q.X i) × (Z ⟶ X₀),
      X := fun p ↦ _root_.CategoryTheory.Over.mk p.2.2.2,
      coversTop := CategoryTheory.GrothendieckTopology.CoversTop.overComma q.coversTop X₀,
      generators := fun p ↦
        _root_.SheafOfModules.LocalGeneratorsData.bindGeneratorsForward
            (_root_.CategoryTheory.Over.mk p.2.2.2)
          (GeneratingSections.overRestrict p.2.2.1 (q.generators p.1)) }
  have hfree : q'.IsLocallyFreeData := ⟨fun p =>
    _root_.SheafOfModules.LocalGeneratorsData.isIso_π_bindGeneratorsForward⟩
  exact IsLocallyFreeOfRank.mk ⟨q', hfree, fun p => hq.rank_eq p.1⟩

end Over

section FinCoproduct

variable [HasPullbacks C]

/-- A coproduct over a sum index type of finite-rank coproducts is
locally free of additive rank, via `coproductSumIso` and the binary
coproduct closure. -/
theorem isLocallyFreeOfRank_coproduct_sum {ι₁ ι₂ : Type*}
    {f₁ : ι₁ → SheafOfModules.{u} R}
    {f₂ : ι₂ → SheafOfModules.{u} R} {m n : ℕ}
    [Small.{u} ι₁] [Small.{u} ι₂]
    [IsLocallyFreeOfRank (R := R) (∐ f₁) m]
    [IsLocallyFreeOfRank (R := R) (∐ f₂) n] :
    IsLocallyFreeOfRank (R := R) (∐ (Sum.elim f₁ f₂)) (m + n) := by
  have h := isLocallyFreeOfRank_coprod (M := ∐ f₁) (N := ∐ f₂)
    (m := m) (n := n)
  exact isLocallyFreeOfRank_of_iso
    (coproductSumIso (f₁ := f₁) (f₂ := f₂)).symm (hM := h)

/-- A `Fin n`-indexed coproduct of finite-rank sheaves is locally free
of rank the sum of the ranks, by induction via `finSumFinEquiv`. The
empty case transports rank zero from `free (ULift Empty)` along the
unique iso between initial objects. -/
theorem isLocallyFreeOfRank_coproduct_fin (n : ℕ)
    (M : Fin n → SheafOfModules.{u} R) (r : Fin n → ℕ)
    (h : ∀ i, IsLocallyFreeOfRank (R := R) (M i) (r i)) :
    IsLocallyFreeOfRank (R := R) (∐ M) (∑ i, r i) := by
  induction n with
  | zero =>
      have hsum : ∑ i : Fin 0, r i = 0 := Fintype.sum_empty _
      rw [hsum]
      exact isLocallyFreeOfRank_of_iso
        ((isInitialCoproductOfIsEmpty
          (fun _ : ULift.{u} Empty => _root_.SheafOfModules.unit R)).uniqueUpToIso
          (isInitialCoproductOfIsEmpty M))
        (hM := isLocallyFreeOfRank_free_ulift_empty)
  | succ n ih =>
      let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
      let f₁ : Fin n → SheafOfModules.{u} R := fun i => M (e (Sum.inl i))
      let f₂ : Fin 1 → SheafOfModules.{u} R := fun j => M (e (Sum.inr j))
      let r₁ : Fin n → ℕ := fun i => r (e (Sum.inl i))
      let r₂ : Fin 1 → ℕ := fun j => r (e (Sum.inr j))
      have h₁ : ∀ i, IsLocallyFreeOfRank (R := R) (f₁ i) (r₁ i) :=
        fun i => h _
      have h₂ : ∀ j, IsLocallyFreeOfRank (R := R) (f₂ j) (r₂ j) :=
        fun j => h _
      have ih1 := ih f₁ r₁ h₁
      have h2rank : IsLocallyFreeOfRank (R := R) (∐ f₂) (r₂ default) := by
        have : IsLocallyFreeOfRank (R := R) (f₂ default) (r₂ default) :=
          h₂ default
        exact isLocallyFreeOfRank_of_iso (coproductUniqueIso f₂).symm
      have := ih1
      have := h2rank
      have hsum := isLocallyFreeOfRank_coproduct_sum (f₁ := f₁)
        (f₂ := f₂) (m := ∑ i, r₁ i) (n := r₂ default)
      have hfun : Sum.elim f₁ f₂ = M ∘ e := by
        funext x
        cases x with
        | inl a => rfl
        | inr b => rfl
      have e1 : ∐ (Sum.elim f₁ f₂) ≅ ∐ (M ∘ e) :=
        Sigma.whiskerEquiv (Equiv.refl (Fin n ⊕ Fin 1))
          (fun x => eqToIso (congrFun hfun x).symm)
      have e2 : ∐ (M ∘ e) ≅ ∐ M := Sigma.reindex e M
      have hrank : (∑ i, r₁ i) + r₂ default = ∑ j, r j := by
        have h1 : ∑ x : Fin n ⊕ Fin 1, r (e x) = ∑ j, r j :=
          Equiv.sum_comp e r
        have h2 : ∑ j : Fin 1, r (e (Sum.inr j)) = r₂ default :=
          Fintype.sum_unique _
        simp only [Fintype.sum_sum_type, h2] at h1
        exact h1
      rw [hrank] at hsum
      exact isLocallyFreeOfRank_of_iso (e1 ≪≫ e2) (hM := hsum)

/-- A fintype-indexed coproduct of finite-rank sheaves is locally free
of rank the sum of the ranks, via `Fintype.equivFin` and the `Fin`
case. This is the form the II.5.18 finite-direct-sum input needs. -/
theorem isLocallyFreeOfRank_coproduct_fintype {ι : Type*} [Fintype ι]
    [Small.{u} ι] (M : ι → SheafOfModules.{u} R) (r : ι → ℕ)
    (h : ∀ i, IsLocallyFreeOfRank (R := R) (M i) (r i)) :
    IsLocallyFreeOfRank (R := R) (∐ M) (∑ i, r i) := by
  let e := Fintype.equivFin ι
  let g : Fin (Fintype.card ι) → SheafOfModules.{u} R :=
    fun j => M (e.symm j)
  let s : Fin (Fintype.card ι) → ℕ := fun j => r (e.symm j)
  have hg : ∀ j, IsLocallyFreeOfRank (R := R) (g j) (s j) :=
    fun j => h _
  have hfin := isLocallyFreeOfRank_coproduct_fin _ g s hg
  have e1 : ∐ M ≅ ∐ g :=
    Sigma.whiskerEquiv e
      (fun i => eqToIso (by change M (e.symm (e i)) = M i; simp))
  have hs : ∑ j, s j = ∑ i, r i := Fintype.sum_equiv e.symm s r
    (fun j => rfl)
  rw [hs] at hfin
  exact isLocallyFreeOfRank_of_iso e1.symm (hM := hfin)

end FinCoproduct

end SheafOfModules

end
