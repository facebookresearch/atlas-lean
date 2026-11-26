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
# Local ranks and coproducts of module sheaves

Let `C : Type u₁` have morphism universe `v₁`, `J` be a topology, and `R : Sheaf J
RingCat.{u}`. A prescribed local rank records the cardinality of local free generating
families. With weak additive sheafification and the locally-bijective comparison on `J`, and
strong and weak additive sheafification with the comparison on every first slice, finite free
sheaves have the cardinality of their index set as local rank. The structure module has rank
one and the empty free sheaf has rank zero.

Local generator data transport through isomorphisms and the direct/iterated slice equivalence.
Assembly across covers uses additive sheafification and the locally-bijective comparison on
second slices. With pullbacks, restriction to a slice preserves rank. With binary products and
pullbacks, binary coproducts and biproducts add ranks; finite indexed coproducts have rank
equal to the sum of the summand ranks.

For a continuous final functor between ringed sites and a coefficient map whose pushforward is
a right adjoint, pullback of a finite free sheaf preserves its prescribed rank, with weak
additive sheafification and the locally-bijective comparison on both base sites.

## References

* R. Hartshorne, *Algebraic Geometry*, II.5.18, for geometric applications of finite locally free presentations.
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
/-- Let `C : Type u₁` have morphism universe `v₁` and binary products, `J` be a topology, and `R :
Sheaf J RingCat.{u}`. Assume weak additive sheafification and the locally-bijective comparison
on `J`, and additive sheafification with that comparison on every slice. For `I : Type u` with
`Fintype I`, `free_R I` is locally free of rank `Fintype.card I`. -/
theorem isLocallyFreeOfRank_free (I : Type u) [Fintype I] :
    IsLocallyFreeOfRank (R := R) (_root_.SheafOfModules.free (R := R) I) (Fintype.card I) := by
  let q := (_root_.SheafOfModules.free.generatingSections (R := R) I).localGeneratorsData
  have hq : q.IsLocallyFreeData := inferInstance
  refine IsLocallyFreeOfRank.mk ⟨q, hq, ?_⟩
  intro i
  exact ⟨Fintype.equivFin I⟩

omit [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{u}] in
/-- Let `(C,J,R)` be a ringed site with binary products in `C`, ring/module universe `u`, weak
additive sheafification and the locally-bijective comparison on `J`, and additive
sheafification with that comparison on all slices. For every `n : ℕ`, `free_R (ULift.{u} (Fin
n))` is locally free of rank `n`. -/
theorem isLocallyFreeOfRank_free_fin (n : ℕ) :
    IsLocallyFreeOfRank (R := R) (_root_.SheafOfModules.free (R := R) (ULift.{u} (Fin n))) n := by
  have hcard : Fintype.card (ULift.{u} (Fin n)) = n := by
    rw [Fintype.card_congr Equiv.ulift, Fintype.card_fin]
  have h := isLocallyFreeOfRank_free (R := R) (ULift.{u} (Fin n))
  rwa [hcard] at h

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasBinaryProducts C] in
/-- Let `(C,J)` be a site with `R : Sheaf J RingCat.{u}`. Assume strong and weak additive
sheafification and the locally-bijective comparison on every slice `J.over X`. For `e : M ≅ N`
between module sheaves of carrier universe `u`, if `M` is locally free of rank `n : ℕ`, then
`N` is locally free of the same rank. -/
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

/-- Let `(C,J)` be a site and `R : Sheaf J RingCat.{u}`, with weak additive sheafification and the
locally-bijective comparison on `J`. For `I : Type u` with `Unique I`, the free sheaf `free_R
I` is isomorphic to `SheafOfModules.unit R`, the structure sheaf regarded as its own left
module. -/
noncomputable def freeUniqueIso (I : Type u) [Unique I] :
    _root_.SheafOfModules.free (R := R) I ≅ _root_.SheafOfModules.unit (R := R) :=
  coproductUniqueIso (fun _ : I => _root_.SheafOfModules.unit (R := R))

/-- Let `(C,J,R)` be a ringed site with binary products in `C`, ring/module universe `u`, weak
additive sheafification and the locally-bijective comparison on `J`, and strong and weak
additive sheafification with that comparison on all slices. The structure module
`SheafOfModules.unit R` is locally free of rank one. -/
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

/-- Let `(C,J,R)` and `(C',K,S)` be ringed sites with ring/module universe `u`, object universes
`u₁,u₂`, and morphism universes `v₁,v₂`. Assume weak additive sheafification and the
locally-bijective comparison on both base sites, binary products in `C`, and strong and weak
additive sheafification with the comparison on all `J`-slices. Let `F : C' ⥤ C` be continuous
and final, and `φ : S → F_*R` have right-adjoint module pushforward. For a finite `I : Type u`
with `Fintype I`, `pullback φ (free_S I)` is locally free of rank `Fintype.card I`. -/
theorem isLocallyFreeOfRank_pullback_free (I : Type u) [Fintype I] :
    IsLocallyFreeOfRank (R := R)
      ((_root_.SheafOfModules.pullback φ).obj (_root_.SheafOfModules.free (R := S) I))
      (Fintype.card I) := by
  have h := isLocallyFreeOfRank_free (R := R) I
  exact isLocallyFreeOfRank_of_iso (_root_.SheafOfModules.pullbackObjFreeIso φ I).symm (hM := h)

end PullbackFree

/-- Let `(C,J,R)` be a ringed site with binary products, weak additive sheafification and the
locally-bijective comparison on `J`, and strong and weak additive sheafification with the
comparison on all slices. For finite index types `I,K : Type u` with `Fintype` structures,
`free_R I ⨿ free_R K` is locally free of rank `Fintype.card I + Fintype.card K`. -/
theorem isLocallyFreeOfRank_coprod_free (I J : Type u) [Fintype I]
    [Fintype J] :
    IsLocallyFreeOfRank (R := R)
      (_root_.SheafOfModules.free (R := R) I ⨿ _root_.SheafOfModules.free (R := R) J)
      (Fintype.card I + Fintype.card J) := by
  have h := isLocallyFreeOfRank_free (R := R) (I ⊕ J)
  rw [Fintype.card_sum] at h
  exact isLocallyFreeOfRank_of_iso (_root_.SheafOfModules.freeSumIso (R := R) I J).symm (hM := h)

/-- Let `(C,J,R)` be a ringed site with binary products, weak additive sheafification and the
locally-bijective comparison on `J`, and strong and weak additive sheafification with the
comparison on all slices, at ring/module universe `u`. For `m,n : ℕ`, `free_R (ULift.{u}(Fin
m)) ⨿ free_R (ULift.{u}(Fin n))` is locally free of rank `m+n`. -/
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
/-- Let `(C,J,R)` be a ringed site with binary products in `C`, weak additive sheafification and
the locally-bijective comparison on `J`, and additive sheafification with the comparison on
all slices, at ring/module universe `u`. Then `free_R (ULift.{u} Empty)` is locally free of
rank zero. -/
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

/-- Let `C' : Type u₂` have morphism universe `v₂`, `J'` be a topology, and `S : Sheaf J'
RingCat.{u}`. For `X∈C'` and `Y∈Over X`, `LocalGeneratorsData.bindEquiv Y` is the canonical
equivalence `SheafOfModules(S.over Y.left) ≌ SheafOfModules((S.over X).over Y)`. -/
noncomputable abbrev _root_.SheafOfModules.LocalGeneratorsData.bindEquiv {X : C'} (Y : Over X) :
    SheafOfModules (S.over Y.left) ≌ SheafOfModules ((S.over X).over Y) :=
  _root_.SheafOfModules.overOverEquivalence (S := S) Y

/-- For a ringed site `(C',J',S)`, `X∈C'`, and `Y∈Over X`, let `E=LocalGeneratorsData.bindEquiv Y`
compare the direct and iterated slices. The isomorphism `unit(S.over Y.left) ≅
E.inverse(unit((S.over X).over Y))` identifies their structure modules through the inverse
equivalence. -/
noncomputable def _root_.SheafOfModules.LocalGeneratorsData.bindEquivUnitIso {X : C'} (Y : Over X) :
    _root_.SheafOfModules.unit (S.over Y.left) ≅
      (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv (S := S) Y).inverse.obj
        (_root_.SheafOfModules.unit ((S.over X).over Y)) :=
  eqToIso (show _root_.SheafOfModules.unit (S.over Y.left) =
    (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv (S := S) Y).inverse.obj
      (_root_.SheafOfModules.unit ((S.over X).over Y)) from rfl)

end BindEquivGeneral

/-- Let `(C,J,R)` be a ringed site with ring/module universe `u`, and assume additive
sheafification with the locally-bijective comparison on first and second iterated slices. For
`X∈C`, `Y∈Over X`, `M : SheafOfModules.{u} R`, and generating sections `G` of `(M.over X).over
Y`, `bindGenerators Y G` gives generating sections of `M.over Y.left`. It uses the inverse
slice equivalence and preserves the generator index set `G.I`. -/
noncomputable def _root_.SheafOfModules.LocalGeneratorsData.bindGenerators {X : C}
    {M : SheafOfModules.{u} R} (Y : Over X)
    (G : ((M.over X).over Y).GeneratingSections) :
    (M.over Y.left).GeneratingSections :=
  (G.map (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).inverse
    (_root_.SheafOfModules.LocalGeneratorsData.bindEquivUnitIso Y)).ofEpi
    ((_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).fullyFaithfulFunctor.preimageIso
      (by exact (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).counitIso.app
            ((M.over X).over Y))).hom

/-- Let `C : Type u₁` have morphism universe `v₁`, `J` be a topology, and `R : Sheaf J
RingCat.{u}`, with additive sheafification and the locally-bijective comparison on first and
second slices. For `M`, a cover `X : I → C` with `I : Type u₁`, and data `D_i :
LocalGeneratorsData.{max u₁ v₁}(M.over(X i))`, `bind M X hX D` is local generator data for `M`
at universe `max u₁ v₁`. Its charts are indexed by pairs `(i,j)` with `j∈D_i.I`, and the chart
object is `(D_i.X j).left`. -/
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

/-- Let `(C,J,R)` be a ringed site with additive sheafification and the locally-bijective
comparison on first and second slices. For a cover `X : I → C` and local generator data `D_i`
for each `M.over(X i)`, assume every `D_i.IsLocallyFreeData`, so each chart's presentation map
is an isomorphism. Then `(LocalGeneratorsData.bind M X hX D).IsLocallyFreeData`: the assembled
chart presentation maps are also isomorphisms. -/
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
/-- Let `C : Type u₁` have morphism universe `v₁`, `J` be a topology, and `R : Sheaf J
RingCat.{u}`. Assume strong and weak additive sheafification with the locally-bijective
comparison on first slices, and additive sheafification with the comparison on second slices.
For `M`, `n : ℕ`, a cover `X : I → C` with `I : Type u₁`, and data `D_i :
LocalGeneratorsData.{max u₁ v₁}(M.over(X i))` each locally free of rank `n`, the global sheaf
`M` is locally free of rank `n`. -/
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

/-- Let `D` be any category, with families `f₁ : ι₁ → D` and `f₂ : ι₂ → D` whose index universes
may differ. Assume the coproducts of `f₁`, `f₂`, and `Sum.elim f₁ f₂` exist, and that the
binary coproduct of `∐ f₁` and `∐ f₂` exists. Then there is a canonical isomorphism `∐
(Sum.elim f₁ f₂) ≅ (∐ f₁) ⨿ (∐ f₂)`. -/
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

/-- Let `D` be any category, `ι` an empty type, and `f : ι → D` a family with a coproduct. Then `∐
f` is an initial object of `D`, by the universal property of the colimit of the empty discrete
diagram. -/
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

/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks in `C`, ring/module universe
`u`, weak additive sheafification and the locally-bijective comparison on `J`, and strong and
weak additive sheafification with the comparison on all slices. For `X∈C`,
`SheafOfModules.overFunctor R X : SheafOfModules R → SheafOfModules(R.over X)` is a left
adjoint. -/
instance overFunctorIsLeftAdjoint (X : C) :
    (_root_.SheafOfModules.overFunctor R X : SheafOfModules.{u} R ⥤
      SheafOfModules.{u} (R.over X)).IsLeftAdjoint := by
  unfold _root_.SheafOfModules.overFunctor
  infer_instance

/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks, weak additive
sheafification and the locally-bijective comparison on `J`, and strong and weak additive
sheafification with the comparison on all slices. For `X∈C` and module sheaves `M,N`,
`overFunctor R X` preserves the colimit of `pair M N`, hence the binary coproduct of that
pair. -/
instance overFunctorPreservesColimitPair (X : C)
    (M N : SheafOfModules.{u} R) :
    PreservesColimit (pair M N) (_root_.SheafOfModules.overFunctor R X) := by
  have : PreservesColimitsOfSize.{u, u} (_root_.SheafOfModules.overFunctor R X) :=
    (Adjunction.ofIsLeftAdjoint
      (_root_.SheafOfModules.overFunctor R X)).leftAdjoint_preservesColimits
  infer_instance

omit [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}] in
/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks in `C`, and weak additive
sheafification with the locally-bijective comparison on the base and every slice. For `f : X →
Y`, a module sheaf `M`, and generating sections `G` of `M.over Y`,
`GeneratingSections.overRestrict f G` gives generating sections of `M.over X`. It transports
`G` along `overMap R f` and the canonical over-functor comparison, retaining the index set
`G.I`. -/
noncomputable def _root_.SheafOfModules.GeneratingSections.overRestrict
    {M : SheafOfModules.{u} R} {X Y : C} (f : X ⟶ Y)
    (G : (M.over Y).GeneratingSections) :
    (M.over X).GeneratingSections :=
  (G.map (_root_.SheafOfModules.overMap R f)
      (_root_.SheafOfModules.overMapUnitIso (R := R) f).symm).ofEpi
    ((_root_.SheafOfModules.overFunctorMap R f).app M).hom

omit [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}] in
/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks, and weak additive
sheafification with the locally-bijective comparison on the base and slice sites. For `f : X →
Y` and a generating family `G` of `M.over Y`, if `G.π : free(G.I) → M.over Y` is an
isomorphism, then the presentation map of `GeneratingSections.overRestrict f G` is an
isomorphism over `X`. -/
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
/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks, and weak additive
sheafification with the locally-bijective comparison on the base and slice sites. For `f : X →
Y` and a generating family `G` of `M.over Y` with finite index set,
`GeneratingSections.overRestrict f G` has a finite index set, so it satisfies
`GeneratingSections.IsFiniteType`. -/
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

/-- Let `(C',J',R')` be a ringed site with weak additive sheafification and the locally-bijective
comparison on `J'`. For module sheaves `M,N` admitting a binary coproduct, let `G,H` be
generating families with isomorphism presentation maps `G.π` and `H.π`. The family
`GeneratingSections.coprod G H` generates `M ⨿ N` with index set `G.I ⊕ H.I`, using the
free-sum comparison followed by the coproduct of the two presentation isomorphisms. -/
noncomputable def _root_.SheafOfModules.GeneratingSections.coprod {M N : SheafOfModules.{u} R'}
    [_root_.CategoryTheory.Limits.HasBinaryCoproduct M N] (G : M.GeneratingSections)
    (H : N.GeneratingSections) [IsIso G.π] [IsIso H.π] :
    (M ⨿ N).GeneratingSections :=
  (_root_.SheafOfModules.free.generatingSections (R := R') (G.I ⊕ H.I)).ofEpi
    ((_root_.SheafOfModules.freeSumIso (R := R') G.I H.I).symm ≪≫
      coprod.mapIso (asIso G.π) (asIso H.π)).hom

/-- Let `(C',J',R')` be a ringed site with weak additive sheafification and the locally-bijective
comparison. For module sheaves `M,N` admitting a binary coproduct and generating families
`G,H` whose presentation maps are isomorphisms, `(GeneratingSections.coprod G H).π` is an
isomorphism from the free sheaf on `G.I ⊕ H.I` to `M ⨿ N`. -/
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
/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks in `C`, and strong and weak
additive sheafification with the locally-bijective comparison on every slice. If module
sheaves `M,N` admit a binary coproduct and are locally free of prescribed ranks `m,n : ℕ`,
then `M ⨿ N` is locally free of rank `m+n`. -/
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
/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks, and strong and weak
additive sheafification with the locally-bijective comparison on all slices. If `M,N` admit a
binary biproduct and are locally free of ranks `m,n : ℕ`, then `M ⊞ N` is locally free of rank
`m+n`. -/
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
/-- Let `(C,J)` be a site with `R : Sheaf J RingCat.{u}`, and assume weak additive sheafification
with the locally-bijective comparison on every slice. For module sheaves `M,N` of carrier
universe `u` and an isomorphism `e : M ≅ N`, local freeness of `M` implies local freeness of
`N`. The local generator index sets may be arbitrary. -/
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
/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks, and strong and weak
additive sheafification with the locally-bijective comparison on all slices. If locally free
module sheaves `M,N` admit a binary coproduct, then `M ⨿ N` is locally free. The chart index
sets may be infinite. -/
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
/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks, and strong and weak
additive sheafification with the locally-bijective comparison on every slice. If locally free
module sheaves `M,N` admit a binary biproduct, then `M ⊞ N` is locally free, with arbitrary
local generator index sets. -/
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

/-- Let `(C,J,R)` be a ringed site, `X∈C`, and `Y∈Over X`. For `E=LocalGeneratorsData.bindEquiv
Y`, the canonical equivalence from the direct to the iterated slice, `bindEquivUnitIsoForward
Y` has direction `unit((R.over X).over Y) ≅ E.functor(unit(R.over Y.left))`. It identifies
their structure modules through the forward equivalence. -/
noncomputable def _root_.SheafOfModules.LocalGeneratorsData.bindEquivUnitIsoForward {X : C}
    (Y : Over X) :
    _root_.SheafOfModules.unit ((R.over X).over Y) ≅
      (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).functor.obj
        (_root_.SheafOfModules.unit (R.over Y.left)) :=
  eqToIso (show _root_.SheafOfModules.unit ((R.over X).over Y) =
    (_root_.SheafOfModules.LocalGeneratorsData.bindEquiv Y).functor.obj
      (_root_.SheafOfModules.unit (R.over Y.left)) from rfl)

/-- Let `(C,J,R)` be a ringed site with additive sheafification and the locally-bijective
comparison on first and second slices. For `X∈C`, `Y∈Over X`, and generating sections `G` of
`M.over Y.left`, `bindGeneratorsForward Y G` gives generating sections of `(M.over X).over Y`.
It uses the forward direct/iterated slice equivalence and preserves `G.I`. -/
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

/-- Let `(C,J,R)` be a ringed site with additive sheafification and the locally-bijective
comparison on first and second slices. For `X∈C`, `Y∈Over X`, and generating sections `G` of
`M.over Y.left`, if `G.π` is an isomorphism, then `(LocalGeneratorsData.bindGeneratorsForward
Y G).π` is an isomorphism presenting `(M.over X).over Y`. -/
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
/-- Let `(C,J,R)` be a ringed site with pullbacks in `C`, ring/module universe `u`, strong and
weak additive sheafification with the locally-bijective comparison on first slices, and
additive sheafification with the comparison on second slices. If `M` is locally free of rank
`n : ℕ`, then for every `X₀∈C`, `M.over X₀` is locally free of rank `n` over `R.over X₀`. -/
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

/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks, weak additive
sheafification and the locally-bijective comparison on `J`, and strong and weak additive
sheafification with the comparison on all first slices. For `u`-small index types `ι₁,ι₂`,
module-sheaf families `f₁,f₂`, and `m,n : ℕ`, if `∐ f₁` has local rank `m` and `∐ f₂` has
local rank `n`, then `∐ (Sum.elim f₁ f₂)` has local rank `m+n`. -/
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

/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks, weak additive
sheafification and the locally-bijective comparison on `J`, and strong and weak additive
sheafification with the comparison on first slices. For `n : ℕ`, a family `M : Fin n →
SheafOfModules.{u} R`, and ranks `r : Fin n → ℕ` with each `M i` locally free of rank `r i`,
the coproduct `∐ M` is locally free of rank `∑ i, r i`. -/
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

/-- Let `(C,J,R)` be a ringed site with binary products and pullbacks, weak additive
sheafification and the locally-bijective comparison on `J`, and strong and weak additive
sheafification with the comparison on first slices. For a finite index type `ι` with `Fintype
ι` and `Small.{u} ι`, module sheaves `M i` locally free of ranks `r i : ℕ` have a coproduct
locally free of rank `∑ i, r i`. -/
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
