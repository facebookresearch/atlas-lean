/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import MathlibExt.AlgebraicTopology.SimplicialSet.FilteredFactorization
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical

/-!
# Filtered-colimit closure for Joyal categorical equivalences (partial)

This module is packet T27 of the Joyal model structure programme
(`Blueprint/JoyalModelStructure/README.md`, phases JY3/JY5): the
filtered-colimit / transfinite-composition closure of
`SSet.categoricalEquivalences` needed to keep relative `J`-cell maps in
`monomorphisms ⊓ categoricalEquivalences` (the weak saturation in
`RecognitionInput`). This is a red gate in `Blueprint/JoyalModelStructure/
STATUS.md`. The module proves the largest part that follows from the
currently landed API and records precisely what remains open.

The neutral infrastructure this closure rests on — simplex/edge/
`2`-simplex factorization through filtered colimits and the functor-object
limit cone `SSet.ihomCone` (`SSet.isLimit_ihomCone`) — lives in
`MathlibExt.AlgebraicTopology.SimplicialSet.FilteredFactorization`, which
mentions no Joyal classes and is public-imported here. This module keeps
only the Joyal closure results.

## What is proved here

* Transfinite compositions of inner anodyne extensions are categorical
  equivalences (indeed lie in `monomorphisms ⊓ categoricalEquivalences`),
  for every well-ordered shape `J` in any universe, in particular for sequential
  `ℕ`-indexed compositions
  (`SSet.transfiniteCompositionsOfShape_innerAnodyneExtensions_le`,
  `SSet.categoricalEquivalences.of_transfiniteCompositionOfShape_innerAnodyne`).
  This is the inner-horn part of the future `J`-cell closure: inner
  anodyne extensions are an `llp` class, hence formally stable under
  transfinite composition, and they are categorical by packet T10
  (`SSet.innerAnodyneExtensions_le_categoricalEquivalences`).

* Categorical equivalences are stable under colimits in the arrow category
  over shapes with a terminal object (stabilizing filtered colimits)
  (`SSet.categoricalEquivalences.of_isColimit_of_isTerminal`).

* Conditional bridges for the remaining step: *if*
  `categoricalEquivalences` is stable under filtered colimits
  (resp. under transfinite compositions of shape `J`), then so is
  `monomorphisms ⊓ categoricalEquivalences`, because the monomorphism
  factor already has these stabilities upstream
  (`Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms`).

## What is not proved (the remaining red-gate form)

The general statements

```text
MorphismProperty.IsStableUnderFilteredColimits.{u, u}
  (SSet.categoricalEquivalences : MorphismProperty SSet.{u})
(monomorphisms SSet.{u} ⊓ SSet.categoricalEquivalences)
  .IsStableUnderTransfiniteCompositionOfShape J   (general J, in particular ℕ)
```

for arbitrary categorical-equivalence steps are **not** proved here, and
neither is stability under filtered colimits in the arrow category for
general filtered shapes without a terminal object. The naive completion
of the proof sketched by the `hFun` limit above is not valid:
`SSet.hoFunctor` is a left adjoint (`SSet.nerveAdjunction`), so it does
not send the limit of functor objects in `SSet` to a limit in `Cat`, and
equivalences of ordinary categories are not stable under strict limits
in `Cat` (already pullbacks: the pullback in `Cat` of the equivalence
from the terminal category selecting one endpoint of the walking
isomorphism along the functor selecting the other endpoint is empty).
The sequential monomorphic case has the same obstruction in disguise:
rectifying stagewise lifts, chosen only up to isomorphism in the
homotopy categories of functor objects, into a strictly compatible
family requires `hoFunctor.map ((pre g).app C)` to be an isofibration
for monomorphisms `g`, equivalently extension of equivalence edges of
functor objects along monomorphisms — the special-outer-horn gate of
phase JY1, available in all dimensions as
`SSet.hasSpecialOuterHornFilling_of_quasicategory`, landed on
this base by #6840 (`SpecialOuterHornGeneral.lean`; not imported
here). The alternative route is the
Dwyer–Kan characterization between quasicategories (packet T28) together
with the landed filtered stability of `SSet.KanComplex.W`
(`SSet.KanComplex.W.isStableUnderFilteredColimits`). Either route would
discharged the general form using the limit cone and factorization
lemmas of `FilteredFactorization`; until then the JY3 filtered/transfinite
bullet for `monomorphisms ⊓ categoricalEquivalences` remains open, and the
conditional bridges above are the exact interface a future proof plugs
into.

## References

* D. Stevenson, *Notes on the Joyal model structure*, §2 (filtered-colimit
  stability of weak categorical equivalences is stated there without the
  finitary detail formalized here).
* P. Goerss and J. Jardine, *Simplicial Homotopy Theory*, VII Lemma 3.5
  (finite simplicial sets factor through filtered colimits).
-/

@[expose] public section

universe u v

open CategoryTheory Limits

namespace SSet

section Closures

/-- Inner anodyne extensions are monomorphisms: they are contained in
(the Kan–Quillen) anodyne extensions
(`SSet.innerAnodyneExtensions_le`), and anodyne extensions are
monomorphisms since both classes are `llp`s and the Kan–Quillen
generators `J` consist of monomorphisms. -/
theorem innerAnodyneExtensions_le_monomorphisms :
    innerAnodyneExtensions.{u} ≤ MorphismProperty.monomorphisms SSet.{u} :=
  le_trans innerAnodyneExtensions_le (by
    rw [anodyneExtensions_eq_llp_rlp, ← modelCategoryQuillen.llp_rlp_I,
      ← rlp_monomorphisms]
    exact MorphismProperty.antitone_llp
      (MorphismProperty.antitone_rlp modelCategoryQuillen.J_le_monomorphisms))

/-- Transfinite compositions of inner anodyne extensions, of any
well-ordered shape `J` in any universe (in particular sequential `ℕ`-indexed
compositions), lie in `monomorphisms ⊓ categoricalEquivalences`.
Indeed, inner anodyne extensions are an `llp` class, hence stable under
transfinite composition upstream
(`SSet.innerAnodyneExtensions.IsStableUnderTransfiniteComposition`),
are monomorphisms (`innerAnodyneExtensions_le_monomorphisms`), and are
categorical equivalences
(`SSet.innerAnodyneExtensions_le_categoricalEquivalences`, packet T10).
This is the inner-horn part of the future `J`-cell saturation; the
general statement for arbitrary steps in
`monomorphisms ⊓ categoricalEquivalences` is the remaining red-gate
form recorded in the module header. -/
theorem transfiniteCompositionsOfShape_innerAnodyneExtensions_le
    (J : Type v) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    innerAnodyneExtensions.{u}.transfiniteCompositionsOfShape J ≤
      MorphismProperty.monomorphisms SSet.{u} ⊓ categoricalEquivalences.{u} :=
  le_inf
    (le_trans (MorphismProperty.transfiniteCompositionsOfShape_le _ J)
      innerAnodyneExtensions_le_monomorphisms)
    (le_trans (MorphismProperty.transfiniteCompositionsOfShape_le _ J)
      innerAnodyneExtensions_le_categoricalEquivalences)

/-- Membership form of
`transfiniteCompositionsOfShape_innerAnodyneExtensions_le`: a
transfinite composition of inner anodyne extensions is a categorical
equivalence. -/
theorem categoricalEquivalences.of_transfiniteCompositionOfShape_innerAnodyne
    (J : Type v) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : innerAnodyneExtensions.TransfiniteCompositionOfShape J f) :
    categoricalEquivalences f :=
  ((MorphismProperty.inf_iff _ _ _).1
    (transfiniteCompositionsOfShape_innerAnodyneExtensions_le J f
      (MorphismProperty.TransfiniteCompositionOfShape.mem f hf))).2

/-- Sequential (`ℕ`-indexed) transfinite compositions of inner anodyne
extensions are categorical equivalences. -/
theorem categoricalEquivalences.of_transfiniteCompositionNat_innerAnodyne
    {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : innerAnodyneExtensions.TransfiniteCompositionOfShape ℕ f) :
    categoricalEquivalences f :=
  categoricalEquivalences.of_transfiniteCompositionOfShape_innerAnodyne ℕ hf

/-- Categorical equivalences are stable under colimits in the arrow
category over a shape with a terminal object: the colimit legs at the
terminal stage are isomorphisms, so the colimit map is isomorphic (in
the arrow category) to the terminal-stage map, and
`categoricalEquivalences` respects isomorphisms. Categories with a
terminal object are filtered, so this is the stabilizing case of
filtered stability; the general filtered case is the remaining
red-gate form recorded in the module header. -/
theorem categoricalEquivalences.of_isColimit_of_isTerminal
    {J : Type u} [Category.{u} J] {t : J} (ht : IsTerminal t)
    {F₁ F₂ : J ⥤ SSet.{u}} {c₁ : Cocone F₁} {c₂ : Cocone F₂}
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) (α : F₁ ⟶ F₂)
    (hα : ∀ j, categoricalEquivalences (α.app j)) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = α.app j ≫ c₂.ι.app j) :
    categoricalEquivalences φ := by
  have key : ∀ {F : J ⥤ SSet.{u}} {c : Cocone F} (_ : IsColimit c),
      IsIso (c.ι.app t) := by
    intro F c hc
    let e : colimit F ≅ c.pt := (colimit.isColimit F).coconePointUniqueUpToIso hc
    have hι : colimit.ι F t ≫ e.hom = c.ι.app t :=
      IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) hc t
    have : IsIso (colimit.ι F t) := isIso_ι_of_isTerminal ht F
    rw [← hι]
    infer_instance
  have := key hc₁
  have := key hc₂
  let e : Arrow.mk φ ≅ Arrow.mk (α.app t) :=
    Arrow.isoMk (asIso (c₁.ι.app t)).symm (asIso (c₂.ι.app t)).symm (by
      simp only [Iso.symm_hom, asIso_inv]
      calc inv (c₁.ι.app t) ≫ α.app t
          = inv (c₁.ι.app t) ≫ (α.app t ≫ c₂.ι.app t) ≫ inv (c₂.ι.app t) := by
            simp [Category.assoc]
        _ = inv (c₁.ι.app t) ≫ (c₁.ι.app t ≫ φ) ≫ inv (c₂.ι.app t) := by
            rw [← hφ t]
        _ = φ ≫ inv (c₂.ι.app t) := by simp [Category.assoc])
  exact (MorphismProperty.arrow_mk_iso_iff categoricalEquivalences e).2 (hα t)

/-- Conditional bridge: if `categoricalEquivalences` is stable under
same-universe filtered colimits, then so is
`monomorphisms ⊓ categoricalEquivalences`, since monomorphisms in
`SSet` already have this stability upstream
(`Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms`). -/
instance monomorphisms_inf_categoricalEquivalences_isStableUnderFilteredColimits
    [MorphismProperty.IsStableUnderFilteredColimits.{u, u} categoricalEquivalences.{u}] :
    MorphismProperty.IsStableUnderFilteredColimits.{u, u}
      (MorphismProperty.monomorphisms SSet.{u} ⊓ categoricalEquivalences.{u}) where
  isStableUnderColimitsOfShape J _ _ := by
    constructor
    intro X₁ X₂ c₁ c₂ hc₁ hc₂ α hα φ hφ
    have hα' (j : J) : MorphismProperty.monomorphisms SSet.{u} (α.app j) ∧
        categoricalEquivalences (α.app j) := by
      simpa only [MorphismProperty.inf_iff] using hα j
    rw [MorphismProperty.inf_iff]
    exact ⟨MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₁ X₂ c₁ c₂ hc₁ hc₂ α (fun j => (hα' j).1) φ hφ,
      MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₁ X₂ c₁ c₂ hc₁ hc₂ α (fun j => (hα' j).2) φ hφ⟩

/-- Conditional bridge: if `categoricalEquivalences` is stable under
transfinite compositions of shape `J`, then so is
`monomorphisms ⊓ categoricalEquivalences`, since monomorphisms in
`SSet` already have this stability. -/
instance monomorphisms_inf_categoricalEquivalences_isStableUnderTransfiniteCompositionOfShape
    (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    [MorphismProperty.IsStableUnderTransfiniteCompositionOfShape categoricalEquivalences.{u} J] :
    MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (MorphismProperty.monomorphisms SSet.{u} ⊓ categoricalEquivalences.{u}) J where
  le X Y f hf := by
    rw [MorphismProperty.inf_iff]
    exact ⟨MorphismProperty.transfiniteCompositionsOfShape_le _ J f
        (MorphismProperty.transfiniteCompositionsOfShape_monotone J inf_le_left f hf),
      MorphismProperty.transfiniteCompositionsOfShape_le _ J f
        (MorphismProperty.transfiniteCompositionsOfShape_monotone J inf_le_right f hf)⟩

/-- Conditional bridge, all same-universe shapes at once: if
`categoricalEquivalences` is stable under transfinite compositions,
then so is `monomorphisms ⊓ categoricalEquivalences`. -/
instance monomorphisms_inf_categoricalEquivalences_isStableUnderTransfiniteComposition
    [MorphismProperty.IsStableUnderTransfiniteComposition.{u} categoricalEquivalences.{u}] :
    MorphismProperty.IsStableUnderTransfiniteComposition.{u}
      (MorphismProperty.monomorphisms SSet.{u} ⊓ categoricalEquivalences.{u}) where

end Closures

end SSet
