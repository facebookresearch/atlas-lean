/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalEquivalences

/-! # Inner anodyne extensions are Joyal categorical equivalences

The main theorem of this module is the first substantial membership result
for the class `SSet.categoricalEquivalences` of Joyal weak categorical
equivalences: every inner anodyne extension is a categorical equivalence,

```text
SSet.innerAnodyneExtensions ≤ SSet.categoricalEquivalences.
```

The proof is the standard one. Fix an inner anodyne extension
`f : X ⟶ Y` and a quasicategory `C`. We show that precomposition with `f`,
`(MonoidalClosed.pre f).app C : (ihom Y).obj C ⟶ (ihom X).obj C`, is a
trivial Kan fibration, in the explicit form
`SSet.modelCategoryQuillen.I.rlp ((pre f).app C)`: it has the right lifting
property against every boundary inclusion `∂Δ[n].ι`. Indeed, under the
parametrized tensor–internal-hom adjunction
`MonoidalClosed.internalHomAdjunction₂`, a lifting problem of `∂Δ[n].ι`
against `(pre f).app C` transposes to a lifting problem of the
pushout-product of `f` with `∂Δ[n].ι` against the terminal map
`C ⟶ ⊤_ SSet`. That pushout-product is inner anodyne by the upstream
pushout-product theorem `SSet.innerAnodyneExtensions_pushoutObjObjι'`
(the boundary inclusion is a monomorphism), and `C ⟶ ⊤_ SSet` is an inner
fibration because `C` is a quasicategory, so the transposed lifting problem
has a solution. The conclusion then follows from
`SSet.hoFunctor_map_isEquivalence_of_rlp_I`: a trivial Kan fibration
induces an equivalence of homotopy categories, which is exactly the
defining `hFun` test for `categoricalEquivalences`.

As a corollary, every inner horn inclusion `Λ[n, i].ι` (`0 < i < n`) is a
categorical equivalence.

## What is not proved here

The second JY3 gate example, that the endpoint inclusion
`Δ[0] ⟶ SSet.coherentIso` is a categorical equivalence, is *not* proved in
this module. It does not follow from the theorem above: the endpoint
inclusion is not inner anodyne (it is not bijective on vertices). The
available proof route — showing that evaluation at the endpoint
`h Fun(coherentIso, C) ⟶ h Fun(Δ[0], C)` is an equivalence of ordinary
categories for every quasicategory `C` — needs one to assemble maps out of
`SSet.coherentIso = nerve WalkingIso` (and out of its prisms
`Δ[1] ⊗ coherentIso`) into an arbitrary quasicategory from edge-level
data. That is the extension statement recorded as
TODO(T08-extension) in
`MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalence.lean`
(an equivalence edge of a quasicategory extends along
`Δ[1] ⟶ SSet.coherentIso`), which has not landed; only the converse
direction (extension implies equivalence) is available. No statement in
this module should be read as claiming the `coherentIso` gate example.

Nothing here opens a model-category scope: the argument uses only
the explicit
morphism properties `SSet.modelCategoryQuillen.I`,
`SSet.innerAnodyneExtensions`, `SSet.innerFibrations` and
`SSet.categoricalEquivalences`.

## References

* J. Lurie, *Higher Topos Theory*, §2.2.5 and Corollary 2.3.2.5 (inner
  anodyne extensions are weak categorical equivalences).
* D. Stevenson, *Notes on the Joyal model structure*, §3.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed

open scoped Simplicial

namespace SSet

variable {X Y : SSet.{u}} {f : X ⟶ Y}

/-- Precomposition with an inner anodyne extension `f` into a
quasicategory `C` is a trivial Kan fibration: the map
`(MonoidalClosed.pre f).app C` has the right lifting property against the
generating cofibrations `SSet.modelCategoryQuillen.I` (the boundary
inclusions). The lifting problem against `∂Δ[n].ι` transposes, under the
parametrized tensor–internal-hom adjunction, to the lifting problem of
the pushout-product of `f` with `∂Δ[n].ι` against the inner fibration
`C ⟶ ⊤_ SSet`, and that pushout-product is inner anodyne by
`SSet.innerAnodyneExtensions_pushoutObjObjι'`. -/
theorem rlp_I_pre_app_of_innerAnodyneExtensions
    (hf : innerAnodyneExtensions f) (C : SSet.{u}) [Quasicategory C] :
    modelCategoryQuillen.I.rlp ((MonoidalClosed.pre f).app C) := by
  intro A B i hi
  obtain ⟨n⟩ := hi
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout
    (MonoidalCategory.curriedTensor SSet.{u}) f ∂Δ[n].ι
  let sq₁₃ := Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom f
    (terminal.from C) terminalIsTerminal
  have hι : innerAnodyneExtensions sq₁₂.ι :=
    innerAnodyneExtensions_pushoutObjObjι' sq₁₂ hf
  have hlift : HasLiftingProperty sq₁₂.ι (terminal.from C) :=
    hι (terminal.from C) (mem_innerFibrations _)
  exact
    (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂ sq₁₃).1 hlift

/-- **Inner anodyne extensions are categorical equivalences.** Every inner
anodyne extension is a Joyal weak categorical equivalence: for every
quasicategory `C`, precomposition with an inner anodyne extension induces
an equivalence `h Fun(Y, C) ⟶ h Fun(X, C)` of homotopy categories, because
that precomposition map is a trivial Kan fibration
(`SSet.rlp_I_pre_app_of_innerAnodyneExtensions`) and trivial Kan
fibrations induce equivalences of homotopy categories
(`SSet.hoFunctor_map_isEquivalence_of_rlp_I`). -/
theorem innerAnodyneExtensions_le_categoricalEquivalences :
    innerAnodyneExtensions.{u} ≤ categoricalEquivalences.{u} := by
  intro P Q f hf C hC
  exact hoFunctor_map_isEquivalence_of_rlp_I
    (@rlp_I_pre_app_of_innerAnodyneExtensions _ _ _ hf C hC)

/-- Membership form of
`SSet.innerAnodyneExtensions_le_categoricalEquivalences`: an inner
anodyne extension is a categorical equivalence. -/
theorem categoricalEquivalences.of_innerAnodyneExtensions
    (hf : innerAnodyneExtensions f) : categoricalEquivalences f :=
  innerAnodyneExtensions_le_categoricalEquivalences f hf

/-- Every inner horn inclusion is a categorical equivalence. -/
theorem categoricalEquivalences.horn_ι {n : ℕ} {i : Fin (n + 1)}
    (h0 : 0 < i) (hn : i < Fin.last n) :
    categoricalEquivalences.{u} Λ[n, i].ι :=
  categoricalEquivalences.of_innerAnodyneExtensions
    (innerAnodyneExtensions.horn_ι h0 hn)

end SSet
