/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Derived solidification of free CW complexes (light condensed mathematics)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.CondensedMathematics.DerivedSolidCWHomology` — derived_solidification_free_CW_homology (manifest `manifests/problems/derived_solidification_free_CW_homology.toml`, rev 1, submitter Dagur Asgeirsson, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.DerivedSolidCWHomologyWanted` namespace. Mathematical
statements are unchanged. Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.DerivedSolidCWHomologyWanted
/-!
# Derived solidification of free CW complexes

This challenge is extracted from the LeanCondensed project
<https://github.com/dagurtomas/LeanCondensed>, which develops the theory of light condensed
mathematics of Clausen–Scholze in Lean.  The target statement is the comparison theorem for a CW
complex `X`: the homology of the derived solidification of the free light condensed abelian group
on `X` is integral singular homology.

The non-`sorry` part of this file develops, using only Mathlib, the definition of
*light solid abelian groups*: a light condensed abelian group `A` is solid if the map
`1 - shift` on the free light condensed abelian group `P = ℤ[ℕ∪{∞}]/ℤ[∞]` induces an isomorphism
on internal homs into `A`.  The full subcategory `Solid` of solid objects is closed under limits,
kernels, cokernels and finite products, hence abelian, and the inclusion into light condensed
abelian groups is exact, so it induces a functor on derived categories.

The `sorry`ed declarations (the holes of this multi-hole problem) are:

* `solidification` — the solidification functor `LightCondAb ⥤ Solid`;
* `solidification_additive` — additivity of the solidification functor;
* `solidificationAdjunction` — solidification is left adjoint to the inclusion;
* `derivedSolidification` — the derived solidification functor
  `DerivedCategory LightCondAb ⥤ DerivedCategory Solid`;
* `derivedSolidificationCounit` — the comparison map exhibiting `derivedSolidification` as a
  functor under degreewise solidification;
* `derivedSolidification_isLeftDerivedFunctor` — `derivedSolidification` is the total left
  derived functor of degreewise solidification;
* `derivedSolidificationAdjunction` — derived solidification is left adjoint to the derived
  inclusion;
* `derivedSolidificationFreeCWFunctor` — the functor on CW complexes whose values are the derived
  inclusion of the derived solidification of the free light condensed abelian group;
* `derivedSolidificationFreeCWFunctorSpec` — an isomorphism identifying
  `derivedSolidificationFreeCWFunctor` with the expected composite functor;
* `derivedSolidification_free_CW_derivedNatIso` — naturally in a CW complex `X`, the derived
  inclusion of the derived solidification of `ℤ[X]` is isomorphic in the derived category of light
  condensed abelian groups to the integral singular chain complex of `X`, viewed as a complex of
  discrete light condensed abelian groups with homological degree `n` placed in cohomological
  degree `-n`, this is the main challenge;
* `derivedSolidification_free_CW_homologyIso` — for a CW complex `X`, the homology of the derived
  solidification of `ℤ[X]` is integral singular homology (the derived category is cohomologically
  indexed, so the `n`-th singular homology group appears in degree `-n`);
* `derivedSolidification_free_CW_homology` — the theorem form of the previous isomorphism;
* `derivedSolidification_free_CW_derivedIso` — the pointwise component of the previous natural
  isomorphism (helper hole replacing the original concrete definition, whose body used the holes
  above);
* `derivedSolidification_free_CW_derivedIso_eq` — identifies that component with the composite
  of `derivedSolidificationFreeCWFunctorSpec` and `derivedSolidification_free_CW_derivedNatIso`.

All holes must be filled compatibly: the adjunctions and derived functor property pin down
`solidification` and `derivedSolidification` up to natural isomorphism, so the final derived
comparison theorem and its pointwise homology form have their intended mathematical content.

Note that the LeanCondensed project contains significant progress towards some of the earlier holes
in this challenge.
-/

open CategoryTheory Limits LightProfinite OnePoint LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace LightProfinite

/-- **The shift map on $\mathbb{N} \cup \{\infty\}$.** Write $\mathbb{N} \cup \{\infty\}$ for the
one-point compactification of $\mathbb{N}$, viewed as a light profinite set. The shift map is the
continuous map $\mathbb{N} \cup \{\infty\} \to \mathbb{N} \cup \{\infty\}$ sending $n$ to $n + 1$
and $\infty$ to $\infty$. -/
def shift : ℕ∪{∞} ⟶ ℕ∪{∞} := ConcreteCategory.ofHom {
  toFun
    | ∞ => ∞
    | OnePoint.some n => (n + 1 : ℕ)
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat, Filter.tendsto_add_atTop_iff_nat, tendsto_atTop_nhds]
    intro U h hU
    simp only [isOpen_iff_of_mem h, isClosed_discrete, isCompact_iff_finite, true_and] at hU
    refine ⟨sSup (Option.some ⁻¹' U)ᶜ + 1, fun n hn ↦ by
      simpa using! notMem_of_csSup_lt (Nat.succ_le_iff.mp hn) (Set.Finite.bddAbove hU)⟩ }

end LightProfinite

namespace LightCondensed

/-- **Inclusion of the point at infinity.** The morphism of light profinite spaces from the
one-point space to the one-point compactification $\mathbb{N} \cup \{\infty\}$ of $\mathbb{N}$
that sends the point to $\infty$. -/
def ι : LightProfinite.of PUnit.{1} ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun _ ↦ ∞, continuous_const⟩

/-- **Splitting of the inclusion of the point at infinity.** The inclusion of the point at infinity
into the one-point compactification $\mathbb{N} \cup \{\infty\}$ of $\mathbb{N}$ is a split
monomorphism of light profinite spaces, with retraction the unique map from
$\mathbb{N} \cup \{\infty\}$ to the one-point space. -/
def ι_split : SplitMono ι where
  retraction := ConcreteCategory.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩
  id := rfl

/-- **The map ℤ[∞] → ℤ[ℕ ∪ {∞}].** For a light profinite set $S$, let $\mathbb{Z}[S]$ be the free
light condensed abelian group on $S$, and let $\iota$ be the inclusion of the point $\infty$ into
$\mathbb{N} \cup \{\infty\}$. This is the morphism
$\mathbb{Z}[\infty] \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}]$ induced by $\iota$, where
$\mathbb{Z}[\infty]$ is the free light condensed abelian group on a point. -/
def P_map :
    (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map ι

/-- **The light condensed abelian group P.** For a light profinite set $S$, let $\mathbb{Z}[S]$ be
the free light condensed abelian group on $S$, and let $\mathbb{N} \cup \{\infty\}$ be the
one-point compactification of $\mathbb{N}$. Then
$P = \mathbb{Z}[\mathbb{N} \cup \{\infty\}]/\mathbb{Z}[\infty]$ is the cokernel of the morphism
$\mathbb{Z}[\infty] \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}]$ induced by the inclusion of the
point $\infty$. -/
def P : LightCondAb := cokernel P_map

/-- **The projection onto P.** Write $\mathbb{Z}[S]$ for the free light condensed abelian group on
a light profinite set $S$, and let $P = \mathbb{Z}[\mathbb{N} \cup \{\infty\}]/\mathbb{Z}[\infty]$.
This is the quotient map $\mathbb{Z}[\mathbb{N} \cup \{\infty\}] \to P$, the cokernel projection
of the map $\mathbb{Z}[\infty] \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}]$ induced by the
inclusion of the point $\infty$. -/
def P_proj : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ P := cokernel.π _

/-- **The short complex defining $P$.** Write $\mathbb{N} \cup \{\infty\}$ for the one-point
compactification of $\mathbb{N}$, viewed as a light profinite set, and $\mathbb{Z}[S]$ for the free
light condensed abelian group on a light profinite set $S$, with $\mathbb{Z}[\infty]$ the one on a
point. This is the short complex of light condensed abelian groups
$\mathbb{Z}[\infty] \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}] \to P$ whose first map is induced by
the inclusion of the point $\infty$ and whose second map is the cokernel projection onto
$P = \mathbb{Z}[\mathbb{N} \cup \{\infty\}]/\mathbb{Z}[\infty]$. -/
def PSequence : ShortComplex LightCondAb :=
  ShortComplex.mk P_map P_proj (cokernel.condition _)

/-- **Short exactness of the sequence defining $P$.** Write $\mathbb{N} \cup \{\infty\}$ for the
one-point compactification of $\mathbb{N}$, viewed as a light profinite set, and $\mathbb{Z}[S]$ for
the free light condensed abelian group on a light profinite set $S$, with $\mathbb{Z}[\infty]$ the
one on a point. The short complex of light condensed abelian groups
$\mathbb{Z}[\infty] \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}] \to P$, whose first map is induced
by the inclusion of the point $\infty$ and whose second map is the cokernel projection onto
$P = \mathbb{Z}[\mathbb{N} \cup \{\infty\}]/\mathbb{Z}[\infty]$, is short exact: the first map is
a monomorphism, the second map is an epimorphism, and the sequence is exact in the middle. -/
lemma PSequence_exact : PSequence.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_
    (SplitMono.mono (ι_split.map (lightProfiniteToLightCondSet ⋙ free ℤ)))
    coequalizer.π_epi
  erw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero,
    ← kernel.condition P_proj]
  rfl

/-- **A splitting of the sequence defining $P$.** Write $\mathbb{N} \cup \{\infty\}$ for the
one-point compactification of $\mathbb{N}$, viewed as a light profinite set, and $\mathbb{Z}[S]$ for
the free light condensed abelian group on a light profinite set $S$, with $\mathbb{Z}[\infty]$ the
one on a point. Let $f \colon \mathbb{Z}[\infty] \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}]$ be
induced by the inclusion of the point $\infty$, and let
$g \colon \mathbb{Z}[\mathbb{N} \cup \{\infty\}] \to P$ be the cokernel projection onto
$P = \mathbb{Z}[\mathbb{N} \cup \{\infty\}]/\mathbb{Z}[\infty]$. This is a chosen splitting of the
short exact sequence of light condensed abelian groups
$\mathbb{Z}[\infty] \xrightarrow{f} \mathbb{Z}[\mathbb{N} \cup \{\infty\}] \xrightarrow{g} P$,
that is, maps $r \colon \mathbb{Z}[\mathbb{N} \cup \{\infty\}] \to \mathbb{Z}[\infty]$ and
$s \colon P \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}]$ such that $r \circ f = \mathrm{id}$,
$g \circ s = \mathrm{id}$ and $f \circ r + s \circ g = \mathrm{id}$, where $r$ is induced by the
map from $\mathbb{N} \cup \{\infty\}$ to the point. -/
def PSequence_split : PSequence.Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    PSequence_exact.exact _
    (ι_split.map (lightProfiniteToLightCondSet ⋙ free ℤ)).id
    coequalizer.π_epi

/-- **P is a retract of ℤ[ℕ ∪ {∞}].** Write $\mathbb{Z}[S]$ for the free light condensed abelian
group on a light profinite set $S$. The quotient
$P = \mathbb{Z}[\mathbb{N} \cup \{\infty\}]/\mathbb{Z}[\infty]$ by the image of the map induced by
the inclusion of the point $\infty$ is a retract of $\mathbb{Z}[\mathbb{N} \cup \{\infty\}]$: the
short exact sequence
$0 \to \mathbb{Z}[\infty] \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}] \to P \to 0$ splits, and a
section of the projection $\mathbb{Z}[\mathbb{N} \cup \{\infty\}] \to P$ from this splitting,
together with the projection, exhibits the retraction. -/
def P_retract : Retract P ((free ℤ).obj (ℕ∪{∞}).toCondensed) where
  i := _
  r := _
  retract := PSequence_split.s_g

/-- **Maps out of P.** Write $\mathbb{Z}[S]$ for the free light condensed abelian group on a light
profinite set $S$, and let $P = \mathbb{Z}[\mathbb{N} \cup \{\infty\}]/\mathbb{Z}[\infty]$ be the
cokernel of the map $\mathbb{Z}[\infty] \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}]$ induced by the
inclusion of the point $\infty$. Let $A$ be a light condensed abelian group and let
$f \colon \mathbb{Z}[\mathbb{N} \cup \{\infty\}] \to A$ be a morphism whose composite with this
map is zero. Then $f$ factors through the projection
$\mathbb{Z}[\mathbb{N} \cup \{\infty\}] \to P$, and this is the induced morphism $P \to A$. -/
def P_homMk (A : LightCondAb) (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ A)
    (hf : P_map ≫ f = 0) : P ⟶ A := cokernel.desc _ f hf

/-- **One minus shift on ℤ[ℕ ∪ {∞}].** Let $\mathbb{Z}[\mathbb{N} \cup \{\infty\}]$ be the free
light condensed abelian group on the light profinite set $\mathbb{N} \cup \{\infty\}$, and let
$\mathrm{shift}$ be its endomorphism induced by the map $n \mapsto n + 1$, $\infty \mapsto \infty$.
This is the endomorphism $1 - \mathrm{shift}$ of $\mathbb{Z}[\mathbb{N} \cup \{\infty\}]$. -/
def oneMinusShift' : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  𝟙 _ - (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift

set_option backward.isDefEq.respectTransparency false in
/-- **One minus shift on P.** Write $\mathbb{Z}[S]$ for the free light condensed abelian group on
a light profinite set $S$, let $\mathbb{N} \cup \{\infty\}$ be the one-point compactification of
$\mathbb{N}$, and let $P = \mathbb{Z}[\mathbb{N} \cup \{\infty\}]/\mathbb{Z}[\infty]$ be the
cokernel of the map induced by the inclusion of the point $\infty$. Let $\mathrm{shift}$ be the
endomorphism of $\mathbb{Z}[\mathbb{N} \cup \{\infty\}]$ induced by $n \mapsto n + 1$,
$\infty \mapsto \infty$. The endomorphism $1 - \mathrm{shift}$ vanishes on $\mathbb{Z}[\infty]$,
so it factors through a morphism $P \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}]$. Composing this
morphism with the projection onto $P$ gives the induced endomorphism $1 - \mathrm{shift}$ of
$P$. -/
def oneMinusShift : P ⟶ P := by
  refine P_homMk _ oneMinusShift' ?_ ≫ P_proj
  rw [oneMinusShift', Preadditive.comp_sub]
  simp only [sub_eq_zero, P_map, ← Functor.map_comp]
  rfl

/-- **Solid light condensed abelian groups.** Write $\mathbb{Z}[S]$ for the free light condensed
abelian group on a light profinite set $S$, let $\mathbb{N} \cup \{\infty\}$ be the one-point
compactification of $\mathbb{N}$, and let
$P = \mathbb{Z}[\mathbb{N} \cup \{\infty\}]/\mathbb{Z}[\infty]$ be the cokernel of the map induced
by the inclusion of the point $\infty$. The shift $n \mapsto n + 1$, $\infty \mapsto \infty$
induces an endomorphism $1 - \mathrm{shift}$ of $\mathbb{Z}[\mathbb{N} \cup \{\infty\}]$, and
hence of $P$. A light condensed abelian group $A$ is *solid* if precomposition with this
endomorphism of $P$ is an isomorphism from the internal hom $\underline{\mathrm{Hom}}(P, A)$ to
itself. -/
def isSolid : ObjectProperty LightCondAb :=
  fun A ↦ IsIso ((MonoidalClosed.pre oneMinusShift).app A)

/-- **The solidity class.** For a light condensed abelian group $A$, the class asserting that $A$
is solid. -/
abbrev IsSolid (A : LightCondAb) := isSolid.Is A

/-- **The category of light solid abelian groups.** Write $\mathbb{Z}[S]$ for the free light
condensed abelian group on a light profinite set $S$, let $\mathbb{N} \cup \{\infty\}$ be the
one-point compactification of $\mathbb{N}$, viewed as a light profinite set, write $\mathrm{pt}$ for
the one-point light profinite set, and let $P$ be the cokernel of the map
$\mathbb{Z}[\mathrm{pt}] \to \mathbb{Z}[\mathbb{N} \cup \{\infty\}]$ induced by the inclusion of
the point $\infty$. The endomorphism $1 - \mathrm{shift}$ of
$\mathbb{Z}[\mathbb{N} \cup \{\infty\}]$, where $\mathrm{shift}$ is induced by $n \mapsto n + 1$
and $\infty \mapsto \infty$, descends to an endomorphism of $P$. A light condensed abelian group
$A$ is solid when this endomorphism of $P$ induces an isomorphism of internal homs
$\underline{\mathrm{Hom}}(P, A) \to \underline{\mathrm{Hom}}(P, A)$. The category of light solid
abelian groups is the full subcategory of light condensed abelian groups on the solid objects. -/
abbrev Solid : Type _ := isSolid.FullSubcategory

namespace Solid

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Solid objects are closed under limits, because internal homs out of a fixed object preserve
limits in the second variable. -/
instance (J : Type) [SmallCategory J] : isSolid.IsClosedUnderLimitsOfShape J := by
  have : PreservesLimitsOfSize.{0, 0} (ihom P) :=
    (ihom.adjunction P).rightAdjoint_preservesLimits
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk
  intro A ⟨⟨F, π, hl⟩, h⟩
  let hl' := isLimitOfPreserves (ihom P) hl
  let α := F.whiskerLeft <| MonoidalClosed.pre oneMinusShift
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    exact h j
  let c := (Cone.postcompose α).obj ((ihom P).mapCone ⟨A, π⟩)
  have : hl'.lift c = (MonoidalClosed.pre oneMinusShift).app A := by
    apply hl'.hom_ext
    intro j
    change _ ≫ ((ihom P).mapCone ⟨A, π⟩).π.app _ = _
    simp only [Functor.comp_obj, Functor.const_obj_obj, IsLimit.fac]
    simp only [Functor.mapCone_pt, Functor.mapCone_π_app]
    simp only [MonoidalClosed.pre, Cone.postcompose_obj_pt, Functor.mapCone_pt,
      Cone.postcompose_obj_π, NatTrans.comp_app, Functor.const_obj_obj, Functor.comp_obj,
      Functor.mapCone_π_app, Functor.whiskerLeft_app, conjugateEquiv_apply_app,
      curriedTensor_obj_obj, ihom.ihom_adjunction_unit, curriedTensor_map_app,
      ihom.ihom_adjunction_counit, ← Functor.map_comp, ihom.coev_naturality_assoc, Category.assoc,
      ← ihom.ev_naturality, Functor.id_obj, c, α]
    rw [← whisker_exchange_assoc]
  rw [isSolid, ← this, ← IsLimit.nonempty_isLimit_iff_isIso_lift]
  exact ⟨(IsLimit.postcomposeHomEquiv (asIso α) _).symm hl'⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Solid objects are closed under colimits of any shape for which internal homs out of `P`
preserve colimits. -/
instance (J : Type) [SmallCategory J] [PreservesColimitsOfShape J (ihom P)] :
    isSolid.IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk
  intro A ⟨⟨F, ι, hc⟩, h⟩
  let hc' := isColimitOfPreserves (ihom P) hc
  let α := F.whiskerLeft <| MonoidalClosed.pre oneMinusShift
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    exact h j
  let c := (Cocone.precompose α).obj ((ihom P).mapCocone ⟨A, ι⟩)
  have hdesc : hc'.desc c = (MonoidalClosed.pre oneMinusShift).app A := by
    apply hc'.hom_ext
    intro j
    simp only [IsColimit.fac]
    simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app]
    simp only [MonoidalClosed.pre, Cocone.precompose_obj_pt, Functor.mapCocone_pt,
      Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.const_obj_obj, Functor.comp_obj,
      Functor.mapCocone_ι_app, Functor.whiskerLeft_app, conjugateEquiv_apply_app,
      curriedTensor_obj_obj, ihom.ihom_adjunction_unit, curriedTensor_map_app,
      ihom.ihom_adjunction_counit, ← Functor.map_comp, ihom.coev_naturality_assoc, Category.assoc,
      ← ihom.ev_naturality, Functor.id_obj, c, α]
    rw [← whisker_exchange_assoc]
  rw [isSolid, ← hdesc, ← IsColimit.nonempty_isColimit_iff_isIso_desc hc']
  exact ⟨(IsColimit.precomposeHomEquiv (asIso α) _).symm hc'⟩

/-- The free light condensed abelian group `ℤ[ℕ∪{∞}]` is internally projective. -/
instance : InternallyProjective ((free ℤ).obj (ℕ∪{∞}).toCondensed) :=
  internallyProjective_free_natUnionInfty ℤ

/-- `P` is internally projective, being a retract of `ℤ[ℕ∪{∞}]`. -/
instance : InternallyProjective P := .ofRetract P_retract

/-- Internal homs out of `P` form an additive functor. -/
instance : (ihom P).Additive := by
  have h : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
    (ihom.adjunction P).leftAdjoint_preservesColimits
  have : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft P) :=
    h.preservesColimitsOfShape
  have : PreservesBinaryBiproducts (tensorLeft P) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (tensorLeft P).Additive := Functor.additive_of_preservesBinaryBiproducts _
  exact (ihom.adjunction P).right_adjoint_additive

/-- Internal homs out of the internally projective object `P` preserve finite colimits. -/
instance : PreservesFiniteColimits (ihom P) := by
  have : PreservesLimitsOfSize.{0, 0} (ihom P) :=
    (ihom.adjunction P).rightAdjoint_preservesLimits
  rw [Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi]
  intro S hS
  have : Epi S.g := hS.epi_g
  exact ⟨((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (ihom P)).1
    inferInstance S hS).1, inferInstance⟩

/-- Solid objects are closed under kernels. -/
instance : isSolid.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨_, k, hk, hf⟩
    exact isSolid.prop_of_isLimit hk (by rintro (_ | _) <;> first | exact hf.1 | exact hf.2)

/-- Solid objects are closed under cokernels. -/
instance : isSolid.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨_, k, hk, hf⟩
    exact isSolid.prop_of_isColimit hk (by rintro (_ | _) <;> first | exact hf.1 | exact hf.2)

/-- Solid objects are closed under finite products. -/
instance : isSolid.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape _ _ := inferInstance

/-- The zero object is solid. -/
instance : isSolid.ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := LightCondAb)
    refine ⟨Z, hZ, ?_⟩
    have hz : IsZero ((ihom P).obj Z) := (ihom P).map_isZero hZ
    have h : (MonoidalClosed.pre oneMinusShift).app Z = (hz.iso hz).hom := hz.eq_of_src _ _
    show IsIso ((MonoidalClosed.pre oneMinusShift).app Z)
    rw [h]
    infer_instance

/-- The category of light solid abelian groups is abelian. -/
instance : Abelian Solid := inferInstanceAs (Abelian isSolid.FullSubcategory)

/-- The inclusion of solid objects preserves finite limits. -/
instance : PreservesFiniteLimits isSolid.ι where
  preservesFiniteLimits _ := inferInstance

/-- The inclusion of solid objects preserves finite colimits. -/
instance : PreservesFiniteColimits isSolid.ι where
  preservesFiniteColimits _ := inferInstance

/-- A choice of derived category of light condensed abelian groups. -/
instance instHasDerivedCategoryLightCondAb : HasDerivedCategory LightCondAb :=
  HasDerivedCategory.standard _

/-- A choice of derived category of light solid abelian groups. -/
instance instHasDerivedCategorySolid : HasDerivedCategory Solid :=
  HasDerivedCategory.standard _

/-- **Derived category of light condensed abelian groups.** The derived category of the abelian
category of light condensed abelian groups. -/
abbrev DLightCondAb := DerivedCategory LightCondAb

/-- **Derived category of light solid abelian groups.** The derived category of the abelian
category of light solid abelian groups. -/
abbrev DSolid := DerivedCategory Solid

/- **Hole 1.** The solidification functor, left adjoint to the inclusion of solid objects. -/
/-- **Solidification.** The solidification functor from the category of light condensed abelian
groups to the category of light solid abelian groups.

This declaration fixes only the functor. Its intended characterization, as left adjoint to the
inclusion of light solid abelian groups into light condensed abelian groups, is the separate
solidification adjunction.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted solidification : LightCondAb ⥤ Solid

/- **Hole 2.** The solidification functor is additive.  (This follows from the adjunction of the
next hole, but is needed as an instance to state the holes below.) -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public instance_wanted solidification_additive : (❰solidification❱).Additive


/- **Hole 3.** The solidification adjunction: solidification is left adjoint to the inclusion of
solid objects in light condensed abelian groups. -/
/-- **Solidification adjunction.** An adjunction exhibiting the solidification functor from light
condensed abelian groups to light solid abelian groups as left adjoint to the inclusion of the full
subcategory of light solid abelian groups into light condensed abelian groups.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted solidificationAdjunction : ❰solidification❱ ⊣ isSolid.ι

/- **Hole 4.** The derived solidification functor. -/
/-- **Derived solidification.** A functor from the derived category of light condensed abelian
groups to the derived category of light solid abelian groups.

Separate statements require it to be the left derived functor of degreewise solidification and
left adjoint to the derived inclusion; these determine it up to natural isomorphism.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidification : DLightCondAb ⥤ DSolid

/- **Hole 5.** The comparison map from derived solidification to degreewise solidification. -/
/-- **Comparison map from derived to degreewise solidification.** Let $Q$ denote the localization
functors from cochain complexes to derived categories. This is a natural transformation from the
functor sending a cochain complex $K$ of light condensed abelian groups to the derived
solidification of $Q(K)$ to the functor sending $K$ to $Q(\mathrm{Sol}(K))$, where
$\mathrm{Sol}(K)$ is the complex of light solid abelian groups obtained by applying solidification
to $K$ degreewise.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidificationCounit :
    DerivedCategory.Q ⋙ ❰derivedSolidification❱ ⟶
      (❰solidification❱).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/- **Hole 6.** Derived solidification, together with the comparison map of the previous hole, is
the total left derived functor of degreewise solidification followed by localization. -/
/-- **Derived solidification is the left derived functor of solidification.** Let $Q$ denote the
localization functors from cochain complexes indexed by $\mathbb{Z}$ to derived categories.
Derived solidification, together with the comparison natural transformation from $Q$ followed by
derived solidification to degreewise solidification followed by $Q$, is a left derived functor of
the functor that applies solidification degreewise to a cochain complex of light condensed abelian
groups and then passes to the derived category of light solid abelian groups, with respect to the
quasi-isomorphisms of cochain complexes of light condensed abelian groups.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidification_isLeftDerivedFunctor :
    (❰derivedSolidification❱).IsLeftDerivedFunctor ❰derivedSolidificationCounit❱
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))

/-- **Degreewise inclusion of complexes of light solid abelian groups.** The functor from cochain
complexes indexed by $\mathbb{Z}$ of light solid abelian groups to cochain complexes indexed by
$\mathbb{Z}$ of light condensed abelian groups that applies the inclusion of light solid abelian
groups into light condensed abelian groups in each degree. -/
abbrev inclusionComplexes :
    CochainComplex Solid ℤ ⥤ CochainComplex LightCondAb ℤ :=
  isSolid.ι.mapHomologicalComplex (ComplexShape.up ℤ)

/-- **Derived inclusion of solid abelian groups.** The inclusion $\iota$ of light solid abelian
groups into light condensed abelian groups is exact, so it induces a functor $D(\iota)$ from the
derived category of light solid abelian groups to the derived category of light condensed abelian
groups. -/
abbrev derivedInclusion : DSolid ⥤ DLightCondAb :=
  isSolid.ι.mapDerivedCategory

/-- **The derived inclusion is computed degreewise.** Let $\iota$ be the inclusion of light solid
abelian groups into light condensed abelian groups, $D(\iota)$ the induced derived inclusion, and
$Q$ the localization functors from cochain complexes to derived categories. This is the natural
isomorphism $D(\iota)(Q K) \cong Q(\iota K)$ for cochain complexes $K$ of light solid abelian
groups, where $\iota K$ is $K$ with $\iota$ applied degreewise. -/
abbrev derivedInclusionFactors :
    DerivedCategory.Q ⋙ derivedInclusion ≅ inclusionComplexes ⋙ DerivedCategory.Q :=
  isSolid.ι.mapDerivedCategoryFactors

/-- **Comparison map for the derived inclusion.** Let $\iota$ be the inclusion of light solid
abelian groups into light condensed abelian groups, $D(\iota)$ the induced derived inclusion, and
$Q$ the localization functors from cochain complexes to derived categories. The comparison map is
the natural transformation from $K \mapsto Q(\iota K)$ to $K \mapsto D(\iota)(Q K)$, for cochain
complexes $K$ of light solid abelian groups, where $\iota K$ is $K$ with $\iota$ applied
degreewise; it is the inverse of the natural isomorphism $D(\iota)(Q K) \cong Q(\iota K)$.

With this comparison map, $D(\iota)$ is a right derived functor of the degreewise inclusion with
respect to quasi-isomorphisms. -/
abbrev derivedInclusionComparison :
    inclusionComplexes ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ derivedInclusion :=
  derivedInclusionFactors.inv

/-- The exact derived inclusion is the right derived functor of the degreewise inclusion. -/
instance derivedInclusion_isRightDerivedFunctor :
    derivedInclusion.IsRightDerivedFunctor derivedInclusionComparison
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) derivedInclusion
    derivedInclusionFactors

/- **Hole 7.** The derived solidification adjunction: derived solidification is left adjoint to
the derived inclusion. -/
/-- **Derived solidification is left adjoint to the derived inclusion.** An adjunction in which
derived solidification, from the derived category of light condensed abelian groups to the derived
category of light solid abelian groups, is left adjoint to the derived inclusion $D(\iota)$ induced
by the inclusion $\iota$ of light solid abelian groups into light condensed abelian groups.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidificationAdjunction : ❰derivedSolidification❱ ⊣ derivedInclusion

/-- **Free light condensed abelian group on a topological space.** For a topological space $X$,
$\mathbb{Z}[X]$ is the free light condensed abelian group on the light condensed set associated
with $X$. -/
abbrev freeLightCondAbOfTop (X : TopCat) : LightCondAb :=
  (free ℤ).obj X.toLightCondSet

/-- **Free light condensed abelian group functor on topological spaces.** The functor from
topological spaces to light condensed abelian groups sending a space $X$ to the free light
condensed abelian group $\mathbb{Z}[X]$ on the light condensed set associated with $X$. -/
abbrev freeLightCondAbOfTopFunctor : TopCat ⥤ LightCondAb :=
  topCatToLightCondSet ⋙ free ℤ

/-- **Singular homology as a light condensed abelian group.** For a topological space $X$ and
$n \in \mathbb{N}$, this is the discrete light condensed abelian group on the $n$-th integral
singular homology group $H_n(X; \mathbb{Z})$. -/
abbrev singularHomologyLightCondAb (X : TopCat) (n : ℕ) : LightCondAb :=
  (LightCondensed.discrete (ModuleCat ℤ)).obj
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj X)

/-- **The singular chain complex as a complex of light condensed abelian groups.** This is the
functor from topological spaces to cochain complexes of light condensed abelian groups sending a
space $X$ to the complex whose term in degree $-n$, for $n \ge 0$, is the discrete light condensed
abelian group on the integral singular $n$-chains $C_n(X; \mathbb{Z})$, with the singular boundary
maps as differentials and zero in positive degrees. -/
abbrev singularChainsLightCondAbComplexFunctor :
    TopCat ⥤ CochainComplex LightCondAb ℤ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)) ⋙
    (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor LightCondAb

/-- **The singular chain functor into the derived category.** This is the functor from topological
spaces to the derived category of light condensed abelian groups sending a space $X$ to its
integral singular chain complex, regarded as a cochain complex of discrete light condensed abelian
groups with the $n$-chains in degree $-n$. -/
abbrev singularChainsLightCondAbDerivedFunctor : TopCat ⥤ DLightCondAb :=
  singularChainsLightCondAbComplexFunctor ⋙ DerivedCategory.Q

/-- **The singular chains of a space in the derived category.** For a topological space $X$, this
is the integral singular chain complex of $X$, regarded as a cochain complex of discrete light
condensed abelian groups with the $n$-chains in degree $-n$, as an object of the derived category
of light condensed abelian groups. -/
abbrev singularChainsLightCondAbDerived (X : TopCat) : DLightCondAb :=
  singularChainsLightCondAbDerivedFunctor.obj X

/-- **Spaces admitting a CW complex structure.** A topological space $X$ has this property when
it admits a classical CW complex structure whose underlying set is all of $X$. -/
abbrev isCWTopCat : ObjectProperty TopCat :=
  fun X ↦ Nonempty (Topology.CWComplex (Set.univ : Set X))

/-- **The category of spaces admitting a CW structure.** The full subcategory of the category of
topological spaces whose objects are the spaces $X$ admitting a classical CW complex structure
with underlying set all of $X$; its morphisms are all continuous maps between such spaces. -/
abbrev CWTopCat : Type _ := isCWTopCat.FullSubcategory

namespace CWTopCat

instance (X : CWTopCat) : Topology.CWComplex (Set.univ : Set X.obj) :=
  Classical.choice X.property

/-- **Inclusion of CW spaces into topological spaces.** The inclusion functor from the full
subcategory of topological spaces admitting a classical CW complex structure into the category of
topological spaces. -/
abbrev toTopCat : CWTopCat ⥤ TopCat := isCWTopCat.ι

end CWTopCat

/- **Hole 8.** The functor sending a CW complex to the derived inclusion of the derived
solidification of the free light condensed abelian group on it. -/
/-- **Derived solidification on CW complexes.** A functor from the category of topological spaces
admitting a CW complex structure, with all continuous maps as morphisms, to the derived category
of light condensed abelian groups.

A separate specification identifies it, up to natural isomorphism, with the functor sending $X$
to the derived inclusion of the derived solidification of the free light condensed abelian group
$\mathbb{Z}[X]$, viewed as a complex concentrated in degree $0$.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidificationFreeCWFunctor : CWTopCat ⥤ DLightCondAb

/- **Hole 9.** The specification identifying `derivedSolidificationFreeCWFunctor` with the
expected composite functor. -/
/-- **Natural isomorphism specifying derived solidification on CW complexes.** A natural
isomorphism between the derived solidification functor on CW complexes and the composite functor
that sends a topological space $X$ admitting a CW complex structure to the free light condensed
abelian group $\mathbb{Z}[X]$, views it as a complex concentrated in degree $0$ in the derived
category of light condensed abelian groups, applies derived solidification, and then applies the
derived inclusion of light solid abelian groups into light condensed abelian groups. Both are
functors from the category of topological spaces admitting a CW complex structure, with all
continuous maps as morphisms, to the derived category of light condensed abelian groups.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidificationFreeCWFunctorSpec :
    ❰derivedSolidificationFreeCWFunctor❱ ≅
      CWTopCat.toTopCat ⋙ freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙
        ❰derivedSolidification❱ ⋙ derivedInclusion

/-- **The singular chain functor on CW spaces.** This is the functor from the category of
topological spaces admitting a CW complex structure, with all continuous maps as morphisms, to the
derived category of light condensed abelian groups sending $X$ to its integral singular chain
complex, regarded as a cochain complex of discrete light condensed abelian groups with the
$n$-chains in degree $-n$. -/
abbrev singularChainsLightCondAbCWDerivedFunctor : CWTopCat ⥤ DLightCondAb :=
  CWTopCat.toTopCat ⋙ singularChainsLightCondAbDerivedFunctor

/- **Hole 10.** The derived comparison theorem, naturally in a CW complex `X`: after applying the
exact derived inclusion from solid light condensed abelian groups to light condensed abelian groups,
the derived solidification of the free light condensed abelian group on `X` is the integral singular
chain complex of `X` as a derived object of light condensed abelian groups. -/
/-- **Derived solidification of free CW complexes computes singular chains.** A natural
isomorphism of functors from the category of spaces admitting a CW structure to the derived
category of light condensed abelian groups, from the derived solidification functor $F$ to the
integral singular chain complex functor. Here $F(X)$ is the derived inclusion of the derived
solidification of the free light condensed abelian group $\mathbb{Z}[X]$ placed in degree $0$ (up
to a specified natural isomorphism), and the singular chain complex of $X$ is viewed as a complex
of discrete light condensed abelian groups with chains of degree $n$ in cohomological degree $-n$.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidification_free_CW_derivedNatIso :
    ❰derivedSolidificationFreeCWFunctor❱ ≅ singularChainsLightCondAbCWDerivedFunctor

/-- **Pointwise derived comparison for CW complexes.** For a topological space $X$ with a CW
complex structure on all of $X$, an isomorphism in the derived category of light condensed abelian
groups from the derived inclusion of the derived solidification of the free light condensed
abelian group $\mathbb{Z}[X]$, placed in degree $0$, to the integral singular chain complex of $X$,
viewed as a complex of discrete light condensed abelian groups with chains of degree $n$ placed in
cohomological degree $-n$. -/
public def_wanted derivedSolidification_free_CW_derivedIso
    (X : TopCat) [Topology.CWComplex (Set.univ : Set X)] :
    derivedInclusion.obj
      ((❰derivedSolidification❱).obj
        ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X))) ≅
      singularChainsLightCondAbDerived X

/-- **The pointwise derived comparison is the component of the natural one.** Let $X$ be a
topological space with a CW complex structure on all of $X$, regarded as an object of the category
of spaces admitting a CW structure, and let $\mathbb{Z}[X]$ be the free light condensed abelian
group on $X$. Let $F$ be the derived solidification functor on spaces admitting a CW structure,
let $\sigma$ be the natural isomorphism from $F$ to the functor sending $X$ to the derived
inclusion of the derived solidification of $\mathbb{Z}[X]$ placed in degree $0$, and let $\nu$ be
the natural isomorphism from $F$ to the integral singular chain complex functor with values in the
derived category of light condensed abelian groups. Then the pointwise isomorphism $\phi_X$ from
the derived inclusion of the derived solidification of $\mathbb{Z}[X]$ (placed in degree $0$) to
the singular chain complex of $X$ equals $\nu_X \circ \sigma_X^{-1}$. -/
public theorem_wanted derivedSolidification_free_CW_derivedIso_eq
    (X : TopCat) [Topology.CWComplex (Set.univ : Set X)] :
    ❰derivedSolidification_free_CW_derivedIso❱ X =
      (❰derivedSolidificationFreeCWFunctorSpec❱.app ⟨X, ⟨inferInstance⟩⟩).symm.trans
        (❰derivedSolidification_free_CW_derivedNatIso❱.app ⟨X, ⟨inferInstance⟩⟩)

/- **Hole 11.** For a CW complex `X`, the homology of the derived solidification of the free
light condensed abelian group on `X` is integral singular homology.  Since the derived category
is cohomologically indexed, the `n`-th singular homology group occurs in degree `-n`. -/
/-- **Derived solidification computes singular homology.** Let $X$ be a topological space
equipped with a CW complex structure, let $n$ be a natural number, and let $\mathbb{Z}[X]$ be the
free light condensed abelian group on $X$, viewed as a complex concentrated in degree $0$ in the
derived category of light condensed abelian groups. Apply derived solidification to
$\mathbb{Z}[X]$, take the homology in cohomological degree $-n$, which is a light solid abelian
group, and regard it as a light condensed abelian group. This is an isomorphism between the
resulting light condensed abelian group and the $n$-th singular homology group $H_n(X; \mathbb{Z})$
of $X$ with integer coefficients, regarded as a discrete light condensed abelian group.

The derived category is cohomologically indexed, so the $n$-th homology group sits in degree $-n$.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidification_free_CW_homologyIso
    (X : TopCat) [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    isSolid.ι.obj
      ((DerivedCategory.homologyFunctor Solid (-(n : ℤ))).obj
        ((❰derivedSolidification❱).obj
          ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X)))) ≅
      singularHomologyLightCondAb X n

/- **Hole 12.** The theorem form of `derivedSolidification_free_CW_homologyIso`: the derived
solidification of the free light condensed abelian group on a CW complex computes integral
singular homology. -/
/-- **Homology of the derived solidification of a free CW complex.** Let $X$ be a topological space
with a CW complex structure on all of $X$, let $\mathbb{Z}[X]$ be the free light condensed abelian
group on $X$, and let $n$ be a natural number. Then the cohomology in degree $-n$ of the derived
solidification of $\mathbb{Z}[X]$ placed in degree $0$, a light solid abelian group regarded as a
light condensed abelian group, is isomorphic to the integral singular homology group
$H_n(X; \mathbb{Z})$ viewed as a discrete light condensed abelian group.

Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public theorem_wanted derivedSolidification_free_CW_homology
    (X : TopCat) [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Nonempty
      (isSolid.ι.obj
        ((DerivedCategory.homologyFunctor Solid (-(n : ℤ))).obj
          ((❰derivedSolidification❱).obj
            ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X)))) ≅
        singularHomologyLightCondAb X n)

end Solid

end LightCondensed

end

end MathlibExt.Topology.DerivedSolidCWHomologyWanted
