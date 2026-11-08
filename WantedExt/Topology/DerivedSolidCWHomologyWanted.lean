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

/-- The shift map `ℕ∪{∞} ⟶ ℕ∪{∞}` sending `n` to `n + 1` and `∞` to `∞`. -/
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

/-- The inclusion of the point at infinity into `ℕ∪{∞}`. -/
def ι : LightProfinite.of PUnit.{1} ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun _ ↦ ∞, continuous_const⟩

/-- The inclusion of the point at infinity into `ℕ∪{∞}` is a split monomorphism. -/
def ι_split : SplitMono ι where
  retraction := ConcreteCategory.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩
  id := rfl

/-- The map `ℤ[∞] ⟶ ℤ[ℕ∪{∞}]` of free light condensed abelian groups induced by `ι`. -/
def P_map :
    (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map ι

/-- The light condensed abelian group `P = ℤ[ℕ∪{∞}]/ℤ[∞]`. -/
def P : LightCondAb := cokernel P_map

/-- The projection `ℤ[ℕ∪{∞}] ⟶ P`. -/
def P_proj : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ P := cokernel.π _

/-- The short complex `ℤ[∞] ⟶ ℤ[ℕ∪{∞}] ⟶ P`. -/
def PSequence : ShortComplex LightCondAb :=
  ShortComplex.mk P_map P_proj (cokernel.condition _)

/-- The short complex `ℤ[∞] ⟶ ℤ[ℕ∪{∞}] ⟶ P` is a short exact sequence. -/
lemma PSequence_exact : PSequence.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_
    (SplitMono.mono (ι_split.map (lightProfiniteToLightCondSet ⋙ free ℤ)))
    coequalizer.π_epi
  erw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero,
    ← kernel.condition P_proj]
  rfl

/-- The short exact sequence `ℤ[∞] ⟶ ℤ[ℕ∪{∞}] ⟶ P` splits. -/
def PSequence_split : PSequence.Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    PSequence_exact.exact _
    (ι_split.map (lightProfiniteToLightCondSet ⋙ free ℤ)).id
    coequalizer.π_epi

/-- `P` is a retract of `ℤ[ℕ∪{∞}]`. -/
def P_retract : Retract P ((free ℤ).obj (ℕ∪{∞}).toCondensed) where
  i := _
  r := _
  retract := PSequence_split.s_g

/-- Construct a map out of `P` from a map out of `ℤ[ℕ∪{∞}]` annihilating `ℤ[∞]`. -/
def P_homMk (A : LightCondAb) (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ A)
    (hf : P_map ≫ f = 0) : P ⟶ A := cokernel.desc _ f hf

/-- The endomorphism `1 - shift` of the free light condensed abelian group `ℤ[ℕ∪{∞}]`. -/
def oneMinusShift' : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  𝟙 _ - (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift

set_option backward.isDefEq.respectTransparency false in
/-- The induced endomorphism `1 - shift` of `P = ℤ[ℕ∪{∞}]/ℤ[∞]`. -/
def oneMinusShift : P ⟶ P := by
  refine P_homMk _ oneMinusShift' ?_ ≫ P_proj
  rw [oneMinusShift', Preadditive.comp_sub]
  simp only [sub_eq_zero, P_map, ← Functor.map_comp]
  rfl

/-- A light condensed abelian group `A` is *solid* if the map `1 - shift` on `P` induces an
isomorphism on internal homs into `A`. -/
def isSolid : ObjectProperty LightCondAb :=
  fun A ↦ IsIso ((MonoidalClosed.pre oneMinusShift).app A)

/-- The class expressing that a light condensed abelian group is solid. -/
abbrev IsSolid (A : LightCondAb) := isSolid.Is A

/-- The category of light solid abelian groups, as the full subcategory of solid objects in light
condensed abelian groups. -/
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

/-- The derived category of light condensed abelian groups. -/
abbrev DLightCondAb := DerivedCategory LightCondAb

/-- The derived category of light solid abelian groups. -/
abbrev DSolid := DerivedCategory Solid

/- **Hole 1.** The solidification functor, left adjoint to the inclusion of solid objects. -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted solidification : LightCondAb ⥤ Solid

/- **Hole 2.** The solidification functor is additive.  (This follows from the adjunction of the
next hole, but is needed as an instance to state the holes below.) -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public instance_wanted solidification_additive : (❰solidification❱).Additive


/- **Hole 3.** The solidification adjunction: solidification is left adjoint to the inclusion of
solid objects in light condensed abelian groups. -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted solidificationAdjunction : ❰solidification❱ ⊣ isSolid.ι

/- **Hole 4.** The derived solidification functor. -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidification : DLightCondAb ⥤ DSolid

/- **Hole 5.** The comparison map from derived solidification to degreewise solidification. -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidificationCounit :
    DerivedCategory.Q ⋙ ❰derivedSolidification❱ ⟶
      (❰solidification❱).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/- **Hole 6.** Derived solidification, together with the comparison map of the previous hole, is
the total left derived functor of degreewise solidification followed by localization. -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidification_isLeftDerivedFunctor :
    (❰derivedSolidification❱).IsLeftDerivedFunctor ❰derivedSolidificationCounit❱
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))

/-- The inclusion of solid abelian groups, applied degreewise to cochain complexes. -/
abbrev inclusionComplexes :
    CochainComplex Solid ℤ ⥤ CochainComplex LightCondAb ℤ :=
  isSolid.ι.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The exact functor on derived categories induced by the inclusion `Solid ⥤ LightCondAb`. -/
abbrev derivedInclusion : DSolid ⥤ DLightCondAb :=
  isSolid.ι.mapDerivedCategory

/-- The derived inclusion is induced by applying the inclusion degreewise to complexes. -/
abbrev derivedInclusionFactors :
    DerivedCategory.Q ⋙ derivedInclusion ≅ inclusionComplexes ⋙ DerivedCategory.Q :=
  isSolid.ι.mapDerivedCategoryFactors

/-- The comparison map exhibiting `derivedInclusion` as a right derived functor of the degreewise
inclusion. -/
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
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidificationAdjunction : ❰derivedSolidification❱ ⊣ derivedInclusion

/-- The free light condensed abelian group on a topological space. -/
abbrev freeLightCondAbOfTop (X : TopCat) : LightCondAb :=
  (free ℤ).obj X.toLightCondSet

/-- The free light condensed abelian group on a topological space, functorially in the space. -/
abbrev freeLightCondAbOfTopFunctor : TopCat ⥤ LightCondAb :=
  topCatToLightCondSet ⋙ free ℤ

/-- Integral singular homology of a topological space, viewed as a discrete light condensed
abelian group. -/
abbrev singularHomologyLightCondAb (X : TopCat) (n : ℕ) : LightCondAb :=
  (LightCondensed.discrete (ModuleCat ℤ)).obj
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj X)

/-- The integral singular chain complex of a topological space, viewed as a cochain complex of
light condensed abelian groups by applying the discrete functor degreewise and placing homological
chain degree `n` in cohomological degree `-n`. -/
abbrev singularChainsLightCondAbComplexFunctor :
    TopCat ⥤ CochainComplex LightCondAb ℤ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)) ⋙
    (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor LightCondAb

/-- The integral singular chain complex of a topological space as an object of the derived category
of light condensed abelian groups. -/
abbrev singularChainsLightCondAbDerivedFunctor : TopCat ⥤ DLightCondAb :=
  singularChainsLightCondAbComplexFunctor ⋙ DerivedCategory.Q

/-- The integral singular chain complex of a topological space as a derived object. -/
abbrev singularChainsLightCondAbDerived (X : TopCat) : DLightCondAb :=
  singularChainsLightCondAbDerivedFunctor.obj X

/-- The property of topological spaces admitting a classical CW complex structure. -/
abbrev isCWTopCat : ObjectProperty TopCat :=
  fun X ↦ Nonempty (Topology.CWComplex (Set.univ : Set X))

/-- The full subcategory of topological spaces admitting a classical CW complex structure. -/
abbrev CWTopCat : Type _ := isCWTopCat.FullSubcategory

namespace CWTopCat

instance (X : CWTopCat) : Topology.CWComplex (Set.univ : Set X.obj) :=
  Classical.choice X.property

/-- The inclusion of CW spaces into topological spaces. -/
abbrev toTopCat : CWTopCat ⥤ TopCat := isCWTopCat.ι

end CWTopCat

/- **Hole 8.** The functor sending a CW complex to the derived inclusion of the derived
solidification of the free light condensed abelian group on it. -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidificationFreeCWFunctor : CWTopCat ⥤ DLightCondAb

/- **Hole 9.** The specification identifying `derivedSolidificationFreeCWFunctor` with the
expected composite functor. -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidificationFreeCWFunctorSpec :
    ❰derivedSolidificationFreeCWFunctor❱ ≅
      CWTopCat.toTopCat ⋙ freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙
        ❰derivedSolidification❱ ⋙ derivedInclusion

/-- The integral singular chains functor on CW complexes, viewed in the derived category of light
condensed abelian groups. -/
abbrev singularChainsLightCondAbCWDerivedFunctor : CWTopCat ⥤ DLightCondAb :=
  CWTopCat.toTopCat ⋙ singularChainsLightCondAbDerivedFunctor

/- **Hole 10.** The derived comparison theorem, naturally in a CW complex `X`: after applying the
exact derived inclusion from solid light condensed abelian groups to light condensed abelian groups,
the derived solidification of the free light condensed abelian group on `X` is the integral singular
chain complex of `X` as a derived object of light condensed abelian groups. -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
public def_wanted derivedSolidification_free_CW_derivedNatIso :
    ❰derivedSolidificationFreeCWFunctor❱ ≅ singularChainsLightCondAbCWDerivedFunctor

/-- The pointwise component of `derivedSolidification_free_CW_derivedNatIso`. -/
public def_wanted derivedSolidification_free_CW_derivedIso
    (X : TopCat) [Topology.CWComplex (Set.univ : Set X)] :
    derivedInclusion.obj
      ((❰derivedSolidification❱).obj
        ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X))) ≅
      singularChainsLightCondAbDerived X

/-- The isomorphism above is the pointwise component specified by the two natural
isomorphisms, as in the original definition. -/
public theorem_wanted derivedSolidification_free_CW_derivedIso_eq
    (X : TopCat) [Topology.CWComplex (Set.univ : Set X)] :
    ❰derivedSolidification_free_CW_derivedIso❱ X =
      (❰derivedSolidificationFreeCWFunctorSpec❱.app ⟨X, ⟨inferInstance⟩⟩).symm.trans
        (❰derivedSolidification_free_CW_derivedNatIso❱.app ⟨X, ⟨inferInstance⟩⟩)

/- **Hole 11.** For a CW complex `X`, the homology of the derived solidification of the free
light condensed abelian group on `X` is integral singular homology.  Since the derived category
is cohomologically indexed, the `n`-th singular homology group occurs in degree `-n`. -/
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
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
/-- Source: https://github.com/dagurtomas/LeanCondensed (LeanCondensed/Projects/DerivedSolidCWHomology.lean); D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658 Via leanprover/lean-eval@38361be, problem `derived_solidification_free_CW_homology`. -/
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
