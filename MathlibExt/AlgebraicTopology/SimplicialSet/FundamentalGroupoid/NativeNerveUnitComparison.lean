/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCertificates
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveCounitEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint
public import MathlibExt.CategoryTheory.NerveHomotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# The actual native unit of a groupoid nerve

The saved native unit on the nerve of a groupoid is the nerve of the
existing canonical section. Its literal native cover is therefore
isomorphic to its actual Under nerve and is contractible over the standard
point. These statements derive the comparisons from the original maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace SSet.KanComplex

variable (G : Type u) [Groupoid.{u} G]

private theorem nerveEquiv_symm_identity_eq_counit :
    (SSet.fundamentalGroupoidNerveEquiv (CategoryTheory.nerve G) G).symm
        (𝟙 (CategoryTheory.nerve G)) = SSet.fundamentalGroupoidNerveCounit G := by
  let B := CategoryTheory.nerve G
  let E := SSet.fundamentalGroupoidNerveEquiv B G
  let F := E.symm (𝟙 B)
  let C := SSet.fundamentalGroupoidNerveCounit G
  let hObj : ∀ x : B _⦋0⦌, F.obj (SSet.FundamentalGroupoid.mk x) =
      C.obj (SSet.FundamentalGroupoid.mk x) := fun x =>
    (SSet.fundamentalGroupoidNerveEquiv_symm_obj_mk B G (𝟙 B) x).trans
      (SSet.fundamentalGroupoidNerveCounit_obj_mk G x).symm
  apply SSet.FundamentalGroupoid.functor_ext hObj
  intro x y e
  have h := SSet.fundamentalGroupoidNerveEquiv_symm_map_homMk B G (𝟙 B) e
  have hId : e.map (𝟙 B) = e := by
    apply SSet.Edge.ext
    rfl
  rw [hId] at h
  change ((SSet.fundamentalGroupoidNerveEquiv B G).symm (𝟙 B)).map
      (SSet.FundamentalGroupoid.homMk e) =
    eqToHom (hObj x) ≫ (SSet.fundamentalGroupoidNerveCounit G).map
      (SSet.FundamentalGroupoid.homMk e) ≫ eqToHom (hObj y).symm
  rw [SSet.fundamentalGroupoidNerveCounit_map_homMk]
  exact h

/-- The original native unit followed by the existing nerve counit is the
literal identity map of the original groupoid nerve. -/
theorem nativeCoverUnit_nerve_comp_counit :
    nativeCoverUnit (CategoryTheory.nerve G) ≫
      CategoryTheory.nerveMap (SSet.fundamentalGroupoidNerveCounit G) =
        𝟙 (CategoryTheory.nerve G) := by
  let B := CategoryTheory.nerve G
  let E := SSet.fundamentalGroupoidNerveEquiv B G
  let C := SSet.fundamentalGroupoidNerveCounit G
  have hPost : nativeCoverUnit B ≫ CategoryTheory.nerveMap C = E C := by
    simpa only [nativeCoverUnit, Functor.id_comp] using
      (SSet.fundamentalGroupoidNerveEquiv_postcomp
        (𝟭 (SSet.FundamentalGroupoid B)) C).symm
  have hCounit : E C = 𝟙 B :=
    (congrArg E (nerveEquiv_symm_identity_eq_counit G).symm).trans (E.apply_symm_apply (𝟙 B))
  exact hPost.trans hCounit

private def nerveCounitIso :
    CategoryTheory.nerve (SSet.FundamentalGroupoid (CategoryTheory.nerve G)) ≅
      CategoryTheory.nerve G where
  hom := CategoryTheory.nerveMap (SSet.fundamentalGroupoidNerveCounit G)
  inv := CategoryTheory.nerveMap (SSet.fundamentalGroupoidNerveSection G)
  hom_inv_id := by
    rw [CategoryTheory.nerveMap_comp,
      SSet.fundamentalGroupoidNerveCounit_comp_section G, CategoryTheory.nerveMap_id]
  inv_hom_id := by
    rw [CategoryTheory.nerveMap_comp,
      SSet.fundamentalGroupoidNerveSection_comp_counit G, CategoryTheory.nerveMap_id]

/-- The actual native nerve unit is invertible, derived from the same strict
counit/section comparison and its actual unit equation. -/
theorem nativeCoverUnit_nerve_isIso : IsIso (nativeCoverUnit (CategoryTheory.nerve G)) := by
  let B := CategoryTheory.nerve G
  let e := nerveCounitIso G
  let c := CategoryTheory.nerveMap (SSet.fundamentalGroupoidNerveCounit G)
  have hc : e.hom = c := rfl
  let : IsIso c := hc ▸ (inferInstance : IsIso e.hom)
  have hLeft : e.inv ≫ c = 𝟙 B :=
    (congrArg (fun k => e.inv ≫ k) hc.symm).trans e.inv_hom_id
  have hUnit : nativeCoverUnit B = e.inv :=
    (cancel_mono c).mp ((nativeCoverUnit_nerve_comp_counit G).trans hLeft.symm)
  rw [hUnit]
  infer_instance

/-- The literal native cover of a groupoid nerve has invertible original
Under projection; its carrier is not replaced by a supplied cover model. -/
theorem nativeCoverUnderProjection_nerve_isIso
    (x : (CategoryTheory.nerve G) _⦋0⦌) :
    IsIso (nativeCoverUnderProjection (CategoryTheory.nerve G) x) := by
  change IsIso (pullback.snd (nativeCoverUnit (CategoryTheory.nerve G))
    (nativeCoverNerveProjection (CategoryTheory.nerve G) x))
  exact (IsPullback.of_hasPullback (nativeCoverUnit (CategoryTheory.nerve G))
    (nativeCoverNerveProjection (CategoryTheory.nerve G) x)).isIso_snd_of_isIso
      (nativeCoverUnit_nerve_isIso G)

/-- Every actual based native cover of this groupoid nerve is contractible,
using its same Under projection and the actual identity Under object. -/
theorem nativeCover_nerve_to_point_mem_realizationWeakEquivalences
    (x : (CategoryTheory.nerve G) _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (nativeCover (CategoryTheory.nerve G) x)) := by
  let B := CategoryTheory.nerve G
  let P := nativeCover B x
  let U := CategoryTheory.nerve (Under (SSet.FundamentalGroupoid.mk x))
  let r : P ⟶ U := nativeCoverUnderProjection B x
  let t : U ⟶ (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from U
  let : IsIso r := nativeCoverUnderProjection_nerve_isIso G x
  have hr : SSet.realizationWeakEquivalences r :=
    (weakEquivalence_iff r).mp (inferInstance : WeakEquivalence r)
  have ht : SSet.realizationWeakEquivalences t :=
    NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isInitial
      (Under.mkIdInitial (X := SSet.FundamentalGroupoid.mk x))
  have hComp : r ≫ t = SSet.stdSimplex.isTerminalObj₀.from P :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact hComp ▸ SSet.realizationWeakEquivalences.comp_mem r t hr ht

end SSet.KanComplex
