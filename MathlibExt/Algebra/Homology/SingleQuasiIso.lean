/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Single-degree projective quasi-isomorphism

For an `ℕ`-indexed chain complex `K` in an abelian category, a projective
object `R` and an isomorphism `R ≅ K.homology n` lift to a chain map from
the single complex concentrated in degree `n` that induces the given
isomorphism on homology and is a quasi-isomorphism when homology vanishes
off `n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace HomologicalComplex

/-- Chain map from the single complex in degree `n` via a projective lift. -/
noncomputable def singleToComplexOfProjective {C : Type u} [Category.{v} C]
    [Abelian C] {K : ChainComplex C ℕ} {R : C} [Projective R] (n : ℕ)
    (e : R ≅ K.homology n) : (single C (ComplexShape.down ℕ) n).obj R ⟶ K :=
  mkHomFromSingle
    (Projective.factorThru e.hom (K.homologyπ n) ≫ K.iCycles n)
    (by intro k hk; simp)

/-- Homology map in degree `n` is the chosen isomorphism after identification. -/
@[reassoc]
theorem singleToComplexOfProjective_homologyMap {C : Type u} [Category.{v} C]
    [Abelian C] {K : ChainComplex C ℕ} {R : C} [Projective R] (n : ℕ)
    (e : R ≅ K.homology n) :
    homologyMap (singleToComplexOfProjective n e) n =
      (singleObjHomologySelfIso (ComplexShape.down ℕ) n R).hom ≫ e.hom := by
  apply (cancel_epi (((single C (ComplexShape.down ℕ) n).obj R).homologyπ n)).mp
  rw [homologyπ_naturality, homologyπ_singleObjHomologySelfIso_hom_assoc,
    ← Projective.factorThru_comp e.hom (K.homologyπ n)]
  have h : cyclesMap (singleToComplexOfProjective n e) n =
      (singleObjCyclesSelfIso (ComplexShape.down ℕ) n R).hom ≫
        Projective.factorThru e.hom (K.homologyπ n) := by
    apply (cancel_mono (K.iCycles n)).mp
    rw [cyclesMap_i]
    simp [singleToComplexOfProjective, singleObjCyclesSelfIso_hom]
  rw [h, Category.assoc]

/-- The projective single map is a quasi-isomorphism when homology vanishes off `n`. -/
theorem singleToComplexOfProjective_quasiIso {C : Type u} [Category.{v} C]
    [Abelian C] {K : ChainComplex C ℕ} {R : C} [Projective R] (n : ℕ)
    (e : R ≅ K.homology n) (hK : ∀ i, i ≠ n → IsZero (K.homology i)) :
    QuasiIso (singleToComplexOfProjective n e) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : i = n
  · subst hi
    rw [singleToComplexOfProjective_homologyMap]
    infer_instance
  · exact IsZero.isIso (isZero_single_obj_homology _ _ _ _ hi) (hK i hi) _

end HomologicalComplex
