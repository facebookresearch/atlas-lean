/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeHomotopyComponentsNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeMonoRightWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeWeakLiftingTest
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ReplacementWeakReduction
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne

/-!
# Exact comparison of full intrinsic mapping weakness and relative testing

Full original mapping weakness implies bijections on the actual mapping
components, naturally identified with original relative homotopy classes.
For the converse, replace both endpoints by the unchanged intrinsic
replacement and factor the same arrow. Genuine fibrant-codomain reverse
recognition makes its right factor mono-right and therefore fully mapping
weak; the native completed left factor is already proved fully weak.
The original unit squares then reflect full weakness to the original
arrow. The proof does not use components alone as a weak-space criterion.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty Opposite

namespace SSet.Marked

/-- Full original Cartesian mapping weakness implies all original relative homotopy-class tests. -/
theorem cartesianWeakEquivalences_le_relativeHomotopyTesting (B : SSet.{u}) [Quasicategory B] :
    cartesianWeakEquivalences B ≤ cartesianRelativeHomotopyTesting B := by
  intro X Y f hf
  apply (cartesianRelativeHomotopyTesting_iff f).mpr
  intro T hT
  let target : CartesianOver B := ⟨T, hT⟩
  let M : relativeMappingComplex .maximal Y.hom T.hom ⟶ relativeMappingComplex .maximal X.hom T.hom :=
    (overMappingFunctor .maximal (max B) T).map f.op
  have hM : KanComplex.W M := (cartesianWeakEquivalences_iff_kan f).mp hf target
  have hπ : Function.Bijective (SSet.mapπ₀ M) := KanComplex.W.bijective_mapπ₀ hM
  let EX := relativeHomotopyClassEquivPi0 (max B) X T
  let EY := relativeHomotopyClassEquivPi0 (max B) Y T
  constructor
  · intro a b hab
    apply EY.injective
    apply hπ.1
    exact (relativeHomotopyClassEquivPi0_pre f a).symm.trans
      ((congrArg EX hab).trans (relativeHomotopyClassEquivPi0_pre f b))
  · intro x
    obtain ⟨z, hz⟩ := hπ.2 (EX x)
    refine ⟨EY.symm z, EX.injective ?_⟩
    exact (relativeHomotopyClassEquivPi0_pre f (EY.symm z)).trans
      ((congrArg (SSet.mapπ₀ M) (EY.apply_symm_apply z)).trans hz)

/-- The same exact component comparison sends full original cocartesian weakness to every native relative
  homotopy test. -/
theorem cocartesianWeakEquivalences_le_relativeHomotopyTesting (B : SSet.{u}) [Quasicategory B] :
    cocartesianWeakEquivalences B ≤ cocartesianRelativeHomotopyTesting B := by
  intro X Y f hf
  apply (cocartesianRelativeHomotopyTesting_iff f).mpr
  intro T hT
  let target : CocartesianOver B := ⟨T, hT⟩
  let M : relativeMappingComplex .maximal Y.hom T.hom ⟶ relativeMappingComplex .maximal X.hom T.hom :=
    (overMappingFunctor .maximal (max B) T).map f.op
  have hM : KanComplex.W M := (cocartesianWeakEquivalences_iff_kan f).mp hf target
  have hπ : Function.Bijective (SSet.mapπ₀ M) := KanComplex.W.bijective_mapπ₀ hM
  let EX := relativeHomotopyClassEquivPi0 (max B) X T
  let EY := relativeHomotopyClassEquivPi0 (max B) Y T
  constructor
  · intro a b hab
    apply EY.injective
    apply hπ.1
    exact (relativeHomotopyClassEquivPi0_pre f a).symm.trans
      ((congrArg EX hab).trans (relativeHomotopyClassEquivPi0_pre f b))
  · intro x
    obtain ⟨z, hz⟩ := hπ.2 (EX x)
    refine ⟨EY.symm z, EX.injective ?_⟩
    exact (relativeHomotopyClassEquivPi0_pre f (EY.symm z)).trans
      ((congrArg (SSet.mapπ₀ M) (EY.apply_symm_apply z)).trans hz)

/-- Native relative homotopy testing implies the FULL original Cartesian mapping weak class on every original arrow. -/
theorem cartesianRelativeHomotopyTesting_le_weakEquivalences (B : SSet.{u}) [Quasicategory B] :
    cartesianRelativeHomotopyTesting B ≤ cartesianWeakEquivalences B := by
  let _ : (cartesianWeakEquivalences B).HasTwoOutOfThreeProperty := cartesianWeakEquivalences_hasTwoOutOfThreeProperty B
  intro X Y f hf
  let d := RelativeBoundarySmallObject.cartesianFunctorialFactorization B
  let g := (cartesianFixedBaseReplacementFunctor B).mapArrow.obj (Arrow.mk f)
  have hw : cartesianRelativeHomotopyTesting B (d.p.app g) :=
    (cartesianRelativeTestRightFactor_testing_iff B (Arrow.mk f)).mpr hf
  have hm : (monomorphisms (Over (max B))).rlp (d.p.app g) :=
    (cartesianRelativeRight_testing_iff_monoRight _ (d.hp g) (cartesianFixedBaseReplacement_intrinsic Y)).mp hw
  have hi : cartesianWeakEquivalences B (d.i.app g) := (cartesianRelativeBoundary_left_le_testing B _ (d.hi g)).2
  have hp : cartesianWeakEquivalences B (d.p.app g) := monoRight_le_cartesianWeakEquivalences B _ hm
  have hR : cartesianWeakEquivalences B ((cartesianFixedBaseReplacementFunctor B).map f) :=
    (congrArg (fun a : g.left ⟶ g.right => cartesianWeakEquivalences B a)
      (show d.i.app g ≫ d.p.app g = g.hom from d.fac_app)).mp
        ((cartesianWeakEquivalences B).comp_mem _ _ hi hp)
  exact (cartesianFixedBaseReplacement_map_weak_iff f).mp hR

/-- The dual native original factors and full unit squares reflect complete cocartesian mapping weakness. -/
theorem cocartesianRelativeHomotopyTesting_le_weakEquivalences (B : SSet.{u}) [Quasicategory B] :
    cocartesianRelativeHomotopyTesting B ≤ cocartesianWeakEquivalences B := by
  let _ : (cocartesianWeakEquivalences B).HasTwoOutOfThreeProperty :=
    cocartesianWeakEquivalences_hasTwoOutOfThreeProperty B
  intro X Y f hf
  let d := RelativeBoundarySmallObject.cocartesianFunctorialFactorization B
  let g := (cocartesianFixedBaseReplacementFunctor B).mapArrow.obj (Arrow.mk f)
  have hw : cocartesianRelativeHomotopyTesting B (d.p.app g) :=
    (cocartesianRelativeTestRightFactor_testing_iff B (Arrow.mk f)).mpr hf
  have hm : (monomorphisms (Over (max B))).rlp (d.p.app g) :=
    (cocartesianRelativeRight_testing_iff_monoRight _ (d.hp g) (cocartesianFixedBaseReplacement_intrinsic Y)).mp hw
  have hi : cocartesianWeakEquivalences B (d.i.app g) := (cocartesianRelativeBoundary_left_le_testing B _ (d.hi g)).2
  have hp : cocartesianWeakEquivalences B (d.p.app g) := monoRight_le_cocartesianWeakEquivalences B _ hm
  have hR : cocartesianWeakEquivalences B ((cocartesianFixedBaseReplacementFunctor B).map f) :=
    (congrArg (fun a : g.left ⟶ g.right => cocartesianWeakEquivalences B a)
      (show d.i.app g ≫ d.p.app g = g.hom from d.fac_app)).mp
        ((cocartesianWeakEquivalences B).comp_mem _ _ hi hp)
  exact (cocartesianFixedBaseReplacement_map_weak_iff f).mp hR

/-- The actual full original Cartesian mapping weak property is EXACTLY its native all-target relative
  homotopy testing property. -/
theorem cartesianWeakEquivalences_eq_relativeHomotopyTesting (B : SSet.{u}) [Quasicategory B] :
    cartesianWeakEquivalences B = cartesianRelativeHomotopyTesting B :=
  le_antisymm (cartesianWeakEquivalences_le_relativeHomotopyTesting B)
    (cartesianRelativeHomotopyTesting_le_weakEquivalences B)

/-- The same exact all-original-arrow weak-property equality holds for the dual original class. -/
theorem cocartesianWeakEquivalences_eq_relativeHomotopyTesting (B : SSet.{u}) [Quasicategory B] :
    cocartesianWeakEquivalences B = cocartesianRelativeHomotopyTesting B :=
  le_antisymm (cocartesianWeakEquivalences_le_relativeHomotopyTesting B)
    (cocartesianRelativeHomotopyTesting_le_weakEquivalences B)

end SSet.Marked
