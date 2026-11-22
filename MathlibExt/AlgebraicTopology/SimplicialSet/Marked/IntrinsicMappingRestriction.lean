/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeCoreEmbedding
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.EquivalenceLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.EquivalenceLifting
import MathlibExt.CategoryTheory.LiftingProperties.CancelMonoRight

/-!
# All original marked mono restrictions into intrinsic fibrations are Kan fibrations

The full ordinary relative core restriction is a Kan fibration by genuine
function-pullback lifting. The actual source marked complex embeds into
that same core by a Kan fibration. Its comparison with the original marked
restriction commutes on every whole prism. Monicity of the target core
embedding recovers the original lift without dropping any source marking
or changing the base point. This includes every native marking-refinement
and boundary generator, over arbitrary original quasicategory bases.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- The actual cartesian core embedding is natural for every original same-base source map. -/
theorem cartesianRelativeCoreEmbedding_natural {X X' : Marked.{u}} {E B : SSet.{u}}
    (i : X' ⟶ X) (r : X ⟶ max B) (r' : X' ⟶ max B) (p : E ⟶ B) (hi : i ≫ r = r')
    [InnerFibration p] [Quasicategory B] :
    relativeMappingPre .maximal i r r' (cartesianProjection p) hi ≫ cartesianRelativeCoreEmbedding r' p =
      cartesianRelativeCoreEmbedding r p ≫ core.map (parameterRelativePre i r r' (cartesianProjection p) hi) := by
  let P : cartesian p ⟶ max B := cartesianProjection p
  let f : relativeMappingComplex .maximal r P ⟶ relativeMappingComplex .maximal r' P :=
    relativeMappingPre .maximal i r r' P hi
  let a : relativeMappingComplex .maximal r P ⟶ (core (parameterRelative r P) : SSet.{u}) :=
    cartesianRelativeCoreEmbedding r p
  let b : relativeMappingComplex .maximal r' P ⟶ (core (parameterRelative r' P) : SSet.{u}) :=
    cartesianRelativeCoreEmbedding r' p
  let q : parameterRelative r P ⟶ parameterRelative r' P := parameterRelativePre i r r' P hi
  let j : (core (parameterRelative r P) : SSet.{u}) ⟶ parameterRelative r P := (core (parameterRelative r P)).ι
  let j' : (core (parameterRelative r' P) : SSet.{u}) ⟶ parameterRelative r' P := (core (parameterRelative r' P)).ι
  have ha : a ≫ j = relativeMappingForget .maximal r P := cartesianRelativeCoreEmbedding_ι r p
  have hb : b ≫ j' = relativeMappingForget .maximal r' P := cartesianRelativeCoreEmbedding_ι r' p
  have hq : core.map q ≫ j' = j ≫ q := core.map_ι q
  change f ≫ b = a ≫ core.map q
  apply (cancel_mono j').mp
  rw [Category.assoc, hb, relativeMappingForget_pre, Category.assoc, hq, ← Category.assoc, ha]

/-- Every original marked mono has Kan restriction into the actual cartesian marking under native strict
  equivalence lifting. -/
theorem cartesian_relativeMappingPre_fibration_of_strict {X X' : Marked.{u}} {E B : SSet.{u}}
    (i : X' ⟶ X) [Mono i] (r : X ⟶ max B) (r' : X' ⟶ max B) (p : E ⟶ B)
    (hi : i ≫ r = r') [InnerFibration p] [Quasicategory B] [HasStrictEquivalenceLifting p] :
    Fibration (relativeMappingPre .maximal i r r' (cartesianProjection p) hi) := by
  let P : cartesian p ⟶ max B := cartesianProjection p
  let f : relativeMappingComplex .maximal r P ⟶ relativeMappingComplex .maximal r' P :=
    relativeMappingPre .maximal i r r' P hi
  let a : relativeMappingComplex .maximal r P ⟶ (core (parameterRelative r P) : SSet.{u}) :=
    cartesianRelativeCoreEmbedding r p
  let b : relativeMappingComplex .maximal r' P ⟶ (core (parameterRelative r' P) : SSet.{u}) :=
    cartesianRelativeCoreEmbedding r' p
  let q : (core (parameterRelative r P) : SSet.{u}) ⟶ (core (parameterRelative r' P) : SSet.{u}) :=
    core.map (parameterRelativePre i r r' P hi)
  let _ : InnerFibration P.hom := inferInstanceAs (InnerFibration p)
  let _ : HasStrictEquivalenceLifting P.hom := inferInstanceAs (HasStrictEquivalenceLifting p)
  let _ : Quasicategory (max B).toSSet := inferInstanceAs (Quasicategory B)
  let _ : Mono i.hom := i.mono_underlying
  let _ : Fibration q := fibration_core_parameterRelativePre i r r' P hi
  let _ : Fibration a := cartesianRelativeCoreEmbedding_fibration r p
  let _ : Mono b := cartesianRelativeCoreEmbedding_mono r' p
  have hc : Fibration (f ≫ b) := by
    have he : f ≫ b = a ≫ q := cartesianRelativeCoreEmbedding_natural i r r' p hi
    rw [he]
    infer_instance
  exact (modelCategoryQuillen.fibration_iff f).mpr
    (modelCategoryQuillen.J.rlp_of_comp_right_of_mono f b ((modelCategoryQuillen.fibration_iff (f ≫ b)).mp hc))

/-- The original cartesian projection has Kan restriction along every supplied marked mono, over any
  quasicategory base. -/
theorem cartesian_relativeMappingPre_fibration {X X' : Marked.{u}} {E B : SSet.{u}}
    (i : X' ⟶ X) [Mono i] (r : X ⟶ max B) (r' : X' ⟶ max B) (p : E ⟶ B)
    (hi : i ≫ r = r') [CartesianFibration p] [Quasicategory B] :
    Fibration (relativeMappingPre .maximal i r r' (cartesianProjection p) hi) := by
  let _ : HasStrictEquivalenceLifting p := CartesianFibration.hasStrictEquivalenceLifting p
  exact cartesian_relativeMappingPre_fibration_of_strict i r r' p hi

/-- The actual cocartesian core embedding is natural for every original same-base source map. -/
theorem cocartesianRelativeCoreEmbedding_natural {X X' : Marked.{u}} {E B : SSet.{u}}
    (i : X' ⟶ X) (r : X ⟶ max B) (r' : X' ⟶ max B) (p : E ⟶ B) (hi : i ≫ r = r')
    [InnerFibration p] [Quasicategory B] :
    relativeMappingPre .maximal i r r' (cocartesianProjection p) hi ≫ cocartesianRelativeCoreEmbedding r' p =
      cocartesianRelativeCoreEmbedding r p ≫ core.map (parameterRelativePre i r r' (cocartesianProjection p) hi) := by
  let P : cocartesian p ⟶ max B := cocartesianProjection p
  let f : relativeMappingComplex .maximal r P ⟶ relativeMappingComplex .maximal r' P :=
    relativeMappingPre .maximal i r r' P hi
  let a : relativeMappingComplex .maximal r P ⟶ (core (parameterRelative r P) : SSet.{u}) :=
    cocartesianRelativeCoreEmbedding r p
  let b : relativeMappingComplex .maximal r' P ⟶ (core (parameterRelative r' P) : SSet.{u}) :=
    cocartesianRelativeCoreEmbedding r' p
  let q : parameterRelative r P ⟶ parameterRelative r' P := parameterRelativePre i r r' P hi
  let j : (core (parameterRelative r P) : SSet.{u}) ⟶ parameterRelative r P := (core (parameterRelative r P)).ι
  let j' : (core (parameterRelative r' P) : SSet.{u}) ⟶ parameterRelative r' P := (core (parameterRelative r' P)).ι
  have ha : a ≫ j = relativeMappingForget .maximal r P := cocartesianRelativeCoreEmbedding_ι r p
  have hb : b ≫ j' = relativeMappingForget .maximal r' P := cocartesianRelativeCoreEmbedding_ι r' p
  have hq : core.map q ≫ j' = j ≫ q := core.map_ι q
  change f ≫ b = a ≫ core.map q
  apply (cancel_mono j').mp
  rw [Category.assoc, hb, relativeMappingForget_pre, Category.assoc, hq, ← Category.assoc, ha]

/-- Every original marked mono has Kan restriction into the actual cocartesian marking under native strict
  equivalence lifting. -/
theorem cocartesian_relativeMappingPre_fibration_of_strict {X X' : Marked.{u}} {E B : SSet.{u}}
    (i : X' ⟶ X) [Mono i] (r : X ⟶ max B) (r' : X' ⟶ max B) (p : E ⟶ B)
    (hi : i ≫ r = r') [InnerFibration p] [Quasicategory B] [HasStrictEquivalenceLifting p] :
    Fibration (relativeMappingPre .maximal i r r' (cocartesianProjection p) hi) := by
  let P : cocartesian p ⟶ max B := cocartesianProjection p
  let f : relativeMappingComplex .maximal r P ⟶ relativeMappingComplex .maximal r' P :=
    relativeMappingPre .maximal i r r' P hi
  let a : relativeMappingComplex .maximal r P ⟶ (core (parameterRelative r P) : SSet.{u}) :=
    cocartesianRelativeCoreEmbedding r p
  let b : relativeMappingComplex .maximal r' P ⟶ (core (parameterRelative r' P) : SSet.{u}) :=
    cocartesianRelativeCoreEmbedding r' p
  let q : (core (parameterRelative r P) : SSet.{u}) ⟶ (core (parameterRelative r' P) : SSet.{u}) :=
    core.map (parameterRelativePre i r r' P hi)
  let _ : InnerFibration P.hom := inferInstanceAs (InnerFibration p)
  let _ : HasStrictEquivalenceLifting P.hom := inferInstanceAs (HasStrictEquivalenceLifting p)
  let _ : Quasicategory (max B).toSSet := inferInstanceAs (Quasicategory B)
  let _ : Mono i.hom := i.mono_underlying
  let _ : Fibration q := fibration_core_parameterRelativePre i r r' P hi
  let _ : Fibration a := cocartesianRelativeCoreEmbedding_fibration r p
  let _ : Mono b := cocartesianRelativeCoreEmbedding_mono r' p
  have hc : Fibration (f ≫ b) := by
    have he : f ≫ b = a ≫ q := cocartesianRelativeCoreEmbedding_natural i r r' p hi
    rw [he]
    infer_instance
  exact (modelCategoryQuillen.fibration_iff f).mpr
    (modelCategoryQuillen.J.rlp_of_comp_right_of_mono f b ((modelCategoryQuillen.fibration_iff (f ≫ b)).mp hc))

/-- The original cocartesian projection has Kan restriction along every supplied marked mono, over any
  quasicategory base. -/
theorem cocartesian_relativeMappingPre_fibration {X X' : Marked.{u}} {E B : SSet.{u}}
    (i : X' ⟶ X) [Mono i] (r : X ⟶ max B) (r' : X' ⟶ max B) (p : E ⟶ B)
    (hi : i ≫ r = r') [CocartesianFibration p] [Quasicategory B] :
    Fibration (relativeMappingPre .maximal i r r' (cocartesianProjection p) hi) := by
  let _ : HasStrictEquivalenceLifting p := CocartesianFibration.hasStrictEquivalenceLifting p
  exact cocartesian_relativeMappingPre_fibration_of_strict i r r' p hi

end SSet.Marked
