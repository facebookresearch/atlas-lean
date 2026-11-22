/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingCoreMarkingInvariance
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeMappingCoreIso
import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplexFibration

/-!
# Native intrinsic relative mapping complexes embed by Kan fibrations

Intrinsic marked-map vertices form whole components in the original
ordinary relative core. Its full-subcomplex inclusion is consequently a
Kan fibration. Composing with the actual marked/core isomorphism gives
the original whole-prism embedding, retaining its base point. The source
marking and base simplicial set are never replaced.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- The actual cartesian relative marked-map condition is invariant across every original relative core edge. -/
theorem cartesian_relativeCoreVertices_edgeInvariant {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (z : (core (parameterRelative r (cartesianProjection p)) : SSet.{u}) _⦋1⦌) :
    (core (parameterRelative r (cartesianProjection p)) : SSet.{u}).δ 1 z ∈
        relativeMappingCoreVertices r (cartesianProjection p) ↔
      (core (parameterRelative r (cartesianProjection p)) : SSet.{u}).δ 0 z ∈
        relativeMappingCoreVertices r (cartesianProjection p) := by
  let q : parameterRelative r (cartesianProjection p) ⟶ parameterMapping X.toSSet E :=
    pullback.fst _ _
  let j : (core (parameterRelative r (cartesianProjection p)) : SSet.{u}) ⟶
      (core (parameterMapping X.toSSet E) : SSet.{u}) := core.map q
  let V : Set ((parameterMapping X.toSSet E) _⦋0⦌) := markedMappingVertices X (cartesian p)
  change (j.app (op ⦋0⦌) ((core (parameterRelative r (cartesianProjection p)) : SSet.{u}).δ 1 z)).val ∈
      V ↔
    (j.app (op ⦋0⦌) ((core (parameterRelative r (cartesianProjection p)) : SSet.{u}).δ 0 z)).val ∈
      V
  have h₁ := congrArg Subtype.val (SSet.δ_naturality_apply j (1 : Fin 2) z)
  have h₀ := congrArg Subtype.val (SSet.δ_naturality_apply j (0 : Fin 2) z)
  rw [h₁, h₀]
  exact cartesian_markedVertices_core_edgeInvariant p (j.app (op ⦋1⦌) z)

/-- The original cartesian full-core inclusion is a Kan fibration with all original source marks. -/
theorem cartesian_relativeCore_inclusion_fibration {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    Fibration (Subcomplex.full (X := (core (parameterRelative r (cartesianProjection p)) : SSet.{u}))
      (relativeMappingCoreVertices r (cartesianProjection p))).ι :=
  Subcomplex.fibration_full_ι_of_edge_invariant _ (cartesian_relativeCoreVertices_edgeInvariant r p)

/-- The original cartesian maximal marked complex maps into its whole ordinary relative core. -/
def cartesianRelativeCoreEmbedding {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    relativeMappingComplex .maximal r (cartesianProjection p) ⟶
      (core (parameterRelative r (cartesianProjection p)) : SSet.{u}) :=
  (cartesianMappingCoreIso r p).hom ≫ (Subcomplex.full (X := (core (parameterRelative r (cartesianProjection
    p)) : SSet.{u})) (relativeMappingCoreVertices r (cartesianProjection p))).ι

/-- The cartesian embedding retains every original full prism and fixed-base coordinate. -/
@[reassoc]
theorem cartesianRelativeCoreEmbedding_ι {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    cartesianRelativeCoreEmbedding r p ≫ (core (parameterRelative r (cartesianProjection p))).ι =
      relativeMappingForget .maximal r (cartesianProjection p) := by
  change ((cartesianMappingCoreIso r p).hom ≫ (Subcomplex.full (X := (core (parameterRelative r
    (cartesianProjection p)) : SSet.{u})) (relativeMappingCoreVertices r (cartesianProjection p))).ι) ≫
      (core (parameterRelative r (cartesianProjection p))).ι = _
  exact (Category.assoc _ _ _).trans (cartesianMappingCoreIso_hom_forget r p)

/-- The actual cartesian whole-prism embedding is monic. -/
theorem cartesianRelativeCoreEmbedding_mono {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    Mono (cartesianRelativeCoreEmbedding r p) := by
  let a : relativeMappingComplex .maximal r (cartesianProjection p) ⟶ relativeMappingCore r (cartesianProjection p) :=
    (cartesianMappingCoreIso r p).hom
  let b : relativeMappingCore r (cartesianProjection p) ⟶ (core (parameterRelative r (cartesianProjection
    p)) : SSet.{u}) :=
    (Subcomplex.full (X := (core (parameterRelative r (cartesianProjection p)) : SSet.{u}))
      (relativeMappingCoreVertices r (cartesianProjection p))).ι
  let _ : Mono a := inferInstanceAs (Mono (cartesianMappingCoreIso r p).hom)
  let _ : Mono b := inferInstanceAs (Mono (Subcomplex.full (X := (core (parameterRelative r
    (cartesianProjection p)) : SSet.{u}))
    (relativeMappingCoreVertices r (cartesianProjection p))).ι)
  change Mono (a ≫ b)
  infer_instance

/-- The actual cartesian whole-prism embedding is a Kan fibration. -/
theorem cartesianRelativeCoreEmbedding_fibration {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    Fibration (cartesianRelativeCoreEmbedding r p) := by
  let a : relativeMappingComplex .maximal r (cartesianProjection p) ⟶ relativeMappingCore r (cartesianProjection p) :=
    (cartesianMappingCoreIso r p).hom
  let b : relativeMappingCore r (cartesianProjection p) ⟶ (core (parameterRelative r (cartesianProjection
    p)) : SSet.{u}) :=
    (Subcomplex.full (X := (core (parameterRelative r (cartesianProjection p)) : SSet.{u}))
      (relativeMappingCoreVertices r (cartesianProjection p))).ι
  let _ : Fibration a := inferInstanceAs (Fibration (cartesianMappingCoreIso r p).hom)
  let _ : Fibration b := cartesian_relativeCore_inclusion_fibration r p
  change Fibration (a ≫ b)
  infer_instance

/-- The actual cocartesian relative marked-map condition is invariant across every original relative core edge. -/
theorem cocartesian_relativeCoreVertices_edgeInvariant {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    (z : (core (parameterRelative r (cocartesianProjection p)) : SSet.{u}) _⦋1⦌) :
    (core (parameterRelative r (cocartesianProjection p)) : SSet.{u}).δ 1 z ∈
        relativeMappingCoreVertices r (cocartesianProjection p) ↔
      (core (parameterRelative r (cocartesianProjection p)) : SSet.{u}).δ 0 z ∈
        relativeMappingCoreVertices r (cocartesianProjection p) := by
  let q : parameterRelative r (cocartesianProjection p) ⟶ parameterMapping X.toSSet E :=
    pullback.fst _ _
  let j : (core (parameterRelative r (cocartesianProjection p)) : SSet.{u}) ⟶
      (core (parameterMapping X.toSSet E) : SSet.{u}) := core.map q
  let V : Set ((parameterMapping X.toSSet E) _⦋0⦌) := markedMappingVertices X (cocartesian p)
  change (j.app (op ⦋0⦌) ((core (parameterRelative r (cocartesianProjection p)) : SSet.{u}).δ 1 z)).val ∈
      V ↔
    (j.app (op ⦋0⦌) ((core (parameterRelative r (cocartesianProjection p)) : SSet.{u}).δ 0 z)).val ∈
      V
  have h₁ := congrArg Subtype.val (SSet.δ_naturality_apply j (1 : Fin 2) z)
  have h₀ := congrArg Subtype.val (SSet.δ_naturality_apply j (0 : Fin 2) z)
  rw [h₁, h₀]
  exact cocartesian_markedVertices_core_edgeInvariant p (j.app (op ⦋1⦌) z)

/-- The original cocartesian full-core inclusion is a Kan fibration with all original source marks. -/
theorem cocartesian_relativeCore_inclusion_fibration {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    Fibration (Subcomplex.full (X := (core (parameterRelative r (cocartesianProjection p)) : SSet.{u}))
      (relativeMappingCoreVertices r (cocartesianProjection p))).ι :=
  Subcomplex.fibration_full_ι_of_edge_invariant _ (cocartesian_relativeCoreVertices_edgeInvariant r p)

/-- The original cocartesian maximal marked complex maps into its whole ordinary relative core. -/
def cocartesianRelativeCoreEmbedding {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    relativeMappingComplex .maximal r (cocartesianProjection p) ⟶
      (core (parameterRelative r (cocartesianProjection p)) : SSet.{u}) :=
  (cocartesianMappingCoreIso r p).hom ≫ (Subcomplex.full (X := (core (parameterRelative r
    (cocartesianProjection p)) : SSet.{u})) (relativeMappingCoreVertices r (cocartesianProjection p))).ι

/-- The cocartesian embedding retains every original full prism and fixed-base coordinate. -/
@[reassoc]
theorem cocartesianRelativeCoreEmbedding_ι {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    cocartesianRelativeCoreEmbedding r p ≫ (core (parameterRelative r (cocartesianProjection p))).ι =
      relativeMappingForget .maximal r (cocartesianProjection p) := by
  change ((cocartesianMappingCoreIso r p).hom ≫ (Subcomplex.full (X := (core (parameterRelative r
    (cocartesianProjection p)) : SSet.{u})) (relativeMappingCoreVertices r (cocartesianProjection p))).ι) ≫
      (core (parameterRelative r (cocartesianProjection p))).ι = _
  exact (Category.assoc _ _ _).trans (cocartesianMappingCoreIso_hom_forget r p)

/-- The actual cocartesian whole-prism embedding is monic. -/
theorem cocartesianRelativeCoreEmbedding_mono {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    Mono (cocartesianRelativeCoreEmbedding r p) := by
  let a : relativeMappingComplex .maximal r (cocartesianProjection p) ⟶ relativeMappingCore r
    (cocartesianProjection p) :=
    (cocartesianMappingCoreIso r p).hom
  let b : relativeMappingCore r (cocartesianProjection p) ⟶ (core (parameterRelative r
    (cocartesianProjection p)) : SSet.{u}) :=
    (Subcomplex.full (X := (core (parameterRelative r (cocartesianProjection p)) : SSet.{u}))
      (relativeMappingCoreVertices r (cocartesianProjection p))).ι
  let _ : Mono a := inferInstanceAs (Mono (cocartesianMappingCoreIso r p).hom)
  let _ : Mono b := inferInstanceAs (Mono (Subcomplex.full (X := (core (parameterRelative r
    (cocartesianProjection p)) : SSet.{u}))
    (relativeMappingCoreVertices r (cocartesianProjection p))).ι)
  change Mono (a ≫ b)
  infer_instance

/-- The actual cocartesian whole-prism embedding is a Kan fibration. -/
theorem cocartesianRelativeCoreEmbedding_fibration {X : Marked.{u}} {E B : SSet.{u}}
    (r : X ⟶ max B) (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    Fibration (cocartesianRelativeCoreEmbedding r p) := by
  let a : relativeMappingComplex .maximal r (cocartesianProjection p) ⟶ relativeMappingCore r
    (cocartesianProjection p) :=
    (cocartesianMappingCoreIso r p).hom
  let b : relativeMappingCore r (cocartesianProjection p) ⟶ (core (parameterRelative r
    (cocartesianProjection p)) : SSet.{u}) :=
    (Subcomplex.full (X := (core (parameterRelative r (cocartesianProjection p)) : SSet.{u}))
      (relativeMappingCoreVertices r (cocartesianProjection p))).ι
  let _ : Fibration a := inferInstanceAs (Fibration (cocartesianMappingCoreIso r p).hom)
  let _ : Fibration b := cocartesian_relativeCore_inclusion_fibration r p
  change Fibration (a ≫ b)
  infer_instance

end SSet.Marked
