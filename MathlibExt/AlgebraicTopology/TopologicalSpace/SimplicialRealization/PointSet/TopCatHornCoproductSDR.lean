/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivCoproducts
public import
  MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingColimits
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatSDRPushoutWeakHomotopy

/-!
# Coproduct strong-deformation-retract data for realized horns

For a `Type u` family of positive-dimensional horns, the coproduct of the
realized horn inclusions carries bundled retraction, homotopy, and pointwise
fix data via `TopCat.homotopySigma`; the comparison iso identifies the
categorical coproduct map with the bundled one for the pushout leg theorem.
No transfinite composition or model structure is claimed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace TopCat

variable (J : Type u) (n : J → ℕ) (k : ∀ j, Fin (n j + 1)) (hn : ∀ j, 0 < n j)

/-- Realized horn family over the index type. -/
noncomputable def hornSDRDomain (j : J) : TopCat.{u} :=
  SSet.toTop.obj (SSet.horn.{u} (n j) (k j))

/-- Realized simplex family over the index type. -/
noncomputable def hornSDRSimplex (j : J) : TopCat.{u} :=
  SSet.toTop.obj (Δ[n j] : SSet.{u})

/-- Family of realized horn inclusions. -/
noncomputable def hornSDRIncl (j : J) :
    hornSDRDomain J n k j ⟶ hornSDRSimplex J n j :=
  SSet.toTop.map (SSet.horn.{u} (n j) (k j)).ι

/-- Bundled coproduct inclusion of the realized horns. -/
noncomputable def hornSDRCopIncl : C((Σ j : J, ↥(hornSDRDomain J n k j)),
    (Σ j : J, ↥(hornSDRSimplex J n j))) :=
  ContinuousMap.sigma fun j : J => (ContinuousMap.sigmaMk j).comp
    (hornSDRIncl J n k j).hom

/-- Bundled coproduct retraction onto the realized horns. -/
noncomputable def hornSDRCopRetract : C((Σ j : J, ↥(hornSDRSimplex J n j)),
    (Σ j : J, ↥(hornSDRDomain J n k j))) :=
  ContinuousMap.sigma fun j : J => (ContinuousMap.sigmaMk j).comp
    (SSet.realizedHornRetract (n j) (k j) (hn j))

/-- The bundled coproduct retraction is left inverse to the inclusion. -/
theorem hornSDRCopRetract_comp : (hornSDRCopRetract J n k hn).comp
      (hornSDRCopIncl J n k) = ContinuousMap.id _ := by
  apply DFunLike.ext; rintro ⟨j, y⟩
  exact congrArg (Sigma.mk j) (SSet.realizedHornRetract_ι (n j) (k j) (hn j) y)

/-- Bundled coproduct homotopy from the identity. -/
noncomputable def hornSDRHomotopy : ContinuousMap.Homotopy (ContinuousMap.id _)
    ((hornSDRCopIncl J n k).comp (hornSDRCopRetract J n k hn)) := by
  have h0 : (ContinuousMap.sigma fun j : J =>
      (ContinuousMap.sigmaMk (X := fun j : J => ↥(hornSDRSimplex J n j)) j).comp
        (ContinuousMap.id _)) = ContinuousMap.id _ := by
    apply DFunLike.ext; rintro ⟨j, x⟩; rfl
  have h1 : (ContinuousMap.sigma fun j : J => (ContinuousMap.sigmaMk j).comp
      (((hornSDRIncl J n k j).hom).comp
        (SSet.realizedHornRetract (n j) (k j) (hn j)))) =
      (hornSDRCopIncl J n k).comp (hornSDRCopRetract J n k hn) := by
    apply DFunLike.ext; rintro ⟨j, x⟩; rfl
  rw [← h0, ← h1]
  exact homotopySigma fun j : J =>
    (ContinuousMap.Homotopy.refl (ContinuousMap.sigmaMk j)).comp
      (SSet.realizedHornHomotopy (n j) (k j) (hn j))

/-- The bundled coproduct homotopy fixes the horns pointwise. -/
theorem hornSDRHomotopy_fix (t : unitInterval) (j : J)
    (y : ↥(hornSDRDomain J n k j)) :
    (hornSDRHomotopy J n k hn).toContinuousMap (t, (hornSDRCopIncl J n k) ⟨j, y⟩) =
      (hornSDRCopIncl J n k) ⟨j, y⟩ := by
  have hfix := SSet.realizedHornHomotopyMap_fix (n j) (k j) (hn j) y t
  have h1 : (hornSDRCopIncl J n k)
        (⟨j, y⟩ : Σ j : J, ↥(hornSDRDomain J n k j)) =
      (ContinuousMap.sigmaMk j) ((hornSDRIncl J n k j).hom y) := rfl
  rw [h1]
  exact congrArg (ContinuousMap.sigmaMk
    (X := fun j : J => ↥(hornSDRSimplex J n j)) j) hfix

/-- Categorical coproduct retraction. -/
noncomputable def hornSDRRetract :
    (∐ fun j : J => hornSDRSimplex J n j) ⟶
      (∐ fun j : J => hornSDRDomain J n k j) :=
  (TopCat.sigmaIsoSigma _).hom ≫ TopCat.ofHom (hornSDRCopRetract J n k hn) ≫
      (TopCat.sigmaIsoSigma _).inv

/-- The categorical inclusion is the bundled one up to the comparison iso. -/
theorem hornSDRIncl_naturality :
    (TopCat.sigmaIsoSigma _).hom ≫ TopCat.ofHom (hornSDRCopIncl J n k) =
      Limits.Sigma.map (fun j : J => hornSDRIncl J n k j) ≫
        (TopCat.sigmaIsoSigma _).hom :=
  TopCat.sigmaIsoSigma_hom_naturality (fun j : J => by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl)

/-- Categorical coproduct retraction law for the bundled map. -/
theorem hornSDR_retract' : TopCat.ofHom (hornSDRCopIncl J n k) ≫
      TopCat.ofHom (hornSDRCopRetract J n k hn) = 𝟙 _ := by
  rw [← TopCat.ofHom_comp, hornSDRCopRetract_comp J n k hn, TopCat.ofHom_id]

/-- Categorical coproduct homotopy from the identity for the bundled map. -/
noncomputable def hornSDRHomotopyTop' : TopCat.Homotopy
    (𝟙 (TopCat.of (Σ j : J, ↥(hornSDRSimplex J n j))))
    (TopCat.ofHom (hornSDRCopRetract J n k hn) ≫ TopCat.ofHom (hornSDRCopIncl J n k)) :=
  ContinuousMap.Homotopy.cast (hornSDRHomotopy J n k hn)
    (TopCat.hom_id (X := TopCat.of (Σ j : J, ↥(hornSDRSimplex J n j)))).symm rfl

/-- The bundled coproduct homotopy fixes the horns pointwise, categorically. -/
theorem hornSDR_stat' (t : unitInterval)
    (a : ↥(TopCat.of (Σ j : J, ↥(hornSDRDomain J n k j)))) :
    (hornSDRHomotopyTop' J n k hn) (t, TopCat.ofHom (hornSDRCopIncl J n k) a) =
      TopCat.ofHom (hornSDRCopIncl J n k) a := by
  obtain ⟨j, y⟩ := (a : Σ j : J, ↥(hornSDRDomain J n k j))
  exact hornSDRHomotopy_fix J n k hn t j y

/-- The categorical coproduct map agrees with the bundled one up to iso. -/
@[nolint defsWithUnderscore]
noncomputable def hornSDR_arrow_iso :
    Arrow.mk (Limits.Sigma.map (fun j : J => hornSDRIncl J n k j)) ≅
      Arrow.mk (TopCat.ofHom (hornSDRCopIncl J n k)) :=
  Arrow.isoMk (TopCat.sigmaIsoSigma _) (TopCat.sigmaIsoSigma _)
    (hornSDRIncl_naturality J n k)

/-- Pushout legs of bundled horn-coproduct inclusions are weak equivalences. -/
theorem hornSDR_pushout_inr_mem (hn : ∀ j, 0 < n j) {Y P : TopCat.{u}}
    {f : TopCat.of (Σ j : J, ↥(hornSDRDomain J n k j)) ⟶ Y}
    {g : TopCat.of (Σ j : J, ↥(hornSDRSimplex J n j)) ⟶ P} {j : Y ⟶ P}
    (h : IsPushout (TopCat.ofHom (hornSDRCopIncl J n k)) f g j) :
    weakHomotopyEquivalences j :=
  sdr_pushout_inr_mem_weakHomotopyEquivalences h
    (TopCat.ofHom (hornSDRCopRetract J n k hn)) (hornSDR_retract' J n k hn)
    (hornSDRHomotopyTop' J n k hn) (hornSDR_stat' J n k hn)

end TopCat
