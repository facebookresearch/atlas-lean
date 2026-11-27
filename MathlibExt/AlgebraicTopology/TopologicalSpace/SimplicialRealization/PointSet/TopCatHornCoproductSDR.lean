/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivCoproducts
public import
  MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingColimits
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatSDRPushoutWeakHomotopy

/-!
# Strong deformation retraction of a horn coproduct

For a family of positive-dimensional horns, the disjoint union of their
realizations retracts from the disjoint union of the realized simplices.
The component horn homotopies assemble to a homotopy from the identity to
retraction followed by inclusion, fixing the horn coproduct pointwise.

The categorical coproduct arrows identify with the bundled disjoint-union
maps. These data also give weak homotopy-equivalence pushout legs for the
bundled horn-coproduct inclusion. The index and space carriers share the
specified universe.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace TopCat

variable (J : Type u) (n : J → ℕ) (k : ∀ j, Fin (n j + 1)) (hn : ∀ j, 0 < n j)

/--
The realized horn `|Λ[n_j,k_j]|` at family index `j`.
-/
noncomputable def hornSDRDomain (j : J) : TopCat.{u} :=
  SSet.toTop.obj (SSet.horn.{u} (n j) (k j))

/--
The realized standard simplex `|Δ[n_j]|` at family index `j`.
-/
noncomputable def hornSDRSimplex (j : J) : TopCat.{u} :=
  SSet.toTop.obj (Δ[n j] : SSet.{u})

/--
The component map `|Λ[n_j,k_j]| → |Δ[n_j]|` in the realized horn family.
-/
noncomputable def hornSDRIncl (j : J) :
    hornSDRDomain J n k j ⟶ hornSDRSimplex J n j :=
  SSet.toTop.map (SSet.horn.{u} (n j) (k j)).ι

/--
The continuous map between the disjoint unions applying the realized horn
inclusion in each component and preserving its index.
-/
noncomputable def hornSDRCopIncl : C((Σ j : J, ↥(hornSDRDomain J n k j)),
    (Σ j : J, ↥(hornSDRSimplex J n j))) :=
  ContinuousMap.sigma fun j : J => (ContinuousMap.sigmaMk j).comp
    (hornSDRIncl J n k j).hom

/--
The continuous retraction of the simplex disjoint union to the horn disjoint
union, applying the component horn retraction and preserving the index.
-/
noncomputable def hornSDRCopRetract : C((Σ j : J, ↥(hornSDRSimplex J n j)),
    (Σ j : J, ↥(hornSDRDomain J n k j))) :=
  ContinuousMap.sigma fun j : J => (ContinuousMap.sigmaMk j).comp
    (SSet.realizedHornRetract (n j) (k j) (hn j))

/--
The bundled horn inclusion followed by the bundled retraction is the identity
on the horn disjoint union.
-/
theorem hornSDRCopRetract_comp : (hornSDRCopRetract J n k hn).comp
      (hornSDRCopIncl J n k) = ContinuousMap.id _ := by
  apply DFunLike.ext; rintro ⟨j, y⟩
  exact congrArg (Sigma.mk j) (SSet.realizedHornRetract_ι (n j) (k j) (hn j) y)

/--
The homotopy from the identity of the simplex disjoint union to retraction
followed by the horn disjoint-union inclusion.
-/
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

/--
At every interval parameter, the coproduct homotopy fixes each included horn
point in its component.
-/
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

/--
The map from the categorical coproduct of realized simplices to the categorical
coproduct of realized horns induced by the bundled retraction.
-/
noncomputable def hornSDRRetract :
    (∐ fun j : J => hornSDRSimplex J n j) ⟶
      (∐ fun j : J => hornSDRDomain J n k j) :=
  (TopCat.sigmaIsoSigma _).hom ≫ TopCat.ofHom (hornSDRCopRetract J n k hn) ≫
      (TopCat.sigmaIsoSigma _).inv

/--
The categorical horn-coproduct inclusion corresponds to the bundled inclusion
under the canonical coproduct-to-disjoint-union isomorphisms.
-/
theorem hornSDRIncl_naturality :
    (TopCat.sigmaIsoSigma _).hom ≫ TopCat.ofHom (hornSDRCopIncl J n k) =
      Limits.Sigma.map (fun j : J => hornSDRIncl J n k j) ≫
        (TopCat.sigmaIsoSigma _).hom :=
  TopCat.sigmaIsoSigma_hom_naturality (fun j : J => by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl)

/--
The bundled horn inclusion followed by the bundled horn retraction is the
identity as a topological morphism.
-/
theorem hornSDR_retract' : TopCat.ofHom (hornSDRCopIncl J n k) ≫
      TopCat.ofHom (hornSDRCopRetract J n k hn) = 𝟙 _ := by
  rw [← TopCat.ofHom_comp, hornSDRCopRetract_comp J n k hn, TopCat.ofHom_id]

/--
The topological homotopy from the identity of the bundled simplex coproduct
to bundled retraction followed by bundled inclusion.
-/
noncomputable def hornSDRHomotopyTop' : TopCat.Homotopy
    (𝟙 (TopCat.of (Σ j : J, ↥(hornSDRSimplex J n j))))
    (TopCat.ofHom (hornSDRCopRetract J n k hn) ≫ TopCat.ofHom (hornSDRCopIncl J n k)) :=
  ContinuousMap.Homotopy.cast (hornSDRHomotopy J n k hn)
    (TopCat.hom_id (X := TopCat.of (Σ j : J, ↥(hornSDRSimplex J n j)))).symm rfl

/--
The bundled topological homotopy fixes every point in the image of the bundled
horn inclusion at every time.
-/
theorem hornSDR_stat' (t : unitInterval)
    (a : ↥(TopCat.of (Σ j : J, ↥(hornSDRDomain J n k j)))) :
    (hornSDRHomotopyTop' J n k hn) (t, TopCat.ofHom (hornSDRCopIncl J n k) a) =
      TopCat.ofHom (hornSDRCopIncl J n k) a := by
  obtain ⟨j, y⟩ := (a : Σ j : J, ↥(hornSDRDomain J n k j))
  exact hornSDRHomotopy_fix J n k hn t j y

/--
The isomorphism of arrows between the categorical horn-coproduct inclusion
and the bundled disjoint-union horn inclusion.
-/
@[nolint defsWithUnderscore]
noncomputable def hornSDR_arrow_iso :
    Arrow.mk (Limits.Sigma.map (fun j : J => hornSDRIncl J n k j)) ≅
      Arrow.mk (TopCat.ofHom (hornSDRCopIncl J n k)) :=
  Arrow.isoMk (TopCat.sigmaIsoSigma _) (TopCat.sigmaIsoSigma _)
    (hornSDRIncl_naturality J n k)

/--
For a family of positive-dimensional horns, any pushout of the bundled
horn-coproduct inclusion has a weak homotopy-equivalence opposite leg.
-/
theorem hornSDR_pushout_inr_mem (hn : ∀ j, 0 < n j) {Y P : TopCat.{u}}
    {f : TopCat.of (Σ j : J, ↥(hornSDRDomain J n k j)) ⟶ Y}
    {g : TopCat.of (Σ j : J, ↥(hornSDRSimplex J n j)) ⟶ P} {j : Y ⟶ P}
    (h : IsPushout (TopCat.ofHom (hornSDRCopIncl J n k)) f g j) :
    weakHomotopyEquivalences j :=
  sdr_pushout_inr_mem_weakHomotopyEquivalences h
    (TopCat.ofHom (hornSDRCopRetract J n k hn)) (hornSDR_retract' J n k hn)
    (hornSDRHomotopyTop' J n k hn) (hornSDR_stat' J n k hn)

end TopCat
