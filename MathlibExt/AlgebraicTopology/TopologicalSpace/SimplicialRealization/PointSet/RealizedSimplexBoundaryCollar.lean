/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedSimplexBoundaryCutoff

/-!
# Radial boundary retraction of a realized simplex

The complement of the barycenter in a realized standard simplex has a continuous
radial retraction onto its realized boundary. Under the standard realization
homeomorphism, this is the radial projection in barycentric coordinates.

The retraction fixes points already in the boundary. Inclusion after retraction
is the radial projection on the barycenter complement. In dimension zero, both
the complement and the realized boundary are empty.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial Topology

noncomputable section

namespace SSet

/--
The realization point corresponding to the uniform barycentric point of the
standard `n`-simplex.
-/
noncomputable def realizedBarycenter (n : ℕ) :
    SSet.toTop.obj (Δ[n] : SSet.{u}) :=
  (⦋n⦌.toTopHomeo).symm Convexity.StdSimplex.barycenter

/-- Transport from the realized barycenter complement to the standard-simplex
barycenter complement. -/
private noncomputable def realizedComplementToStd (n : ℕ) :
    C({q : SSet.toTop.obj (Δ[n] : SSet.{u}) // q ≠ realizedBarycenter n},
      {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        x ≠ Convexity.StdSimplex.barycenter}) where
  toFun q := ⟨(⦋n⦌.toTopHomeo) q.val, by
    intro hq
    apply q.property
    apply (⦋n⦌.toTopHomeo).injective
    simpa [realizedBarycenter] using hq⟩
  continuous_toFun := Continuous.subtype_mk
    ((⦋n⦌.toTopHomeo).continuous.comp continuous_subtype_val) _

/-- The transported radial projection, before lifting it to the realized
boundary. -/
private noncomputable def realizedBoundaryRadialAmbient (n : ℕ) :
    C({q : SSet.toTop.obj (Δ[n] : SSet.{u}) // q ≠ realizedBarycenter n},
      SSet.toTop.obj (Δ[n] : SSet.{u})) where
  toFun q := (⦋n⦌.toTopHomeo).symm
    (StdSimplexRadialBoundary.radialMap n (realizedComplementToStd n q))
  continuous_toFun := (⦋n⦌.toTopHomeo).symm.continuous.comp
    ((StdSimplexRadialBoundary.continuous_radialMap n).comp
      (realizedComplementToStd n).continuous)

/--
The continuous map from the realized standard simplex with its barycenter removed
to its realized boundary, induced by radial projection. Both spaces are empty
in dimension zero.
-/
noncomputable def realizedBoundaryRadialRetraction (n : ℕ) :
    TopCat.of ({q : SSet.toTop.obj (Δ[n] : SSet.{u}) //
      q ≠ realizedBarycenter n}) ⟶
      SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) := by
  let hEmb : IsEmbedding (SSet.toTop.map (SSet.boundary.{u} n).ι).hom :=
    (TopCat.closedT1Embeddings_le_isClosedEmbedding _
      (SSet.boundary.closedT1Embeddings_toTop_map_ι n)).isEmbedding
  have hNotBary : ∀ q : {q : SSet.toTop.obj (Δ[n] : SSet.{u}) //
      q ≠ realizedBarycenter n},
      (⦋n⦌.toTopHomeo) q.val ≠ Convexity.StdSimplex.barycenter := by
    intro q hq
    apply q.property
    apply (⦋n⦌.toTopHomeo).injective
    simpa [realizedBarycenter] using hq
  let qStd :
      C({q : SSet.toTop.obj (Δ[n] : SSet.{u}) // q ≠ realizedBarycenter n},
        {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
          x ≠ Convexity.StdSimplex.barycenter}) :=
    ⟨fun q => ⟨(⦋n⦌.toTopHomeo) q.val, hNotBary q⟩,
      Continuous.subtype_mk
        ((⦋n⦌.toTopHomeo).continuous.comp continuous_subtype_val) hNotBary⟩
  let ambient :
      C({q : SSet.toTop.obj (Δ[n] : SSet.{u}) // q ≠ realizedBarycenter n},
        SSet.toTop.obj (Δ[n] : SSet.{u})) :=
    ⟨fun q => (⦋n⦌.toTopHomeo).symm
        (StdSimplexRadialBoundary.radialMap n (qStd q)),
      (⦋n⦌.toTopHomeo).symm.continuous.comp
        ((StdSimplexRadialBoundary.continuous_radialMap n).comp qStd.continuous)⟩
  have hRange : ∀ q : {q : SSet.toTop.obj (Δ[n] : SSet.{u}) //
      q ≠ realizedBarycenter n},
      ambient q ∈ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom := by
    intro q
    obtain ⟨j, hj⟩ :=
      StdSimplexRadialBoundary.exists_radialMap_weights_eq_zero n (qStd q)
    exact SSet.mem_realizedBoundary_of_zeroCoord n _ j hj
  let toRange :
      C({q : SSet.toTop.obj (Δ[n] : SSet.{u}) // q ≠ realizedBarycenter n},
        Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom) :=
    ⟨fun q => ⟨ambient q, hRange q⟩,
      Continuous.subtype_mk ambient.continuous hRange⟩
  exact TopCat.ofHom
    ⟨fun q => hEmb.toHomeomorph.symm (toRange q),
      hEmb.toHomeomorph.symm.continuous.comp toRange.continuous⟩

/--
The realized boundary inclusion after radial retraction equals the standard
radial projection transported through the realization homeomorphism.
-/
@[simp]
theorem realizedBoundaryRadialRetraction_ι_apply (n : ℕ)
    (q : {q : SSet.toTop.obj (Δ[n] : SSet.{u}) //
      q ≠ realizedBarycenter n}) :
    SSet.toTop.map (SSet.boundary.{u} n).ι
      (realizedBoundaryRadialRetraction n q) =
      (⦋n⦌.toTopHomeo).symm
        (StdSimplexRadialBoundary.radialMap n
          ⟨(⦋n⦌.toTopHomeo) q.val, by
            intro hq
            apply q.property
            apply (⦋n⦌.toTopHomeo).injective
            simpa [realizedBarycenter] using hq⟩) := by
  change SSet.toTop.map (SSet.boundary.{u} n).ι
      (realizedBoundaryRadialRetraction n q) =
    realizedBoundaryRadialAmbient n q
  let hEmb : IsEmbedding (SSet.toTop.map (SSet.boundary.{u} n).ι).hom :=
    (TopCat.closedT1Embeddings_le_isClosedEmbedding _
      (SSet.boundary.closedT1Embeddings_toTop_map_ι n)).isEmbedding
  let y : Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom :=
    ⟨realizedBoundaryRadialAmbient n q, by
      obtain ⟨j, hj⟩ :=
        StdSimplexRadialBoundary.exists_radialMap_weights_eq_zero n
          (realizedComplementToStd n q)
      exact SSet.mem_realizedBoundary_of_zeroCoord n _ j hj⟩
  have h := hEmb.toHomeomorph.apply_symm_apply y
  exact congrArg Subtype.val h

/--
For a realized boundary point whose image is not the barycenter, the radial
retraction of that included point is the original boundary point.
-/
theorem realizedBoundaryRadialRetraction_on_boundary (n : ℕ)
    (x : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}))
    (hx : SSet.toTop.map (SSet.boundary.{u} n).ι x ≠
      realizedBarycenter n) :
    realizedBoundaryRadialRetraction n
      ⟨SSet.toTop.map (SSet.boundary.{u} n).ι x, hx⟩ = x := by
  apply (TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (SSet.boundary.closedT1Embeddings_toTop_map_ι n)).isEmbedding.injective
  rw [realizedBoundaryRadialRetraction_ι_apply]
  obtain ⟨j, hj⟩ :=
    SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange n
      (SSet.toTop.map (SSet.boundary.{u} n).ι x) ⟨x, rfl⟩
  rw [StdSimplexRadialBoundary.radialMap_eq_of_has_zero n _ j hj]
  exact (⦋n⦌.toTopHomeo).symm_apply_apply _

end SSet
