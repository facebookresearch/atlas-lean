/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.FiniteRelativeApproximation
public import MathlibExt.AlgebraicTopology.SimplicialComplex.Subdivision

/-!
# Simplicial approximation on actual finite subdivisions

The finite domain has finitely many actual faces, with no finiteness
assumption on unused ambient labels. The target retains its arbitrary weak
finite-face topology. The subdivision, comparison maps, shrinking mesh and
continuous carrier homotopy are constructed from the actual complexes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Topology

universe u v

namespace PreAbstractSimplicialComplex

variable {V : Type u} {W : Type v}

namespace Realization

private theorem faceBarycenter_point {P : PreAbstractSimplicialComplex V} (s : Face P) :
    (faceBarycenter s).point = Convexity.StdSimplex.subBarycenter s.val
      (P.isRelLowerSet_faces s.property).1 := by
  classical
  let := (P.isRelLowerSet_faces s.property).1.to_subtype
  change (Convexity.StdSimplex.subBarycenter (K := ℝ) (Finset.univ : Finset s.val)
    Finset.univ_nonempty).map (Subtype.val : s.val → V) = _
  rw [map_subBarycenter_injective _ Subtype.val_injective]
  congr 1
  exact Finset.attach_image_val

private theorem diam_iteratedFace_succ_le (P : PreAbstractSimplicialComplex V)
    [Finite (Face P)] (N n : ℕ)
    (hN : ∀ a : Face (subdivisionIter P n), a.val.card ≤ N + 1)
    (s : Face (subdivisionIter P (n + 1))) :
    letI := finiteCoordinateMetricSpace P
    Metric.diam ((iteratedHomeomorph P (n + 1)) ''
      Set.range (faceMap (subdivisionIter P (n + 1)) s)) ≤
      (N : ℝ) / ((N : ℝ) + 1) * Metric.diam ((iteratedHomeomorph P n) ''
        Set.range (faceMap (subdivisionIter P n)
          (subdivisionLastFace (subdivisionIter P n) s))) := by
  classical
  let := finiteCoordinateMetricSpace P
  let R := subdivisionIter P n
  let e : C(Realization R, Realization P) :=
    ⟨iteratedHomeomorph P n, (iteratedHomeomorph P n).continuous⟩
  let F : Convexity.StdSimplex ℝ s.val → Realization P :=
    fun q => iteratedHomeomorph P (n + 1) (faceMap (subdivisionIter P (n + 1)) s q)
  let enum := OrderComplex.faceEnumeration (α := Face R) s
  let faces : Fin (s.val.card - 1 + 1) → Face R := fun j => (enum j).val
  have hchain : Monotone faces := fun i j hij => enum.monotone hij
  have hv (a : s.val) : F (Convexity.StdSimplex.single a) = e (faceBarycenter a.val) := by
    change iteratedHomeomorph P n
      (barycentricHomeomorph R
        (faceMap (barycentricSubdivision R) s (Convexity.StdSimplex.single a))) = _
    apply congrArg (iteratedHomeomorph P n)
    apply Realization.ext
    erw [barycentricHomeomorph_faceMap_point R s (Convexity.StdSimplex.single a),
      Convexity.iConvexComb_single,
      faceBarycenter_point]
  have hrange : Set.range (fun a : s.val => F (Convexity.StdSimplex.single a)) =
      Set.range (fun j => e (faceBarycenter (faces j))) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨enum.symm a, ?_⟩
      have he : faces (enum.symm a) = a.val :=
        congrArg (fun b : s.val => b.val) (enum.apply_symm_apply a)
      change e (faceBarycenter (faces (enum.symm a))) = F (Convexity.StdSimplex.single a)
      erw [he]
      exact (hv a).symm
    · rintro ⟨j, rfl⟩
      exact ⟨enum j, hv (enum j)⟩
  have hwhole := diam_range_affine_le F
    (fun a : s.val => F (Convexity.StdSimplex.single a))
    (fun q => iteratedHomeomorph_faceMap_point P (n + 1) s q)
  rw [hrange] at hwhole
  have hvertices := diam_faceBarycenters_chain_le e faces hchain
    (hN (faces (Fin.last (s.val.card - 1))))
    (fun j => isAffineMap_iteratedHomeomorph_faceMap P n (faces j))
  have hsource : (iteratedHomeomorph P (n + 1)) ''
      Set.range (faceMap (subdivisionIter P (n + 1)) s) = Set.range F :=
    (Set.range_comp (iteratedHomeomorph P (n + 1))
      (faceMap (subdivisionIter P (n + 1)) s)).symm
  rw [hsource]
  exact hwhole.trans hvertices

/-- The actual finite subdivision iterates have a derived geometric mesh bound
in the fixed original polyhedron. Its coefficient is obtained from the actual
uniform face-cardinality bound, including the empty complex. -/
theorem exists_iterated_mesh_bound (P : PreAbstractSimplicialComplex V)
    [Finite (Face P)] :
    letI := finiteCoordinateMetricSpace P
    ∃ N : ℕ, ∀ (n : ℕ) (s : Face (subdivisionIter P n)),
      Metric.diam ((iteratedHomeomorph P n) ''
        Set.range (faceMap (subdivisionIter P n) s)) ≤
          ((N : ℝ) / ((N : ℝ) + 1)) ^ n *
            Metric.diam (Set.univ : Set (Realization P)) := by
  let := finiteCoordinateMetricSpace P
  obtain ⟨N, hN⟩ := exists_uniform_subdivisionIter_card_bound P
  refine ⟨N, ?_⟩
  intro n
  induction n with
  | zero =>
      intro s
      change Metric.diam (_root_.id '' Set.range (faceMap P s)) ≤ _
      rw [Set.image_id, pow_zero, one_mul]
      exact Metric.diam_mono (Set.subset_univ _) isCompact_univ.isBounded
  | succ n ih =>
      intro s
      have hstep := diam_iteratedFace_succ_le P N n (hN n) s
      have hfactor : 0 ≤ (N : ℝ) / ((N : ℝ) + 1) := by positivity
      calc
        Metric.diam ((iteratedHomeomorph P (n + 1)) ''
            Set.range (faceMap (subdivisionIter P (n + 1)) s)) ≤
            (N : ℝ) / ((N : ℝ) + 1) * Metric.diam ((iteratedHomeomorph P n) ''
              Set.range (faceMap (subdivisionIter P n)
                (subdivisionLastFace (subdivisionIter P n) s))) := hstep
        _ ≤ (N : ℝ) / ((N : ℝ) + 1) *
            (((N : ℝ) / ((N : ℝ) + 1)) ^ n *
              Metric.diam (Set.univ : Set (Realization P))) :=
          mul_le_mul_of_nonneg_left (ih _) hfactor
        _ = ((N : ℝ) / ((N : ℝ) + 1)) ^ (n + 1) *
            Metric.diam (Set.univ : Set (Realization P)) := by ring

end Realization

/-- The actual continuous comparison of the specified finite subdivision with
the original polyhedron, obtained from its constructed homeomorphism. -/
def subdivisionRealizationMap (P : PreAbstractSimplicialComplex V) (n : ℕ) :
    C(Realization (subdivisionIter P n), Realization P) :=
  ⟨iteratedHomeomorph P n, (iteratedHomeomorph P n).continuous⟩

/-- The actual inverse comparison, retaining the original weak topology. -/
def subdivisionRealizationInverse (P : PreAbstractSimplicialComplex V) (n : ℕ) :
    C(Realization P, Realization (subdivisionIter P n)) :=
  ⟨(iteratedHomeomorph P n).symm, (iteratedHomeomorph P n).symm.continuous⟩

/-- Every continuous map from an actual finite weak polyhedron has a genuine
simplicial approximation on a constructed finite subdivision and a jointly
continuous straight carrier homotopy. Every prescribed original vertex with
a literal target vertex value retains that value and stays fixed. -/
theorem exists_simplicialApproximation_onSubdivision
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W)
    [Finite (Face P)] (f : C(Realization P, Realization Q)) :
    ∃ n : ℕ, ∃ g : Morphism (subdivisionIter P n) Q,
      ∃ H : ContinuousMap.Homotopy (f.comp (subdivisionRealizationMap P n)) g.realization,
        (∀ x, (g.realization x).point.weights.support ⊆
          (f (iteratedHomeomorph P n x)).point.weights.support) ∧
        (∀ t x, (H (t, x)).point = Realization.segmentPoint t
          (f (iteratedHomeomorph P n x)).point (g.realization x).point) ∧
        (∀ v : Vertex P, ∀ w : Vertex Q,
          f (Realization.vertex P v.val v.property) =
              Realization.vertex Q w.val w.property →
            g.vertexMap (persistentVertex P n v) = w ∧ ∀ t : unitInterval,
              H (t, Realization.vertex (subdivisionIter P n)
                (persistentVertex P n v).val (persistentVertex P n v).property) =
                  f (Realization.vertex P v.val v.property)) := by
  let := Realization.finiteCoordinateMetricSpace P
  obtain ⟨ε, hε, hstars⟩ := Morphism.exists_starMap_mesh_bound f
  obtain ⟨N, hmesh⟩ := Realization.exists_iterated_mesh_bound P
  let q := (N : ℝ) / ((N : ℝ) + 1)
  let D := Metric.diam (Set.univ : Set (Realization P))
  have hq : q < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hsmall : ∃ n : ℕ, ∀ s : Face (subdivisionIter P n),
      Metric.diam ((iteratedHomeomorph P n) ''
        Set.range (Realization.faceMap (subdivisionIter P n) s)) ≤ ε := by
    by_cases hD : D = 0
    · refine ⟨0, fun s => (hmesh 0 s).trans ?_⟩
      change q ^ 0 * D ≤ ε
      rw [pow_zero, one_mul, hD]
      exact hε.le
    · have hDpos : 0 < D := lt_of_le_of_ne Metric.diam_nonneg (Ne.symm hD)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hDpos) hq
      exact ⟨n, fun s => (hmesh n s).trans
        (le_of_lt ((lt_div_iff₀ hDpos).mp hn))⟩
  obtain ⟨n, hn⟩ := hsmall
  let := finiteFaces_subdivisionIter P n
  let e := subdivisionRealizationMap P n
  obtain ⟨m, hm⟩ := hstars (subdivisionVertexType P n) (subdivisionIter P n) e hn
  let g := Morphism.ofStarMap (f.comp e) m hm
  let H := Morphism.starCarrierHomotopy (f.comp e) m hm
  refine ⟨n, g, H, ?_, ?_, ?_⟩
  · exact Morphism.ofStarMap_support_subset (f.comp e) m hm
  · intro t x
    exact Realization.carrierHomotopy_point (f.comp e) g.realization
      (Morphism.ofStarMap_support_subset (f.comp e) m hm) (t, x)
  · intro v w hv
    have hp : (f.comp e) (Realization.vertex (subdivisionIter P n)
        (persistentVertex P n v).val (persistentVertex P n v).property) =
          Realization.vertex Q w.val w.property := by
      change f (iteratedHomeomorph P n (Realization.vertex (subdivisionIter P n)
        (persistentVertex P n v).val (persistentVertex P n v).property)) = _
      rw [iteratedHomeomorph_persistentVertex]
      exact hv
    refine ⟨Morphism.ofStarMap_vertexMap_eq (f.comp e) m hm
      (persistentVertex P n v) w hp, ?_⟩
    intro t
    calc
      H (t, Realization.vertex (subdivisionIter P n)
          (persistentVertex P n v).val (persistentVertex P n v).property) =
          (f.comp e) (Realization.vertex (subdivisionIter P n)
            (persistentVertex P n v).val (persistentVertex P n v).property) :=
        Morphism.starCarrierHomotopy_fixed_vertex (f.comp e) m hm
          (persistentVertex P n v) w hp t
      _ = f (Realization.vertex P v.val v.property) :=
        congrArg f (iteratedHomeomorph_persistentVertex P n v)

/-- Simplicial approximation on a constructed finite subdivision, with the
actual jointly continuous carrier homotopy on the original domain. The inverse
comparison is constructed, and all prescribed original vertex values are fixed. -/
theorem exists_simplicialApproximation
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W)
    [Finite (Face P)] (f : C(Realization P, Realization Q)) :
    ∃ n : ℕ, ∃ g : Morphism (subdivisionIter P n) Q,
      ∃ H : ContinuousMap.Homotopy f
        (g.realization.comp (subdivisionRealizationInverse P n)),
        (∀ x, (g.realization (subdivisionRealizationInverse P n x)).point.weights.support ⊆
          (f x).point.weights.support) ∧
        (∀ t x, (H (t, x)).point = Realization.segmentPoint t (f x).point
          (g.realization (subdivisionRealizationInverse P n x)).point) ∧
        (∀ v : Vertex P, ∀ w : Vertex Q,
          f (Realization.vertex P v.val v.property) =
              Realization.vertex Q w.val w.property →
            g.vertexMap (persistentVertex P n v) = w ∧ ∀ t : unitInterval,
              H (t, Realization.vertex P v.val v.property) =
                f (Realization.vertex P v.val v.property)) := by
  obtain ⟨n, g, Hs, hsupport, hpoint, hfixed⟩ :=
    exists_simplicialApproximation_onSubdivision P Q f
  let inv := subdivisionRealizationInverse P n
  have hzero : (f.comp (subdivisionRealizationMap P n)).comp inv = f := by
    apply ContinuousMap.ext
    intro x
    exact congrArg f ((iteratedHomeomorph P n).apply_symm_apply x)
  let H := (Hs.compContinuousMap inv).cast hzero rfl
  refine ⟨n, g, H, ?_, ?_, ?_⟩
  · intro x
    have h := hsupport (inv x)
    have hi : iteratedHomeomorph P n (inv x) = x :=
      (iteratedHomeomorph P n).apply_symm_apply x
    rw [hi] at h
    exact h
  · intro t x
    change (Hs (t, inv x)).point = _
    rw [hpoint]
    have hi : iteratedHomeomorph P n (inv x) = x :=
      (iteratedHomeomorph P n).apply_symm_apply x
    rw [hi]
  · intro v w hv
    refine ⟨(hfixed v w hv).1, ?_⟩
    intro t
    change Hs (t, inv (Realization.vertex P v.val v.property)) = _
    have hi : inv (Realization.vertex P v.val v.property) =
        Realization.vertex (subdivisionIter P n)
          (persistentVertex P n v).val (persistentVertex P n v).property :=
      iteratedHomeomorph_symm_vertex P n v
    rw [hi]
    exact (hfixed v w hv).2 t

end PreAbstractSimplicialComplex

end
