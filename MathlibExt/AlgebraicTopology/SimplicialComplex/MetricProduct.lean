/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.BoxProduct
public import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricRealization
public import MathlibExt.AlgebraicTopology.SimplicialComplex.FiniteRelativeApproximation
public import Mathlib.Topology.Homotopy.Product
import Mathlib.Tactic.Ring

/-!
# Genuine metric product equivalence through the box complex

The inclusion has the original product barycentric coordinates. The
projection uses the existing supported return to the weak box followed by
its two actual affine projections. Coordinate continuity proves that the
inclusion is continuous in the metric topology; no continuity into the
ordinary weak product is assumed. Both inverse homotopies are actual
barycentric segments in derived common faces. Every belonging vertex is
fixed by both corresponding singleton-relative inverse families.
-/

noncomputable section

open scoped Classical

open CategoryTheory Topology
open scoped unitInterval NNReal

universe u v z

namespace PreAbstractSimplicialComplex
namespace MetricProductConstruction

variable {V : Type u} {W : Type v}

private def pointData {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    (x : MetricRealization P) : P.Realization := Classical.choose x.property

private theorem pointData_weights {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    (x : MetricRealization P) : (pointData P x).point.weights = x.val.ofLp :=
  congrArg WithLp.ofLp (Classical.choose_spec x.property)

private theorem coordinate_continuous {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    (i : VertexType) :
    Continuous (fun x : MetricRealization P => x.val.ofLp i) :=
  (MetricRealization.continuous_iff_coordinates P (fun x => x)).mp continuous_id i

private theorem finsetUnion_eq_of_decidableEq {VertexType : Type*}
    (e₁ e₂ : DecidableEq VertexType) (s t : Finset VertexType) :
    @Union.union (Finset VertexType) (@Finset.instUnion VertexType e₁) s t =
      @Union.union (Finset VertexType) (@Finset.instUnion VertexType e₂) s t :=
  congrArg (fun e : DecidableEq VertexType =>
    @Union.union (Finset VertexType) (@Finset.instUnion VertexType e) s t)
      (Subsingleton.elim e₁ e₂)

private def metricSegmentValue {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    {D : Type z} [TopologicalSpace D] (f g : C(D, MetricRealization P))
    (h : ∀ d, (f d).val.ofLp.support ∪ (g d).val.ofLp.support ∈ P)
    (t : unitInterval) (d : D) : MetricRealization P :=
  Realization.toMetric P
    ⟨Realization.segmentPoint t (pointData P (f d)).point (pointData P (g d)).point,
      (P.isRelLowerSet_faces (h d)).2
        (by
          have hs := Realization.segmentPoint_support_subset t
            (pointData P (f d)).point (pointData P (g d)).point
          rw [pointData_weights, pointData_weights] at hs
          exact hs)
        (Realization.segmentPoint t (pointData P (f d)).point
          (pointData P (g d)).point).support_weights_nonempty⟩

private theorem metricSegmentValue_weight {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    {D : Type z} [TopologicalSpace D] (f g : C(D, MetricRealization P))
    (h : ∀ d, (f d).val.ofLp.support ∪ (g d).val.ofLp.support ∈ P)
    (t : unitInterval) (d : D) (i : VertexType) :
    (metricSegmentValue P f g h t d).val.ofLp i =
      (1 - (t : ℝ)) * (f d).val.ofLp i + (t : ℝ) * (g d).val.ofLp i := by
  change (Realization.toMetric P _).val.ofLp i = _
  rw [Realization.toMetric_weights]
  change (Realization.segmentPoint t (pointData P (f d)).point
    (pointData P (g d)).point).weights i = _
  rw [Realization.segmentPoint_weights]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, pointData_weights]

private theorem metricSegmentValue_continuous {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    {D : Type z} [TopologicalSpace D] (f g : C(D, MetricRealization P))
    (h : ∀ d, (f d).val.ofLp.support ∪ (g d).val.ofLp.support ∈ P) :
    Continuous (fun x : unitInterval × D => metricSegmentValue P f g h x.1 x.2) := by
  apply (MetricRealization.continuous_iff_coordinates P _).mpr
  intro i
  simp_rw [metricSegmentValue_weight]
  have hf : Continuous (fun x : unitInterval × D => (f x.2).val.ofLp i) :=
    (coordinate_continuous P i).comp (f.continuous.comp continuous_snd)
  have hg : Continuous (fun x : unitInterval × D => (g x.2).val.ofLp i) :=
    (coordinate_continuous P i).comp (g.continuous.comp continuous_snd)
  have ht : Continuous (fun x : unitInterval × D => (x.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hOne : Continuous (fun _ : unitInterval × D => (1 : ℝ)) := continuous_const
  exact ((hOne.sub ht).mul hf).add (ht.mul hg)

private theorem metricSegmentValue_zero {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    {D : Type z} [TopologicalSpace D] (f g : C(D, MetricRealization P))
    (h : ∀ d, (f d).val.ofLp.support ∪ (g d).val.ofLp.support ∈ P) (d : D) :
    metricSegmentValue P f g h 0 d = f d := by
  apply Subtype.ext
  apply WithLp.ofLp_injective (1 : ℝ≥0)
  ext i
  rw [metricSegmentValue_weight]
  simp

private theorem metricSegmentValue_one {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    {D : Type z} [TopologicalSpace D] (f g : C(D, MetricRealization P))
    (h : ∀ d, (f d).val.ofLp.support ∪ (g d).val.ofLp.support ∈ P) (d : D) :
    metricSegmentValue P f g h 1 d = g d := by
  apply Subtype.ext
  apply WithLp.ofLp_injective (1 : ℝ≥0)
  ext i
  rw [metricSegmentValue_weight]
  simp

private def metricFaceHomotopy {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    {D : Type z} [TopologicalSpace D] (f g : C(D, MetricRealization P))
    (h : ∀ d, (f d).val.ofLp.support ∪ (g d).val.ofLp.support ∈ P) :
    ContinuousMap.Homotopy f g where
  toFun x := metricSegmentValue P f g h x.1 x.2
  continuous_toFun := metricSegmentValue_continuous P f g h
  map_zero_left d := metricSegmentValue_zero P f g h d
  map_one_left d := metricSegmentValue_one P f g h d

private theorem metricFaceHomotopy_fixed {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    {D : Type z} [TopologicalSpace D] (f g : C(D, MetricRealization P))
    (h : ∀ d, (f d).val.ofLp.support ∪ (g d).val.ofLp.support ∈ P)
    (d : D) (hd : f d = g d) (t : unitInterval) :
    metricFaceHomotopy P f g h (t, d) = f d := by
  apply Subtype.ext
  apply WithLp.ofLp_injective (1 : ℝ≥0)
  ext i
  change (metricSegmentValue P f g h t d).val.ofLp i = (f d).val.ofLp i
  rw [metricSegmentValue_weight, ← hd]
  ring

private def metricFaceHomotopyRel {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    {D : Type z} [TopologicalSpace D] (f g : C(D, MetricRealization P))
    (h : ∀ d, (f d).val.ofLp.support ∪ (g d).val.ofLp.support ∈ P)
    (S : Set D) (hS : ∀ d ∈ S, f d = g d) : ContinuousMap.HomotopyRel f g S where
  toHomotopy := metricFaceHomotopy P f g h
  prop' t d hd := metricFaceHomotopy_fixed P f g h d (hS d hd) t

private def firstMetric (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) :
    C(MetricRealization (boxProduct P Q), MetricRealization P) :=
  (Realization.toMetric P).comp
    ((boxFirst P Q).comp (MetricRealization.toWeak (boxProduct P Q)))

private def secondMetric (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) :
    C(MetricRealization (boxProduct P Q), MetricRealization Q) :=
  (Realization.toMetric Q).comp
    ((boxSecond P Q).comp (MetricRealization.toWeak (boxProduct P Q)))

private def projectionMetric (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) :
    C(MetricRealization (boxProduct P Q), MetricRealization P × MetricRealization Q) :=
  (firstMetric P Q).prodMk (secondMetric P Q)

private def pairValue (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : MetricRealization P × MetricRealization Q) :
    MetricRealization (boxProduct P Q) :=
  Realization.toMetric (boxProduct P Q)
    (boxProductPoint P Q (pointData P x.1) (pointData Q x.2))

private theorem pairValue_weight (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : MetricRealization P × MetricRealization Q)
    (v : V) (w : W) :
    (pairValue P Q x).val.ofLp (v, w) = x.1.val.ofLp v * x.2.val.ofLp w := by
  change (Realization.toMetric (boxProduct P Q)
    (boxProductPoint P Q (pointData P x.1) (pointData Q x.2))).val.ofLp (v, w) = _
  rw [Realization.toMetric_weights, boxProductPoint_weight,
    pointData_weights, pointData_weights]

private theorem pairValue_continuous (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : Continuous (pairValue P Q) := by
  apply (MetricRealization.continuous_iff_coordinates (boxProduct P Q) _).mpr
  rintro ⟨v, w⟩
  simp_rw [pairValue_weight]
  exact ((coordinate_continuous P v).comp continuous_fst).mul
    ((coordinate_continuous Q w).comp continuous_snd)

private def inclusionMetric (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) :
    C(MetricRealization P × MetricRealization Q, MetricRealization (boxProduct P Q)) :=
  ⟨pairValue P Q, pairValue_continuous P Q⟩

private theorem firstMetric_support (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : MetricRealization (boxProduct P Q)) :
    (firstMetric P Q x).val.ofLp.support ⊆ x.val.ofLp.support.image Prod.fst := by
  classical
  change (Realization.toMetric P
    (boxFirst P Q (MetricRealization.toWeak (boxProduct P Q) x))).val.ofLp.support ⊆ _
  rw [Realization.toMetric_weights]
  exact (boxFirst_support P Q _).trans
    (Finset.image_subset_image (MetricRealization.toWeak_support (boxProduct P Q) x))

private theorem secondMetric_support (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : MetricRealization (boxProduct P Q)) :
    (secondMetric P Q x).val.ofLp.support ⊆ x.val.ofLp.support.image Prod.snd := by
  classical
  change (Realization.toMetric Q
    (boxSecond P Q (MetricRealization.toWeak (boxProduct P Q) x))).val.ofLp.support ⊆ _
  rw [Realization.toMetric_weights]
  exact (boxSecond_support P Q _).trans
    (Finset.image_subset_image (MetricRealization.toWeak_support (boxProduct P Q) x))

private theorem inclusionMetric_first_support (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : MetricRealization P × MetricRealization Q) :
    (inclusionMetric P Q x).val.ofLp.support.image Prod.fst ⊆ x.1.val.ofLp.support := by
  classical
  change (Realization.toMetric (boxProduct P Q)
    (boxProductPoint P Q (pointData P x.1) (pointData Q x.2))).val.ofLp.support.image
      Prod.fst ⊆ _
  rw [Realization.toMetric_weights]
  simpa only [pointData_weights] using
    boxProductPoint_first_support P Q (pointData P x.1) (pointData Q x.2)

private theorem inclusionMetric_second_support (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : MetricRealization P × MetricRealization Q) :
    (inclusionMetric P Q x).val.ofLp.support.image Prod.snd ⊆ x.2.val.ofLp.support := by
  classical
  change (Realization.toMetric (boxProduct P Q)
    (boxProductPoint P Q (pointData P x.1) (pointData Q x.2))).val.ofLp.support.image
      Prod.snd ⊆ _
  rw [Realization.toMetric_weights]
  simpa only [pointData_weights] using
    boxProductPoint_second_support P Q (pointData P x.1) (pointData Q x.2)

private theorem first_inverse_face (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : MetricRealization P × MetricRealization Q) :
    x.1.val.ofLp.support ∪ (firstMetric P Q (inclusionMetric P Q x)).val.ofLp.support ∈ P := by
  classical
  have h := (firstMetric_support P Q _).trans (inclusionMetric_first_support P Q x)
  rw [Finset.union_eq_left.mpr h]
  exact (pointData_weights P x.1) ▸ (pointData P x.1).support_mem

private theorem second_inverse_face (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : MetricRealization P × MetricRealization Q) :
    x.2.val.ofLp.support ∪ (secondMetric P Q (inclusionMetric P Q x)).val.ofLp.support ∈ Q := by
  classical
  have h := (secondMetric_support P Q _).trans (inclusionMetric_second_support P Q x)
  rw [Finset.union_eq_left.mpr h]
  exact (pointData_weights Q x.2) ▸ (pointData Q x.2).support_mem

private theorem box_inverse_face (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : MetricRealization (boxProduct P Q)) :
    x.val.ofLp.support ∪
      (inclusionMetric P Q (projectionMetric P Q x)).val.ofLp.support ∈ boxProduct P Q := by
  classical
  let S := x.val.ofLp.support
  let T := (inclusionMetric P Q (projectionMetric P Q x)).val.ofLp.support
  have hfst : T.image Prod.fst ⊆ S.image Prod.fst :=
    (inclusionMetric_first_support P Q _).trans (firstMetric_support P Q x)
  have hsnd : T.image Prod.snd ⊆ S.image Prod.snd :=
    (inclusionMetric_second_support P Q _).trans (secondMetric_support P Q x)
  have hSupport : (pointData (boxProduct P Q) x).point.weights.support = S :=
    congrArg (fun a : (V × W) →₀ ℝ => a.support)
      (pointData_weights (boxProduct P Q) x)
  have hS : S ∈ boxProduct P Q :=
    Eq.mp (congrArg (fun s : Finset (V × W) => s ∈ boxProduct P Q) hSupport)
      (pointData (boxProduct P Q) x).support_mem
  have hS₀ : S.Nonempty := by
    simpa only [pointData_weights] using
      (pointData (boxProduct P Q) x).point.support_weights_nonempty
  have hne : (S ∪ T).Nonempty := hS₀.mono Finset.subset_union_left
  apply (boxProduct_mem P Q _).mpr
  constructor
  · apply (P.isRelLowerSet_faces ((boxProduct_mem P Q S).mp hS).1).2
      (by simpa only [Finset.image_union] using
        (Finset.union_subset_iff.mpr ⟨Finset.Subset.refl _, hfst⟩)) (hne.image Prod.fst)
  · apply (Q.isRelLowerSet_faces ((boxProduct_mem P Q S).mp hS).2).2
      (by simpa only [Finset.image_union] using
        (Finset.union_subset_iff.mpr ⟨Finset.Subset.refl _, hsnd⟩)) (hne.image Prod.snd)

private def leftForwardHomotopy (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : ContinuousMap.Homotopy
      (ContinuousMap.id (MetricRealization (boxProduct P Q)))
      ((inclusionMetric P Q).comp (projectionMetric P Q)) :=
  metricFaceHomotopy (boxProduct P Q) _ _ (by
    intro d
    refine Eq.mpr (congrArg (fun s : Finset (V × W) => s ∈ boxProduct P Q) ?_)
      (box_inverse_face P Q d)
    exact finsetUnion_eq_of_decidableEq
      (fun a b : V × W => Classical.propDecidable (a = b))
      (inferInstance : DecidableEq (V × W))
      d.val.ofLp.support
      (inclusionMetric P Q (projectionMetric P Q d)).val.ofLp.support)

private def firstRightForwardHomotopy (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : ContinuousMap.Homotopy
      (ContinuousMap.fst : C(MetricRealization P × MetricRealization Q, MetricRealization P))
      ((firstMetric P Q).comp (inclusionMetric P Q)) :=
  metricFaceHomotopy P _ _ (first_inverse_face P Q)

private def secondRightForwardHomotopy (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : ContinuousMap.Homotopy
      (ContinuousMap.snd : C(MetricRealization P × MetricRealization Q, MetricRealization Q))
      ((secondMetric P Q).comp (inclusionMetric P Q)) :=
  metricFaceHomotopy Q _ _ (second_inverse_face P Q)

private theorem pair_projections_id (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) :
    ((ContinuousMap.fst : C(MetricRealization P × MetricRealization Q, MetricRealization P)).prodMk
      ContinuousMap.snd) = ContinuousMap.id (MetricRealization P × MetricRealization Q) := by
  apply ContinuousMap.ext
  intro x
  exact Prod.ext rfl rfl

private theorem pair_compositions (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) :
    (((firstMetric P Q).comp (inclusionMetric P Q)).prodMk
      ((secondMetric P Q).comp (inclusionMetric P Q))) =
      (projectionMetric P Q).comp (inclusionMetric P Q) := by
  apply ContinuousMap.ext
  intro x
  exact Prod.ext rfl rfl

private def rightInverseHomotopy (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : ContinuousMap.Homotopy
      ((projectionMetric P Q).comp (inclusionMetric P Q))
      (ContinuousMap.id (MetricRealization P × MetricRealization Q)) :=
  ((firstRightForwardHomotopy P Q).prod (secondRightForwardHomotopy P Q)).symm.cast
    (pair_compositions P Q) (pair_projections_id P Q)

private def metricEquiv (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : ContinuousMap.HomotopyEquiv
      (MetricRealization (boxProduct P Q)) (MetricRealization P × MetricRealization Q) where
  toFun := projectionMetric P Q
  invFun := inclusionMetric P Q
  left_inv := ⟨(leftForwardHomotopy P Q).symm⟩
  right_inv := ⟨rightInverseHomotopy P Q⟩

private theorem metricEquiv_toFun (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : (metricEquiv P Q).toFun = projectionMetric P Q := rfl

private theorem metricEquiv_invFun (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : (metricEquiv P Q).invFun = inclusionMetric P Q := rfl

private def metricVertex {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    (i : VertexType) (hi : {i} ∈ P) :
    MetricRealization P := Realization.toMetric P (Realization.vertex P i hi)

private theorem projection_vertex (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    projectionMetric P Q (metricVertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb)) =
      (metricVertex P a ha, metricVertex Q b hb) := by
  apply Prod.ext
  · change Realization.toMetric P (boxFirst P Q
      (MetricRealization.toWeak (boxProduct P Q)
        (Realization.toMetric (boxProduct P Q) (Realization.vertex (boxProduct P Q) (a, b)
          (boxProduct_vertex P Q a ha b hb))))) = metricVertex P a ha
    rw [MetricRealization.toWeak_vertex, boxFirst_vertex P Q a ha b hb]
    rfl
  · change Realization.toMetric Q (boxSecond P Q
      (MetricRealization.toWeak (boxProduct P Q)
        (Realization.toMetric (boxProduct P Q) (Realization.vertex (boxProduct P Q) (a, b)
          (boxProduct_vertex P Q a ha b hb))))) = metricVertex Q b hb
    rw [MetricRealization.toWeak_vertex, boxSecond_vertex P Q a ha b hb]
    rfl

private theorem pointData_metricVertex {VertexType : Type*} (P : PreAbstractSimplicialComplex VertexType)
    (i : VertexType) (hi : {i} ∈ P) : pointData P (metricVertex P i hi) = Realization.vertex P i hi := by
  apply Realization.ext
  apply Convexity.StdSimplex.ext
  exact (pointData_weights P (metricVertex P i hi)).trans
    (Realization.toMetric_weights P (Realization.vertex P i hi))

private theorem inclusion_vertex (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    inclusionMetric P Q (metricVertex P a ha, metricVertex Q b hb) =
      metricVertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb) := by
  change Realization.toMetric (boxProduct P Q)
    (boxProductPoint P Q (pointData P (metricVertex P a ha))
      (pointData Q (metricVertex Q b hb))) = _
  rw [pointData_metricVertex, pointData_metricVertex, boxProductPoint_vertex]
  rfl

private def leftInverseRelative (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    ContinuousMap.HomotopyRel ((inclusionMetric P Q).comp (projectionMetric P Q))
      (ContinuousMap.id (MetricRealization (boxProduct P Q)))
      {metricVertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb)} := by
  let x := metricVertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb)
  have hx : (inclusionMetric P Q).comp (projectionMetric P Q) x = x := by
    exact (congrArg (inclusionMetric P Q) (projection_vertex P Q a ha b hb)).trans
      (inclusion_vertex P Q a ha b hb)
  exact (metricFaceHomotopyRel (boxProduct P Q)
    (ContinuousMap.id _) ((inclusionMetric P Q).comp (projectionMetric P Q))
      (by
        intro d
        refine Eq.mpr (congrArg (fun s : Finset (V × W) => s ∈ boxProduct P Q) ?_)
          (box_inverse_face P Q d)
        exact finsetUnion_eq_of_decidableEq
          (fun a b : V × W => Classical.propDecidable (a = b))
          (inferInstance : DecidableEq (V × W))
          d.val.ofLp.support
          (inclusionMetric P Q (projectionMetric P Q d)).val.ofLp.support) {x} (by
        intro d hd
        obtain rfl := Set.mem_singleton_iff.mp hd
        exact hx.symm)).symm

private def rightInverseRelative (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    ContinuousMap.HomotopyRel ((projectionMetric P Q).comp (inclusionMetric P Q))
      (ContinuousMap.id (MetricRealization P × MetricRealization Q))
      {(metricVertex P a ha, metricVertex Q b hb)} := by
  let x := (metricVertex P a ha, metricVertex Q b hb)
  have hx : (projectionMetric P Q).comp (inclusionMetric P Q) x = x := by
    exact (congrArg (projectionMetric P Q) (inclusion_vertex P Q a ha b hb)).trans
      (projection_vertex P Q a ha b hb)
  let H₁ := metricFaceHomotopyRel P
    (ContinuousMap.fst : C(MetricRealization P × MetricRealization Q, MetricRealization P))
    ((firstMetric P Q).comp (inclusionMetric P Q)) (first_inverse_face P Q) {x} (by
      intro d hd
      obtain rfl := Set.mem_singleton_iff.mp hd
      exact (congrArg Prod.fst hx).symm)
  let H₂ := metricFaceHomotopyRel Q
    (ContinuousMap.snd : C(MetricRealization P × MetricRealization Q, MetricRealization Q))
    ((secondMetric P Q).comp (inclusionMetric P Q)) (second_inverse_face P Q) {x} (by
      intro d hd
      obtain rfl := Set.mem_singleton_iff.mp hd
      exact (congrArg Prod.snd hx).symm)
  exact (H₁.prod H₂).symm.cast (pair_compositions P Q) (pair_projections_id P Q)

end MetricProductConstruction

/-- The actual continuous projection through the supported weak return. -/
public def metricProductProjection {V : Type u} {W : Type v}
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W) :
    C(MetricRealization (boxProduct P Q), MetricRealization P × MetricRealization Q) :=
  MetricProductConstruction.projectionMetric P Q

/-- The actual continuous inclusion with product barycentric coordinates. -/
public def metricProductInclusion {V : Type u} {W : Type v}
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W) :
    C(MetricRealization P × MetricRealization Q, MetricRealization (boxProduct P Q)) :=
  MetricProductConstruction.inclusionMetric P Q

/-- A genuine product homotopy equivalence, with both inverse families derived. -/
public def metricProductHomotopyEquiv {V : Type u} {W : Type v}
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W) :
    ContinuousMap.HomotopyEquiv (MetricRealization (boxProduct P Q))
      (MetricRealization P × MetricRealization Q) := MetricProductConstruction.metricEquiv P Q

/-- The forward field is the same constructed continuous projection. -/
public theorem metricProductHomotopyEquiv_toFun {V : Type u} {W : Type v}
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W) :
    (metricProductHomotopyEquiv P Q).toFun = metricProductProjection P Q := by
  unfold metricProductHomotopyEquiv metricProductProjection
  exact MetricProductConstruction.metricEquiv_toFun P Q

/-- The inverse field is the actual product-coordinate inclusion. -/
public theorem metricProductHomotopyEquiv_invFun {V : Type u} {W : Type v}
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W) :
    (metricProductHomotopyEquiv P Q).invFun = metricProductInclusion P Q := by
  unfold metricProductHomotopyEquiv metricProductInclusion
  exact MetricProductConstruction.metricEquiv_invFun P Q

/-- Every belonging product vertex is preserved by the forward map. -/
public theorem metricProductProjection_vertex {V : Type u} {W : Type v}
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W)
    (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    metricProductProjection P Q
      (Realization.toMetric (boxProduct P Q)
        (Realization.vertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb))) =
      (Realization.toMetric P (Realization.vertex P a ha),
        Realization.toMetric Q (Realization.vertex Q b hb)) := by
  unfold metricProductProjection
  exact MetricProductConstruction.projection_vertex P Q a ha b hb

/-- Every belonging product vertex is preserved by the inverse map. -/
public theorem metricProductInclusion_vertex {V : Type u} {W : Type v}
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W)
    (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    metricProductInclusion P Q
      (Realization.toMetric P (Realization.vertex P a ha),
        Realization.toMetric Q (Realization.vertex Q b hb)) =
      Realization.toMetric (boxProduct P Q)
        (Realization.vertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb)) := by
  unfold metricProductInclusion
  exact MetricProductConstruction.inclusion_vertex P Q a ha b hb

/-- The original box-side inverse family fixes the literal product vertex. -/
public def metricProductLeftHomotopy {V : Type u} {W : Type v}
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W)
    (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    ContinuousMap.HomotopyRel
      ((metricProductInclusion P Q).comp (metricProductProjection P Q))
      (ContinuousMap.id (MetricRealization (boxProduct P Q)))
      {Realization.toMetric (boxProduct P Q)
        (Realization.vertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb))} := by
  unfold metricProductInclusion metricProductProjection
  exact MetricProductConstruction.leftInverseRelative P Q a ha b hb

/-- The original product-side inverse family fixes the literal pair of vertices. -/
public def metricProductRightHomotopy {V : Type u} {W : Type v}
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W)
    (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    ContinuousMap.HomotopyRel
      ((metricProductProjection P Q).comp (metricProductInclusion P Q))
      (ContinuousMap.id (MetricRealization P × MetricRealization Q))
      {(Realization.toMetric P (Realization.vertex P a ha),
        Realization.toMetric Q (Realization.vertex Q b hb))} := by
  unfold metricProductInclusion metricProductProjection
  exact MetricProductConstruction.rightInverseRelative P Q a ha b hb

end PreAbstractSimplicialComplex

end
