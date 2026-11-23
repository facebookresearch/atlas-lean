/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.Morphism
public import MathlibExt.Analysis.Convex.StdSimplex
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# A finite-face box complex for actual product models

A face belongs to the box complex when each of its two projections is a
face of the original complex. The two projection morphisms reuse the
existing arbitrary-vertex realization functor. Product barycentric weights
supply a point in the box, without any choice of a comparison or CW model.
-/

noncomputable section

open scoped Classical

open CategoryTheory Topology
open scoped BigOperators

universe u v

namespace PreAbstractSimplicialComplex

variable {V : Type u} {W : Type v}

open Classical in
/-- The finite-face box complex, retaining arbitrary and unused vertex labels. -/
public def boxProduct (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : PreAbstractSimplicialComplex (V × W) where
  faces := {s | s.image Prod.fst ∈ P ∧ s.image Prod.snd ∈ Q}
  isRelLowerSet_faces := by
    intro s hs
    constructor
    · obtain ⟨a, ha⟩ := (P.isRelLowerSet_faces hs.1).1
      obtain ⟨p, hp, _⟩ := Finset.mem_image.mp ha
      exact ⟨p, hp⟩
    · intro t hts ht
      exact ⟨(P.isRelLowerSet_faces hs.1).2 (Finset.image_subset_image hts)
          (ht.image Prod.fst),
        (Q.isRelLowerSet_faces hs.2).2 (Finset.image_subset_image hts)
          (ht.image Prod.snd)⟩

/-- The exact face criterion for the computed box. -/
public theorem boxProduct_mem (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (s : Finset (V × W)) :
    s ∈ boxProduct P Q ↔ s.image Prod.fst ∈ P ∧ s.image Prod.snd ∈ Q := by
  unfold boxProduct
  rfl

/-- Every pair of belonging vertices is a literal belonging box vertex. -/
public theorem boxProduct_vertex (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    {(a, b)} ∈ boxProduct P Q := by
  classical
  exact (boxProduct_mem P Q _).mpr ⟨by simpa using ha, by simpa using hb⟩

private def firstMorphism (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : Morphism (boxProduct P Q) P where
  vertexMap x := ⟨x.val.1, by
    have h := (boxProduct_mem P Q _).mp x.property
    simpa using h.1⟩
  face_mem s := by
    classical
    have h : (s.val.image Prod.fst) ∈ P := ((boxProduct_mem P Q _).mp s.property).1
    have he : (faceVertices (boxProduct P Q) s).image
        (fun x => ((⟨x.val.1, by
          have hx := (boxProduct_mem P Q _).mp x.property
          simpa using hx.1⟩ : Vertex P)).val) = s.val.image Prod.fst := by
      apply Finset.ext
      intro v
      constructor
      · intro hv
        obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image.mpr ⟨z.val, Finset.mem_subtype.mp hz, hzv⟩
      · intro hv
        obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hv
        let z : Vertex (boxProduct P Q) :=
          ⟨p, singleton_mem_of_face (boxProduct P Q) s hp⟩
        exact Finset.mem_image.mpr ⟨z, Finset.mem_subtype.mpr hp, hpv⟩
    exact he.symm ▸ h

private def secondMorphism (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : Morphism (boxProduct P Q) Q where
  vertexMap x := ⟨x.val.2, by
    have h := (boxProduct_mem P Q _).mp x.property
    simpa using h.2⟩
  face_mem s := by
    classical
    have h : (s.val.image Prod.snd) ∈ Q := ((boxProduct_mem P Q _).mp s.property).2
    have he : (faceVertices (boxProduct P Q) s).image
        (fun x => ((⟨x.val.2, by
          have hx := (boxProduct_mem P Q _).mp x.property
          simpa using hx.2⟩ : Vertex Q)).val) = s.val.image Prod.snd := by
      apply Finset.ext
      intro w
      constructor
      · intro hw
        obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hw
        exact Finset.mem_image.mpr ⟨z.val, Finset.mem_subtype.mp hz, hzw⟩
      · intro hw
        obtain ⟨p, hp, hpw⟩ := Finset.mem_image.mp hw
        let z : Vertex (boxProduct P Q) :=
          ⟨p, singleton_mem_of_face (boxProduct P Q) s hp⟩
        exact Finset.mem_image.mpr ⟨z, Finset.mem_subtype.mpr hp, hpw⟩
    exact he.symm ▸ h

/-- The actual first affine projection of the weak box realization. -/
public def boxFirst (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : C((boxProduct P Q).Realization, P.Realization) :=
  (firstMorphism P Q).realization

/-- The actual second affine projection of the weak box realization. -/
public def boxSecond (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) : C((boxProduct P Q).Realization, Q.Realization) :=
  (secondMorphism P Q).realization

/-- The first projection retains the original marginal of the distribution. -/
public theorem boxFirst_point (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : (boxProduct P Q).Realization) :
    (boxFirst P Q x).point = x.point.map Prod.fst := by
  unfold boxFirst
  have h := (firstMorphism P Q).realizationMap_point x
  change ((firstMorphism P Q).realization x).point =
    (Realization.vertexCoordinates x).map (fun a => a.val.1) at h
  exact h.trans
    ((Convexity.StdSimplex.map_map (Realization.vertexCoordinates x)
      (Subtype.val : Vertex (boxProduct P Q) → V × W) Prod.fst).symm.trans
        (congrArg (fun p => p.map Prod.fst) (Realization.map_vertexCoordinates x)))

/-- The second projection retains the original marginal of the distribution. -/
public theorem boxSecond_point (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : (boxProduct P Q).Realization) :
    (boxSecond P Q x).point = x.point.map Prod.snd := by
  unfold boxSecond
  have h := (secondMorphism P Q).realizationMap_point x
  change ((secondMorphism P Q).realization x).point =
    (Realization.vertexCoordinates x).map (fun a => a.val.2) at h
  exact h.trans
    ((Convexity.StdSimplex.map_map (Realization.vertexCoordinates x)
      (Subtype.val : Vertex (boxProduct P Q) → V × W) Prod.snd).symm.trans
        (congrArg (fun p => p.map Prod.snd) (Realization.map_vertexCoordinates x)))

/-- The first projected support is contained in the original first face. -/
public theorem boxFirst_support (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : (boxProduct P Q).Realization) :
    (boxFirst P Q x).point.weights.support ⊆ x.point.weights.support.image Prod.fst := by
  classical
  rw [boxFirst_point, Convexity.StdSimplex.weights_map]
  exact Finsupp.mapDomain_support

/-- The second projected support is contained in the original second face. -/
public theorem boxSecond_support (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (x : (boxProduct P Q).Realization) :
    (boxSecond P Q x).point.weights.support ⊆ x.point.weights.support.image Prod.snd := by
  classical
  rw [boxSecond_point, Convexity.StdSimplex.weights_map]
  exact Finsupp.mapDomain_support

namespace BoxProductConstruction

private theorem first_support_productSimplex (a : Convexity.StdSimplex ℝ V)
    (b : Convexity.StdSimplex ℝ W) :
    (Convexity.StdSimplex.prod a b).weights.support.image Prod.fst ⊆ a.weights.support := by
  classical
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  have hprod : (Convexity.StdSimplex.prod a b).weights p =
      a.weights p.1 * b.weights p.2 :=
    Convexity.StdSimplex.prod_apply a b p.1 p.2
  exact Finsupp.mem_support_iff.mpr (fun ha =>
    (Finsupp.mem_support_iff.mp hp) (hprod.trans (by rw [ha, zero_mul])))

private theorem second_support_productSimplex (a : Convexity.StdSimplex ℝ V)
    (b : Convexity.StdSimplex ℝ W) :
    (Convexity.StdSimplex.prod a b).weights.support.image Prod.snd ⊆ b.weights.support := by
  classical
  intro w hw
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
  have hprod : (Convexity.StdSimplex.prod a b).weights p =
      a.weights p.1 * b.weights p.2 :=
    Convexity.StdSimplex.prod_apply a b p.1 p.2
  exact Finsupp.mem_support_iff.mpr (fun hb =>
    (Finsupp.mem_support_iff.mp hp) (hprod.trans (by rw [hb, mul_zero])))

private def productPoint (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : P.Realization) (b : Q.Realization) :
    (boxProduct P Q).Realization where
  point := Convexity.StdSimplex.prod a.point b.point
  support_mem := by
    classical
    apply (boxProduct_mem P Q _).mpr
    exact ⟨(P.isRelLowerSet_faces a.support_mem).2
        (first_support_productSimplex a.point b.point)
        ((Convexity.StdSimplex.prod a.point b.point).support_weights_nonempty.image Prod.fst),
      (Q.isRelLowerSet_faces b.support_mem).2
        (second_support_productSimplex a.point b.point)
        ((Convexity.StdSimplex.prod a.point b.point).support_weights_nonempty.image Prod.snd)⟩

private theorem productPoint_vertex (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    productPoint P Q (Realization.vertex P a ha) (Realization.vertex Q b hb) =
      Realization.vertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb) := by
  classical
  apply Realization.ext
  apply Convexity.StdSimplex.ext
  ext p
  rcases p with ⟨v, w⟩
  change (Convexity.StdSimplex.prod (Convexity.StdSimplex.single a)
    (Convexity.StdSimplex.single b)).weights (v, w) = Finsupp.single (a, b) 1 (v, w)
  rw [Convexity.StdSimplex.prod_apply]
  by_cases hv : a = v <;> by_cases hw : b = w <;>
    simp [Convexity.StdSimplex.weights_single, hv, hw, Prod.mk.injEq]

end BoxProductConstruction

/-- The actual product distribution, valued in the computed weak box point set.
No continuity from the ordinary weak product is asserted here. -/
public def boxProductPoint (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : P.Realization) (b : Q.Realization) :
    (boxProduct P Q).Realization := BoxProductConstruction.productPoint P Q a b

/-- Every product coordinate is the product of the two original coordinates. -/
public theorem boxProductPoint_weight (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : P.Realization) (b : Q.Realization) (p : V × W) :
    (boxProductPoint P Q a b).point.weights p = a.point.weights p.1 * b.point.weights p.2 := by
  unfold boxProductPoint BoxProductConstruction.productPoint
  exact Convexity.StdSimplex.prod_apply a.point b.point p.1 p.2

/-- The first support of the product distribution stays in the original first face. -/
public theorem boxProductPoint_first_support (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : P.Realization) (b : Q.Realization) :
    (boxProductPoint P Q a b).point.weights.support.image Prod.fst ⊆ a.point.weights.support := by
  unfold boxProductPoint BoxProductConstruction.productPoint
  exact BoxProductConstruction.first_support_productSimplex a.point b.point

/-- The second support of the product distribution stays in the original second face. -/
public theorem boxProductPoint_second_support (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : P.Realization) (b : Q.Realization) :
    (boxProductPoint P Q a b).point.weights.support.image Prod.snd ⊆ b.point.weights.support := by
  unfold boxProductPoint BoxProductConstruction.productPoint
  exact BoxProductConstruction.second_support_productSimplex a.point b.point

/-- Literal pairs of belonging vertices give the literal box vertex. -/
public theorem boxProductPoint_vertex (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    boxProductPoint P Q (Realization.vertex P a ha) (Realization.vertex Q b hb) =
      Realization.vertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb) := by
  unfold boxProductPoint
  exact BoxProductConstruction.productPoint_vertex P Q a ha b hb

/-- The first original box projection preserves every literal vertex. -/
public theorem boxFirst_vertex (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    boxFirst P Q (Realization.vertex (boxProduct P Q) (a, b)
      (boxProduct_vertex P Q a ha b hb)) = Realization.vertex P a ha := by
  unfold boxFirst
  let v : Vertex (boxProduct P Q) := ⟨(a, b), boxProduct_vertex P Q a ha b hb⟩
  have h := (firstMorphism P Q).realization_vertex v
  have he : (firstMorphism P Q).vertexMap v = (⟨a, ha⟩ : Vertex P) := Subtype.ext rfl
  exact h.trans (congrArg (fun z : Vertex P => Realization.vertex P z.val z.property) he)

/-- The second original box projection preserves every literal vertex. -/
public theorem boxSecond_vertex (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    boxSecond P Q (Realization.vertex (boxProduct P Q) (a, b)
      (boxProduct_vertex P Q a ha b hb)) = Realization.vertex Q b hb := by
  unfold boxSecond
  let v : Vertex (boxProduct P Q) := ⟨(a, b), boxProduct_vertex P Q a ha b hb⟩
  have h := (secondMorphism P Q).realization_vertex v
  have he : (secondMorphism P Q).vertexMap v = (⟨b, hb⟩ : Vertex Q) := Subtype.ext rfl
  exact h.trans (congrArg (fun z : Vertex Q => Realization.vertex Q z.val z.property) he)

end PreAbstractSimplicialComplex

end
