/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FixedVertex

@[expose] public section

/-!
# Fixed-vertex simplicial sets: client test

Downstream client for `SSet.FixedVertex`, exercised with vertex set
`O = Fin 2` and the object `Δ[1]` with its standard vertex labelling.
The test checks: the labelling itself; that the identity is
vertex-bijective while a constant simplicial endomap of `Δ[1]` is
not (hence is not an `SSet(O)` morphism); the initial map from the
discrete object, which sends label `1` to the constant edge at
vertex `1` (all vertices of the image edge have label `1` — this
distinguishes the genuine constant simplex from the identity edge);
the terminal map to the codiscrete object, which records, through
`Codiscrete.equivFun`, the tuple of vertex labels (`i ↦ i` on the
identity edge); the pullback/pushout/product/initial/terminal
instances; reflection of the isomorphism `pullbackFst (𝟙 _) (𝟙 _)`;
the monomorphism characterisation on the identity; membership of
the identity in `innerFibrations (Fin 2)` and
`categoricalEquivalences (Fin 2)`; the identification of
`discreteSSet` with the constant functor; and the codiscrete nerve
model of `codiscreteObj`, including its vertex identification in
degree `0`.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite SSet
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FixedVertexTest

/-- The standard `1`-simplex as an object of `SSet(Fin 2)`, with its
standard identification of vertices. -/
def Δ1Obj : SSet.FixedVertex (Fin 2) where
  underlying := Δ[1]
  vertexEquiv := SSet.stdSimplex.obj₀Equiv

/-- The `i`-th vertex of `Δ[1]`. -/
def vertex (i : Fin 2) : (Δ[1] : SSet.{0}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm i

/-- The identity edge of `Δ[1]`, with vertices `0` and `1`. -/
def idEdge : (Δ[1] : SSet.{0}) _⦋1⦌ :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)

lemma vertexEquiv_vertex (i : Fin 2) :
    Δ1Obj.vertexEquiv (vertex i) = i :=
  Equiv.apply_symm_apply _ _

lemma vertex_idEdge (i : Fin 2) :
    (Δ[1] : SSet.{0}).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op
        idEdge =
      vertex i := by
  ext j
  fin_cases j
  rfl

/-- The identity morphism of `Δ1Obj` is vertex-bijective. -/
example : SSet.IsVertexBijective
    ((SSet.FixedVertex.forget (Fin 2)).map (𝟙 Δ1Obj)) :=
  SSet.FixedVertex.forget_map_isVertexBijective _

/-- A constant simplicial endomap of `Δ[1]` is not vertex-bijective,
hence is not a morphism of `SSet(Fin 2)` between copies of `Δ1Obj`. -/
theorem not_isVertexBijective_const :
    ¬ SSet.IsVertexBijective
      (SSet.const (vertex 0) : (Δ[1] : SSet.{0}) ⟶ Δ[1]) := by
  have hc : ∀ v : (Δ[1] : SSet.{0}) _⦋0⦌,
      (SSet.const (vertex 0) : (Δ[1] : SSet.{0}) ⟶ Δ[1]).app
          (op ⦋0⦌) v = vertex 0 := by
    intro v
    show (Δ[1] : SSet.{0}).map
        (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op (vertex 0) = vertex 0
    rw [SimplexCategory.const_eq_id]
    simp
  intro h
  have hinj : vertex 0 = vertex 1 := h.1 (by rw [hc, hc])
  have h01 := congrArg Δ1Obj.vertexEquiv hinj
  rw [vertexEquiv_vertex, vertexEquiv_vertex] at h01
  exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- The image of label `1` under the initial map into `Δ1Obj` is the
constant edge at vertex `1`: every vertex of it is `vertex 1`. -/
theorem vertex_fromDiscreteObj_app_one (i : Fin 2) :
    (Δ[1] : SSet.{0}).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op
        ((SSet.FixedVertex.fromDiscreteObj Δ1Obj).hom.app (op ⦋1⦌)
          (1 : Fin 2)) =
      vertex 1 := by
  have hedge : (SSet.FixedVertex.fromDiscreteObj Δ1Obj).hom.app
        (op ⦋1⦌) (1 : Fin 2) =
      (Δ[1] : SSet.{0}).map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op
        (vertex 1) :=
    rfl
  have hcomp : (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op ≫
        (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op =
      𝟙 (op ⦋0⦌) := by
    have h01 : (SimplexCategory.const ⦋0⦌ ⦋1⦌ i) ≫
          (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) = 𝟙 ⦋0⦌ :=
      (SimplexCategory.eq_const_to_zero _).trans
        SimplexCategory.const_eq_id
    show ((SimplexCategory.const ⦋0⦌ ⦋1⦌ i) ≫
        (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)).op = 𝟙 (op ⦋0⦌)
    rw [h01]
    rfl
  rw [hedge, ← Functor.map_comp_apply, hcomp]
  simp

/-- The terminal map records vertex labels: on the identity edge
the `equivFun` tuple of its image is `i ↦ i`. -/
theorem toCodiscreteObj_idEdge (i : Fin 2) :
    CategoryTheory.Codiscrete.equivFun
        ((SSet.FixedVertex.toCodiscreteObj Δ1Obj).hom.app (op ⦋1⦌)
          idEdge) i = i := by
  show Δ1Obj.vertexEquiv
      ((Δ[1] : SSet.{0}).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op
        idEdge) = i
  rw [vertex_idEdge, vertexEquiv_vertex]

/-- The underlying map of the morphism corresponding to
`fromDiscreteObj` under the hom-equivalence is `fromDiscrete` of the
labelling. -/
example : (SSet.FixedVertex.homEquivCompatible
      (SSet.FixedVertex.fromDiscreteObj Δ1Obj)).1 =
    SSet.FixedVertex.fromDiscrete (fun o ↦ Δ1Obj.vertexEquiv.symm o) :=
  rfl

/-- The discrete simplicial set is (definitionally) the constant
functor: `discreteSSet` is defined as `(Functor.const _).obj _`, so
the two are equal by `rfl` and the `rfl` simp lemmas
`discreteSSet_obj`/`discreteSSet_map_apply` apply to it directly. -/
example : SSet.FixedVertex.discreteSSet (Fin 2) =
    (Functor.const SimplexCategoryᵒᵖ).obj (Fin 2) :=
  rfl

/-- The codiscrete object is (definitionally) the codiscrete nerve:
its underlying simplicial set is `Codiscrete.functorToSSet.obj _`. -/
example : (SSet.FixedVertex.codiscreteObj (Fin 2)).underlying =
    CategoryTheory.Codiscrete.functorToSSet.obj (Fin 2) :=
  rfl

/-- `equivFun` inverts `equivFun.symm` on the identity tuple in
degree `1`. -/
example (i : Fin 2) :
    CategoryTheory.Codiscrete.equivFun
        (CategoryTheory.Codiscrete.equivFun.symm
          (fun j : Fin 2 => j)) i = i := by
  rw [Equiv.apply_symm_apply]

/-- In degree `0`, the vertex identification inverts its symmetric
(the nerve `0`-simplex on the constant tuple at `1`, via
`equivFun.symm`) at `1`. -/
example : SSet.FixedVertex.codiscreteVertexEquiv (Fin 2)
      ((SSet.FixedVertex.codiscreteVertexEquiv (Fin 2)).symm 1) = 1 :=
  Equiv.apply_symm_apply _ _

/-- In degree `0`, the terminal map sends `vertex 1` to the nerve
simplex whose vertex identification is `1`. -/
example : SSet.FixedVertex.codiscreteVertexEquiv (Fin 2)
      ((SSet.FixedVertex.toCodiscreteObj Δ1Obj).hom.app (op ⦋0⦌)
        (vertex 1)) = 1 := by
  have h := (SSet.FixedVertex.toCodiscreteObj Δ1Obj).w (vertex 1)
  rw [vertexEquiv_vertex] at h
  exact h

/-- The limit/colimit instances of `SSet(Fin 2)` are available. -/
example : HasInitial (SSet.FixedVertex (Fin 2)) := inferInstance
example : HasTerminal (SSet.FixedVertex (Fin 2)) := inferInstance
example : HasPullbacks (SSet.FixedVertex (Fin 2)) := inferInstance
example : HasPushouts (SSet.FixedVertex (Fin 2)) := inferInstance
example : HasBinaryProducts (SSet.FixedVertex (Fin 2)) :=
  inferInstance
example : (SSet.FixedVertex.forget (Fin 2)).Faithful :=
  inferInstance
example : ReflectsLimitsOfShape WalkingCospan
    (SSet.FixedVertex.forget (Fin 2)) := inferInstance
example : ReflectsColimitsOfShape WalkingSpan
    (SSet.FixedVertex.forget (Fin 2)) := inferInstance

/-- The first projection of the pullback of two identities is an
isomorphism in `SSet(Fin 2)`, reflected from `SSet`. -/
example : IsIso (SSet.FixedVertex.pullbackFst (𝟙 Δ1Obj) (𝟙 Δ1Obj)) := by
  have : IsIso ((SSet.FixedVertex.forget (Fin 2)).map
      (SSet.FixedVertex.pullbackFst (𝟙 Δ1Obj) (𝟙 Δ1Obj))) := by
    show IsIso (pullback.fst (𝟙 (Δ[1] : SSet.{0}))
      (𝟙 (Δ[1] : SSet.{0})))
    infer_instance
  exact isIso_of_reflects_iso (F := SSet.FixedVertex.forget (Fin 2))
    (SSet.FixedVertex.pullbackFst (𝟙 Δ1Obj) (𝟙 Δ1Obj))

/-- The identity is a monomorphism, detected underlying-simplicially
through the monomorphism characterisation. -/
example : Mono (𝟙 Δ1Obj) :=
  (SSet.FixedVertex.mono_iff_mono_forget (𝟙 Δ1Obj)).mpr (by
    rw [CategoryTheory.Functor.map_id]
    infer_instance)

/-- The identity is an inner fibration in `SSet(Fin 2)`. -/
example : SSet.FixedVertex.innerFibrations (Fin 2) (𝟙 Δ1Obj) := by
  rw [SSet.FixedVertex.innerFibrations_mem_iff,
    CategoryTheory.Functor.map_id]
  exact fun g _ ↦ inferInstance

/-- The identity is a categorical equivalence in `SSet(Fin 2)`, and
the vertex-bijectivity clause of its characterisation holds. -/
example : SSet.FixedVertex.categoricalEquivalences (Fin 2)
    (𝟙 Δ1Obj) ∧
    SSet.IsVertexBijective
      ((SSet.FixedVertex.forget (Fin 2)).map (𝟙 Δ1Obj)) :=
  ⟨(SSet.FixedVertex.categoricalEquivalences_iff (𝟙 Δ1Obj)).mpr
      ⟨SSet.FixedVertex.forget_map_isVertexBijective _,
        by rw [CategoryTheory.Functor.map_id]; exact
          SSet.categoricalEquivalences.of_isIso _⟩,
    SSet.FixedVertex.forget_map_isVertexBijective _⟩

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FixedVertexTest
