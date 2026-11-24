/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.Grading
public import MathlibExt.KTheory.Milnor.MapLaws
public import MathlibExt.RingTheory.GradedAlgebra.AlgHom

/-!
# Degree maps for Milnor K-theory

Degree preservation for `tensorMap` and `map`, the induced map on degree
pieces, and its identity and composition laws.

The tensor map `tensorMapAlg f : TensorRing F →ₐ[ℤ] TensorRing K` is the
`TensorAlgebra.lift` of the generator map `ι ∘ unitsAddHom f`. Since each
generator lands in degree one, the lift is a graded algebra homomorphism
`TensorRing.degree F →ₐᵍ[ℤ] TensorRing.degree K` by
`TensorAlgebra.liftGradedAlgHom`. Its `n`-th homogeneous component is the
typed linear map `tensorMapDegree f n : TensorRing.degree F n →ₗ[ℤ]
TensorRing.degree K n`, defined as `(tensorMapGradedAlgHom f).component n`
via `GradedAlgHom.component`. Degree preservation for `tensorMap` and `map`
follows directly from this component.

## Main definitions
* `MilnorKRing.tensorMapGradedAlgHom`
* `MilnorKRing.tensorMapDegree`
* `MilnorKRing.mapDegree`

## Main results
* `MilnorKRing.tensorMapDegree_coe`
* `MilnorKRing.tensorMap_mem_degree`
* `MilnorKRing.tensorMap_degree_le`
* `MilnorKRing.map_mem_degree`
* `MilnorKRing.mapDegree_id`
* `MilnorKRing.mapDegree_comp`
-/

@[expose] public section

open TensorAlgebra DirectSum
open scoped TensorAlgebra

namespace MilnorK

variable {F K L : Type*} [Field F] [Field K] [Field L]

namespace MilnorKRing

/-- The tensor-ring map as a graded algebra homomorphism. Its underlying
`ℤ`-algebra map is `tensorMapAlg f`, and its underlying ring map agrees with
`tensorMap f`. -/
noncomputable def tensorMapGradedAlgHom (f : F →+* K) :
    (TensorRing.degree F) →ₐᵍ[ℤ] (TensorRing.degree K) :=
  TensorAlgebra.liftGradedAlgHom
    ((TensorAlgebra.ι ℤ).comp (unitsAddHom f).toIntLinearMap)
    (fun a => by
      rw [TensorRing.degree, TensorAlgebra.degree_one]
      exact LinearMap.mem_range_self _ _)

/-- Underlying algebra homomorphism of `tensorMapGradedAlgHom` is `tensorMapAlg`. -/
@[simp]
theorem tensorMapGradedAlgHom_toAlgHom (f : F →+* K) :
    (tensorMapGradedAlgHom f).toAlgHom = tensorMapAlg f :=
  rfl

/-- `tensorMapGradedAlgHom` agrees with `tensorMap` as a function. -/
@[simp]
theorem tensorMapGradedAlgHom_apply (f : F →+* K) (x : TensorRing F) :
    tensorMapGradedAlgHom (F := F) (K := K) f x = tensorMap f x :=
  rfl

/-- Typed `n`-th component of `tensorMapGradedAlgHom`. This is the canonical
linear map `TensorRing.degree F n →ₗ[ℤ] TensorRing.degree K n`. -/
noncomputable def tensorMapDegree (f : F →+* K) (n : ℕ) :
    TensorRing.degree F n →ₗ[ℤ] TensorRing.degree K n :=
  (tensorMapGradedAlgHom f).component n

/-- Underlying tensor-ring value of `tensorMapDegree` is `tensorMap`. -/
@[simp]
theorem tensorMapDegree_coe (f : F →+* K) (n : ℕ)
    (x : TensorRing.degree F n) :
    (tensorMapDegree f n x : TensorRing K) = tensorMap f (x : TensorRing F) :=
  rfl

/-- `tensorMap` preserves the tensor degree `n` piece, via the typed component
`tensorMapDegree`. -/
theorem tensorMap_mem_degree (f : F →+* K) {n : ℕ} {x : TensorRing F}
    (hx : x ∈ TensorRing.degree F n) :
    tensorMap f x ∈ TensorRing.degree K n := by
  simpa [tensorMapDegree_coe] using (tensorMapDegree f n ⟨x, hx⟩).2

/-- Submodule version of `tensorMap` degree preservation. -/
theorem tensorMap_degree_le (f : F →+* K) (n : ℕ) :
    Submodule.map (tensorMap f).toAddMonoidHom.toIntLinearMap (TensorRing.degree F n) ≤
      TensorRing.degree K n := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  exact tensorMap_mem_degree f hx

/-- `map` preserves the Milnor degree `n` piece. -/
theorem map_mem_degree (f : F →+* K) (n : ℕ) {x : MilnorKRing F}
    (hx : x ∈ degree F n) : map f x ∈ degree K n := by
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx
  have hTensor : tensorMap f y ∈ TensorRing.degree K n :=
    tensorMap_mem_degree f hy
  have hMapEq : map f (mkLinear F y) = mkLinear K (tensorMap f y) := by
    simp [mkLinear_apply, map_mk]
  have hEq : map f x = mkLinear K (tensorMap f y) := by
    calc map f x = map f (mkLinear F y) := by rw [← hxy]
      _ = mkLinear K (tensorMap f y) := hMapEq
  rw [hEq]
  exact Submodule.mem_map_of_mem hTensor

/-- The induced map `degree F n →ₗ[ℤ] degree K n`. -/
noncomputable def mapDegree (f : F →+* K) (n : ℕ) :
    degree F n →ₗ[ℤ] degree K n :=
  ((map f).toAddMonoidHom.toIntLinearMap).restrict
    (fun x hx => map_mem_degree f n (x := x) hx)

/-- Computation of `mapDegree`. -/
@[simp]
lemma mapDegree_apply (f : F →+* K) (n : ℕ) (_x : degree F n) :
    (mapDegree f n _x : MilnorKRing K) = map f (_x : MilnorKRing F) :=
  rfl

/-- Identity law for `mapDegree`. -/
theorem mapDegree_id (n : ℕ) :
    mapDegree (RingHom.id F) n = LinearMap.id := by
  ext x : 1
  apply Subtype.ext
  simp [map_id]

/-- Composition law for `mapDegree`. -/
theorem mapDegree_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    mapDegree (g.comp f) n =
      (mapDegree g n).comp (mapDegree f n) := by
  ext x : 1
  apply Subtype.ext
  simp [map_comp]

/-- Pointwise composition for `mapDegree`. -/
theorem mapDegree_comp_apply (f : F →+* K) (g : K →+* L) (n : ℕ)
    (x : degree F n) :
    mapDegree (g.comp f) n x =
      mapDegree g n (mapDegree f n x) := by
  apply Subtype.ext
  simp [map_comp]

end MilnorKRing

end MilnorK
