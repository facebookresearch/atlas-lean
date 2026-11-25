/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# The original upper-maximum cone layer is the entire coherent Hom

Every subset in the upper layer retains the specified original least
vertex and actual maximum. The whole same finite subset is precisely
an original coherent path with both endpoints. The native functors
retain all original inclusions in both directions. The upper layer is
maximally marked; no ordinary minimal-product marking is substituted.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual original upper layer consists of the same complete cone subsets with their given maximum. -/
abbrev UpperCone {n : ℕ} (i k : Vertex.{u} n) := {a : ConeSubset i // a.maximum = k}

/-- A whole original coherent path supplies its same finite endpoint-containing cone subset. -/
def pathCone {n : ℕ} {i k : Vertex.{u} n} (p : SimplicialThickening.Path i k) : ConeSubset i where
  vertices := p.I.toFinite.toFinset
  mem := p.I.toFinite.mem_toFinset.mpr p.left
  lower j hj := p.left_le j (p.I.toFinite.mem_toFinset.mp hj)

/-- Its actual maximum is exactly the original terminal path endpoint. -/
theorem pathCone_maximum {n : ℕ} {i k : Vertex.{u} n} (p : SimplicialThickening.Path i k) :
    (pathCone p).maximum = k := by
  apply le_antisymm
  · exact p.le_right _ (p.I.toFinite.mem_toFinset.mp (pathCone p).maximum_mem)
  · exact (pathCone p).le_maximum _ (p.I.toFinite.mem_toFinset.mpr p.right)

/-- The upper layer reads as the same original whole endpoint-containing path, preserving its entire vertex subset. -/
def upperConePath {n : ℕ} {i k : Vertex.{u} n} (a : UpperCone i k) : SimplicialThickening.Path i k where
  I := a.val.vertices
  left := a.val.mem
  right := by
    change k ∈ a.val.vertices
    exact Eq.mp (congrArg (fun v : Vertex.{u} n => v ∈ a.val.vertices) a.property) a.val.maximum_mem
  left_le j hj := a.val.lower j hj
  le_right j hj := (a.val.le_maximum j hj).trans a.property.le

/-- The same original path is placed in its actual original upper-maximum cone layer. -/
def pathUpperCone {n : ℕ} {i k : Vertex.{u} n} (p : SimplicialThickening.Path i k) : UpperCone i k :=
  ⟨pathCone p, pathCone_maximum p⟩

/-- Converting a whole original path through the upper layer leaves its entire subset unchanged. -/
theorem upperConePath_pathUpperCone {n : ℕ} {i k : Vertex.{u} n} (p : SimplicialThickening.Path i k) :
    upperConePath (pathUpperCone p) = p := by
  apply SimplicialThickening.Path.ext
  exact p.I.toFinite.coe_toFinset

/-- The inverse conversion retains the whole original upper-layer cone subset and its actual maximum. -/
theorem pathUpperCone_upperConePath {n : ℕ} {i k : Vertex.{u} n} (a : UpperCone i k) :
    pathUpperCone (upperConePath a) = a := by
  apply Subtype.ext
  apply ConeSubset.ext
  ext j
  exact (upperConePath a).I.toFinite.mem_toFinset

/-- Whole original path inclusions define the native functor to the actual upper layer. -/
def pathUpperConeFunctor {n : ℕ} (i k : Vertex.{u} n) : SimplicialThickening.Path i k ⥤ UpperCone i k where
  obj p := pathUpperCone p
  map {p q} f := homOfLE (show pathCone p ≤ pathCone q by
    intro j hj
    exact q.I.toFinite.mem_toFinset.mpr ((leOfHom f.1) (p.I.toFinite.mem_toFinset.mp hj)))

/-- The original upper-layer inclusions give exactly their same whole native coherent path inclusions. -/
def upperConePathFunctor {n : ℕ} (i k : Vertex.{u} n) : UpperCone i k ⥤ SimplicialThickening.Path i k where
  obj a := upperConePath a
  map {a b} f := ⟨homOfLE (show (upperConePath a).I ⊆ (upperConePath b).I from leOfHom f)⟩

/-- The native path/upper-layer object correspondence uses only these actual whole subset conversions. -/
def upperConePathEquiv {n : ℕ} (i k : Vertex.{u} n) : UpperCone i k ≃ SimplicialThickening.Path i k where
  toFun := upperConePath
  invFun := pathUpperCone
  left_inv := pathUpperCone_upperConePath
  right_inv := upperConePath_pathUpperCone

end SSet.Marked.CoherentWeight
