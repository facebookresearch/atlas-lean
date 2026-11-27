/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Basic
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.Data.Finset.Max

/-!
# Original finite cone subsets and their maximum-preserving marking

The vertices are nonempty original ordinal subsets with a specified
least vertex. They are ordered by inclusion. Their nerve is marked
exactly on inclusions that retain the same maximum. Monotone ordinal
maps act by the original direct image, including noninjective maps;
maximum naturality proves that all these maps preserve the marking.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

/-- Original ordinal vertices lifted only to the chosen coefficient universe. -/
abbrev Vertex (n : ℕ) := ULift.{u} (Fin (n + 1))

/-- Local vertex equality uses the native linear-order decision procedure for all original finite-set maxima. -/
local instance vertexDecidableEq (n : ℕ) : DecidableEq (Vertex.{u} n) :=
  (inferInstance : LinearOrder (Vertex.{u} n)).toDecidableEq

/-- A cone subset retains the specified original least vertex and every other original vertex. -/
@[ext]
structure ConeSubset {n : ℕ} (i : Vertex.{u} n) where
  /-- The entire original finite subset. -/
  vertices : Finset (Vertex.{u} n)
  /-- The designated original vertex belongs to the subset. -/
  mem : i ∈ vertices
  /-- It is the least original vertex in the subset. -/
  lower (j : Vertex.{u} n) (hj : j ∈ vertices) : i ≤ j

instance {n : ℕ} (i : Vertex.{u} n) : PartialOrder (ConeSubset i) :=
  PartialOrder.lift ConeSubset.vertices (fun _ _ h => ConeSubset.ext h)

/-- The maximum is an actual original vertex of the entire supplied subset. -/
def ConeSubset.maximum {n : ℕ} {i : Vertex.{u} n} (a : ConeSubset i) : Vertex.{u} n :=
  a.vertices.max' ⟨i, a.mem⟩

/-- The maximum belongs to the same whole original subset. -/
theorem ConeSubset.maximum_mem {n : ℕ} {i : Vertex.{u} n} (a : ConeSubset i) :
    a.maximum ∈ a.vertices := Finset.max'_mem _ _

/-- Each retained original vertex is bounded by this actual maximum. -/
theorem ConeSubset.le_maximum {n : ℕ} {i : Vertex.{u} n} (a : ConeSubset i)
    (j : Vertex.{u} n) (hj : j ∈ a.vertices) : j ≤ a.maximum :=
  Finset.le_max' _ _ hj

/-- Inclusion of whole cone subsets is monotone on their original maxima. -/
theorem ConeSubset.maximum_mono {n : ℕ} {i : Vertex.{u} n}
    {a b : ConeSubset i} (h : a ≤ b) : a.maximum ≤ b.maximum :=
  b.le_maximum _ (h a.maximum_mem)

/-- The exact original maximum is a functor from the inclusion category to the ordinal. -/
def maximumFunctor {n : ℕ} (i : Vertex.{u} n) : ConeSubset i ⥤ Vertex.{u} n where
  obj a := a.maximum
  map f := homOfLE (ConeSubset.maximum_mono (leOfHom f))

/-- The marked cone weight keeps every original subset and marks precisely the constant-maximum edges. -/
def coneWeight {n : ℕ} (i : Vertex.{u} n) : Marked.{u} where
  toSSet := nerve (ConeSubset i)
  marking := {e | (e.obj 0).maximum = (e.obj 1).maximum}
  degenerate_mem _ := rfl

/-- A marked edge is exactly an inclusion that keeps the same original maximum. -/
theorem coneWeight_marking {n : ℕ} (i : Vertex.{u} n)
    (e : (nerve (ConeSubset i)) _⦋1⦌) :
    e ∈ (coneWeight i).marking ↔ (e.obj 0).maximum = (e.obj 1).maximum := Iff.rfl

/-- Original monotone ordinal maps act by the whole direct image of the supplied subset. -/
def ConeSubset.image {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    {i : Vertex.{u} n} (a : ConeSubset i) : ConeSubset (f i) where
  vertices := a.vertices.image f
  mem := Finset.mem_image_of_mem _ a.mem
  lower j hj := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact f.monotone (a.lower k hk)

/-- The original maximum commutes with every monotone ordinal image, including degeneracies. -/
theorem ConeSubset.image_maximum {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    {i : Vertex.{u} n} (a : ConeSubset i) : (a.image f).maximum = f a.maximum := by
  change (a.vertices.image f).max' _ = f (a.vertices.max' _)
  exact Finset.max'_image f.monotone a.vertices _

/-- Whole subset images retain the original inclusion order. -/
theorem ConeSubset.image_mono {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    {i : Vertex.{u} n} {a b : ConeSubset i} (h : a ≤ b) : a.image f ≤ b.image f :=
  Finset.image_subset_image h

/-- A monotone original ordinal map induces the genuine whole cone-subset functor. -/
def coneImageFunctor {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m) (i : Vertex.{u} n) :
    ConeSubset i ⥤ ConeSubset (f i) where
  obj a := a.image f
  map h := homOfLE (ConeSubset.image_mono f (leOfHom h))

/-- Its native nerve map preserves precisely the original maximum-preserving marking. -/
def coneImage {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m) (i : Vertex.{u} n) :
    coneWeight i ⟶ coneWeight (f i) where
  hom := nerveMap (coneImageFunctor f i)
  preserve he := by
    change ((coneImageFunctor f i).obj _).maximum = ((coneImageFunctor f i).obj _).maximum
    exact (ConeSubset.image_maximum f _).trans
      ((congrArg f he).trans (ConeSubset.image_maximum f _).symm)

/-- An image keeps exactly the original finite vertex image, without removing repeated-image endpoints. -/
theorem coneImage_vertices {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m) (i : Vertex.{u} n)
    (a : ConeSubset i) : ((coneImageFunctor f i).obj a).vertices = a.vertices.image f := rfl

end SSet.Marked.CoherentWeight
