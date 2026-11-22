/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.NervePreorderSubtype
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfter
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCoordinateFaces
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# Upper-coordinate cover at every original cone coefficient

A cone word whose first maximum exceeds the cutoff retains that
original vertex in every later subset. Its entire simplex therefore
lies in the corresponding upper coordinate face. This gives the whole
positive-maximum coefficient, at every original source vertex, as the
union of its original upper faces with unchanged markings.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- Original vertices strictly beyond the chosen cutoff, with their original order. -/
abbrev AfterVertex {n : ℕ} (k : Vertex.{u} n) := {j : Vertex.{u} n // k < j}

/-- The whole cone subcomplex whose original maxima exceed the cutoff. -/
def coneAfterSubcomplex {n : ℕ} (i k : Vertex.{u} n) : (nerve (ConeSubset i)).Subcomplex :=
  preorderSubtypeSubcomplex (fun a : ConeSubset i => k < a.maximum)

/-- All original upper coordinate faces strictly beyond the cutoff. -/
def coneAfterUpperSupport {n : ℕ} (i k : Vertex.{u} n) : (nerve (ConeSubset i)).Subcomplex :=
  ⨆ j : AfterVertex k, coneCoordinateFace i j.val true

/-- The upper-coordinate cover is exact on every whole scalar simplex at every original coefficient. -/
theorem coneAfterSubcomplex_eq_upper {n : ℕ} (i k : Vertex.{u} n) :
    coneAfterSubcomplex i k = coneAfterUpperSupport i k := by
  ext q x
  change (∀ t, k < (x.obj t).maximum) ↔ _
  simp only [coneAfterUpperSupport, Subfunctor.iSup_obj, Set.mem_iUnion,
    coneCoordinateFace, Set.mem_ofPred_eq, iff_true]
  constructor
  · intro hx
    let j : AfterVertex k := ⟨(x.obj 0).maximum, hx 0⟩
    refine ⟨j, fun t => ?_⟩
    have ht : (x.obj 0).vertices ⊆ (x.obj t).vertices :=
      leOfHom (x.map (homOfLE (Fin.zero_le t)))
    exact ht (x.obj 0).maximum_mem
  · rintro ⟨j, hj⟩ t
    exact j.property.trans_le ((x.obj t).le_maximum j.val (hj t))

/-- The support has exactly the original maximum-preserving marked edges. -/
def coneAfterSupportMarked {n : ℕ} (i k : Vertex.{u} n) : Marked.{u} :=
  comap (coneWeight i) (coneAfterSubcomplex i k).ι

/-- Original positive-maximum subset words identify the whole coefficient with its actual marked support. -/
def coneAfterSupportIso {n : ℕ} (i k : Vertex.{u} n) :
    coneAfterWeight i k ≅ coneAfterSupportMarked i k :=
  isoMk (nervePreorderSubtypeIso (fun a : ConeSubset i => k < a.maximum))
    (fun _ => Iff.rfl)

end SSet.Marked.CoherentWeight
