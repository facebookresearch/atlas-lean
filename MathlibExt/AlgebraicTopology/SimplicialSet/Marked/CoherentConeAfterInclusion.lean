/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfter
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# Actual positive-maximum cone inclusion and original upper values

The full original positive-maximum subdiagram includes by the same
whole subset nerve. At an original least vertex already beyond the
cutoff every cone subset satisfies the bound; the inclusion is the
genuine identity-on-subsets marked isomorphism, not an assumed
relative model-class comparison.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual positive-maximum subset inclusion retains its whole original vertex subset. -/
def coneAfterForgetFunctor {n : ℕ} (i k : Vertex.{u} n) : ConeAfter i k ⥤ ConeSubset i where
  obj := Subtype.val
  map f := homOfLE (leOfHom f)

/-- The whole original positive-maximum marked inclusion. -/
def coneAfterInclusion {n : ℕ} (i k : Vertex.{u} n) : coneAfterWeight i k ⟶ coneWeight i where
  hom := nerveMap (coneAfterForgetFunctor i k)
  preserve h := h

/-- The original positive-maximum inclusion commutes with every entire native coherent Hom action. -/
def coneAfterDiagramInclusion {n : ℕ} (k : Vertex.{u} n) : coneAfterDiagram k ⟶ coneDiagram n where
  app i := coneAfterInclusion i.unop.as k
  naturality i j := by
    ext q h
    apply Hom.ext
    ext r z
    refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- Above the actual cutoff, every full original subset has its genuine bound proof. -/
def coneAfterLiftFunctor {n : ℕ} {i k : Vertex.{u} n} (hi : k < i) : ConeSubset i ⥤ ConeAfter i k where
  obj a := ⟨a, hi.trans_le (a.le_maximum i a.mem)⟩
  map f := homOfLE (leOfHom f)

/-- The original upper cone values are identical whole subset nerves through the actual inclusion and bound
  insertion. -/
def coneAfterAboveNerveIso {n : ℕ} {i k : Vertex.{u} n} (hi : k < i) :
    (coneAfterWeight i k).toSSet ≅ (coneWeight i).toSSet where
  hom := nerveMap (coneAfterForgetFunctor i k)
  inv := nerveMap (coneAfterLiftFunctor hi)
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    change (x ⋙ coneAfterForgetFunctor i k) ⋙ coneAfterLiftFunctor hi = x
    refine CategoryTheory.Functor.ext (fun t => Subtype.ext rfl) (fun _ _ _ => Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    change (x ⋙ coneAfterLiftFunctor hi) ⋙ coneAfterForgetFunctor i k = x
    refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- Above the actual cutoff, the entire original positive-maximum inclusion is a genuine marked isomorphism
  with unchanged maximum-preserving edges. -/
def coneAfterAboveIso {n : ℕ} {i k : Vertex.{u} n} (hi : k < i) :
    coneAfterWeight i k ≅ coneWeight i := isoMk (coneAfterAboveNerveIso hi) (fun _ => Iff.rfl)

/-- The forward upper-value isomorphism is exactly the original whole positive-maximum inclusion. -/
theorem coneAfterAboveIso_hom {n : ℕ} {i k : Vertex.{u} n} (hi : k < i) :
    (coneAfterAboveIso hi).hom = coneAfterInclusion i k := rfl

end SSet.Marked.CoherentWeight
