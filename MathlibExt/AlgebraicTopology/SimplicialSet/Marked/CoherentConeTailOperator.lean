/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailCoefficient
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailPaths
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedActionNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagramComponentIso

/-!
# The original zeroth-coface operator into the positive cone

The original smaller cone restricts from the positive-maximum cone
through its actual coface coefficient and Hom isomorphisms. Full
native path-image naturality gives the whole enriched operator, not
only its vertex components. Its component inverses give the genuine
restricted diagram isomorphism with unchanged original marks.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual original zeroth coface gives its same whole opposite enriched index map. -/
def coneTailIndex (n : ℕ) : EnrichedFunctor SSet.{u} (Index.{u} n)ᵒᵖ (Index.{u} (n + 1))ᵒᵖ :=
  EnrichedFunctor.opposite (indexMap (coneTailEmbedding n).toOrderHom)

/-- The original cone coface images commute with the same whole positive-tail action and native Hom map. -/
theorem coneTailAfter_action {n : ℕ} (i j : Vertex.{u} n) :
    coneAction i j ≫ (coneTailAfterCoefficientIso n i).hom =
      prodMap (coneTailPathMarkedIso i j).hom (coneTailAfterCoefficientIso n j).hom ≫
        coneAfterAction (coneTailEmbedding n i) (coneTailEmbedding n j) (⊥ : Vertex.{u} (n + 1)) := by
  apply Hom.ext
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro x
  refine CategoryTheory.Functor.ext (fun t => Subtype.ext ?_) (fun _ _ _ => Subsingleton.elim _ _)
  exact ConeSubset.image_prepend (coneTailEmbedding n).toOrderHom (x.1.obj t) (x.2.obj t)

/-- The whole original positive cone restricts along the actual zeroth-coface index. -/
def coneTailRestricted (n : ℕ) : EnrichedDiagram (Index.{u} n)ᵒᵖ :=
  (coneTailIndex n).comp SSet.{u} (coneAfterDiagram (⊥ : Vertex.{u} (n + 1)))

/-- The full native zeroth-coface operator carries the original smaller cone into its genuine positive-tail
  restriction. -/
def coneTailOperator (n : ℕ) : coneDiagram n ⟶ coneTailRestricted.{u} n :=
  EnrichedDiagramMap.ofAction (fun x => (coneTailAfterCoefficientIso n x.unop.as).hom) (by
    intro x y
    let i := y.unop.as
    let j := x.unop.as
    let fi := coneTailEmbedding n i
    let fj := coneTailEmbedding n j
    let root : Vertex.{u} (n + 1) := ⊥
    change maxUncurry (maxCurry (coneAction i j)) ≫ (coneTailAfterCoefficientIso n i).hom =
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path i j)))) (coneTailAfterCoefficientIso n j).hom ≫
        maxUncurry (((indexMap (coneTailEmbedding n).toOrderHom).map
          (SimplicialThickening.mk i) (SimplicialThickening.mk j)) ≫ maxCurry (coneAfterAction fi fj root))
    simp only [maxUncurry_pre, maxUncurry_maxCurry]
    have hm :
        prodMap (𝟙 (max (nerve (SimplicialThickening.Path i j)))) (coneTailAfterCoefficientIso n j).hom ≫
          prodMap (coneTailPathMarkedIso i j).hom (𝟙 (coneAfterWeight fj root)) =
        prodMap (coneTailPathMarkedIso i j).hom (coneTailAfterCoefficientIso n j).hom := by
      apply Hom.ext
      rfl
    exact (coneTailAfter_action i j).trans
      ((congrArg (fun f => f ≫ coneAfterAction fi fj root) hm).symm.trans (Category.assoc _ _ _)))

/-- The genuine whole restricted cone comparison uses the original coefficient inverses at all original objects. -/
def coneTailOperatorIso (n : ℕ) : coneDiagram n ≅ coneTailRestricted.{u} n := by
  let _ (i : (Index.{u} n)ᵒᵖ) : IsIso ((coneTailOperator n).app i) :=
    (coneTailAfterCoefficientIso n i.unop.as).isIso_hom
  exact enrichedDiagramAsIsoOfComponents (coneTailOperator n)

/-- The entire comparison retains its original native coface coefficient map. -/
theorem coneTailOperator_app (n : ℕ) (i : (Index.{u} n)ᵒᵖ) :
    (coneTailOperator n).app i = (coneTailAfterCoefficientIso n i.unop.as).hom := rfl

end SSet.Marked.CoherentWeight
