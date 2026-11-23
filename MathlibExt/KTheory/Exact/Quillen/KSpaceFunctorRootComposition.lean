/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorCoherence
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct

/-!
# Composition of the actual exact-functor zero roots

The canonical mixed realization and comparison of the zero roots identify
the direct and iterated source points in six independent category object
and Hom universes. The target path is transported to the original mapped
first root followed by the second root. The original choice of a full family
on that type is retained, including both endpoint laws at every time.
No root coherence witness is a caller hypothesis.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open scoped ZeroObject

universe uC vC uD vD uE vE

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

private theorem canonicalFunctorCompositeBasepointComputed
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).hom (NQReal.basepoint C) =
      (NQRealFunctorWeaklyPointed G).hom
        ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C)) := by
  have hWhole := congrArg
    (fun k : ContinuousMap (NQReal C) (NQReal E) => k (NQReal.basepoint C))
    (NQRealFunctorWeaklyPointed_comp_hom F G)
  have hComp := DFunLike.congr_fun
    (ContinuousMap.WeaklyPointed.comp_hom
      (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)) (NQReal.basepoint C)
  exact hWhole.trans hComp

/-- The actual original image-zero vertices identify the direct and
iterated source points, retaining all SIX category object/Hom levels. -/
theorem NQRealFunctor_comp_basepoint_eq
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).hom (NQReal.basepoint C) =
      (NQRealFunctorWeaklyPointed G).hom
        ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C)) :=
  canonicalFunctorCompositeBasepointComputed F G

private theorem canonicalFunctorCompMappedRootTarget
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (((NQRealFunctorWeaklyPointed F).comp (NQRealFunctorWeaklyPointed G)).rootPath.cast
        (congrArg
          (fun k : ContinuousMap (NQReal C) (NQReal E) => k (NQReal.basepoint C))
          (NQRealFunctorWeaklyPointed_comp_hom F G)) rfl) =
      ((((NQRealFunctorWeaklyPointed F).rootPath.map
        (NQRealFunctorWeaklyPointed G).hom.continuous).cast
          (NQRealFunctor_comp_basepoint_eq F G) rfl).trans
            (NQRealFunctorWeaklyPointed G).rootPath) := by
  apply Path.ext
  funext t
  exact congrArg
    (fun p : Path
      (((NQRealFunctorWeaklyPointed F).comp (NQRealFunctorWeaklyPointed G)).hom
        (NQReal.basepoint C)) (NQReal.basepoint E) => p.toContinuousMap.toFun t)
    (ContinuousMap.WeaklyPointed.comp_rootPath
      (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G))

private theorem canonicalFunctorRootCompositionComputed
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).rootPath.Homotopic
      ((((NQRealFunctorWeaklyPointed F).rootPath.map
        (NQRealFunctorWeaklyPointed G).hom.continuous).cast
          (NQRealFunctor_comp_basepoint_eq F G) rfl).trans
            (NQRealFunctorWeaklyPointed G).rootPath) :=
  ⟨(NQRealFunctorCompRootHomotopy F G).cast rfl (canonicalFunctorCompMappedRootTarget F G)⟩

/-- The ENTIRE actual direct zero root is homotopic to the actual mapped
first root followed by the actual second root, with all SIX category levels independent. -/
theorem NQRealFunctor_comp_rootPath_homotopic
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).rootPath.Homotopic
      ((((NQRealFunctorWeaklyPointed F).rootPath.map
        (NQRealFunctorWeaklyPointed G).hom.continuous).cast
          (NQRealFunctor_comp_basepoint_eq F G) rfl).trans
            (NQRealFunctorWeaklyPointed G).rootPath) :=
  canonicalFunctorRootCompositionComputed F G

/-- The original choice of a full family on the mapped first root followed by
its second root, independent of every source loop. Its choice is retained
separately from the canonical family for the stored composite. -/
def NQRealFunctorCompMappedRootHomotopy
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).rootPath.Homotopy
      ((((NQRealFunctorWeaklyPointed F).rootPath.map
        (NQRealFunctorWeaklyPointed G).hom.continuous).cast
          (NQRealFunctor_comp_basepoint_eq F G) rfl).trans
            (NQRealFunctorWeaklyPointed G).rootPath) :=
  (NQRealFunctor_comp_rootPath_homotopic F G).some

/-- The full source-root boundary is fixed at every homotopy time. -/
theorem NQRealFunctorCompMappedRootHomotopy_source
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t : unitInterval) :
    (NQRealFunctorCompMappedRootHomotopy F G).eval t 0 =
      (NQRealFunctorWeaklyPointed (F ⋙ G)).hom (NQReal.basepoint C) :=
  ((NQRealFunctorCompMappedRootHomotopy F G).eval t).source

/-- The full original chosen-zero target boundary is fixed at every homotopy time. -/
theorem NQRealFunctorCompMappedRootHomotopy_target
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t : unitInterval) :
    (NQRealFunctorCompMappedRootHomotopy F G).eval t 1 = NQReal.basepoint E :=
  ((NQRealFunctorCompMappedRootHomotopy F G).eval t).target

end AlgebraicKTheory

end
