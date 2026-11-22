/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDoubleCofaceSupport
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailCoefficient

/-!
# Original positive coface coefficients and their full tail comparison

The original double-coface identity with face zero identifies exactly
the same positive original target vertex in both composites. The
whole coface cone image enters that actual positive coefficient with
its genuine original vertex transport and positive support inverse.
The two original whole marked coefficient composites are equal.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original face-zero double-coface identity retains exactly the same actual positive original target vertex. -/
theorem coneTailCofaceVertex {n : ℕ} (k : Fin (n + 3)) (hk : 0 < k) (i : Vertex.{u} n) :
    coneTailEmbedding (n + 1) (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i) =
      coneCofaceEmbedding k (coneTailEmbedding n i) :=
  congrArg (fun f => f i) (coneDoubleCofaceEmbedding_eq (0 : Fin (n + 2)) k hk)

/-- The actual original coface image at a positive coefficient enters its same entire positive cone after precisely
the original double-coface vertex transport and original positive support isomorphism. -/
def coneCofacePositiveCoefficient {n : ℕ} (k : Fin (n + 3)) (hk : 0 < k) (i : Vertex.{u} n) :
    coneWeight (coneTailEmbedding n i) ⟶
      coneAfterWeight (coneTailEmbedding (n + 1) (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i))
        (⊥ : Vertex.{u} (n + 2)) :=
  (coneImage (coneCofaceEmbedding k).toOrderHom (coneTailEmbedding n i) ≫
    eqToHom (congrArg (fun v : Vertex.{u} (n + 2) => coneWeight v) (coneTailCofaceVertex k hk i).symm)) ≫
      (coneAfterAboveIso (coneTailEmbedding_positive (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i))).inv

/-- The original positive coefficient map retains exactly its unchanged coface cone image and original vertex
transport after its actual whole positive inclusion. -/
theorem coneCofacePositiveCoefficient_inclusion {n : ℕ} (k : Fin (n + 3)) (hk : 0 < k) (i : Vertex.{u} n) :
    coneCofacePositiveCoefficient k hk i ≫
      coneAfterInclusion (coneTailEmbedding (n + 1) (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i)) (⊥ : Vertex.{u}
        (n + 2)) =
        coneImage (coneCofaceEmbedding k).toOrderHom (coneTailEmbedding n i) ≫
          eqToHom (congrArg (fun v : Vertex.{u} (n + 2) => coneWeight v) (coneTailCofaceVertex k hk i).symm) := by
  let e := coneAfterAboveIso (coneTailEmbedding_positive (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i))
  let a := coneImage (coneCofaceEmbedding k).toOrderHom (coneTailEmbedding n i) ≫
    eqToHom (congrArg (fun v : Vertex.{u} (n + 2) => coneWeight v) (coneTailCofaceVertex k hk i).symm)
  change (a ≫ e.inv) ≫ e.hom = a
  exact (Category.assoc _ _ _).trans ((congrArg (fun z => a ≫ z) e.inv_hom_id).trans (Category.comp_id _))

/-- The full original face-zero and positive coface coefficient composites agree as whole marked maps into the same
actual positive coefficient, with every original scalar word and maximum mark retained. -/
theorem coneCofacePositiveCoefficient_tail {n : ℕ} (k : Fin (n + 3)) (hk : 0 < k) (i : Vertex.{u} n) :
    coneImage (coneCofaceEmbedding (k.pred (ne_of_gt hk))).toOrderHom i ≫
      (coneTailAfterCoefficientIso (n + 1) (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i)).hom =
        (coneTailCoefficientIso n i).hom ≫ coneCofacePositiveCoefficient k hk i := by
  let f := (coneCofaceEmbedding.{u} (k.pred (ne_of_gt hk))).toOrderHom
  let b := (coneTailEmbedding.{u} (n + 1)).toOrderHom
  let c := (coneTailEmbedding.{u} n).toOrderHom
  let g := (coneCofaceEmbedding.{u} k).toOrderHom
  let v := coneTailEmbedding (n + 1) (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i)
  let ι := coneAfterInclusion v (⊥ : Vertex.{u} (n + 2))
  let hp := coneTailEmbedding_positive (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i)
  let a := coneImage f i
  let e := coneTailAfterCoefficientIso (n + 1) (f i)
  let q := (coneTailCoefficientIso n i).hom
  let t := eqToHom (congrArg (fun w : Vertex.{u} (n + 2) => coneWeight w) (coneTailCofaceVertex k hk i).symm)
  have hι : (coneAfterAboveIso hp).hom = ι := coneAfterAboveIso_hom hp
  have : IsIso ι := hι ▸ (coneAfterAboveIso hp).isIso_hom
  apply (cancel_mono ι).mp
  have hl : (a ≫ e.hom) ≫ ι = coneImage (b.comp f) i :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => a ≫ z) (coneTailAfterCoefficientIso_inclusion (n + 1) (f i))).trans (coneImage_comp f b i))
  have hr : (q ≫ coneCofacePositiveCoefficient k hk i) ≫ ι = coneImage (g.comp c) i ≫ t :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => q ≫ z) (coneCofacePositiveCoefficient_inclusion k hk i)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ t)
            ((congrArg (fun z => z ≫ coneImage g (c i)) (coneTailCoefficientIso_hom n i)).trans (coneImage_comp c g
              i)))))
  have he : b.comp f = g.comp c :=
    congrArg (fun p : Vertex.{u} n ↪o Vertex.{u} (n + 2) => p.toOrderHom)
      (coneDoubleCofaceEmbedding_eq (0 : Fin (n + 2)) k hk)
  let z := fun p : Vertex.{u} n →o Vertex.{u} (n + 2) => coneImage p i
  have ht : coneImage (g.comp c) i ≫ t = coneImage (b.comp f) i :=
    (eqToHom_naturality z he.symm).trans (Category.id_comp _)
  exact hl.trans (hr.trans ht).symm

end SSet.Marked.CoherentWeight
