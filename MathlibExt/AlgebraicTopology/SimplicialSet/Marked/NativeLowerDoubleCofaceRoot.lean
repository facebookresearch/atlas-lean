/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryUnitDoubleCoface
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerRootInverseUnit

/-!
# Genuine lower double-coface root sections in the original native source

Both positive original omitted vertices leave the same original root
fixed. The actual original double-coface unit equality therefore reads
the whole marked smaller root cone into the same genuine native source
coefficient after the original root/base transports. No native source
comparison is cancelled to prove this compatibility.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The complete original double-coface coefficient has exactly the same original global base-root target through
its two genuine positive-root equalities. -/
theorem nativeDoubleCofaceRootTarget (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (outer : Fin (n + 3)) (hout : 0 < outer) (inner : Fin (n + 2)) (hin : 0 < inner) :
    (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))).obj
        ((EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ outer).op σ))).obj
          (op (SimplicialThickening.mk (coneCofaceEmbedding inner (⊥ : Vertex.{u} n))))) =
      nativeBoundarySourceRootValue B (n + 2) σ :=
  (congrArg (fun i : Vertex.{u} (n + 1) =>
    (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))).obj
      ((EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ outer).op σ))).obj
        (op (SimplicialThickening.mk i)))) (coneCofaceEmbedding_root inner hin)).trans
    (nativeLowerCofaceRootTarget B σ outer hout (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))))

/-- The actual marked coface unit section at the original inner image root retains exactly its two original
root/base transports and unchanged outer coface-root section. -/
theorem nativeDoubleCofaceRootSection_transport (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (outer : Fin (n + 3)) (hout : 0 < outer) (inner : Fin (n + 2)) (hin : 0 < inner) :
    (coneImage (coneCofaceEmbedding inner).toOrderHom (⊥ : Vertex.{u} n) ≫
      (EnrichedLeftKan.universalHomEquiv
        (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ outer).op σ)))
        (coneDiagram (n + 1)) (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))
        (nativeBoundaryCofaceChartMap B (n + 1) σ outer)).app
          (op (SimplicialThickening.mk (coneCofaceEmbedding inner (⊥ : Vertex.{u} n))))) ≫
        eqToHom (nativeDoubleCofaceRootTarget B n σ outer hout inner hin) =
      (coneImage (coneCofaceEmbedding inner).toOrderHom (⊥ : Vertex.{u} n) ≫
        eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneWeight i) (coneCofaceEmbedding_root inner hin))) ≫
          nativeLowerCofaceRootSection B σ outer ≫
            eqToHom (nativeLowerCofaceRootTarget B σ outer hout
              (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))) := by
  let F := nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))
  let k := EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ outer).op σ))
  let U := EnrichedLeftKan.universalHomEquiv k (coneDiagram (n + 1)) F
    (nativeBoundaryCofaceChartMap B (n + 1) σ outer)
  let u := fun i : Vertex.{u} (n + 1) => U.app (op (SimplicialThickening.mk i))
  let a := coneImage (coneCofaceEmbedding inner).toOrderHom (⊥ : Vertex.{u} n)
  let v := coneCofaceEmbedding inner (⊥ : Vertex.{u} n)
  let h := coneCofaceEmbedding_root.{u} inner hin
  let hi := congrArg (fun i : Vertex.{u} (n + 1) => F.obj (k.obj (op (SimplicialThickening.mk i)))) h
  let ho := nativeLowerCofaceRootTarget B σ outer hout F
  let r := eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneWeight i) h)
  have hn : u v ≫ eqToHom hi = r ≫ u (⊥ : Vertex.{u} (n + 1)) := eqToHom_naturality u h
  have h₁ : (a ≫ u v) ≫ eqToHom (hi.trans ho) = ((a ≫ u v) ≫ eqToHom hi) ≫ eqToHom ho :=
    (congrArg (fun z => (a ≫ u v) ≫ z) (eqToHom_trans hi ho).symm).trans (Category.assoc _ _ _).symm
  have h₂ : (a ≫ u v) ≫ eqToHom hi = (a ≫ r) ≫ u (⊥ : Vertex.{u} (n + 1)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => a ≫ z) hn).trans (Category.assoc _ _ _).symm)
  exact h₁.trans ((congrArg (fun z => z ≫ eqToHom ho) h₂).trans (Category.assoc _ _ _))

private theorem coefficient_heq_same_target {A X Y T : Marked.{u}}
    (a : A ⟶ X) (b : A ⟶ Y) (hab : HEq a b) (hx : X = T) (hy : Y = T) :
    a ≫ eqToHom hx = b ≫ eqToHom hy := by
  cases hx
  cases hy
  exact (Category.comp_id a).trans ((eq_of_heq hab).trans (Category.comp_id b).symm)

/-- Both complete original positive double-coface root-cone sections agree in the same actual original native
all-face source coefficient after their genuine original root/base transports. -/
theorem nativeLowerDoubleCofaceRoot_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (j : Fin (n + 2)) (k : Fin (n + 3)) (h : j.castSucc < k) (hj : 0 < j) :
    (coneImage (coneCofaceEmbedding (k.pred h.ne_zero)).toOrderHom (⊥ : Vertex.{u} n) ≫
      eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneWeight i)
        (coneCofaceEmbedding_root (k.pred h.ne_zero)
          (lt_of_lt_of_le hj ((Fin.le_pred_iff h.ne_zero).mpr (Fin.castSucc_lt_iff_succ_le.mp h)))))) ≫
        nativeLowerCofaceRootSection B σ j.castSucc ≫
          eqToHom (nativeLowerCofaceRootTarget B σ j.castSucc hj
            (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))) =
      (coneImage (coneCofaceEmbedding j).toOrderHom (⊥ : Vertex.{u} n) ≫
        eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneWeight i) (coneCofaceEmbedding_root j hj))) ≫
          nativeLowerCofaceRootSection B σ k ≫
            eqToHom (nativeLowerCofaceRootTarget B σ k
              ((show (0 : Fin (n + 3)) < j.castSucc from hj).trans h)
              (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))) := by
  have hp : 0 < k.pred h.ne_zero :=
    lt_of_lt_of_le hj ((Fin.le_pred_iff h.ne_zero).mpr (Fin.castSucc_lt_iff_succ_le.mp h))
  have hk : 0 < k := (show (0 : Fin (n + 3)) < j.castSucc from hj).trans h
  have hc := nativeBoundaryCofaceSections_double_heq B n σ j k h
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
  have ht := coefficient_heq_same_target _ _ hc
    (nativeDoubleCofaceRootTarget B n σ j.castSucc hj (k.pred h.ne_zero) hp)
    (nativeDoubleCofaceRootTarget B n σ k hk j hj)
  exact (nativeDoubleCofaceRootSection_transport B n σ j.castSucc hj (k.pred h.ne_zero) hp).symm.trans
    (ht.trans (nativeDoubleCofaceRootSection_transport B n σ k hk j hj))

end SSet.Marked
