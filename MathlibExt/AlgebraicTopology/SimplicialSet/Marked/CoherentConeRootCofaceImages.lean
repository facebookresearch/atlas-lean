/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeLowerRootFace

/-!
# Original marked coface images at the unchanged root

Every positive original coface fixes the original root. Its entire
cone-image map therefore has the same genuine original root transport.
Consecutive such maps retain exactly the original composed ordinal
image and its root transport, using the original whole cone-image law.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original full marked cone image of a positive coface enters the same original root coefficient after
precisely its genuine original root equality. -/
def coneRootCofaceImage {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneWeight (⊥ : Vertex.{u} n) ⟶ coneWeight (⊥ : Vertex.{u} (n + 1)) :=
  coneImage (coneCofaceEmbedding j).toOrderHom (⊥ : Vertex.{u} n) ≫
    eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneWeight i) (coneCofaceEmbedding_root j hj))

/-- The original whole lower-root coordinate isomorphism retains precisely its same original root-coface image as
its full inclusion. -/
theorem coneLowerRootFaceIso_rootImage {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (coneLowerRootFaceIso.{u} j hj).hom ≫ coneLowerRootFaceInclusion j = coneRootCofaceImage j hj :=
  coneLowerRootFaceIso_inclusion j hj

/-- The two actual original root-coface images compose to exactly their original whole composed ordinal cone image
and original composite root transport. -/
theorem coneRootCofaceImage_comp {n : ℕ} (inner : Fin (n + 2)) (hin : 0 < inner)
    (outer : Fin (n + 3)) (hout : 0 < outer) :
    coneRootCofaceImage.{u} inner hin ≫ coneRootCofaceImage outer hout =
      coneImage ((coneCofaceEmbedding outer).toOrderHom.comp (coneCofaceEmbedding inner).toOrderHom)
          (⊥ : Vertex.{u} n) ≫
        eqToHom (congrArg (fun i : Vertex.{u} (n + 2) => coneWeight i)
          ((congrArg (coneCofaceEmbedding outer) (coneCofaceEmbedding_root inner hin)).trans
            (coneCofaceEmbedding_root outer hout))) := by
  let f := (coneCofaceEmbedding.{u} inner).toOrderHom
  let g := (coneCofaceEmbedding.{u} outer).toOrderHom
  let hi := coneCofaceEmbedding_root.{u} inner hin
  let ho := congrArg (fun i : Vertex.{u} (n + 2) => coneWeight i) (coneCofaceEmbedding_root outer hout)
  let h₀ := congrArg (fun i : Vertex.{u} (n + 1) => coneWeight i) hi
  let h₁ := congrArg (fun i : Vertex.{u} (n + 1) => coneWeight (g i)) hi
  let a := coneImage f (⊥ : Vertex.{u} n)
  let b := coneImage g (⊥ : Vertex.{u} (n + 1))
  let c := coneImage g (f (⊥ : Vertex.{u} n))
  have ht : eqToHom h₀ ≫ b = c ≫ eqToHom h₁ :=
    (eqToHom_naturality (fun i : Vertex.{u} (n + 1) => coneImage g i) hi).symm
  have ha : (a ≫ eqToHom h₀) ≫ (b ≫ eqToHom ho) = a ≫ ((eqToHom h₀ ≫ b) ≫ eqToHom ho) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z => a ≫ z) (Category.assoc _ _ _).symm)
  have hb : a ≫ ((c ≫ eqToHom h₁) ≫ eqToHom ho) = (a ≫ c) ≫ (eqToHom h₁ ≫ eqToHom ho) :=
    (congrArg (fun z => a ≫ z) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm
  have hc : a ≫ c = coneImage (g.comp f) (⊥ : Vertex.{u} n) := coneImage_comp f g _
  exact ha.trans
    ((congrArg (fun z => a ≫ (z ≫ eqToHom ho)) ht).trans
      (hb.trans ((congrArg (fun z => z ≫ (eqToHom h₁ ≫ eqToHom ho)) hc).trans
        (congrArg (fun z => coneImage (g.comp f) (⊥ : Vertex.{u} n) ≫ z) (eqToHom_trans h₁ ho)))))

/-- Equal original ordinal maps fixing the same original root retain exactly the same whole marked cone-image map
with their genuine root transports. -/
theorem coneRootConeImage_congr {n m : ℕ} (f g : Vertex.{u} n →o Vertex.{u} m)
    (hf : f ⊥ = ⊥) (hg : g ⊥ = ⊥) (h : f = g) :
    coneImage f (⊥ : Vertex.{u} n) ≫ eqToHom (congrArg (fun i : Vertex.{u} m => coneWeight i) hf) =
      coneImage g (⊥ : Vertex.{u} n) ≫ eqToHom (congrArg (fun i : Vertex.{u} m => coneWeight i) hg) := by
  cases h
  rfl

end SSet.Marked.CoherentWeight
