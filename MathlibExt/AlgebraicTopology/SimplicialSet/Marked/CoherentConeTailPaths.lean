/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailVertices
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# Original whole coherent paths in the positive tail

A path whose original first endpoint is positive cannot contain the
new root. It is therefore exactly the image of its full original
zeroth-coface preimage. The actual inverse commutes with the original
path identity and union composition. Nerves and maximum marking keep
all scalar operators and whole coherent Hom parameters.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq
private instance {n : ℕ} (i j : Vertex.{u} n) (p q : SimplicialThickening.Path i j) : Subsingleton (p ⟶ q) :=
  ⟨fun _ _ => InducedCategory.Hom.ext (Subsingleton.elim _ _)⟩

/-- The original tail path is read by the whole preimage of its original coherent subset. -/
def coneTailPathPreimage {n : ℕ} (i j : Vertex.{u} n)
    (p : SimplicialThickening.Path (coneTailEmbedding n i) (coneTailEmbedding n j)) :
    SimplicialThickening.Path i j where
  I := (coneTailEmbedding n) ⁻¹' p.I
  left := p.left
  right := p.right
  left_le l hl := (coneTailEmbedding n).le_iff_le.mp (p.left_le (coneTailEmbedding n l) hl)
  le_right l hl := (coneTailEmbedding n).le_iff_le.mp (p.le_right (coneTailEmbedding n l) hl)

/-- The entire original path is recovered from its actual native coface image. -/
theorem coneTailPathPreimage_image {n : ℕ} (i j : Vertex.{u} n) (p : SimplicialThickening.Path i j) :
    coneTailPathPreimage i j
        ((SimplicialThickening.functorMap (coneTailEmbedding n).toOrderHom
          (SimplicialThickening.mk i) (SimplicialThickening.mk j)).obj p) = p := by
  apply SimplicialThickening.Path.ext
  ext z
  change coneTailEmbedding n z ∈ (coneTailEmbedding n) '' p.I ↔ z ∈ p.I
  constructor
  · rintro ⟨w, hw, h⟩
    exact (coneTailEmbedding n).injective h ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Every entire original positive tail path is recovered from its whole original preimage. -/
theorem coneTailPathImage_preimage {n : ℕ} (i j : Vertex.{u} n)
    (p : SimplicialThickening.Path (coneTailEmbedding n i) (coneTailEmbedding n j)) :
    (SimplicialThickening.functorMap (coneTailEmbedding n).toOrderHom
      (SimplicialThickening.mk i) (SimplicialThickening.mk j)).obj (coneTailPathPreimage i j p) = p := by
  apply SimplicialThickening.Path.ext
  ext z
  change z ∈ (coneTailEmbedding n) '' ((coneTailEmbedding n) ⁻¹' p.I) ↔ z ∈ p.I
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    have hpos : (⊥ : Vertex.{u} (n + 1)) < z :=
      (coneTailEmbedding_positive i).trans_le (p.left_le z hz)
    obtain ⟨w, hw⟩ := (mem_coneCofaceEmbedding_range (0 : Fin (n + 2)) z).mpr (ne_of_gt hpos)
    refine ⟨w, ?_, hw⟩
    change coneTailEmbedding n w ∈ p.I
    exact hw.symm ▸ hz

/-- The original full path preimage preserves each native coherent subset inclusion. -/
def coneTailPathPreimageFunctor {n : ℕ} (i j : Vertex.{u} n) :
    SimplicialThickening.Path (coneTailEmbedding n i) (coneTailEmbedding n j) ⥤
      SimplicialThickening.Path i j where
  obj := coneTailPathPreimage i j
  map f := ⟨⟨⟨Set.preimage_mono f.1.1.1⟩⟩⟩

/-- The actual native zeroth-coface Hom map is a strict isomorphism of whole original path nerves. -/
def coneTailPathNerveIso {n : ℕ} (i j : Vertex.{u} n) :
    nerve (SimplicialThickening.Path i j) ≅
      nerve (SimplicialThickening.Path (coneTailEmbedding n i) (coneTailEmbedding n j)) where
  hom := nerveMap (SimplicialThickening.functorMap (coneTailEmbedding n).toOrderHom
    (SimplicialThickening.mk i) (SimplicialThickening.mk j))
  inv := nerveMap (coneTailPathPreimageFunctor i j)
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    refine CategoryTheory.Functor.ext (fun t => coneTailPathPreimage_image i j (x.obj t))
      (fun _ _ _ => Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    refine CategoryTheory.Functor.ext (fun t => coneTailPathImage_preimage i j (x.obj t))
      (fun _ _ _ => Subsingleton.elim _ _)

/-- The whole original maximal marking is carried by the same strict native tail-path isomorphism. -/
def coneTailPathMarkedIso {n : ℕ} (i j : Vertex.{u} n) :
    max (nerve (SimplicialThickening.Path i j)) ≅
      max (nerve (SimplicialThickening.Path (coneTailEmbedding n i) (coneTailEmbedding n j))) :=
  maximal.mapIso (coneTailPathNerveIso i j)

/-- The entire forward marked Hom map is exactly the original native coface index Hom map. -/
theorem coneTailPathMarkedIso_hom {n : ℕ} (i j : Vertex.{u} n) :
    (coneTailPathMarkedIso i j).hom =
      maximal.map ((indexMap (coneTailEmbedding n).toOrderHom).map
        (SimplicialThickening.mk i) (SimplicialThickening.mk j)) := rfl

/-- Whole original preimages preserve the same coherent identity path. -/
theorem coneTailPathPreimage_id {n : ℕ} (i : Vertex.{u} n) :
    coneTailPathPreimage i i (𝟙 (SimplicialThickening.mk (coneTailEmbedding n i))) =
      𝟙 (SimplicialThickening.mk i) := by
  apply SimplicialThickening.Path.ext
  ext z
  change coneTailEmbedding n z = coneTailEmbedding n i ↔ z = i
  exact (coneTailEmbedding n).injective.eq_iff

/-- Whole original preimages preserve the actual native union composite of both full paths. -/
theorem coneTailPathPreimage_comp {n : ℕ} (i j k : Vertex.{u} n)
    (p : SimplicialThickening.Path (coneTailEmbedding n i) (coneTailEmbedding n j))
    (q : SimplicialThickening.Path (coneTailEmbedding n j) (coneTailEmbedding n k)) :
    coneTailPathPreimage i k
        ((show SimplicialThickening.mk (coneTailEmbedding n i) ⟶ SimplicialThickening.mk (coneTailEmbedding
          n j) from p) ≫
          (show SimplicialThickening.mk (coneTailEmbedding n j) ⟶ SimplicialThickening.mk (coneTailEmbedding
            n k) from q)) =
      (show SimplicialThickening.mk i ⟶ SimplicialThickening.mk j from coneTailPathPreimage i j p) ≫
        (show SimplicialThickening.mk j ⟶ SimplicialThickening.mk k from coneTailPathPreimage j k q) := by
  apply SimplicialThickening.Path.ext
  rfl

end SSet.Marked.CoherentWeight
