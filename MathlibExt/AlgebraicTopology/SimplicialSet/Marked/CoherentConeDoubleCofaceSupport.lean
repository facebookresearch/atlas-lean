/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeLowerRootFace

/-!
# Whole original double-coface marked cone support

Both original composite cofaces have the same lifted ordinal image.
Their image omits exactly the two original omitted vertices. The
actual supported cone subcomplex is therefore the full intersection
of the same two lower coordinate faces in every scalar degree,
with the original maximum marking and original cone image retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original full ordered double coface acts by its unchanged composed lifted ordinal embedding. -/
def coneDoubleCofaceEmbedding {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3)) (h : j.castSucc < k) :
    Vertex.{u} n ↪o Vertex.{u} (n + 2) :=
  (coneCofaceEmbedding (k.pred h.ne_zero)).comp (coneCofaceEmbedding j.castSucc)

/-- The original double-coface simplicial identity retains the entire same lifted ordinal embedding on the
alternative original coface composite. -/
theorem coneDoubleCofaceEmbedding_eq {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3)) (h : j.castSucc < k) :
    coneDoubleCofaceEmbedding.{u} j k h = (coneCofaceEmbedding j).comp (coneCofaceEmbedding k) := by
  apply DFunLike.ext
  intro x
  apply ULift.ext
  exact congrArg (fun f : ⦋n⦌ ⟶ ⦋n + 2⦌ => f.toOrderHom x.down) (SimplexCategory.δ_comp_δ' h).symm

/-- The original outer coface carries the actual predecessor of the second omitted vertex to precisely that same
original second vertex. -/
theorem coneDoubleCoface_outer_pred {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3)) (h : j.castSucc < k) :
    coneCofaceEmbedding.{u} j.castSucc (ULift.up (k.pred h.ne_zero)) = ULift.up k := by
  apply ULift.ext
  have hp : j ≤ k.pred h.ne_zero := (Fin.le_pred_iff h.ne_zero).mpr (Fin.castSucc_lt_iff_succ_le.mp h)
  exact (Fin.succAbove_of_le_castSucc j.castSucc _ (Fin.castSucc_le_castSucc_iff.mpr hp)).trans
    (Fin.succ_pred k h.ne_zero)

/-- The complete original double-coface range consists exactly of all original vertices except its two original
omitted vertices. -/
theorem mem_coneDoubleCofaceEmbedding_range {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3))
    (h : j.castSucc < k) (x : Vertex.{u} (n + 2)) :
    x ∈ Set.range (coneDoubleCofaceEmbedding j k h) ↔ x ≠ ULift.up j.castSucc ∧ x ≠ ULift.up k := by
  let f := coneCofaceEmbedding.{u} j.castSucc
  let g := coneCofaceEmbedding.{u} (k.pred h.ne_zero)
  constructor
  · rintro ⟨a, rfl⟩
    have hx : coneDoubleCofaceEmbedding j k h a ∈ Set.range f := ⟨g a, rfl⟩
    have hy : coneDoubleCofaceEmbedding j k h a ∈ Set.range (coneCofaceEmbedding k) :=
      ⟨coneCofaceEmbedding j a, congrArg (fun p => p a) (coneDoubleCofaceEmbedding_eq j k h).symm⟩
    exact ⟨(mem_coneCofaceEmbedding_range j.castSucc _).mp hx, (mem_coneCofaceEmbedding_range k _).mp hy⟩
  · rintro ⟨hj, hk⟩
    obtain ⟨y, hy⟩ := (mem_coneCofaceEmbedding_range j.castSucc x).mpr hj
    have hyp : y ≠ ULift.up (k.pred h.ne_zero) := by
      intro he
      subst y
      exact hk (hy.symm.trans (coneDoubleCoface_outer_pred j k h))
    obtain ⟨a, ha⟩ := (mem_coneCofaceEmbedding_range (k.pred h.ne_zero) y).mpr hyp
    exact ⟨a, (congrArg f ha).trans hy⟩

/-- The entire original supported double-coface cone image is precisely the full intersection of both original lower
coordinate faces in every original scalar degree. -/
theorem coneDoubleCofaceSupportedSubcomplex {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3))
    (h : j.castSucc < k) (i : Vertex.{u} n) :
    coneSupportedSubcomplex (coneDoubleCofaceEmbedding j k h) i =
      coneCoordinateFace (coneDoubleCofaceEmbedding j k h i) (ULift.up j.castSucc) false ⊓
        coneCoordinateFace (coneDoubleCofaceEmbedding j k h i) (ULift.up k) false := by
  ext q x
  change (∀ t, ∀ v ∈ (x.obj t).vertices, v ∈ Set.range (coneDoubleCofaceEmbedding j k h)) ↔
    (∀ t, (ULift.up j.castSucc ∈ (x.obj t).vertices) ↔ false = true) ∧
      (∀ t, (ULift.up k ∈ (x.obj t).vertices) ↔ false = true)
  simp only [mem_coneDoubleCofaceEmbedding_range, Bool.false_eq_true, iff_false]
  constructor
  · intro hx
    exact ⟨fun t ht => (hx t _ ht).1 rfl, fun t ht => (hx t _ ht).2 rfl⟩
  · rintro ⟨hj, hk⟩ t v hv
    exact ⟨fun he => hj t (he ▸ hv), fun he => hk t (he ▸ hv)⟩

/-- The complete original smaller cone is genuinely isomorphic as a marked simplicial set to the full original
two-lower-face intersection, with the same inherited maximum marking. -/
def coneDoubleCofaceMarkedIso {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3))
    (h : j.castSucc < k) (i : Vertex.{u} n) :
    coneWeight i ≅ comap (coneWeight (coneDoubleCofaceEmbedding j k h i))
      (coneCoordinateFace (coneDoubleCofaceEmbedding j k h i) (ULift.up j.castSucc) false ⊓
        coneCoordinateFace (coneDoubleCofaceEmbedding j k h i) (ULift.up k) false).ι :=
  coneEmbeddingSupportedIso (coneDoubleCofaceEmbedding j k h) i ≪≫
    eqToIso (congrArg (fun A : (nerve (ConeSubset (coneDoubleCofaceEmbedding j k h i))).Subcomplex =>
      comap (coneWeight (coneDoubleCofaceEmbedding j k h i)) A.ι) (coneDoubleCofaceSupportedSubcomplex j k h i))

/-- The same original marked double-coface intersection isomorphism retains exactly the entire unchanged original
cone image as its full attaching composite. -/
theorem coneDoubleCofaceMarkedIso_inclusion {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3))
    (h : j.castSucc < k) (i : Vertex.{u} n) :
    (coneDoubleCofaceMarkedIso j k h i).hom ≫
      comapHom (coneWeight (coneDoubleCofaceEmbedding j k h i))
        (coneCoordinateFace (coneDoubleCofaceEmbedding j k h i) (ULift.up j.castSucc) false ⊓
          coneCoordinateFace (coneDoubleCofaceEmbedding j k h i) (ULift.up k) false).ι =
        coneImage (coneDoubleCofaceEmbedding j k h).toOrderHom i := by
  let f := coneDoubleCofaceEmbedding.{u} j k h
  let e := coneEmbeddingSupportedIso f i
  let hs := coneDoubleCofaceSupportedSubcomplex j k h i
  let z := fun A : (nerve (ConeSubset (f i))).Subcomplex => comapHom (coneWeight (f i)) A.ι
  have ht : eqToHom (congrArg (fun A : (nerve (ConeSubset (f i))).Subcomplex => comap (coneWeight (f i)) A.ι) hs) ≫
      z (coneCoordinateFace (f i) (ULift.up j.castSucc) false ⊓ coneCoordinateFace (f i) (ULift.up k) false) =
        z (coneSupportedSubcomplex f i) := (eqToHom_naturality z hs).symm.trans (Category.comp_id _)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => e.hom ≫ a) ht).trans (coneEmbeddingSupportedIso_inclusion f i))

/-- Omitting two positive original vertices leaves exactly the same original root fixed. -/
theorem coneDoubleCofaceEmbedding_root {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3))
    (h : j.castSucc < k) (hj : 0 < j) :
    coneDoubleCofaceEmbedding.{u} j k h (⊥ : Vertex.{u} n) = (⊥ : Vertex.{u} (n + 2)) := by
  have hp : 0 < k.pred h.ne_zero :=
    lt_of_lt_of_le hj ((Fin.le_pred_iff h.ne_zero).mpr (Fin.castSucc_lt_iff_succ_le.mp h))
  exact (congrArg (coneCofaceEmbedding j.castSucc) (coneCofaceEmbedding_root (k.pred h.ne_zero) hp)).trans
    (coneCofaceEmbedding_root j.castSucc hj)

end SSet.Marked.CoherentWeight
