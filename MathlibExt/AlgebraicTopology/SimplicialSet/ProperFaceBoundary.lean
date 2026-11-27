/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.Matching
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc

/-!
# The simplex boundary as a colimit of proper faces

The standard simplex boundary is the colimit of the standard simplices
indexed by the opposite proper-face matching category. The face inclusions
agree with their ordinal maps, and compatible maps from all proper faces
extend uniquely to the boundary.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.ProperFaceBoundary

private theorem properFace_not_surjective {n : ℕ} (a : SimplicialObject.matchingIndex n) :
    ¬ Function.Surjective a.obj.hom.unop.toOrderHom := by
  intro h
  let _ : Epi a.obj.hom.unop := (SimplexCategory.epi_iff_surjective (f := a.obj.hom.unop)).mpr h
  exact (Nat.not_le_of_lt a.property.2) (SimplexCategory.len_le_of_epi a.obj.hom.unop)

/-- Each original proper injection factors through the actual inner boundary, with no chosen face
omitted. -/
def properFaceBoundaryInclusion {n : ℕ} (a : SimplicialObject.matchingIndex n) :
    (SSet.stdSimplex.{u}.obj a.obj.right.unop) ⟶ (SSet.boundary.{u} n : SSet.{u}) :=
  SSet.Subcomplex.lift (SSet.stdSimplex.map a.obj.hom.unop) (by
    rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff, SSet.yonedaEquiv_map]
    change ¬ Function.Surjective a.obj.hom.unop.toOrderHom
    exact properFace_not_surjective a)

/-- The inclusion in the original simplex is exactly the prescribed ordinal map. -/
@[reassoc]
theorem properFaceBoundaryInclusion_ι {n : ℕ} (a : SimplicialObject.matchingIndex n) :
    properFaceBoundaryInclusion.{u} a ≫ (SSet.boundary.{u} n).ι =
      SSet.stdSimplex.map a.obj.hom.unop := SSet.Subcomplex.lift_ι _ _

/-- Every proper-face morphism retains the original boundary inclusion equation. -/
theorem properFaceBoundaryInclusion_naturality {n : ℕ}
    {a b : SimplicialObject.matchingIndex n} (g : a ⟶ b) :
    SSet.stdSimplex.map g.hom.right.unop ≫ properFaceBoundaryInclusion.{u} a =
      properFaceBoundaryInclusion.{u} b := by
  apply (cancel_mono (SSet.boundary.{u} n).ι).mp
  rw [Category.assoc, properFaceBoundaryInclusion_ι, properFaceBoundaryInclusion_ι,
    ← SSet.stdSimplex.map_comp]
  apply SSet.stdSimplex.congr_map
  exact congrArg Quiver.Hom.unop (StructuredArrow.w g.hom)

/-- The entire opposite matching index is the actual inner proper-simplex face diagram. -/
def properFaceSimplexDiagram (n : ℕ) : (SimplicialObject.matchingIndex n)ᵒᵖ ⥤ SSet.{u} where
  obj a := SSet.stdSimplex.obj a.unop.obj.right.unop
  map g := SSet.stdSimplex.map g.unop.hom.right.unop
  map_id a := by
    change SSet.stdSimplex.map (𝟙 a.unop.obj.right.unop) = 𝟙 _
    exact SSet.stdSimplex.map_id _
  map_comp g h := by
    rw [← SSet.stdSimplex.map_comp]
    rfl

/-- The canonical cocone includes every actual proper injection into the same boundary. -/
def properFaceBoundaryCocone (n : ℕ) : Cocone (properFaceSimplexDiagram.{u} n) where
  pt := (SSet.boundary.{u} n : SSet.{u})
  ι :=
    { app := fun a => properFaceBoundaryInclusion a.unop
      naturality := by
        intro a b g
        change SSet.stdSimplex.map g.unop.hom.right.unop ≫
          properFaceBoundaryInclusion b.unop =
            properFaceBoundaryInclusion a.unop ≫ 𝟙 _
        rw [Category.comp_id]
        exact properFaceBoundaryInclusion_naturality g.unop }

private abbrev cofaceIndex (n : ℕ) (i : Fin (n + 2)) : SimplicialObject.matchingIndex (n + 1) :=
  ⟨StructuredArrow.mk (SimplexCategory.δ i).op,
    ⟨by change Mono (SimplexCategory.δ i); infer_instance, by change n < n + 1; omega⟩⟩

private def properFaceIndexHom {n : ℕ} (a b : SimplicialObject.matchingIndex n)
    (g : b.obj.right.unop ⟶ a.obj.right.unop)
    (hg : g ≫ a.obj.hom.unop = b.obj.hom.unop) : a ⟶ b :=
  ObjectProperty.homMk (StructuredArrow.homMk g.op (by
    apply Quiver.Hom.unop_inj
    exact hg))

private theorem cofaceInclusion (n : ℕ) (i : Fin (n + 2)) :
    properFaceBoundaryInclusion.{u} (cofaceIndex n i) = SSet.boundary.ι.{u} i := by
  apply (cancel_mono (SSet.boundary.{u} (n + 1)).ι).mp
  rw [properFaceBoundaryInclusion_ι, SSet.boundary.ι_ι]
  rfl

private theorem cofacePairEquation (n : ℕ) (i j : Fin (n + 3)) (hij : i < j) :
    SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij)) ≫ SimplexCategory.δ i =
      SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij)) ≫ SimplexCategory.δ j := by
  have h : (i.castPred (Fin.ne_last_of_lt hij)).castSucc < j := by simpa using hij
  simpa using (SimplexCategory.δ_comp_δ' h).symm

private abbrev cofacePairIndex (n : ℕ) (i j : Fin (n + 3)) (hij : i < j) :
    SimplicialObject.matchingIndex (n + 2) :=
  ⟨StructuredArrow.mk
      (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij)) ≫ SimplexCategory.δ i).op,
    ⟨by change Mono (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij)) ≫ SimplexCategory.δ i)
        infer_instance,
      by change n < n + 2; omega⟩⟩

/-- Every full proper-face section family descends uniquely to the actual inner boundary. -/
theorem properFaceBoundary_sections (n : ℕ) (Q : SSet.{u})
    (s : ∀ a : SimplicialObject.matchingIndex n, SSet.stdSimplex.obj a.obj.right.unop ⟶ Q)
    (hs : ∀ {a b : SimplicialObject.matchingIndex n} (g : a ⟶ b),
      SSet.stdSimplex.map g.hom.right.unop ≫ s a = s b) :
    ∃! f : (SSet.boundary.{u} n : SSet.{u}) ⟶ Q,
      ∀ a, properFaceBoundaryInclusion a ≫ f = s a := by
  cases n with
  | zero =>
      have h0 : IsInitial (SSet.boundary.{u} 0 : SSet.{u}) := by
        simpa only [SSet.boundary_zero] using
            (SSet.Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u})))
      refine ⟨h0.to Q, ?_, ?_⟩
      · intro a
        exact False.elim (Nat.not_lt_zero _ a.property.2)
      · intro f hf
        exact h0.hom_ext _ _
  | succ n =>
      let faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ Q) := fun i => s (cofaceIndex n i)
      have compatible : SSet.boundary.IsCompatible faces := by
        cases n with
        | zero => trivial
        | succ t =>
            intro i j hij
            let a := cofacePairIndex t i j hij
            let gi : cofaceIndex (t + 1) i ⟶ a := properFaceIndexHom _ _
              (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))) rfl
            let gj : cofaceIndex (t + 1) j ⟶ a := properFaceIndexHom _ _
              (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij)))
                  (cofacePairEquation t i j hij).symm
            exact (hs gi).trans (hs gj).symm
      let f := compatible.desc
      have fac (a : SimplicialObject.matchingIndex (n + 1)) :
          properFaceBoundaryInclusion.{u} a ≫ f = s a := by
        obtain ⟨i, theta, htheta⟩ := SimplexCategory.eq_comp_δ_of_not_surjective
          a.obj.hom.unop (properFace_not_surjective a)
        let q : cofaceIndex n i ⟶ a := properFaceIndexHom _ _ theta htheta.symm
        have inclusion : properFaceBoundaryInclusion.{u} a = SSet.stdSimplex.map theta ≫
            SSet.boundary.ι i := by
          apply (cancel_mono (SSet.boundary.{u} (n + 1)).ι).mp
          rw [properFaceBoundaryInclusion_ι, Category.assoc, SSet.boundary.ι_ι]
          change SSet.stdSimplex.map a.obj.hom.unop =
            SSet.stdSimplex.map theta ≫ SSet.stdSimplex.map (SimplexCategory.δ i)
          rw [← SSet.stdSimplex.map_comp, ← htheta]
        rw [inclusion, Category.assoc, SSet.boundary.IsCompatible.ι_desc]
        exact hs q
      refine ⟨f, fac, ?_⟩
      intro g hg
      apply SSet.boundary.hom_ext
      intro i
      rw [← cofaceInclusion, hg, fac]

/-- The whole proper-injection diagram is a genuine colimit presentation of the inner boundary. -/
def properFaceBoundaryIsColimit (n : ℕ) : IsColimit (properFaceBoundaryCocone.{u} n) := by
  let data (c : Cocone (properFaceSimplexDiagram.{u} n)) :=
    properFaceBoundary_sections n c.pt (fun a => c.ι.app (op a))
      (fun g => by
        simpa only [properFaceSimplexDiagram, Quiver.Hom.unop_op] using c.w g.op)
  refine
    { desc := fun c => Classical.choose (data c)
      fac := ?_
      uniq := ?_ }
  · intro c a
    exact (Classical.choose_spec (data c)).1 a.unop
  · intro c f hf
    exact (Classical.choose_spec (data c)).2 f (fun a => hf (op a))

end SSet.ProperFaceBoundary
