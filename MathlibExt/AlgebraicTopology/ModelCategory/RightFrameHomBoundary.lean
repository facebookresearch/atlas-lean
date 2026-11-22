/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.RightFrameHomKan
public import MathlibExt.AlgebraicTopology.ModelCategory.BrownSourceFunctor
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Full-boundary lifting for the original right resolution Hom

Every map of a complete simplex boundary into the right resolution Hom gives
the actual cone on all proper face maps.  A coefficient lift against the full
matching fibration extends that same boundary.  Consequently original trivial
cofibrations give trivial Kan fibrations of right Hom complexes.  Brown's
factorization then gives weak invariance for the original cofibrant sources.

Only the coefficient model structure and its finite matching limits are used.
The simplicial diagram is not supplied with a mapping-space preservation law,
and no model structure on its diagram category is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MorphismProperty Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.RightFrameHomBoundary

/-- The original source arrow acts by precomposition in every right-Hom degree. -/
abbrev precomp {C : Type u} [Category.{v} C] {X X' : C} (i : X ⟶ X')
    (B : SimplicialObject C) :
    ResolutionHomComplex.right X' B ⟶ ResolutionHomComplex.right X B :=
  ResolutionHomComplex.precomp ((CosimplicialObject.const C).map i) B

/-- Each original proper face has its original label in the complete boundary. -/
def boundaryLabel (n : ℕ) (a : SimplexCategory.PartialMatching.Index n Finset.univ) :
    (SSet.boundary.{v} n : SSet.{v}).obj (SimplexCategory.PartialMatching.target a) :=
  ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.PartialMatching.arrow a).unop,
    by
      rw [SSet.boundary_obj_eq_univ _ n (SimplexCategory.PartialMatching.target_lt a)]
      exact Set.mem_univ _⟩

/-- The unchanged matching comparison gives the same original boundary simplex. -/
theorem boundaryLabel_comparison (n : ℕ)
    {a b : SimplexCategory.PartialMatching.Index n Finset.univ} (f : a ⟶ b) :
    (SSet.boundary.{v} n : SSet.{v}).map (SimplexCategory.PartialMatching.comparison f)
      (boundaryLabel n a) = boundaryLabel n b := by
  apply Subtype.ext
  change SSet.stdSimplex.objEquiv.symm
    ((SimplexCategory.PartialMatching.comparison f).unop ≫
      (SimplexCategory.PartialMatching.arrow a).unop) = _
  exact congrArg SSet.stdSimplex.objEquiv.symm
    (congrArg Quiver.Hom.unop (SimplexCategory.PartialMatching.arrow_comparison f))

variable {C : Type u} [Category.{v} C]

/-- The complete original boundary map gives all of its actual Hom coordinates. -/
def boundaryCoordinate (X : C) (B : SimplicialObject C) (n : ℕ)
    (z : (SSet.boundary.{v} n : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (a : SimplexCategory.PartialMatching.Index n Finset.univ) :
    X ⟶ B.obj (SimplexCategory.PartialMatching.target a) :=
  z.app (SimplexCategory.PartialMatching.target a) (boundaryLabel n a)

/-- Every coordinate retains the original matching naturality triangle. -/
theorem boundaryCoordinate_naturality (X : C) (B : SimplicialObject C) (n : ℕ)
    (z : (SSet.boundary.{v} n : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    {a b : SimplexCategory.PartialMatching.Index n Finset.univ} (f : a ⟶ b) :
    boundaryCoordinate X B n z b = boundaryCoordinate X B n z a ≫
      B.map (SimplexCategory.PartialMatching.comparison f) := by
  have hl := congrArg (fun x => z.app (SimplexCategory.PartialMatching.target b) x)
    (boundaryLabel_comparison n f)
  have hn := z.naturality_apply (SimplexCategory.PartialMatching.comparison f)
    (boundaryLabel n a)
  exact (hl.symm.trans hn).trans
    (ResolutionHomComplex.right_map_apply X B (SimplexCategory.PartialMatching.comparison f)
      (boundaryCoordinate X B n z a))

/-- The actual full-boundary Hom map gives the cone on every original proper face. -/
def boundaryHomCone (X : C) (B : SimplicialObject C) (n : ℕ)
    (z : (SSet.boundary.{v} n : SSet.{v}) ⟶ ResolutionHomComplex.right X B) :
    Cone (PartialFaceMatching.diagram B n Finset.univ) where
  pt := X
  π.app a := boundaryCoordinate X B n z a
  π.naturality {_a _b} f :=
    (Category.id_comp _).trans (boundaryCoordinate_naturality X B n z f)

variable [HasFiniteLimits C]

/-- The whole original full-boundary cone maps to the actual finite matching limit. -/
def boundaryHomMap (X : C) (B : SimplicialObject C) (n : ℕ)
    (z : (SSet.boundary.{v} n : SSet.{v}) ⟶ ResolutionHomComplex.right X B) :
    X ⟶ PartialFaceMatching.object B n Finset.univ :=
  limit.lift _ (boundaryHomCone X B n z)

/-- Every original matching projection recovers the actual full-boundary coordinate. -/
@[reassoc]
theorem boundaryHomMap_π (X : C) (B : SimplicialObject C) (n : ℕ)
    (z : (SSet.boundary.{v} n : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (a : SimplexCategory.PartialMatching.Index n Finset.univ) :
    boundaryHomMap X B n z ≫ limit.π (PartialFaceMatching.diagram B n Finset.univ) a =
      z.app (SimplexCategory.PartialMatching.target a) (boundaryLabel n a) :=
  limit.lift_π _ a

/-- The actual matching lift extends the unchanged original full boundary, including degree zero. -/
theorem homSimplex_boundary_extension (X : C) (B : SimplicialObject C) (n : ℕ)
    (z : (SSet.boundary.{v} n : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (f : X ⟶ B.obj (op ⦋n⦌))
    (hf : f ≫ PartialFaceMatching.map B n Finset.univ = boundaryHomMap X B n z) :
    (SSet.boundary.{v} n).ι ≫ RightFrameHornGeometry.homSimplex X B n f = z := by
  cases n with
  | zero => exact SSet.boundary.hom_ext₀
  | succ n =>
    apply SSet.boundary.hom_ext
    intro j
    apply SSet.yonedaEquiv.injective
    let a := SimplexCategory.PartialMatching.faceMk Finset.univ j (Finset.mem_univ j)
    have h := congrArg
      (fun q => q ≫ limit.π (PartialFaceMatching.diagram B (n + 1) Finset.univ) a) hf
    rw [Category.assoc, PartialFaceMatching.map_π, boundaryHomMap_π] at h
    change f ≫ B.map (SimplexCategory.δ j).op =
      z.app (op ⦋n⦌) (boundaryLabel (n + 1) a) at h
    change (RightFrameHornGeometry.homSimplex X B (n + 1) f).app (op ⦋n⦌)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ j)) =
      z.app (op ⦋n⦌) (boundaryLabel (n + 1) a)
    exact ((SSet.yonedaEquiv_symm_app_objEquiv_symm
      (X := ResolutionHomComplex.right X B) f (SimplexCategory.δ j)).trans
        (ResolutionHomComplex.right_map_apply X B (SimplexCategory.δ j).op f)).trans h

/-- The complete original right-Hom boundary square gives its whole coefficient matching square. -/
theorem coefficientBoundarySquareOfPrecomp {X X' : C} (i : X ⟶ X')
    (B : SimplicialObject C) (n : ℕ)
    (z : (SSet.boundary.{v} n : SSet.{v}) ⟶ ResolutionHomComplex.right X' B)
    (b : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (sq : CommSq z (SSet.boundary.{v} n).ι (precomp i B) b) :
    CommSq (SSet.yonedaEquiv b) i (PartialFaceMatching.map B n Finset.univ)
      (boundaryHomMap X' B n z) := by
  let t : X ⟶ B.obj (op ⦋n⦌) := SSet.yonedaEquiv b
  change CommSq t i (PartialFaceMatching.map B n Finset.univ) (boundaryHomMap X' B n z)
  constructor
  apply limit.hom_ext
  intro a
  rw [Category.assoc, PartialFaceMatching.map_π, Category.assoc, boundaryHomMap_π]
  have h := congrArg (fun q => q.app (SimplexCategory.PartialMatching.target a)
    (boundaryLabel n a)) sq.w
  change i ≫ z.app (SimplexCategory.PartialMatching.target a) (boundaryLabel n a) =
    b.app (SimplexCategory.PartialMatching.target a)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.PartialMatching.arrow a).unop) at h
  have hb := (SSet.yonedaEquiv_symm_app_objEquiv_symm
    (X := ResolutionHomComplex.right X B) (SSet.yonedaEquiv b)
      (SimplexCategory.PartialMatching.arrow a).unop).trans
    (ResolutionHomComplex.right_map_apply X B (SimplexCategory.PartialMatching.arrow a)
      (SSet.yonedaEquiv b))
  rw [SSet.yonedaEquiv.symm_apply_apply] at hb
  exact hb.symm.trans h.symm

section Model

variable [ModelCategory C]

/-- An original trivial cofibration lifts every full boundary against actual matching fibrations. -/
theorem precomp_boundary_hasLift {X X' : C} (i : X ⟶ X') [Cofibration i]
    [WeakEquivalence i] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (n : ℕ)
    (z : (SSet.boundary.{v} n : SSet.{v}) ⟶ ResolutionHomComplex.right X' B)
    (b : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (sq : CommSq z (SSet.boundary.{v} n).ι (precomp i B) b) : sq.HasLift := by
  let _ : HasLiftingProperty i (PartialFaceMatching.map B n Finset.univ) :=
    hasLiftingProperty_of_wfs _ _ (mem_trivialCofibrations i)
      (RightFrameHornGeometry.fullPartialMatching_fibration B hB n)
  let t : X ⟶ B.obj (op ⦋n⦌) := SSet.yonedaEquiv b
  let c : CommSq t i (PartialFaceMatching.map B n Finset.univ) (boundaryHomMap X' B n z) :=
    coefficientBoundarySquareOfPrecomp i B n z b sq
  let _ : c.HasLift := inferInstance
  refine CommSq.HasLift.mk'
    { l := RightFrameHornGeometry.homSimplex X' B n c.lift
      fac_left := homSimplex_boundary_extension X' B n z c.lift c.fac_right
      fac_right := ?_ }
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, RightFrameHornGeometry.homSimplex]
  exact (congrArg (fun f : (ResolutionHomComplex.right X' B).obj (op ⦋n⦌) =>
    (precomp i B).app (op ⦋n⦌) f)
      (SSet.yonedaEquiv.apply_symm_apply c.lift)).trans c.fac_left

/-- Original trivial cofibrations give trivial Kan fibrations of the same whole right Hom map. -/
theorem precomp_trivialFibration {X X' : C} (i : X ⟶ X') [Cofibration i]
    [WeakEquivalence i] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j)) :
    trivialFibrations SSet.{v} (precomp i B) := by
  rw [← cofibrations_rlp SSet.{v}, SSet.modelCategoryQuillen.cofibrations_eq,
    SSet.rlp_monomorphisms]
  intro K L j hj
  obtain ⟨n⟩ := hj
  exact { sq_hasLift := fun sq => precomp_boundary_hasLift i B hB n _ _ sq }

end Model

omit [HasFiniteLimits C] in
/-- The actual right-Hom source functor retains every original coefficient arrow. -/
def sourceFunctor (B : SimplicialObject C) : Cᵒᵖ ⥤ SSet.{v} :=
  (CosimplicialObject.const C).op ⋙ ResolutionHomComplex.bifunctor.flip.obj B

omit [HasFiniteLimits C] in
/-- The whole source-functor arrow is the original right-Hom precomposition map. -/
theorem sourceFunctor_map {X X' : C} (i : X ⟶ X') (B : SimplicialObject C) :
    (sourceFunctor B).map i.op = precomp i B := rfl

section Model

variable [ModelCategory C]

/-- Brown's actual coefficient factorization gives weak invariance at the original cofibrant sources. -/
theorem precomp_weak {X X' : C} (i : X ⟶ X') [WeakEquivalence i]
    [IsCofibrant X] [IsCofibrant X'] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j)) :
    WeakEquivalence (precomp i B) := by
  change WeakEquivalence ((sourceFunctor B).map i.op)
  apply sourceFunctor_weak_of_trivialCofibrations
  intro U V j _ _
  exact ((mem_trivialFibrations_iff (f := precomp j B)).mp
    (precomp_trivialFibration j B hB)).2

end Model

end HomotopicalAlgebra.RightFrameHomBoundary
