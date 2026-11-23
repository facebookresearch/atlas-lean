/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpaceTelescopeFundamentalGroup
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveFilteredContractible
public import MathlibExt.CategoryTheory.CategoryBar.QuillenTheoremARight
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# The actual finite-GL telescope projection is a realization weak equivalence

The right comma of the original telescope projection is filtered.
Actual finite matrix representatives move its objects to a common rank.
Equality in the actual stable group supplies a later rank coequalizing
parallel comma arrows. No comma, contractibility, projection equivalence,
or naturality witness is an input.

Filtered-nerve weak contractibility and the existing right-comma Quillen A
then apply to the original named telescope nerve map. No inverse is chosen
and no source map of a Q/plus equivalence is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

private abbrev telescopeStageObject (n : ℕ) : FiniteBGLTelescopeCategory R :=
  ⟨n, SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ⟩

private def telescopeStageArrow (X : FiniteBGLTelescopeCategory R) (n : ℕ)
    (h : X.base ≤ n) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    X ⟶ telescopeStageObject R n where
  base := homOfLE h
  fiber := MulOpposite.op g

private theorem telescopeProjection_map_scalar
    {X Y : FiniteBGLTelescopeCategory R} (f : X ⟶ Y) :
    (show (StableGL R)ᵐᵒᵖ from (finiteBGLTelescopeToStableCategory R).map f) =
      MulOpposite.op (StableGL.of (MulOpposite.unop
        (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from f.fiber))) := by
  change MulOpposite.op
      (((StableGL.inclusion Y.base).app (SemiRingCat.of R)).hom
        (MulOpposite.unop (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from f.fiber))) =
    MulOpposite.op (StableGL.of _)
  exact congrArg MulOpposite.op (StableGL.inclusion_apply Y.base R _)

private theorem telescopeFiberComp_scalar
    {X Y Z : FiniteBGLTelescopeCategory R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from (f ≫ g).fiber) =
      (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from g.fiber) *
        (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from
          (finiteOppositeMonoidDiagram R).map g.base
            (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from f.fiber)) := by
  have hs := congrArg
    (fun a : ((finiteClassifyingCategoryDiagram R).map (f.base ≫ g.base)).toFunctor.obj
        X.fiber ⟶ Z.fiber =>
      (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from a))
    (Grothendieck.comp_fiber f g)
  simp only [finiteClassifyingCategoryDiagram_eqToHom,
    finiteClassifyingCategoryDiagram_map_map] at hs
  change (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from (f ≫ g).fiber) =
    ((show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from g.fiber) *
      (show (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ from
        (finiteOppositeMonoidDiagram R).map g.base
          (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from f.fiber))) *
      (1 : (Matrix.GeneralLinearGroup (Fin Z.base) R)ᵐᵒᵖ) at hs
  exact hs.trans (mul_one _)

private theorem telescopeHom_eq_of_scalar
    {X Y : FiniteBGLTelescopeCategory R} (f g : X ⟶ Y)
    (h : (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from f.fiber) =
      (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from g.fiber)) : f = g := by
  apply Grothendieck.ext f g (Subsingleton.elim _ _)
  rw [finiteClassifyingCategoryDiagram_eqToHom]
  change (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from f.fiber) * 1 =
    (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from g.fiber)
  exact (mul_one (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from f.fiber)).trans h

private theorem stable_of_transition {a b : ℕ} (f : a ⟶ b)
    (g : Matrix.GeneralLinearGroup (Fin a) R) :
    StableGL.of ((finiteGLDiagram.obj (SemiRingCat.of R)).map f g) = StableGL.of g := by
  apply StableGL.of_eq_iff.mpr
  refine ⟨b, 𝟙 b, f, ?_⟩
  rw [(finiteGLDiagram.obj (SemiRingCat.of R)).map_id]
  rfl

private theorem stable_of_one (n : ℕ) :
    StableGL.of (1 : Matrix.GeneralLinearGroup (Fin n) R) = (1 : StableGL R) :=
  ((StableGL.inclusion n).app (SemiRingCat.of R)).hom.map_one

/-- The actual projection's right comma is filtered by finite matrix representatives. -/
public instance finiteBGLTelescopeProjectionCommaIsFiltered :
    IsFiltered (CostructuredArrow (finiteBGLTelescopeToStableCategory R)
      (SingleObj.star (StableGL R)ᵐᵒᵖ)) where
  nonempty := ⟨CostructuredArrow.mk
    (Y := finiteBGLTelescopeBaseObject R) (𝟙 (SingleObj.star (StableGL R)ᵐᵒᵖ))⟩
  cocone_objs A B := by
    let a : StableGL R := MulOpposite.unop A.hom
    let b : StableGL R := MulOpposite.unop B.hom
    obtain ⟨r, ar, har⟩ := StableGL.exists_finite_rep a
    obtain ⟨s, bs, hbs⟩ := StableGL.exists_finite_rep b
    let k := max (max A.left.base B.left.base) (max r s)
    have hAk : A.left.base ≤ k :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hBk : B.left.base ≤ k :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    have hrk : r ≤ k :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hsk : s ≤ k :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    let ak := (finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE hrk) ar
    let bk := (finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE hsk) bs
    have hak : StableGL.of ak = a := (stable_of_transition R (homOfLE hrk) ar).trans har
    have hbk : StableGL.of bk = b := (stable_of_transition R (homOfLE hsk) bs).trans hbs
    let α := telescopeStageArrow R A.left k hAk ak
    let β := telescopeStageArrow R B.left k hBk bk
    let Z : CostructuredArrow (finiteBGLTelescopeToStableCategory R)
        (SingleObj.star (StableGL R)ᵐᵒᵖ) :=
      CostructuredArrow.mk (Y := telescopeStageObject R k) (𝟙 (SingleObj.star (StableGL R)ᵐᵒᵖ))
    have hα : (finiteBGLTelescopeToStableCategory R).map α = A.hom :=
      (telescopeProjection_map_scalar R α).trans
        ((congrArg MulOpposite.op hak).trans (MulOpposite.op_unop A.hom))
    have hβ : (finiteBGLTelescopeToStableCategory R).map β = B.hom :=
      (telescopeProjection_map_scalar R β).trans
        ((congrArg MulOpposite.op hbk).trans (MulOpposite.op_unop B.hom))
    let α' : A ⟶ Z := CostructuredArrow.homMk α (by
      change (1 : (StableGL R)ᵐᵒᵖ) *
        (show (StableGL R)ᵐᵒᵖ from (finiteBGLTelescopeToStableCategory R).map α) =
          (show (StableGL R)ᵐᵒᵖ from A.hom)
      exact (one_mul
        (show (StableGL R)ᵐᵒᵖ from (finiteBGLTelescopeToStableCategory R).map α)).trans hα)
    let β' : B ⟶ Z := CostructuredArrow.homMk β (by
      change (1 : (StableGL R)ᵐᵒᵖ) *
        (show (StableGL R)ᵐᵒᵖ from (finiteBGLTelescopeToStableCategory R).map β) =
          (show (StableGL R)ᵐᵒᵖ from B.hom)
      exact (one_mul
        (show (StableGL R)ᵐᵒᵖ from (finiteBGLTelescopeToStableCategory R).map β)).trans hβ)
    exact ⟨Z, α', β', trivial⟩
  cocone_maps {A B} f g := by
    have hπ : (finiteBGLTelescopeToStableCategory R).map f.left =
        (finiteBGLTelescopeToStableCategory R).map g.left := by
      apply (cancel_mono B.hom).1
      exact (CostructuredArrow.w f).trans (CostructuredArrow.w g).symm
    have hStable : StableGL.of (MulOpposite.unop
          (show (Matrix.GeneralLinearGroup (Fin B.left.base) R)ᵐᵒᵖ from f.left.fiber)) =
        StableGL.of (MulOpposite.unop
          (show (Matrix.GeneralLinearGroup (Fin B.left.base) R)ᵐᵒᵖ from g.left.fiber)) := by
      have hScalar :
          (show (StableGL R)ᵐᵒᵖ from (finiteBGLTelescopeToStableCategory R).map f.left) =
            (show (StableGL R)ᵐᵒᵖ from (finiteBGLTelescopeToStableCategory R).map g.left) := hπ
      exact congrArg MulOpposite.unop
        ((telescopeProjection_map_scalar R f.left).symm.trans
          (hScalar.trans (telescopeProjection_map_scalar R g.left)))
    obtain ⟨k, p, q, hpq⟩ := StableGL.of_eq_iff.mp hStable
    have hq : q = p := Subsingleton.elim _ _
    subst q
    let α := telescopeStageArrow R B.left k (leOfHom p) (1 : Matrix.GeneralLinearGroup (Fin k) R)
    have hBase : α.base = p := Subsingleton.elim _ _
    have hα : (finiteBGLTelescopeToStableCategory R).map α =
        𝟙 (SingleObj.star (StableGL R)ᵐᵒᵖ) :=
      (telescopeProjection_map_scalar R α).trans (congrArg MulOpposite.op (stable_of_one R k))
    let Z : CostructuredArrow (finiteBGLTelescopeToStableCategory R)
        (SingleObj.star (StableGL R)ᵐᵒᵖ) :=
      CostructuredArrow.mk (Y := telescopeStageObject R k) B.hom
    let α' : B ⟶ Z := CostructuredArrow.homMk α (by
      change (show (StableGL R)ᵐᵒᵖ from B.hom) *
        (show (StableGL R)ᵐᵒᵖ from (finiteBGLTelescopeToStableCategory R).map α) =
          (show (StableGL R)ᵐᵒᵖ from B.hom)
      have hScalar :
          (show (StableGL R)ᵐᵒᵖ from (finiteBGLTelescopeToStableCategory R).map α) =
            (1 : (StableGL R)ᵐᵒᵖ) := hα
      exact (congrArg
        (fun x : (StableGL R)ᵐᵒᵖ => (show (StableGL R)ᵐᵒᵖ from B.hom) * x) hScalar).trans
          (mul_one (show (StableGL R)ᵐᵒᵖ from B.hom)))
    have hFiber :
        (show (Matrix.GeneralLinearGroup (Fin k) R)ᵐᵒᵖ from (f.left ≫ α).fiber) =
          (show (Matrix.GeneralLinearGroup (Fin k) R)ᵐᵒᵖ from (g.left ≫ α).fiber) := by
      have hStabilized :
          (show Matrix.GeneralLinearGroup (Fin k) R from
            (finiteGLDiagram.obj (SemiRingCat.of R)).map α.base
              (MulOpposite.unop
                (show (Matrix.GeneralLinearGroup (Fin B.left.base) R)ᵐᵒᵖ from f.left.fiber))) =
            (show Matrix.GeneralLinearGroup (Fin k) R from
              (finiteGLDiagram.obj (SemiRingCat.of R)).map α.base
                (MulOpposite.unop
                  (show (Matrix.GeneralLinearGroup (Fin B.left.base) R)ᵐᵒᵖ from
                    g.left.fiber))) := by
        rw [hBase]
        exact hpq
      have hMap :
          (show (Matrix.GeneralLinearGroup (Fin k) R)ᵐᵒᵖ from
            (finiteOppositeMonoidDiagram R).map α.base
              (show (Matrix.GeneralLinearGroup (Fin B.left.base) R)ᵐᵒᵖ from f.left.fiber)) =
            (show (Matrix.GeneralLinearGroup (Fin k) R)ᵐᵒᵖ from
              (finiteOppositeMonoidDiagram R).map α.base
                (show (Matrix.GeneralLinearGroup (Fin B.left.base) R)ᵐᵒᵖ from g.left.fiber)) :=
        (finiteOppositeMonoidDiagram_map_apply R α.base _).trans
          ((congrArg MulOpposite.op hStabilized).trans
            (finiteOppositeMonoidDiagram_map_apply R α.base _).symm)
      exact (telescopeFiberComp_scalar R f.left α).trans
        ((congrArg
          (fun x : (Matrix.GeneralLinearGroup (Fin k) R)ᵐᵒᵖ =>
            (show (Matrix.GeneralLinearGroup (Fin k) R)ᵐᵒᵖ from α.fiber) * x) hMap).trans
          (telescopeFiberComp_scalar R g.left α).symm)
    have hArrow : f.left ≫ α = g.left ≫ α :=
      telescopeHom_eq_of_scalar R _ _ hFiber
    have hComma : f ≫ α' = g ≫ α' :=
      CostructuredArrow.hom_ext _ _ hArrow
    exact ⟨Z, α', hComma⟩

/-- The original named telescope nerve projection is a realization weak equivalence. -/
public theorem finiteBGLTelescopeNerveToStableNerve_mem_realizationWeakEquivalences :
    SSet.realizationWeakEquivalences (finiteBGLTelescopeNerveToStableNerve R) := by
  change SSet.realizationWeakEquivalences (nerveMap (finiteBGLTelescopeToStableCategory R))
  apply SSet.OppositeRealization.nerveMap_mem_of_costructuredArrow
    (finiteBGLTelescopeToStableCategory R)
  intro d
  have hd : d = SingleObj.star (StableGL R)ᵐᵒᵖ := Subsingleton.elim _ _
  subst d
  exact NerveFiltered.nerve_to_terminal_mem_realizationWeakEquivalences_of_isFiltered
    (CostructuredArrow (finiteBGLTelescopeToStableCategory R)
      (SingleObj.star (StableGL R)ᵐᵒᵖ))

end AlgebraicKTheory.StableGL
