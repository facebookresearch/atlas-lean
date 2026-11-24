/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftHomEquiv
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup
public import MathlibExt.AlgebraicTopology.SimplicialSet.ULiftKan

/-!
# Full original pointed simplices under universe lift

The actual full original standard-simplex map lifts and lowers through
its same scalar Yoneda dictionary. Every original boundary face and
constant endpoint remains fixed, in all original dimensions and
independent coefficient universes.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- The boundary-constant simplex and its universe lift have explicit inverse maps. -/
def uliftPointedSimplexEquiv (X : SSet.{u}) (n : ℕ) (x : X _⦋0⦌) :
    X.PtSimplex n x ≃ (uliftFunctor.{v,u}.obj X).PtSimplex n (ULift.up x) where
  toFun p :=
    { map := uliftStandardHomEquiv.{u,v} X ⦋n⦌ p.map
      comm := by
        cases n with
        | zero =>
          apply SSet.hom_ext
          intro q
          apply ConcreteCategory.hom_ext
          intro a
          have ha := a.property
          simp only [boundary_zero, Subfunctor.bot_obj, Set.mem_empty_iff_false] at ha
        | succ n =>
          apply SSet.boundary.hom_ext
          intro i
          change SSet.boundary.ι i ≫ (SSet.boundary (n + 1)).ι ≫
            uliftStandardHomEquiv.{u,v} X ⦋n + 1⦌ p.map = SSet.const (ULift.up x)
          rw [← Category.assoc, SSet.boundary.ι_ι]
          exact (uliftStandardHomEquiv_precomp.{u,v} X (SimplexCategory.δ i) p.map).symm.trans
            ((congrArg (uliftStandardHomEquiv.{u,v} X ⦋n⦌) (p.δ_map i)).trans
              (uliftStandardHomEquiv_const.{u,v} X n x)) }
  invFun p :=
    { map := (uliftStandardHomEquiv.{u,v} X ⦋n⦌).symm p.map
      comm := by
        cases n with
        | zero =>
          apply SSet.hom_ext
          intro q
          apply ConcreteCategory.hom_ext
          intro a
          have ha := a.property
          simp only [boundary_zero, Subfunctor.bot_obj, Set.mem_empty_iff_false] at ha
        | succ n =>
          apply SSet.boundary.hom_ext
          intro i
          change SSet.boundary.ι i ≫ (SSet.boundary (n + 1)).ι ≫
            (uliftStandardHomEquiv.{u,v} X ⦋n + 1⦌).symm p.map = SSet.const x
          rw [← Category.assoc, SSet.boundary.ι_ι]
          apply (uliftStandardHomEquiv.{u,v} X ⦋n⦌).injective
          exact (uliftStandardHomEquiv_precomp.{u,v} X (SimplexCategory.δ i) _).trans
            ((congrArg (fun f => SSet.stdSimplex.δ i ≫ f)
              (Equiv.apply_symm_apply (uliftStandardHomEquiv.{u,v} X ⦋n + 1⦌) p.map)).trans
                ((p.δ_map i).trans (uliftStandardHomEquiv_const.{u,v} X n x).symm)) }
  left_inv p := by
    apply RelativeMorphism.ext
    exact Equiv.symm_apply_apply (uliftStandardHomEquiv.{u,v} X ⦋n⦌) p.map
  right_inv p := by
    apply RelativeMorphism.ext
    exact Equiv.apply_symm_apply (uliftStandardHomEquiv.{u,v} X ⦋n⦌) p.map

end SSet
