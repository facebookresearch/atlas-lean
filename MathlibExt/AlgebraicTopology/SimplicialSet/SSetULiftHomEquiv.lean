/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftStandardIso
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct

@[expose] public section

/-!
# Full original standard-simplex maps under universe lift

Both inverse directions lift or lower the same entire original simplex
map. Every face and original constant vertex equation is retained.
This is the exact scalar dictionary for original pointed homotopy maps.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- The same original represented simplex map and its actual full lifted counterpart have both
inverse directions. -/
def uliftObjEquiv (X : SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    X.obj q ≃ (uliftFunctor.{v,u}.obj X).obj q where
  toFun x := ULift.up x
  invFun x := x.down
  left_inv _ := rfl
  right_inv x := ULift.up_down x

/-- The coefficient equivalence retains the original simplex in its literal wrapper. -/
@[simp]
theorem uliftObjEquiv_apply (X : SSet.{u}) (q : SimplexCategoryᵒᵖ) (x : X.obj q) :
    uliftObjEquiv.{u, v} X q x = ULift.up x := by
  rfl

/-- Each original simplicial source map retains its coefficient-lift square. -/
theorem uliftObjEquiv_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (q : SimplexCategoryᵒᵖ) (x : X.obj q) :
    (uliftFunctor.{v, u}.map f).app q (uliftObjEquiv.{u, v} X q x) =
      uliftObjEquiv.{u, v} Y q (f.app q x) := by
  simp only [uliftObjEquiv_apply]
  rfl

private theorem uliftObjEquiv_map (X : SSet.{u}) {q r : SimplexCategoryᵒᵖ}
    (θ : q ⟶ r) (x : X.obj q) :
    uliftObjEquiv.{u,v} X r (X.map θ x) =
      (uliftFunctor.{v,u}.obj X).map θ (uliftObjEquiv X q x) := rfl

/-- Both full original represented-simplex directions use the same rigid coefficient equivalence. -/
def uliftStandardHomEquiv (X : SSet.{u}) (n : SimplexCategory) :
    (stdSimplex.{u}.obj n ⟶ X) ≃ (stdSimplex.{max u v}.obj n ⟶ uliftFunctor.{v,u}.obj X) :=
  (SSet.yonedaEquiv (X := X) (n := n)).trans
    ((uliftObjEquiv.{u,v} X (op n)).trans
      (SSet.yonedaEquiv (X := uliftFunctor.{v,u}.obj X) (n := n)).symm)

/-- Every lifted full original standard-simplex map is its same coefficient-universe lift
through the original standard-simplex iso. -/
theorem uliftStandardHomEquiv_apply (X : SSet.{u}) (n : SimplexCategory)
    (f : stdSimplex.obj n ⟶ X) :
    uliftStandardHomEquiv.{u,v} X n f =
      (uliftStandardSimplexIso.{u,v} n).inv ≫ uliftFunctor.map f := by
  apply SSet.yonedaEquiv.injective
  have h := Equiv.apply_symm_apply (SSet.yonedaEquiv (X := uliftFunctor.{v,u}.obj X) (n := n))
    (uliftObjEquiv.{u,v} X (op n) (SSet.yonedaEquiv f))
  exact h

/-- The same original face operator is retained by the full represented-simplex lift. -/
theorem uliftStandardHomEquiv_precomp (X : SSet.{u}) {n m : SimplexCategory}
    (θ : n ⟶ m) (f : stdSimplex.{u}.obj m ⟶ X) :
    uliftStandardHomEquiv.{u,v} X n (stdSimplex.map θ ≫ f) =
      stdSimplex.map θ ≫ uliftStandardHomEquiv.{u,v} X m f := by
  apply SSet.yonedaEquiv.injective
  have hn := Equiv.apply_symm_apply (SSet.yonedaEquiv (X := uliftFunctor.{v,u}.obj X) (n := n))
    (uliftObjEquiv.{u,v} X (op n) (SSet.yonedaEquiv (stdSimplex.map θ ≫ f)))
  have hm := Equiv.apply_symm_apply (SSet.yonedaEquiv (X := uliftFunctor.{v,u}.obj X) (n := m))
    (uliftObjEquiv.{u,v} X (op m) (SSet.yonedaEquiv f))
  change SSet.yonedaEquiv (uliftStandardHomEquiv.{u,v} X m f) =
    uliftObjEquiv.{u,v} X (op m) (SSet.yonedaEquiv f) at hm
  exact hn.trans (by
    have hr := SSet.yonedaEquiv_naturality (X := uliftFunctor.{v,u}.obj X) θ
      (uliftStandardHomEquiv X m f)
    have hl := SSet.yonedaEquiv_naturality (X := X) θ f
    exact (congrArg (uliftObjEquiv.{u,v} X (op n)) hl.symm).trans
      ((uliftObjEquiv_map X θ.op (SSet.yonedaEquiv f)).trans
        ((congrArg ((uliftFunctor.{v,u}.obj X).map θ.op) hm).symm.trans hr)))

/-- Every same original constant endpoint map is retained by the full represented-simplex lift. -/
theorem uliftStandardHomEquiv_const (X : SSet.{u}) (n : ℕ) (x : X _⦋0⦌) :
    uliftStandardHomEquiv.{u,v} X ⦋n⦌ (SSet.const (X := (Δ[n] : SSet.{u})) x) =
      SSet.const (X := (Δ[n] : SSet.{max u v})) (ULift.up x) := by
  apply SSet.yonedaEquiv.injective
  have h := Equiv.apply_symm_apply (SSet.yonedaEquiv (X := uliftFunctor.{v,u}.obj X) (n := ⦋n⦌))
    (uliftObjEquiv.{u,v} X (op ⦋n⦌) (SSet.yonedaEquiv (SSet.const (X := (Δ[n] : SSet.{u})) x)))
  exact h

end SSet
