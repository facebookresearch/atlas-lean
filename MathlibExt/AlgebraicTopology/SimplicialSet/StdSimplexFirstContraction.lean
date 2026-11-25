/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexContraction

/-!
# Contraction of the standard simplex from its first vertex

The standard `n`-simplex is the nerve of the ordinal
`ULift (Fin (n + 1))`. The natural transformation from the constant functor
at its bottom element to the identity induces a cylinder homotopy from the
constant map at the first vertex to the identity of `Δ[n]`.

This is the directed companion to `SSet.stdSimplex.homotopyIdConstLast`.
It does not assert symmetry of simplicial homotopy or construct a deformation
retract.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial MonoidalCategory

universe u

namespace SSet.stdSimplex

/-- Conjugating the constant nerve map at the bottom vertex by `isoNerve`
gives the constant map at the first vertex. -/
private lemma constFirstEndpoint (n : ℕ) :
    (isoNerve.{u} n).hom ≫
        nerveMap
          ((Functor.const (ULift.{u} (Fin (n + 1)))).obj
            (ULift.up (0 : Fin (n + 1)))) ≫
        (isoNerve.{u} n).inv =
      SSet.const (obj₀Equiv.symm 0) := by
  apply SSet.yonedaEquiv.injective
  refine SSet.stdSimplex.ext _ _ (fun i => ?_)
  rfl

/-- Cylinder homotopy from the constant map at the first vertex of the
standard simplex to its identity map. -/
noncomputable def homotopyConstFirstId (n : ℕ) :
    SSet.Homotopy
      (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0))
      (𝟙 (Δ[n] : SSet.{u})) := by
  let η :
      (Functor.const (ULift.{u} (Fin (n + 1)))).obj
          (ULift.up (0 : Fin (n + 1))) ⟶
        𝟭 (ULift.{u} (Fin (n + 1))) :=
    { app := fun X => homOfLE (Fin.zero_le X.down)
      naturality := by
        intro X Z f
        dsimp
        exact Subsingleton.elim _ _ }
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm _)
    (SSet.RelativeMorphism.botEquiv.symm _)
  constructor
  · change SSet.ι₀ ≫ _ = SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)
    calc
      SSet.ι₀ ≫ ((isoNerve.{u} n).hom ▷ (Δ[1] : SSet.{u}) ≫
          (NatTrans.nerveHomotopy η).h ≫ (isoNerve.{u} n).inv) =
          (((isoNerve.{u} n).hom ≫ SSet.ι₀ ≫
            (NatTrans.nerveHomotopy η).h) ≫ (isoNerve.{u} n).inv) := by
            simp only [← Category.assoc, SSet.ι₀_comp]
      _ = SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) := by
        simp only [SSet.Homotopy.h₀]
        exact constFirstEndpoint n
  · change SSet.ι₁ ≫ _ = 𝟙 (Δ[n] : SSet.{u})
    calc
      SSet.ι₁ ≫ ((isoNerve.{u} n).hom ▷ (Δ[1] : SSet.{u}) ≫
          (NatTrans.nerveHomotopy η).h ≫ (isoNerve.{u} n).inv) =
          (((isoNerve.{u} n).hom ≫ SSet.ι₁ ≫
            (NatTrans.nerveHomotopy η).h) ≫ (isoNerve.{u} n).inv) := by
            simp only [← Category.assoc, SSet.ι₁_comp]
      _ = 𝟙 (Δ[n] : SSet.{u}) := by
        simp only [SSet.Homotopy.h₁, CategoryTheory.nerveMap_id,
          Category.comp_id, CategoryTheory.Iso.hom_inv_id]
  · ext m ⟨⟨x, hx⟩, t⟩
    cases hx

/-- The whole contraction retains its original monotone coordinate formula at every scalar degree.
-/
theorem homotopyConstFirstId_coordinate (n : ℕ) (d : SimplexCategoryᵒᵖ)
    (x : (Δ[n] : SSet.{u}).obj d) (t : (Δ[1] : SSet.{u}).obj d)
    (i : Fin (d.unop.len + 1)) :
    (((homotopyConstFirstId (n)).h).app d (x, t)).down.toOrderHom.toFun i =
      if t.down.toOrderHom.toFun i = 0 then 0 else x.down.toOrderHom.toFun i := by
  let η :
      (Functor.const (ULift.{u} (Fin (n + 1)))).obj
          (ULift.up (0 : Fin (n + 1))) ⟶
        𝟭 (ULift.{u} (Fin (n + 1))) :=
    { app := fun X => homOfLE (Fin.zero_le X.down)
      naturality := by
        intro X Z f
        dsimp
        exact Subsingleton.elim _ _ }
  let K : Functor (Fin (d.unop.len + 1)) (ULift.{u} (Fin (n + 1))) :=
    (isoNerve.{u} n).hom.app d x
  let T : Functor (Fin (d.unop.len + 1)) (Fin 2) :=
    (SSet.stdSimplex.asOrderHom t).toFunctor
  change
    ((((NatTrans.nerveCylinderFunctor η).mapComposableArrows _).obj
      (K.prod' T)).obj i).down =
      if SSet.stdSimplex.asOrderHom t i = 0 then 0 else SSet.stdSimplex.asOrderHom x i
  generalize ht : SSet.stdSimplex.asOrderHom t i = ti
  fin_cases ti
  · have hT : T.obj i = (0 : Fin 2) := ht
    change ((NatTrans.nerveCylinderFunctor η).obj (K.obj i, T.obj i)).down = _
    rw [hT, NatTrans.nerveCylinderFunctor_obj_zero]
    rfl
  · have hT : T.obj i = (1 : Fin 2) := ht
    have hK : (K.obj i).down = SSet.stdSimplex.asOrderHom x i := rfl
    change ((NatTrans.nerveCylinderFunctor η).obj (K.obj i, T.obj i)).down = _
    rw [hT, NatTrans.nerveCylinderFunctor_obj_one]
    exact hK

/-- The endpoint-zero formula after moving the interval factor to the left.
This is the orientation used by minimal-fibration pullback comparison. -/
@[reassoc]
lemma ι₀_β_hom_homotopyConstFirstId_h :
    SSet.ι₀ ≫ (β_ _ _).hom ≫
        (homotopyConstFirstId.{u} 1).h =
      SSet.const (obj₀Equiv.symm 0) := by
  apply SSet.yonedaEquiv.injective
  ext i : 1
  fin_cases i <;> rfl

end SSet.stdSimplex

end
