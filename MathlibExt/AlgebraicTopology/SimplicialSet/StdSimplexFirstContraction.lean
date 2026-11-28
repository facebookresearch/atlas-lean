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
# First-vertex contraction of the standard simplex

View Δ[n] as the nerve of the finite ordinal with bottom vertex 0. The natural transformation
from the constant functor at 0 to the identity gives a simplicial cylinder homotopy H : Δ[n] ×
Δ[1] → Δ[n], directed from the first-vertex constant map to identity.

For simplices x,t in degree d and a vertex i, H(x,t)(i) is 0 when t(i)=0 and x(i) when t(i)=1.
The construction and coordinate formula apply to standard simplices in every universe.
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

/-- Cylinder homotopy from the first vertex to identity.

For n : ℕ, the natural transformation const(0) → id of the ordinal Fin(n+1) induces a
simplicial homotopy from the constant map at the first vertex of Δ[n] to id_{Δ[n]}. Its
cylinder uses the interval factor on the right. -/
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

/-- Vertex-coordinate formula for the first-vertex contraction.

For degree-d simplices x of Δ[n] and t of Δ[1], and i ∈ Fin(d+1), the contraction has
coordinate H(x,t)(i) = 0 if t(i)=0 and H(x,t)(i)=x(i) otherwise. The formula includes n = 0. -/
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

/-- Zero-endpoint formula for the braided one-simplex cylinder.

For the contraction H of Δ[1], the composite of the zero endpoint inclusion, the indicated
braiding and H is the constant map at its first vertex: ι₀ ≫ β ≫ H = const(0). This is the
equation with the interval factor moved to the left. -/
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
