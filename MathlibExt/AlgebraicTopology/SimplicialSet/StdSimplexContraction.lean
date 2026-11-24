/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Contraction of the standard simplex onto its last vertex

The standard `n`-simplex is the nerve of the ordinal `ULift (Fin (n + 1))`
(`SSet.stdSimplex.isoNerve`). The unique natural transformation from the identity
functor to the constant functor at the top element `ULift.up (Fin.last n)`
induces a cylinder homotopy on the nerve via
`CategoryTheory.NatTrans.nerveHomotopy`; conjugating by `isoNerve` gives a
cylinder homotopy from the identity of `Δ[n]` to the constant map at its last
vertex.

Mathematical source: Goerss–Jardine, *Simplicial Homotopy Theory*, Chapter I
(the standard simplex is the nerve of a finite ordinal and contracts along the
unique map to its terminal object).

Nonclaims: no fibrancy, Kan, fibration, lifting, or model-category content.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial MonoidalCategory

universe u

namespace SSet.stdSimplex

/-- Conjugating the constant nerve map at the top vertex by `isoNerve` gives
the constant map at the last vertex. -/
private lemma constEndpoint (n : ℕ) :
    (isoNerve.{u} n).hom ≫
        nerveMap
          ((Functor.const (ULift.{u} (Fin (n + 1)))).obj (ULift.up (Fin.last n))) ≫
        (isoNerve.{u} n).inv =
      SSet.const (obj₀Equiv.symm (Fin.last n)) := by
  apply SSet.yonedaEquiv.injective
  refine SSet.stdSimplex.ext _ _ (fun i => ?_)
  rfl

/-- Cylinder homotopy from the identity of the standard simplex to the constant
map at its last vertex.

The cylinder map is the nerve cylinder of the unique natural transformation to
the top vertex, transported across `SSet.stdSimplex.isoNerve`. -/
noncomputable def homotopyIdConstLast (n : ℕ) :
    SSet.Homotopy (𝟙 (Δ[n] : SSet.{u}))
      (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
  let η : 𝟭 (ULift.{u} (Fin (n + 1))) ⟶
      (Functor.const (ULift.{u} (Fin (n + 1)))).obj (ULift.up (Fin.last n)) :=
    { app := fun X => homOfLE (show X.down ≤ Fin.last n from Fin.le_last _)
      naturality := by
        intro X Z f
        dsimp
        exact Subsingleton.elim _ _ }
  change SSet.RelativeMorphism.Homotopy (SSet.RelativeMorphism.botEquiv.symm _)
    (SSet.RelativeMorphism.botEquiv.symm _)
  constructor
  · change SSet.ι₀ ≫ _ = 𝟙 (Δ[n] : SSet.{u})
    calc SSet.ι₀ ≫ ((isoNerve.{u} n).hom ▷ (Δ[1] : SSet.{u}) ≫
            (NatTrans.nerveHomotopy η).h ≫ (isoNerve.{u} n).inv)
        = (((isoNerve.{u} n).hom ≫ SSet.ι₀ ≫
            (NatTrans.nerveHomotopy η).h) ≫ (isoNerve.{u} n).inv) := by
          simp only [← Category.assoc, SSet.ι₀_comp]
      _ = 𝟙 (Δ[n] : SSet.{u}) := by
          simp only [SSet.Homotopy.h₀, CategoryTheory.nerveMap_id, Category.comp_id,
            CategoryTheory.Iso.hom_inv_id]
  · change SSet.ι₁ ≫ _ = SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))
    calc SSet.ι₁ ≫ ((isoNerve.{u} n).hom ▷ (Δ[1] : SSet.{u}) ≫
            (NatTrans.nerveHomotopy η).h ≫ (isoNerve.{u} n).inv)
        = (((isoNerve.{u} n).hom ≫ SSet.ι₁ ≫
            (NatTrans.nerveHomotopy η).h) ≫ (isoNerve.{u} n).inv) := by
          simp only [← Category.assoc, SSet.ι₁_comp]
      _ = SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
          simp only [SSet.Homotopy.h₁]
          exact constEndpoint n
  · ext m ⟨⟨x, hx⟩, t⟩
    cases hx

/-- Arbitrary-time pointwise formula for the contraction cylinder.  At a
vertex where the interval simplex has value `0`, the original simplex is
retained; at value `1`, it has reached the last vertex. -/
theorem homotopyIdConstLast_h_app_apply (n : ℕ)
    (a : SimplexCategoryᵒᵖ)
    (α : (Δ[n] : SSet.{u}).obj a)
    (t : (Δ[1] : SSet.{u}).obj a)
    (i : Fin (a.unop.len + 1)) :
    SSet.stdSimplex.asOrderHom
        ((homotopyIdConstLast.{u} n).h.app a ⟨α, t⟩) i =
      if SSet.stdSimplex.asOrderHom t i = 0 then
        SSet.stdSimplex.asOrderHom α i else Fin.last n := by
  let η : Functor.id (ULift.{u} (Fin (n + 1))) ⟶
      (Functor.const (ULift.{u} (Fin (n + 1)))).obj
        (ULift.up (Fin.last n)) :=
    { app := fun X => homOfLE (show X.down ≤ Fin.last n from Fin.le_last _)
      naturality := by
        intro X Z f
        dsimp
        exact Subsingleton.elim _ _ }
  let K : Functor (Fin (a.unop.len + 1)) (ULift.{u} (Fin (n + 1))) :=
    (isoNerve.{u} n).hom.app a α
  let T : Functor (Fin (a.unop.len + 1)) (Fin 2) :=
    (SSet.stdSimplex.asOrderHom t).toFunctor
  change
    ((((NatTrans.nerveCylinderFunctor η).mapComposableArrows _).obj
      (K.prod' T)).obj i).down = _
  generalize ht : SSet.stdSimplex.asOrderHom t i = ti
  fin_cases ti
  · have hT : T.obj i = (0 : Fin 2) := ht
    have hK : (K.obj i).down = SSet.stdSimplex.asOrderHom α i := rfl
    change ((NatTrans.nerveCylinderFunctor η).obj
      (K.obj i, T.obj i)).down = _
    rw [hT, NatTrans.nerveCylinderFunctor_obj_zero]
    exact hK
  · have hT : T.obj i = (1 : Fin 2) := ht
    change ((NatTrans.nerveCylinderFunctor η).obj
      (K.obj i, T.obj i)).down = _
    rw [hT, NatTrans.nerveCylinderFunctor_obj_one]
    rfl

/-- The contraction only moves simplex vertices upward toward the last
vertex, pointwise at every interval time. -/
theorem le_homotopyIdConstLast_h_app_apply (n : ℕ)
    (a : SimplexCategoryᵒᵖ)
    (α : (Δ[n] : SSet.{u}).obj a)
    (t : (Δ[1] : SSet.{u}).obj a) :
    ∀ i : Fin (a.unop.len + 1),
      SSet.stdSimplex.asOrderHom α i ≤
        SSet.stdSimplex.asOrderHom
          ((homotopyIdConstLast.{u} n).h.app a ⟨α, t⟩) i := by
  intro i
  rw [homotopyIdConstLast_h_app_apply]
  split_ifs
  · exact le_rfl
  · exact Fin.le_last _

end SSet.stdSimplex

end
