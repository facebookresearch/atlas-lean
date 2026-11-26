/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Contraction of a standard simplex to its last vertex

For every `n : ℕ` and universe `u`, the standard simplex `Δ[n] : SSet.{u}` admits a cylinder
homotopy from its identity to the constant map at `Fin.last n`. The homotopy is induced by the
natural transformation from the identity of the ordinal `ULift (Fin (n + 1))` to the constant
functor at its top element, through the isomorphism between `Δ[n]` and the nerve of that
ordinal.

For a simplex `α`, an interval simplex `t`, and each coordinate `i`, the homotopy takes the
value of `α` at `i` when `t(i) = 0`, and the last vertex when `t(i) = 1`. Its value is
therefore pointwise greater than or equal to `α`.

See Goerss–Jardine, *Simplicial Homotopy Theory*, Chapter I, for the standard simplex as the
nerve of a finite ordinal and its contraction to a terminal object.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial MonoidalCategory

universe u

namespace SSet.stdSimplex

/-- For `n : ℕ`, transport the nerve of the constant functor on `ULift.{u} (Fin (n + 1))` with value `ULift.up (Fin.last n)` through `isoNerve.{u} n`. The resulting endomorphism of `Δ[n] : SSet.{u}` is the constant map at the last vertex:
`(isoNerve n).hom ≫ nerveMap ((Functor.const _).obj (ULift.up (Fin.last n))) ≫ (isoNerve n).inv = SSet.const (obj₀Equiv.symm (Fin.last n))`. -/
private lemma constEndpoint (n : ℕ) :
    (isoNerve.{u} n).hom ≫
        nerveMap
          ((Functor.const (ULift.{u} (Fin (n + 1)))).obj (ULift.up (Fin.last n))) ≫
        (isoNerve.{u} n).inv =
      SSet.const (obj₀Equiv.symm (Fin.last n)) := by
  apply SSet.yonedaEquiv.injective
  refine SSet.stdSimplex.ext _ _ (fun i => ?_)
  rfl

/-- For `n : ℕ`, a cylinder homotopy in `SSet.{u}` from `𝟙 Δ[n]` to the constant map at
`obj₀Equiv.symm (Fin.last n)`. Its cylinder map `Δ[n] ⊗ Δ[1] ⟶ Δ[n]` is induced, through
`isoNerve`, by the natural transformation from the identity of the finite ordinal to the
constant functor at its last element. -/
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

/-- Let `n : ℕ`, `a : SimplexCategoryᵒᵖ`, `α ∈ (Δ[n] : SSet.{u}).obj a`, and `t ∈ (Δ[1] : SSet.{u}).obj a`. For every `i : Fin (a.unop.len + 1)`, the `i`-th coordinate of the contraction cylinder is
`asOrderHom ((homotopyIdConstLast n).h.app a ⟨α, t⟩) i = if asOrderHom t i = 0 then asOrderHom α i else Fin.last n`.
Thus the formula applies to every interval simplex `t`. -/
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

/-- For `n : ℕ`, `a : SimplexCategoryᵒᵖ`, simplices `α ∈ (Δ[n] : SSet.{u}).obj a` and `t ∈ (Δ[1] : SSet.{u}).obj a`, and every `i : Fin (a.unop.len + 1)`,
`asOrderHom α i ≤ asOrderHom ((homotopyIdConstLast n).h.app a ⟨α, t⟩) i`.
The contraction fixes a coordinate when the corresponding interval coordinate is zero and otherwise sends it to the last vertex. -/
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
