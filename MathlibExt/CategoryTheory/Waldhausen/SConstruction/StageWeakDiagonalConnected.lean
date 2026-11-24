/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonal
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalVertex
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZero
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakCategory
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeak
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Connectedness of the StageWeak diagonal via zero-to-vertex edges

For a Waldhausen category `C`, every `0`-simplex of `stageWeakDiagonal C` is
`ComposableArrows.mk₀ X'` for `X' : StageWeakCategory C 0` via
`CategoryTheory.nerveEquiv`. The terminal map into `stageZero C` is an iso
because both ends are pointwise zero, so its inverse gives a Stage-0 weak
morphism `⟨stageZero C⟩ ⟶ X'`. Reindexing along `σ (0 : Fin 1)` lifts it to
level 1; `mk₁` of the lift is a diagonal `1`-simplex whose faces collapse by
`δ ≫ σ = 𝟙` to the zero vertex and `X'`.

Orientation: `δ 1` source is `stageWeakDiagonalZeroVertex C`, `δ 0` target is
`ComposableArrows.mk₀ X'`.

Nonclaims: no contractibility, additivity, `π₀ = K₀`, strict pointedness,
spectra, Q/S comparison, or Milnor/Bloch-Kato work. No extension-diagonal
sharing.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial ZeroObject

open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Underlying `Stage C 0` iso between the zero stage and an arbitrary stage.
Both sides are pointwise zero, so the components are the unique zero isos. -/
private noncomputable def stageZeroIsoStage (X : Stage C 0) : stageZero C ≅ X := by
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun A => ?_) ?_)
  · have hA : A = diag (0 : Fin 1) := by
      obtain ⟨a, b, g, rfl⟩ := CategoryTheory.Arrow.mk_surjective A
      fin_cases a
      fin_cases b
      rfl
    have hX : IsZero (X.obj.obj A) := hA ▸ X.property.diag_isZero 0
    exact (isZero_zero C).iso hX
  · intro A B f
    have hB : IsZero (X.obj.obj B) := by
      have hA : B = diag (0 : Fin 1) := by
        obtain ⟨a, b, g, rfl⟩ := CategoryTheory.Arrow.mk_surjective B
        fin_cases a
        fin_cases b
        rfl
      exact hA ▸ X.property.diag_isZero 0
    exact (hB).eq_of_tgt _ _

/-- Stage-0 weak morphism from the zero object to an arbitrary weak stage,
as the inverse of the terminal map (which is an iso between zero stages). -/
private noncomputable def stageWeakZeroToObj (X' : StageWeakCategory C 0) :
    (⟨stageZero C⟩ : StageWeakCategory C 0) ⟶ X' := by
  let X : Stage C 0 := X'.obj
  let f : X ⟶ stageZero C := (stageZero_isTerminal C).from X
  have he : f = (stageZeroIsoStage C X).inv := by
    apply (stageZero_isTerminal C).hom_ext
  have hIso : IsIso f := he ▸ inferInstance
  have hWeak : stageWeak C 0 f := (stageWeak C 0).of_isIso f
  have hInvWeak : stageWeak C 0 (inv f) := (stageWeak C 0).of_isIso (inv f)
  exact ⟨inv f, hInvWeak⟩

/-- Reindexing along `σ 0` and either face returns a degree-zero weak stage. -/
private theorem reindexStageWeak_sigmaZero_delta_obj
    (X : StageWeakCategory C 0) (i : Fin 2) :
    ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)) ⋙
      reindexStageWeak C (SimplexCategory.δ i)).obj X) = X := by
  fin_cases i
  · change ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)) ⋙
      reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).obj X) = X
    rw [← reindexStageWeak_comp]
    have hδσ : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.σ (0 : Fin 1) =
        𝟙 (⦋0⦌ : SimplexCategory) := by
      simpa using SimplexCategory.δ_comp_σ_self (n := 0) (i := (0 : Fin 1))
    rw [hδσ, reindexStageWeak_id]
    rfl
  · change ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)) ⋙
      reindexStageWeak C (SimplexCategory.δ (1 : Fin 2))).obj X) = X
    rw [← reindexStageWeak_comp]
    have hδσ : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.σ (0 : Fin 1) =
        𝟙 (⦋0⦌ : SimplexCategory) := by
      simpa using SimplexCategory.δ_comp_σ_succ (n := 0) (i := (0 : Fin 1))
    rw [hδσ, reindexStageWeak_id]
    rfl

/-- Diagonal zero-to-vertex edge with `δ 1` the zero vertex and `δ 0` the target. -/
private noncomputable def diagonalZeroToVertexEdge (X' : StageWeakCategory C 0) :
    (stageWeakDiagonal C).Edge (stageWeakDiagonalZeroVertex C)
      (ComposableArrows.mk₀ X') := by
  let σ : (⦋1⦌ : SimplexCategory) ⟶ ⦋0⦌ := SimplexCategory.σ (0 : Fin 1)
  let φ : (⟨stageZero C⟩ : StageWeakCategory C 0) ⟶ X' := stageWeakZeroToObj C X'
  let ψ : (reindexStageWeak C σ).obj ⟨stageZero C⟩ ⟶ (reindexStageWeak C σ).obj X' :=
    (reindexStageWeak C σ).map φ
  let s : (stageWeakDiagonal C).obj (op ⦋1⦌) := ComposableArrows.mk₁ ψ
  refine SSet.Edge.ofEq (SSet.Edge.mk' s) ?_ ?_
  · have hInner :
        ((CategoryTheory.nerve (StageWeakCategory C 1)).map
          (SimplexCategory.δ 1).op) s =
          ComposableArrows.mk₀ ((reindexStageWeak C σ).obj ⟨stageZero C⟩) := by
      change ((CategoryTheory.nerve (StageWeakCategory C 1)).map
        (SimplexCategory.δ 1).op) (ComposableArrows.mk₁ ψ) = _
      apply ComposableArrows.ext₀
      rfl
    have hOuter :
        (CategoryTheory.nerveMap (reindexStageWeak C (SimplexCategory.δ 1))).app
          (op ⦋0⦌) (ComposableArrows.mk₀ ((reindexStageWeak C σ).obj ⟨stageZero C⟩)) =
          ComposableArrows.mk₀ (⟨stageZero C⟩ : StageWeakCategory C 0) := by
      rw [CategoryTheory.nerveMap_app_mk₀]
      have hObj : ((reindexStageWeak C σ ⋙ reindexStageWeak C (SimplexCategory.δ (1 : Fin 2))).obj
          ⟨stageZero C⟩) = ⟨stageZero C⟩ := by
        simpa [σ] using reindexStageWeak_sigmaZero_delta_obj C
          (⟨stageZero C⟩ : StageWeakCategory C 0) (1 : Fin 2)
      exact congrArg ComposableArrows.mk₀ hObj
    have hMap : (stageWeakDiagonal C).map (SimplexCategory.δ (1 : Fin 2)).op s =
        (CategoryTheory.nerveMap (reindexStageWeak C (SimplexCategory.δ (1 : Fin 2)))).app
          (op ⦋0⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 1)).map
            (SimplexCategory.δ (1 : Fin 2)).op) s) := rfl
    change (stageWeakDiagonal C).map (SimplexCategory.δ (1 : Fin 2)).op s = _
    rw [hMap, hInner, hOuter]
    rfl
  · have hInner :
        ((CategoryTheory.nerve (StageWeakCategory C 1)).map
          (SimplexCategory.δ 0).op) s =
          ComposableArrows.mk₀ ((reindexStageWeak C σ).obj X') := by
      change ((CategoryTheory.nerve (StageWeakCategory C 1)).map
        (SimplexCategory.δ 0).op) (ComposableArrows.mk₁ ψ) = _
      apply ComposableArrows.ext₀
      rfl
    have hOuter :
        (CategoryTheory.nerveMap (reindexStageWeak C (SimplexCategory.δ 0))).app
          (op ⦋0⦌) (ComposableArrows.mk₀ ((reindexStageWeak C σ).obj X')) =
          ComposableArrows.mk₀ X' := by
      rw [CategoryTheory.nerveMap_app_mk₀]
      have hObj : ((reindexStageWeak C σ ⋙ reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).obj
          X') = X' := by
        simpa [σ] using reindexStageWeak_sigmaZero_delta_obj C X' (0 : Fin 2)
      exact congrArg ComposableArrows.mk₀ hObj
    have hMap : (stageWeakDiagonal C).map (SimplexCategory.δ (0 : Fin 2)).op s =
        (CategoryTheory.nerveMap (reindexStageWeak C (SimplexCategory.δ (0 : Fin 2)))).app
          (op ⦋0⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 1)).map
            (SimplexCategory.δ (0 : Fin 2)).op) s) := rfl
    change (stageWeakDiagonal C).map (SimplexCategory.δ (0 : Fin 2)).op s = _
    rw [hMap, hInner, hOuter]
    rfl

/-- The StageWeak diagonal is connected, as a theorem (not a global instance). -/
theorem stageWeakDiagonal_isConnected : (stageWeakDiagonal C).IsConnected := by
  have key : ∀ v : (stageWeakDiagonal C).obj (op ⦋0⦌),
      SSet.π₀.mk (stageWeakDiagonalZeroVertex C) = SSet.π₀.mk v := by
    intro v
    let X' : StageWeakCategory C 0 := CategoryTheory.nerveEquiv v
    have hv : ComposableArrows.mk₀ X' = v :=
      CategoryTheory.nerveEquiv.left_inv v
    have e : (stageWeakDiagonal C).Edge (stageWeakDiagonalZeroVertex C) v :=
      SSet.Edge.ofEq (diagonalZeroToVertexEdge C X') rfl hv
    exact SSet.π₀.sound e
  rw [SSet.isConnected_iff]
  constructor
  · refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective b
    exact (key x).symm.trans (key y)
  · exact ⟨stageWeakDiagonalZeroVertex C⟩

end CategoryTheory.Waldhausen.SConstruction
