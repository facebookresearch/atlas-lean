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

public import MathlibExt.KTheory.Ring.StableGeneralLinear.MatrixStabilizationSquare

/-!
# Matrix diagram isomorphism for `K₁` matrix invariance

For a finite nonempty index type `ι` and a semiring `R`, this file proves

`matrixFiniteGLDiagram (R := R) (ι := ι) ≅ scaledBaseFiniteGLDiagram (R := R) (ι := ι)`

in `ℕ ⥤ GrpCat`. The forward component at `n` is the finite flattening
`matrixGLIso n : GLₙ (Matrix ι ι R) ≃* GL_{n * card ι} R` via `Matrix.comp`
and product reindexing, and the inverse component is its inverse.

Orientation and component formulas:

* Source is `matrixFiniteGLDiagram` (`n ↦ GLₙ (Matrix ι ι R)`), target is
  `scaledBaseFiniteGLDiagram` (`n ↦ GL_{n * card ι} R`).
* `matrixFiniteGLDiagramIso.hom.app n = (matrixGLIso n).hom` (flattening).
* `matrixFiniteGLDiagramIso.inv.app n = (matrixGLIso n).inv` (unflattening).

Both `ι` and `R` live in the same universe `u` (`ι : Type u`, `R : Type u`);
diagrams live in `GrpCat.{u}` and the underlying `SemiRingCat` object
`Matrix ι ι R` in `SemiRingCat.{u}`, consistently with `MatrixDiagram` and
`MatrixStabilizationSquare`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicKTheory
namespace MatrixDiagram

variable {R : Type u} [Semiring R]
variable {ι : Type u} [DecidableEq ι] [Fintype ι] [Nonempty ι]

private lemma matrixGLIso_hom_succ (n : ℕ) :
    (matrixFiniteGLDiagram (R := R) (ι := ι)).map (homOfLE (Nat.le_add_right n 1)) ≫
        (matrixGLIso (R := R) (ι := ι) (n + 1)).hom =
      (matrixGLIso (R := R) (ι := ι) n).hom ≫
        (scaledBaseFiniteGLDiagram (R := R) (ι := ι)).map
          (homOfLE (Nat.le_add_right n 1)) := by
  have hF : (matrixFiniteGLDiagram (R := R) (ι := ι)).map
      (homOfLE (Nat.le_add_right n 1)) =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization (Matrix ι ι R)) := by
    have h := finiteGLDiagram_obj_map_succ
        (R := SemiRingCat.of (Matrix ι ι R)) n
    simp [matrixFiniteGLDiagram, h]
  rw [hF, scaledBaseFiniteGLDiagram_map_succ (R := R) (ι := ι) n]
  have hComp := matrixBlockStabilization_comp_matrixGLMulEquiv (R := R) (ι := ι) n
  calc GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization (Matrix ι ι R)) ≫
          (matrixGLIso (R := R) (ι := ι) (n + 1)).hom
      = GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization (Matrix ι ι R)) ≫
          GrpCat.ofHom (matrixGLMulEquiv (R := R) (ι := ι) (n + 1)).toMonoidHom := rfl
    _ = GrpCat.ofHom
          ((matrixGLMulEquiv (R := R) (ι := ι) (n + 1)).toMonoidHom.comp
            (Matrix.GeneralLinearGroup.stabilization (Matrix ι ι R))) := by
        rw [← GrpCat.ofHom_comp]
    _ = GrpCat.ofHom
          ((matrixBlockStabilization (R := R) (ι := ι) n).comp
            (matrixGLMulEquiv (R := R) (ι := ι) n).toMonoidHom) := by
        rw [← hComp]
    _ = GrpCat.ofHom (matrixGLMulEquiv (R := R) (ι := ι) n).toMonoidHom ≫
          GrpCat.ofHom (matrixBlockStabilization (R := R) (ι := ι) n) := by
        rw [GrpCat.ofHom_comp]
    _ = (matrixGLIso (R := R) (ι := ι) n).hom ≫
          GrpCat.ofHom (matrixBlockStabilization (R := R) (ι := ι) n) := rfl

private noncomputable def matrixFiniteGLDiagramTrans :
    matrixFiniteGLDiagram (R := R) (ι := ι) ⟶
      scaledBaseFiniteGLDiagram (R := R) (ι := ι) :=
  NatTrans.ofSequence (fun n => (matrixGLIso (R := R) (ι := ι) n).hom)
    (fun n => matrixGLIso_hom_succ n)

private lemma matrixFiniteGLDiagramTrans_app_aux (n : ℕ) :
    (matrixFiniteGLDiagramTrans (R := R) (ι := ι)).app n =
      (matrixGLIso (R := R) (ι := ι) n).hom :=
  rfl

/-- Natural isomorphism
`matrixFiniteGLDiagram (R := R) (ι := ι) ≅ scaledBaseFiniteGLDiagram (R := R) (ι := ι)`
in `ℕ ⥤ GrpCat.{u}`.

Orientation: source is `matrixFiniteGLDiagram` (`n ↦ GLₙ (Matrix ι ι R)`),
target is `scaledBaseFiniteGLDiagram` (`n ↦ GL_{n * card ι} R` via
`natMulFunctor (card ι)`). At `n`, `hom` is `(matrixGLIso n).hom`, the flattening
`GLₙ (Matrix ι ι R) →* GL_{n * card ι} R` via `Matrix.comp`, and `inv` is
`(matrixGLIso n).inv`. -/
noncomputable def matrixFiniteGLDiagramIso :
    matrixFiniteGLDiagram (R := R) (ι := ι) ≅
      scaledBaseFiniteGLDiagram (R := R) (ι := ι) :=
  NatIso.ofComponents (fun n => matrixGLIso (R := R) (ι := ι) n)
    (fun {X Y} f => by
      have hNat := (matrixFiniteGLDiagramTrans (R := R) (ι := ι)).naturality f
      have : Nonempty ι := inferInstance
      simpa only [matrixFiniteGLDiagramTrans_app_aux] using hNat)

/-- Forward component formula for `matrixFiniteGLDiagramIso`: at `n`,
`hom.app n = (matrixGLIso n).hom`, i.e. the flattening
`GLₙ (Matrix ι ι R) →* GL_{n * card ι} R`. Orientation matches
`matrixFiniteGLDiagram` → `scaledBaseFiniteGLDiagram`. -/
@[simp]
lemma matrixFiniteGLDiagramIso_hom_app (n : ℕ) :
    (matrixFiniteGLDiagramIso (R := R) (ι := ι)).hom.app n =
      (matrixGLIso (R := R) (ι := ι) n).hom := by
  have : Nonempty ι := inferInstance
  rfl

/-- Inverse component formula for `matrixFiniteGLDiagramIso`: at `n`,
`inv.app n = (matrixGLIso n).inv`, i.e. unflattening
`GL_{n * card ι} R →* GLₙ (Matrix ι ι R)`. Orientation is the reverse of `hom`. -/
@[simp]
lemma matrixFiniteGLDiagramIso_inv_app (n : ℕ) :
    (matrixFiniteGLDiagramIso (R := R) (ι := ι)).inv.app n =
      (matrixGLIso (R := R) (ι := ι) n).inv := by
  have : Nonempty ι := inferInstance
  rfl

end MatrixDiagram
end AlgebraicKTheory

end
