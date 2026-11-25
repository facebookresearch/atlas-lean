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

public import MathlibExt.KTheory.Ring.StableGeneralLinear.MatrixDiagramIso
public import MathlibExt.KTheory.Ring.StableGeneralLinear.Basic

/-!
# Stable-GL matrix equivalence

For finite nonempty `ι : Type u` and semiring `R : Type u`, flattening
`GLₙ (Matrix ι ι R) ≃* GL_{n*card ι} R` assembles into
`matrixFiniteGLDiagramIso : matrixFiniteGLDiagram ≅ scaledBaseFiniteGLDiagram`
in `ℕ ⥤ GrpCat.{u}`. Its image under the chosen filtered colimits
(`IsColimit.coconePointsIsoOfNatIso` of `colimitCoconeIsColimit`) is the first
step matrix-to-base, and `natMulColimitIso (card ι)` gives cofinality
`colimit (scaled) ≅ colimit (base)`. The composite is
`stableGLMatrixGrpIso : GrpCat.of (StableGL (Matrix ι ι R)) ≅ GrpCat.of (StableGL R)`,
matrix-to-base in `GrpCat.{u}`, with `MulEquiv` `stableGLMatrixMulEquiv`.

Representative orientations: `hom` sends finite matrix representative
`StableGL.of g` with `g : GLₙ (Matrix ι ι R)` to base representative
`StableGL.of (matrixGLMulEquiv n g)`; `inv` sends base representative
`StableGL.of g` to matrix representative via padding `n ≤ n*card ι` and
`(matrixGLMulEquiv n).symm` (base-to-matrix, finite-to-finite).
-/

@[expose] public section

open CategoryTheory Limits AlgebraicKTheory MatrixDiagram GrpCat.FilteredColimits

universe u

noncomputable section

namespace AlgebraicKTheory
namespace StableGL

variable {R : Type u} [Semiring R]
variable {ι : Type u} [DecidableEq ι] [Fintype ι] [Nonempty ι]

/-- `GrpCat` isomorphism `StableGL (Matrix ι ι R) ≅ StableGL R`, matrix-to-base;
the underlying colimit composite of `matrixFiniteGLDiagramIso` and `natMulColimitIso`.
On representatives, `hom` is flattening `GLₙ (Matrix) → GL_{n*card} R`,
`inv` is base-to-matrix via `n ≤ n*card ι` and `matrixGLMulEquiv` symm. -/
noncomputable def stableGLMatrixGrpIso :
    GrpCat.of (StableGL (Matrix ι ι R)) ≅ GrpCat.of (StableGL R) :=
  ((colimitCoconeIsColimit (matrixFiniteGLDiagram (R := R) (ι := ι))).coconePointsIsoOfNatIso
      (colimitCoconeIsColimit (scaledBaseFiniteGLDiagram (R := R) (ι := ι)))
      (matrixFiniteGLDiagramIso (R := R) (ι := ι))).trans
    (natMulColimitIso (Fintype.card ι) Fintype.card_pos
      (finiteGLDiagram.obj (SemiRingCat.of R)))

/-- Multiplicative equivalence `StableGL (Matrix ι ι R) ≃* StableGL R`,
matrix-to-base, underlying `stableGLMatrixGrpIso`. On finite representatives it sends
`StableGL.of g` to `StableGL.of (matrixGLMulEquiv n g)`, with inverse base-to-matrix. -/
noncomputable def stableGLMatrixMulEquiv :
    StableGL (Matrix ι ι R) ≃* StableGL R :=
  stableGLMatrixGrpIso.groupIsoToMulEquiv

/-- `hom` of `stableGLMatrixGrpIso` on a finite matrix representative:
matrix-to-base and representative orientation `StableGL.of g ↦ StableGL.of (matrixGLMulEquiv n g)`
for `g : GLₙ (Matrix ι ι R)`. -/
theorem stableGLMatrixGrpIso_hom_of {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) (Matrix ι ι R)) :
    stableGLMatrixGrpIso.hom (StableGL.of g) =
      StableGL.of (matrixGLMulEquiv (R := R) (ι := ι) n g) := by
  have hk : 0 < Fintype.card ι := Fintype.card_pos
  let F₁ := matrixFiniteGLDiagram (R := R) (ι := ι)
  let F₂ := scaledBaseFiniteGLDiagram (R := R) (ι := ι)
  let F := finiteGLDiagram.obj (SemiRingCat.of R)
  let α := (matrixFiniteGLDiagramIso (R := R) (ι := ι)).hom
  change (natMulColimitIso (Fintype.card ι) hk F).hom
      ((colimitCoconeIsColimit F₁).map (colimitCocone F₂) α (G.mk (F := F₁) ⟨n, g⟩)) =
    G.mk (F := F)
      ⟨n * Fintype.card ι, matrixGLMulEquiv (R := R) (ι := ι) n g⟩
  have hCol : (colimitCoconeIsColimit F₁).map (colimitCocone F₂) α (G.mk (F := F₁) ⟨n, g⟩) =
      G.mk (F := F₂) ⟨n, α.app n g⟩ :=
    ConcreteCategory.congr_hom ((colimitCoconeIsColimit F₁).ι_map (colimitCocone F₂) α n) g
  have hApp : α.app n g = matrixGLMulEquiv (R := R) (ι := ι) n g := by
    rw [matrixFiniteGLDiagramIso_hom_app]
    rfl
  have hFirst : (colimitCoconeIsColimit F₁).map (colimitCocone F₂) α (G.mk (F := F₁) ⟨n, g⟩) =
      G.mk (F := F₂) ⟨n, matrixGLMulEquiv (R := R) (ι := ι) n g⟩ :=
    hCol.trans (by rw [hApp])
  have hLift : (natMulColimitIso (Fintype.card ι) hk F).hom
      ((colimitCoconeIsColimit F₁).map (colimitCocone F₂) α (G.mk (F := F₁) ⟨n, g⟩)) =
      (natMulColimitIso (Fintype.card ι) hk F).hom
        (G.mk (F := F₂) ⟨n, matrixGLMulEquiv (R := R) (ι := ι) n g⟩) :=
    congrArg (fun x => (natMulColimitIso (Fintype.card ι) hk F).hom x) hFirst
  have hCof : (natMulColimitIso (Fintype.card ι) hk F).hom
      (G.mk (F := F₂) ⟨n, matrixGLMulEquiv (R := R) (ι := ι) n g⟩) =
      G.mk (F := F)
        ⟨n * Fintype.card ι, matrixGLMulEquiv (R := R) (ι := ι) n g⟩ :=
    natMulColimitIso_hom_mk (Fintype.card ι) hk F n
      (matrixGLMulEquiv (R := R) (ι := ι) n g)
  exact hLift.trans hCof

/-- `MulEquiv` version of the hom orientation: matrix-to-base
and representative orientation `StableGL.of g ↦ StableGL.of (matrixGLMulEquiv n g)`
for `g : GLₙ (Matrix ι ι R)`, underlying the `GrpCat` iso. -/
theorem stableGLMatrixMulEquiv_of {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) (Matrix ι ι R)) :
    stableGLMatrixMulEquiv (StableGL.of g) =
      StableGL.of (matrixGLMulEquiv (R := R) (ι := ι) n g) := by
  change stableGLMatrixGrpIso (R := R) (ι := ι).hom (StableGL.of g) = _
  exact stableGLMatrixGrpIso_hom_of (R := R) (ι := ι) g

/-- `inv` of `stableGLMatrixGrpIso` on a finite base representative:
base-to-matrix and representative orientation, `StableGL.of g` with `g : GLₙ R`
maps to `StableGL.of ((matrixGLMulEquiv n).symm (F.map (n ≤ n*card) g))`,
i.e. padding along `n ≤ n*card ι` then de-flattening. -/
theorem stableGLMatrixGrpIso_inv_of {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    stableGLMatrixGrpIso.inv (StableGL.of g) =
      StableGL.of
        ((matrixGLMulEquiv (R := R) (ι := ι) n).symm
          ((finiteGLDiagram.obj (SemiRingCat.of R)).map
            (homOfLE (Nat.le_mul_of_pos_right n Fintype.card_pos)) g)) := by
  have hk : 0 < Fintype.card ι := Fintype.card_pos
  let F := finiteGLDiagram.obj (SemiRingCat.of R)
  let F₁ := matrixFiniteGLDiagram (R := R) (ι := ι)
  let F₂ := scaledBaseFiniteGLDiagram (R := R) (ι := ι)
  let β := (matrixFiniteGLDiagramIso (R := R) (ι := ι)).inv
  let g' := F.map (homOfLE (Nat.le_mul_of_pos_right n hk)) g
  change (colimitCoconeIsColimit F₂).map (colimitCocone F₁) β
      ((natMulColimitIso (Fintype.card ι) hk F).inv (G.mk (F := F) ⟨n, g⟩)) =
    G.mk (F := F₁)
      ⟨n, (matrixGLMulEquiv (R := R) (ι := ι) n).symm
        g'⟩
  have hInv : (natMulColimitIso (Fintype.card ι) hk F).inv
      (G.mk (F := F) ⟨n, g⟩) = G.mk (F := F₂) ⟨n, g'⟩ :=
    natMulColimitIso_inv_mk (Fintype.card ι) hk F n g
  have hCol : (colimitCoconeIsColimit F₂).map (colimitCocone F₁) β (G.mk (F := F₂) ⟨n, g'⟩) =
      G.mk (F := F₁) ⟨n, β.app n g'⟩ :=
    ConcreteCategory.congr_hom ((colimitCoconeIsColimit F₂).ι_map (colimitCocone F₁) β n) g'
  have hApp : β.app n g' =
      (matrixGLMulEquiv (R := R) (ι := ι) n).symm g' := by
    rw [matrixFiniteGLDiagramIso_inv_app]
    rfl
  have hLift : (colimitCoconeIsColimit F₂).map (colimitCocone F₁) β
      ((natMulColimitIso (Fintype.card ι) hk F).inv (G.mk (F := F) ⟨n, g⟩)) =
      (colimitCoconeIsColimit F₂).map (colimitCocone F₁) β (G.mk (F := F₂) ⟨n, g'⟩) :=
    congrArg (fun x => (colimitCoconeIsColimit F₂).map (colimitCocone F₁) β x) hInv
  have hLast : G.mk (F := F₁) ⟨n, β.app n g'⟩ =
      G.mk (F := F₁)
        ⟨n, (matrixGLMulEquiv (R := R) (ι := ι) n).symm g'⟩ := by
    rw [hApp]
  exact hLift.trans (hCol.trans hLast)

end StableGL
end AlgebraicKTheory

end
