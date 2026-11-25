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

public import MathlibExt.Algebra.Homology.TensorCochainCoherence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Total-differential co-Leibniz combination (abstract)

Let `C` be a preadditive monoidal category, `K : CochainComplex C ℤ`,
`D : K ⟶ K ⊗ K` a decomultiplication-shaped chain map, and
`Fi FE : Cochain K K 1` degree-one cochains (differential summands).
Each summand satisfies its co-Leibniz equation in the
`HomComplex.Cochain.comp`/`tensor` algebra:

`F ≫ D = (D ≫ (F ⊗ I)) + (D ≫ (I ⊗ F))` with `I = ofHom (𝟙 K)`

and explicit degree witnesses (`add_zero 1` on the face-first side,
`0 + (1 + 0) = 1` / `0 + (0 + 1) = 1` on the split-first side). The main
theorem `dgTotal_coLeibniz_combination` proves the total differential
`F = Fi + FE` satisfies the same shape. Nothing is Bar-concrete: `K`,
`D`, `Fi`, `FE` are all variables, so any decomultiplication-shaped
packaging instantiates it; the Cobar (multiplication-shaped) side uses
the dual `dgTotal_leibniz_combination` instead.

## Informal proof tree

```text
Goal: (Fi+FE) ≫ D = (D ≫ ((Fi+FE)⊗I)) + (D ≫ (I⊗(Fi+FE)))
├─ LHS: (Fi+FE).comp D = Fi.comp D + FE.comp D      [Cochain.add_comp]
├─ Fi.comp D = (D≫(Fi⊗I)) + (D≫(I⊗Fi))                   [hFi]
├─ FE.comp D = (D≫(FE⊗I)) + (D≫(I⊗FE))                   [hFE]
├─ (Fi+FE)⊗I = Fi⊗I + FE⊗I                           [Cochain.tensor_add_left]
├─ I⊗(Fi+FE) = I⊗Fi + I⊗FE                           [Cochain.tensor_add_right]
├─ (D≫(X+Y)) = (D≫X) + (D≫Y)  (twice)                      [Cochain.comp_add]
└─ (a+b)+(c+d) = (a+c)+(b+d)                         [add_add_add_comm]
```

## Role of the chain-map law for `D`

`D` is taken as a general morphism `C ⟶ tensorObj K K`, i.e. a chain map, so
its chain-map law `HomologicalComplex.Hom.comm D` is in scope by construction.
The combination implication itself is pure additivity and needs no further
property of `D`: at Bar, the internal hypothesis `hFi` is discharged from the
chain-map law (the per-length instance is `barShiftedInternal_coLeibniz_incl`,
which is literally `Hom.comm`), while the external hypothesis `hFE` is
discharged from `barShiftedCarrierExternalCoLeibniz`. Lifting the internal
instance to the carrier `comp`/`tensor` shape is the packager's adapter, not
part of this lemma.

## Bar-side instantiation sketch (comment only; no unmerged imports)

```lean
-- K  := barShiftedCarrier ε
-- D  := tensorCoalgebraDeconcat (barShiftedIdeal ε)
-- Fi := HomComplex.Cochain.diff C            -- internal differential, degree 1
-- FE := barShiftedCarrierExternalFace ε μbar h
-- hFE := barShiftedCarrierExternalCoLeibniz ε μbar h hSum
-- hFi := <carrier internal co-Leibniz; per-length case is
--         barShiftedInternal_coLeibniz_incl, i.e. Hom.comm>
-- #check dgTotal_coLeibniz_combination D Fi FE hFi hFE
```

## Declaration inventory (this leaf)

* `dgTotal_coLeibniz_combination`: per-summand co-Leibniz equations for `Fi`,
  `FE` imply the total co-Leibniz equation for `Fi + FE`.

## Nonclaims

No Bar/Cobar concreteness: no faces, insertions, sums, carriers, deconcat
components, or straddle analysis. No proof of either per-summand hypothesis,
no chain-map-law derivation, no tensor-differential decomposition, no
square-zero, anticommutation, counit, totalization, or adjunction claim.

## Import justification

`TensorCochainCoherence` supplies `Cochain.tensor`, `tensor_v`,
`tensor_add_left`, and `tensor_add_right`. `HomComplex` supplies the
`Cochain.comp`/`add` API (`add_comp`, `comp_add`, `ext`, `add_v`).
`Monoidal` supplies `tensorObj`. `Preadditive` supplies
`MonoidalPreadditive.tensor_add`. No other import is used.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
variable {K : CochainComplex C ℤ}

variable [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]

/-- Abstract total-differential co-Leibniz combination: if the internal and
external degree-one summands each satisfy the carrier co-Leibniz shape
`F.comp (ofHom D) = D.comp (F ⊗ I) + D.comp (I ⊗ F)` against a deconcat-shaped
chain map `D`, so does the total differential `Fi + FE`. The per-summand
hypotheses match the conclusion shape of `barShiftedCarrierExternalCoLeibniz`
(up to the abstract `C`/`D`/`Fi`/`FE`); `D` is a general morphism so its
chain-map law `HomologicalComplex.Hom.comm D` is in scope at instantiation. -/
theorem dgTotal_coLeibniz_combination
    (D : K ⟶ HomologicalComplex.tensorObj K K)
    (Fi FE : HomComplex.Cochain K K 1)
    (hFi : Fi.comp (HomComplex.Cochain.ofHom D) (add_zero 1) =
      (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor Fi (HomComplex.Cochain.ofHom (𝟙 K)))
          (show (0 : ℤ) + (1 + 0) = 1 by omega)
        + (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K)) Fi)
          (show (0 : ℤ) + (0 + 1) = 1 by omega))
    (hFE : FE.comp (HomComplex.Cochain.ofHom D) (add_zero 1) =
      (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor FE (HomComplex.Cochain.ofHom (𝟙 K)))
          (show (0 : ℤ) + (1 + 0) = 1 by omega)
        + (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K)) FE)
          (show (0 : ℤ) + (0 + 1) = 1 by omega)) :
    (Fi + FE).comp (HomComplex.Cochain.ofHom D) (add_zero 1) =
      (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (Fi + FE) (HomComplex.Cochain.ofHom (𝟙 K)))
          (show (0 : ℤ) + (1 + 0) = 1 by omega)
        + (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K)) (Fi + FE))
          (show (0 : ℤ) + (0 + 1) = 1 by omega) := by
  rw [HomComplex.Cochain.add_comp, hFi, hFE,
    HomComplex.Cochain.tensor_add_left, HomComplex.Cochain.tensor_add_right]
  simp only [HomComplex.Cochain.comp_add]
  apply add_add_add_comm

end CochainComplex
