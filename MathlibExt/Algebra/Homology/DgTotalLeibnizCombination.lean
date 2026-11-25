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
# Total-differential Leibniz combination (abstract)

Let `C` be a preadditive monoidal category, `K : CochainComplex C ℤ`,
`μ : K ⊗ K ⟶ K` a multiplication-shaped chain map, and
`Fi FE : Cochain K K 1` degree-one cochains (differential summands).
Each summand satisfies its Leibniz equation in the
`HomComplex.Cochain.comp`/`tensor` algebra:

`μ ≫ F = ((F ⊗ I) ≫ μ) + ((I ⊗ F) ≫ μ)` with `I = ofHom (𝟙 K)`

with explicit degree witnesses (`zero_add 1` on the multiply-first side,
`add_zero 1` on each differentiate-first leg), exactly the carrier shape of
`cobarShiftedInsertionSum_concatLeibniz_of_full` (same `comp` order, same
leg order, same witnesses; the two per-pair rejoins collapse to the single
carrier `μ`). The main theorem `dgTotal_leibniz_combination` proves the
total differential `F = Fi + FE` satisfies the same shape. Nothing is
Cobar-concrete: `K`, `μ`, `Fi`, `FE` are all variables. This is the
multiplication-shaped dual of `dgTotal_coLeibniz_combination` in
`DgTotalCoLeibnizCombination.lean` (same file structure, `comp`/`tensor`
roles dualized).

## Informal proof tree

```text
Goal: μ ≫ (Fi+FE) = (((Fi+FE)⊗I) ≫ μ) + ((I⊗(Fi+FE)) ≫ μ)
├─ LHS: μ.comp (Fi+FE) = μ.comp Fi + μ.comp FE      [Cochain.comp_add]
├─ μ.comp Fi = ((Fi⊗I)≫μ) + ((I⊗Fi)≫μ)                   [hFi]
├─ μ.comp FE = ((FE⊗I)≫μ) + ((I⊗FE)≫μ)                   [hFE]
├─ (Fi+FE)⊗I = Fi⊗I + FE⊗I                           [Cochain.tensor_add_left]
├─ I⊗(Fi+FE) = I⊗Fi + I⊗FE                           [Cochain.tensor_add_right]
├─ ((X+Y)≫μ) = (X≫μ) + (Y≫μ)  (twice)                      [Cochain.add_comp]
└─ (a+b)+(c+d) = (a+c)+(b+d)                         [add_add_add_comm]
```

## Role of the chain-map law for `μ`

`μ` is taken as a general morphism `tensorObj K K ⟶ C`, i.e. a chain map, so
its chain-map law `HomologicalComplex.Hom.comm μ` is in scope by construction.
The combination implication itself is pure additivity and needs no further
property of `μ`: at Cobar, the internal hypothesis `hFi` is discharged from
the chain-map law (the multiplication-shaped analogue of
`barShiftedInternal_coLeibniz_incl`, which is literally `Hom.comm`), while
the external hypothesis `hFE` is discharged from the carrier insertion/concat
Leibniz assembly built on `cobarShiftedInsertionSum_concatLeibniz_of_full`.
Lifting the per-pair instance (two rejoins) to the carrier `comp`/`tensor`
shape with a single `μ` is the packager's adapter, not part of this lemma.

## Cobar-side instantiation sketch (comment only; no unmerged imports)

```lean
-- C  := cobar carrier (shifted tensor powers of the reduced coalgebra)
-- μ  := carrier concat (multiplication-shaped chain map)
-- Fi := HomComplex.Cochain.diff C            -- internal differential, degree 1
-- FE := carrier insertion sum                -- external differential, degree 1
-- hFE := <carrier insertion/concat Leibniz; per-pair case is
--         cobarShiftedInsertionSum_concatLeibniz_of_full>
-- hFi := <carrier internal Leibniz; per-length case is Hom.comm>
-- #check dgTotal_leibniz_combination μ Fi FE hFi hFE
```

## Leg-order convention (forced by the Sum-module statement)

The first RHS summand carries `F` on the LEFT leg (`F ⊗ I`) and the second
on the RIGHT leg (`I ⊗ F`), verbatim the summand order of
`cobarShiftedInsertionSum_concatLeibniz_of_full`. The swapped-leg variant
(`(I ⊗ F) ≫ μ` first) is an equally valid combination lemma but would force
the Cobar packager to commute the sum at instantiation; it is deliberately
not provided. Once the length-indexed per-block law is lifted to the
carrier single-`μ` shape, the packager instantiates this statement with
zero adaptation.

## Declaration inventory (this leaf)

* `dgTotal_leibniz_combination`: per-summand Leibniz equations for `Fi`,
  `FE` imply the total Leibniz equation for `Fi + FE`.

Unlike the co-Leibniz dual, no private tensor-additivity helper is needed:
`HomComplex.Cochain.tensor_add_right` is public in
`TensorCochainCoherence.lean` (the dual file's private
`cochain_tensor_add_right` predates/duplicates it and is `private`, hence not
importable).

## Nonclaims

No Cobar concreteness: no insertions, concats, sums, carriers, per-pair
interchange families, or seam analysis. No proof of either per-summand
hypothesis, no chain-map-law derivation, no tensor-differential
decomposition, no square-zero, anticommutation, counit, coaugmentation,
totalization, or adjunction claim.

## Import justification

`TensorCochainCoherence` supplies `Cochain.tensor`, `tensor_add_left`, and
`tensor_add_right`. `HomComplex` supplies the `Cochain.comp`/`add` API
(`comp_add`, `add_comp`). `Monoidal` supplies `tensorObj`. `Preadditive`
supplies the `MonoidalPreadditive` class used by the tensor-additivity
lemmas. No `Bifunctor` import is needed since both tensor-additivity
lemmas come from the library. No other import is used.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
variable {K : CochainComplex C ℤ}

variable [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]

/-- Abstract total-differential Leibniz combination: if the internal and
external degree-one summands each satisfy the carrier Leibniz shape
`(ofHom μ).comp F = (F ⊗ I).comp μ + (I ⊗ F).comp μ` against a
concat-shaped chain map `μ`, so does the total differential `Fi + FE`. The
per-summand hypotheses match the conclusion shape of
`cobarShiftedInsertionSum_concatLeibniz_of_full` (up to the abstract
`K`/`μ`/`Fi`/`FE` and the single carrier `μ`); `μ` is a general morphism so
its chain-map law `HomologicalComplex.Hom.comm μ` is in scope at
instantiation. -/
theorem dgTotal_leibniz_combination
    (μ : HomologicalComplex.tensorObj K K ⟶ K)
    (Fi FE : HomComplex.Cochain K K 1)
    (hFi : (HomComplex.Cochain.ofHom μ).comp Fi (zero_add 1) =
      (HomComplex.Cochain.tensor Fi (HomComplex.Cochain.ofHom (𝟙 K))).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1)
        + (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K)) Fi).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1))
    (hFE : (HomComplex.Cochain.ofHom μ).comp FE (zero_add 1) =
      (HomComplex.Cochain.tensor FE (HomComplex.Cochain.ofHom (𝟙 K))).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1)
        + (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K)) FE).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1)) :
    (HomComplex.Cochain.ofHom μ).comp (Fi + FE) (zero_add 1) =
      (HomComplex.Cochain.tensor (Fi + FE)
          (HomComplex.Cochain.ofHom (𝟙 K))).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1)
        + (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
          (Fi + FE)).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1) := by
  rw [HomComplex.Cochain.comp_add, hFi, hFE,
    HomComplex.Cochain.tensor_add_left, HomComplex.Cochain.tensor_add_right]
  simp only [HomComplex.Cochain.add_comp]
  apply add_add_add_comm

end CochainComplex
