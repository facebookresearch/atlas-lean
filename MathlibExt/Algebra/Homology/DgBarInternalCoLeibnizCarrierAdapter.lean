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

public import MathlibExt.Algebra.Homology.TensorDifferentialUpInt
public import MathlibExt.Algebra.Homology.HomotopyCategory.HomComplexCochainSquare

/-!
# Carrier internal co-Leibniz adapter (abstract)

Let `C` be a preadditive monoidal category, `K : CochainComplex C ℤ`, and
`D : K ⟶ K ⊗ K` a decomultiplication-shaped chain map. The internal
differential `Fi := diff K` satisfies the carrier co-Leibniz equation in the
`HomComplex.Cochain.comp`/`tensor` algebra:

`Fi ≫ D = (D ≫ (Fi ⊗ I)) + (D ≫ (I ⊗ Fi))` with `I = ofHom (𝟙 K)`

and explicit degree witnesses (`add_zero 1` on the face-first side,
`0 + (1 + 0) = 1` / `0 + (0 + 1) = 1` on the split-first side), exactly the
carrier shape of `barShiftedCarrierExternalCoLeibniz` and hypothesis `hFi` of
`CochainComplex.dgTotal_coLeibniz_combination`. Nothing is Bar-concrete: `K`
and `D` are variables, so the Bar packager instantiates
`K := barShiftedCarrier ε`, `D := tensorCoalgebraDeconcat _`.

This module also hosts the multiplication-shaped dual
`dgInternal_leibniz_carrier`: for a concat-shaped chain map
`μ : K ⊗ K ⟶ K`, `μ ≫ Fi = ((Fi ⊗ I) ≫ μ) + ((I ⊗ Fi) ≫ μ)` with
`zero_add 1` on the multiply-first side and `add_zero 1` on each
differentiate-first leg — hypothesis `hFi` of
`dgTotal_leibniz_combination`. The Cobar packager instantiates
`K := <cobar carrier>`, `μ := <carrier concat>`.

## Informal proof tree

```text
Goal: Fi.comp D = D.comp (Fi⊗I) + D.comp (I⊗Fi)
├─ ofHom D .comp diff(K⊗K) = diff K .comp ofHom D   [chain-map law, Hom.comm]
├─ diff(C⊗C) = Fi⊗I + I⊗Fi                          [CochainComplex.diff_tensorObj]
├─ D.comp (X+Y) = D.comp X + D.comp Y               [Cochain.comp_add]
└─ witness alignment (0+1 vs 0+(1+0)/0+(0+1))       [rfl: comp ignores h]
```

## Declaration inventory (this leaf)

* `dgInternal_coLeibniz_carrier`: general internal co-Leibniz adapter,
  discharging `hFi` of `dgTotal_coLeibniz_combination` for `Fi := diff K`.
* `dgInternal_leibniz_carrier`: multiplication-shaped dual, discharging
  `hFi` of `dgTotal_leibniz_combination` for `Fi := diff K`.

Both adapters reuse the public cochain-form chain-map law `ofHom_comp_diff`.

## Bar-side instantiation sketch (comment only; left to the packager)

The packager (which already imports the Bar files and carries their
`PreservesColimit`/`HasTensor₄ObjExt`/`HasGoodTensor` variables) discharges
`hFi` with one line:

```lean
-- hFi := dgInternal_coLeibniz_carrier
--   (K := barShiftedCarrier ε) (tensorCoalgebraDeconcat (barShiftedIdeal ε))
```

`barShiftedCarrier ε` is a reducible abbrev for
`tensorCoalgebraCarrier (barShiftedIdeal ε)`, so the general statement
specializes definitionally. Kept out of this leaf because stating it here
would require importing `TensorCoalgebraShiftedBar`/`TensorCoalgebra` and
their variable blocks (the direct attempt fails with missing
`MonoidalCategoryStruct (CochainComplex (ModuleCat R) ℤ)` /
`HasGoodTensor₁₂Tensor` instances plus a `whnf` timeout); the packager
context already has all of these.

## Nonclaims

No Bar/Cobar concreteness: no faces, insertions, sums, carriers, deconcat
components, or straddle analysis. No proof of the external hypothesis `hFE`,
no combination step, no square-zero, anticommutation, counit, totalization,
or adjunction claim. The tensor-differential decomposition is reused from
`TensorDifferentialUpInt`, not re-proved.

## Import justification

`TensorDifferentialUpInt` supplies `CochainComplex.diff_tensorObj` (the
`diff (C⊗C) = diff⊗I + I⊗diff` decomposition) and, transitively,
`Cochain.tensor`/`tensor_v`. `HomComplexCochainSquare` supplies
`Cochain.ofHom_comp_diff` and the underlying `Cochain.comp`/`add` API.
The `Additive` instances `diff_tensorObj` requires are section variables.
No other import is used.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]
variable {K : CochainComplex C ℤ}

variable [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]

/-- Abstract carrier internal co-Leibniz adapter: the internal differential
`Fi := HomComplex.Cochain.diff K` satisfies the carrier co-Leibniz shape
`Fi.comp (ofHom D) = D.comp (Fi ⊗ I) + D.comp (I ⊗ Fi)` against any
deconcat-shaped chain map `D`, with the exact degree witnesses of hypothesis
`hFi` of `dgTotal_coLeibniz_combination`. -/
theorem dgInternal_coLeibniz_carrier
    (D : K ⟶ HomologicalComplex.tensorObj K K) :
    (HomComplex.Cochain.diff K).comp (HomComplex.Cochain.ofHom D) (add_zero 1) =
      (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
            (HomComplex.Cochain.ofHom (𝟙 K)))
          (show (0 : ℤ) + (1 + 0) = 1 by omega)
        + (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
            (HomComplex.Cochain.diff K))
          (show (0 : ℤ) + (0 + 1) = 1 by omega) := by
  have hchain := HomComplex.Cochain.ofHom_comp_diff D
  have hdecomp := diff_tensorObj K K
  calc (HomComplex.Cochain.diff K).comp (HomComplex.Cochain.ofHom D)
          (add_zero 1)
      = (HomComplex.Cochain.ofHom D).comp
          (HomComplex.Cochain.diff (HomologicalComplex.tensorObj K K))
          (zero_add 1) := hchain.symm
    _ = (HomComplex.Cochain.ofHom D).comp
          (Add.add (α := HomComplex.Cochain (HomologicalComplex.tensorObj K K)
              (HomologicalComplex.tensorObj K K) 1)
            (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
              (HomComplex.Cochain.ofHom (𝟙 K)))
            (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
              (HomComplex.Cochain.diff K))) (zero_add 1) := by rw [hdecomp]
    _ = (HomComplex.Cochain.ofHom D).comp
            (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
              (HomComplex.Cochain.ofHom (𝟙 K))) (zero_add 1) +
          (HomComplex.Cochain.ofHom D).comp
            (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
              (HomComplex.Cochain.diff K)) (zero_add 1) :=
        HomComplex.Cochain.comp_add _ _ _ _
    _ = _ := rfl

/-- Abstract carrier internal Leibniz adapter: the internal differential
`Fi := HomComplex.Cochain.diff K` satisfies the carrier Leibniz shape
`(ofHom μ).comp Fi = (Fi ⊗ I).comp μ + (I ⊗ Fi).comp μ` against any
concat-shaped chain map `μ`, with the exact degree witnesses of hypothesis
`hFi` of `dgTotal_leibniz_combination` (`zero_add 1` on the multiply-first
side, `add_zero 1` on each differentiate-first leg).

Multiplication-shaped dual of `dgInternal_coLeibniz_carrier` (same proof
architecture, `comp` arguments dualized: the chain-map law runs `μ` before
`diff` instead of `D` after `diff`, and the additivity step is
`Cochain.add_comp` instead of `Cochain.comp_add`). The Cobar packager
instantiates `K := <cobar carrier>`, `μ := <carrier concat>`. -/
theorem dgInternal_leibniz_carrier
    (μ : HomologicalComplex.tensorObj K K ⟶ K) :
    (HomComplex.Cochain.ofHom μ).comp (HomComplex.Cochain.diff K) (zero_add 1) =
      (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
          (HomComplex.Cochain.ofHom (𝟙 K))).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1)
        + (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
          (HomComplex.Cochain.diff K)).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1) := by
  have hchain := HomComplex.Cochain.ofHom_comp_diff μ
  have hdecomp := diff_tensorObj K K
  calc (HomComplex.Cochain.ofHom μ).comp (HomComplex.Cochain.diff K)
          (zero_add 1)
      = (HomComplex.Cochain.diff (HomologicalComplex.tensorObj K K)).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1) := hchain
    _ = (Add.add (α := HomComplex.Cochain (HomologicalComplex.tensorObj K K)
              (HomologicalComplex.tensorObj K K) 1)
            (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
              (HomComplex.Cochain.ofHom (𝟙 K)))
            (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
              (HomComplex.Cochain.diff K))).comp
          (HomComplex.Cochain.ofHom μ) (add_zero 1) := by rw [hdecomp]
    _ = (HomComplex.Cochain.tensor (HomComplex.Cochain.diff K)
              (HomComplex.Cochain.ofHom (𝟙 K))).comp
            (HomComplex.Cochain.ofHom μ) (add_zero 1) +
          (HomComplex.Cochain.tensor (HomComplex.Cochain.ofHom (𝟙 K))
              (HomComplex.Cochain.diff K)).comp
            (HomComplex.Cochain.ofHom μ) (add_zero 1) :=
        HomComplex.Cochain.add_comp _ _ _ _
    _ = _ := rfl

end CochainComplex
