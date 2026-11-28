/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tsutomu Okano
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Alternating Alexander–Whitney component

This file defines the generic degreewise Alexander–Whitney component on
Mathlib's alternating-face complexes.

For `X Y : SimplicialObject C` the component at degree `n` is the finite sum
over `p : Fin (n + 1)` of the tensor of the front and back faces followed by
the canonical inclusion into the tensor product of homological complexes.

The chain-map identity is proved in `AlexanderWhitney.Differential`, and
`AlexanderWhitney.ChainMap` packages the resulting natural chain map.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Simplicial

namespace AlgebraicTopology.AlexanderWhitney

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
  (X Y : SimplicialObject C)
  [HomologicalComplex.HasTensor ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]

/-- Generic degreewise Alexander–Whitney component on alternating-face complexes.

For `n : ℕ` this is a morphism from degree `n` of
`(alternatingFaceMapComplex C).obj (X ⊗ Y)` to degree `n` of
`HomologicalComplex.tensorObj` of the alternating-face complexes of `X` and `Y`,
given by `∑ p : Fin (n + 1)`,
`let q := n - (p : ℕ)`, `have h : (p : ℕ) + q = n := by omega`,
`(frontFace X h ⊗ₘ backFace Y h) ≫ HomologicalComplex.ιTensorObj _ _ _ _ _ h`.

`AlexanderWhitney.ChainMap` packages these components as a natural chain map. -/
noncomputable def alternatingComponent (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj (X ⊗ Y)).X n ⟶
      (HomologicalComplex.tensorObj ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)).X n :=
  ∑ p : Fin (n + 1),
    let q := n - (p : ℕ)
    have h : (p : ℕ) + q = n := by
      omega
    (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
      HomologicalComplex.ιTensorObj ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) (p : ℕ) q n h

omit [HasZeroObject C] in
theorem alternatingComponent_eq_sum (n : ℕ) :
    alternatingComponent X Y n =
      ∑ p : Fin (n + 1),
        let q := n - (p : ℕ)
        have h : (p : ℕ) + q = n := by
          omega
        (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
          HomologicalComplex.ιTensorObj ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) (p : ℕ) q n h := rfl
end AlgebraicTopology.AlexanderWhitney
