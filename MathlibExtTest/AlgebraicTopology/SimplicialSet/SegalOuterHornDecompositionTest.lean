/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.AlgebraicTopology.SimplicialSet.SegalOuterHornDecomposition

/-! # Public original H/C geometric contracts -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

example (n : ℕ) :
    (SSet.Rezk.outerHornC.{u} (n + 1)).preimage
      (SSet.stdSimplex.δ (1 : Fin (n + 2))) = SSet.horn n 0 :=
  SSet.Rezk.outerHornC_preimage_cofaceOne n

example (n : ℕ) :
    (SSet.horn.{u} n 0).image (SSet.stdSimplex.δ (1 : Fin (n + 2))) =
      SSet.Rezk.outerHornC (n + 1) ⊓ SSet.stdSimplex.face {(1 : Fin (n + 2))}ᶜ :=
  SSet.Rezk.outerHorn_image_cofaceOne n

example (m : ℕ) (K : (Δ[m + 2] : SSet.{u}).Subcomplex)
    (h : SSet.Rezk.outerHornTail m ∉ K.obj (op ⦋m⦌)) :
    K ≤ SSet.Rezk.outerHornC (m + 2) :=
  SSet.Rezk.le_outerHornC_of_tail_not_mem m K h

example (n : ℕ) {X : SSet.{u}}
    (f : (Δ[n] : SSet.{u}) ⟶ X)
    (g : (SSet.Rezk.outerHornC (n + 1) : SSet.{u}) ⟶ X)
    (h : (SSet.horn n 0).ι ≫ f = SSet.Rezk.outerHornCoface n ≫ g) :
    ∃! d : (SSet.horn (n + 1) 0 : SSet.{u}) ⟶ X,
      SSet.horn.ι 0 (1 : Fin (n + 2)) (by intro h; have := congrArg Fin.val h; simp at this) ≫ d = f ∧
        SSet.Rezk.outerHornCInclusion n ≫ d = g :=
  SSet.Rezk.existsUnique_outerHornCDesc n f g h
