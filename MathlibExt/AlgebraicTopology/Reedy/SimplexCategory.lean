/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.Reedy.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Order.SuccPred.Nat

/-!
# The Reedy structure on the simplex category

Epimorphisms lower simplex degree, monomorphisms raise it, and the canonical image factorization is
the unique epi--mono factorization because `SimplexCategory` is skeletal.

This file supplies structural Reedy data only.  It defines no diagram model structure, latching or
matching object, or model-category instance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra

namespace SimplexCategory

/-- The canonical Reedy structure on the simplex category: epimorphisms lower degree and
monomorphisms raise it. -/
noncomputable def reedyStructure :
    ReedyStructure (epimorphisms SimplexCategory)
      (monomorphisms SimplexCategory) ℕ where
  deg X := X.len
  lt₁ {X Y} f hf hf' := by
    let _ : Epi f := hf
    apply lt_of_le_of_ne (len_le_of_epi f)
    intro h
    apply hf'
    obtain rfl : X = Y := by aesop
    rw [eq_id_of_epi f]
    exact .mk X
  lt₂ {X Y} f hf hf' := by
    let _ : Mono f := hf
    apply lt_of_le_of_ne (len_le_of_mono f)
    intro h
    apply hf'
    obtain rfl : X = Y := by aesop
    rw [eq_id_of_mono f]
    exact .mk X
  nonempty_unique {X Y} f := by
    let canonical :
        (epimorphisms SimplexCategory).MapFactorizationData
          (monomorphisms SimplexCategory) f :=
      .mk (image f) (factorThruImage f) (image.ι f) (image.fac f)
        (by infer_instance) (by infer_instance)
    refine ⟨{ default := canonical, uniq := ?_ }⟩
    rintro ⟨Z, i, p, hfac, hi, hp⟩
    let _ : Epi i := hi
    let _ : Mono p := hp
    obtain rfl : image f = Z := image_eq hfac
    have hi' : factorThruImage f = i := factorThruImage_eq hfac
    have hp' : image.ι f = p := image_ι_eq hfac
    subst i
    subst p
    rfl

end SimplexCategory
