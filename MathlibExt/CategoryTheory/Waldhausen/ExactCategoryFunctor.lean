/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor

/-!
# Exact-category functors as Waldhausen-exact functors

An additive Quillen-exact functor between exact categories is explicitly
Waldhausen exact for the named standard exact-category Waldhausen structures.
The result is a proof term, not an instance: exact categories may carry other
Waldhausen structures.

No global Waldhausen structure, general pushout-preservation instance, Stage
map, approximation factorization, comma-category result, or K-theory
consequence is introduced here.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor.IsWaldhausenExact

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- An additive exact functor is Waldhausen exact for the named standard
exact-category Waldhausen structures.  The structures are selected locally;
no global instance is installed. -/
theorem ofExactCategory (F : C ⥤ D) [F.Additive] [F.IsExact] :
    letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
    letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
    F.IsWaldhausenExact := by
  let _ : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let _ : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  refine
    { map_isZero := ?_
      map_cofibration := ?_
      map_weakEquivalence := ?_
      map_pushout := ?_ }
  · intro X hX
    exact F.map_isZero hX
  · intro X Y f hf
    change IsAdmissibleMono f at hf
    change IsAdmissibleMono (F.map f)
    obtain ⟨Q, q, w, hS⟩ := hf
    exact ⟨F.obj Q, F.map q, by rw [← F.map_comp, w, F.map_zero],
      F.map_admissibleExact _ hS⟩
  · intro X Y f hf
    change IsIso f at hf
    change IsIso (F.map f)
    let _ : IsIso f := hf
    infer_instance
  · intro X Y X' P i f inl inr hi hpo
    change IsAdmissibleMono i at hi
    exact F.map_isPushout_of_isAdmissibleMono hpo hi

end CategoryTheory.Functor.IsWaldhausenExact
