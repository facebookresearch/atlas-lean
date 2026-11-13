/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Andres Barei Bueno
-/
module

public import MathlibExt.CategoryTheory.Tensor.Fusion

@[expose] public section

namespace MathlibExtTest.CategoryTheory.Tensor.Fusion

open MetaMathlibExt

-- Algebra 477: Fusion Category

theorem tensorUnit_neq_zero.{u,v,w} (k : Type w) [Field k]
  (C : Type u) [CategoryTheory.Category.{v} C] [Fusion k C] :
  CategoryTheory.CategoryStruct.id (CategoryTheory.MonoidalCategoryStruct.tensorUnit C) ≠ 0
  := by
    let _ : CategoryTheory.Simple
        (CategoryTheory.MonoidalCategoryStruct.tensorUnit C) :=
      Fusion.simple_monoidal_unit (k := k) (C := C)
    exact CategoryTheory.id_nonzero _

-- Algebra 478: Rank of a fusion category

theorem two_simples_from_rank_ge_two.{u,v,w} (k : Type w) [Field k]
  (C : Type u) [CategoryTheory.Category.{v} C] [Fusion k C] :
    Fusion.Rank k C ≥ 2 →
    ∃ S T : C, CategoryTheory.Simple S ∧ CategoryTheory.Simple T ∧
      IsEmpty (S ≅ T)
  := by
    intro hyp
    -- unfold Fusion.Rank at hyp
    obtain ⟨S, hSimple, hClassifies⟩ :=
      Exists.choose_spec
        (Fusion.finite_simples (k := k) (C := C))
    let i : Fin (Fusion.Rank k C) := ⟨0, by omega⟩
    let j : Fin (Fusion.Rank k C) := ⟨1, by omega⟩
    use S i, S j
    constructor
    · exact hSimple i
    · constructor
      · exact hSimple j
      · rw [← not_nonempty_iff]
        rintro ⟨iso⟩
        obtain ⟨r, _, hUnique⟩ := hClassifies (S i) (hSimple i)
        have hj : j = r := hUnique j ⟨iso⟩
        have hi : i = r := hUnique i ⟨CategoryTheory.Iso.refl (S i)⟩
        have hij : i = j := hi.trans hj.symm
        have hvalues : (0 : ℕ) = 1 := by simpa [i, j] using congrArg Fin.val hij
        exact Nat.zero_ne_one hvalues

end MathlibExtTest.CategoryTheory.Tensor.Fusion

end
