/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image

@[expose] public section

/-!
# Gluing functions along a finset

`pasteOn A x z` glues a function on a finset `A` and a function on its complement into a
function on the whole index type. `finsetMapComplEquiv` transports the complement of a finset
along a permutation. Mathlib's `Finset.equivMap` transports the finset itself.

Extracted from the absolutely-maximally-entangled-state development now in
`PhyslibExt.QuantumInfo.AbsolutelyMaximallyEntangled`.
-/

namespace MetaMathlibExt

/-- For a finite type `α` with decidable equality, a permutation `e` of `α` restricts to an
equivalence between the complement of a finset `S` and the complement of its image
`S.map e.toEmbedding`. -/
def finsetMapComplEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (S : Finset α) :
    ↥(Sᶜ) ≃ ↥((S.map e.toEmbedding)ᶜ) :=
  e.subtypeEquiv fun x => by
    simp only [Finset.mem_compl, Finset.mem_map_equiv, Equiv.symm_apply_apply]

/-- Glue a function defined on a finset `A` and a function defined on its complement into
a function on the whole index type. -/
def pasteOn {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) : ι → R :=
  fun i => if hi : i ∈ A then x ⟨i, hi⟩ else z ⟨i, hi⟩

/-- On `A`, `pasteOn` is the first function. -/
@[simp] lemma pasteOn_mem {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) (i : A) :
    pasteOn A x z i.1 = x i := by simp [pasteOn, i.2]

/-- Off `A`, `pasteOn` is the second function. -/
@[simp] lemma pasteOn_not_mem {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) (i : {i : ι // i ∉ A}) :
    pasteOn A x z i.1 = z i := by simp [pasteOn, i.2]

end MetaMathlibExt
