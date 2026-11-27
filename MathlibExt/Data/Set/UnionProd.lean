/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Equiv.Set

/-!
# The union product of two sets

For `s ⊆ α` and `t ⊆ β`, `s.unionProd t` is the subset
`(α × t) ∪ (s × β)` of `α × β`.  It is the subset underlying the
standard product of pairs.
-/

@[expose] public section

namespace Set

variable {α β γ α' β' : Type*}

/-- The subset `(α × t) ∪ (s × β)` underlying the product of two pairs. -/
def unionProd (s : Set α) (t : Set β) : Set (α × β) :=
  univ ×ˢ t ∪ s ×ˢ univ

@[simp]
theorem mem_unionProd {s : Set α} {t : Set β} {x : α × β} :
    x ∈ s.unionProd t ↔ x.1 ∈ s ∨ x.2 ∈ t := by
  simp [unionProd, or_comm]

/-- Product maps preserve union products when their components preserve the
corresponding subsets. -/
theorem MapsTo.unionProd {s : Set α} {t : Set β} {s' : Set α'} {t' : Set β'}
    {f : α → α'} {g : β → β'} (hf : MapsTo f s s') (hg : MapsTo g t t') :
    MapsTo (Prod.map f g) (s.unionProd t) (s'.unionProd t') := by
  rintro ⟨x, y⟩ h
  rw [mem_unionProd] at h ⊢
  exact h.imp (fun hx ↦ hf hx) (fun hy ↦ hg hy)

/-- The product associator identifies the two bracketings of a union product. -/
@[simp]
theorem prodAssoc_preimage_unionProd (s : Set α) (t : Set β) (u : Set γ) :
    Equiv.prodAssoc α β γ ⁻¹' s.unionProd (t.unionProd u) =
      (s.unionProd t).unionProd u := by
  ext ⟨⟨x, y⟩, z⟩
  simp only [mem_preimage, mem_unionProd, Equiv.prodAssoc_apply]
  exact or_assoc.symm

/-- The inverse product associator identifies the two bracketings of a union product. -/
@[simp]
theorem prodAssoc_symm_preimage_unionProd (s : Set α) (t : Set β) (u : Set γ) :
    (Equiv.prodAssoc α β γ).symm ⁻¹' (s.unionProd t).unionProd u =
      s.unionProd (t.unionProd u) := by
  ext ⟨x, y, z⟩
  simp only [mem_preimage, mem_unionProd, Equiv.prodAssoc_symm_apply]
  exact or_assoc

/-- `PUnit` with the empty subset is a right unit for union products. -/
@[simp]
theorem prodPUnit_preimage_unionProd (s : Set α) :
    Equiv.prodPUnit α ⁻¹' s = s.unionProd (∅ : Set PUnit) := by
  ext ⟨x, y⟩
  simp

/-- `PUnit` with the empty subset is a left unit for union products. -/
@[simp]
theorem punitProd_preimage_unionProd (s : Set α) :
    Equiv.punitProd α ⁻¹' s = (∅ : Set PUnit).unionProd s := by
  ext ⟨x, y⟩
  simp

/-- Swapping factors swaps the two subsets in a union product. -/
@[simp]
theorem prodComm_preimage_unionProd (s : Set α) (t : Set β) :
    Equiv.prodComm α β ⁻¹' t.unionProd s = s.unionProd t := by
  ext ⟨x, y⟩
  simp [or_comm]

end Set
