/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
module

/-
Completed proof port; original Apache 2.0 author/license header retained.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Order/Hom/ULift.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only import paths and the TauCeti helper namespace are adapted.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.Order.Hom.Basic

/-!
# Range of lifted order homomorphisms

Mathlib's `OrderHom.uliftMap` lifts an order homomorphism `f : α →o β` to
`ULift α →o ULift β`. This file records that its range consists of the lifts of the elements of the
range of `f`. For instance, the coface maps `(SimplexCategory.δ j).toOrderHom.uliftMap` between the
`ULift (Fin _)` index types of simplicial thickenings inherit their range from `Fin.succAbove`.
(Injectivity of the lift is Mathlib's `ULift.map_injective`, since the underlying function of
`f.uliftMap` is `ULift.map f`.)
-/

public section

namespace OrderHom

variable {α β : Type*} [Preorder α] [Preorder β] {f : α →o β}

/-- An element of `ULift β` is in the range of `f.uliftMap` if and only if its underlying element
is in the range of `f`. -/
theorem mem_range_uliftMap_iff {x : ULift β} : x ∈ Set.range f.uliftMap ↔ x.down ∈ Set.range f :=
  ⟨fun ⟨y, hy⟩ ↦ ⟨y.down, congrArg ULift.down hy⟩, fun ⟨y, hy⟩ ↦ ⟨⟨y⟩, ULift.ext hy⟩⟩

end OrderHom

end
