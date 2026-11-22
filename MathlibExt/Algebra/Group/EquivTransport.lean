/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.TransferInstance
public meta import Mathlib.Tactic.FastInstance

/-!
# Group transport with explicit instance fields

The original equivalence transports the given group. Explicit fields
keep instance elaboration from unfolding a large composed equivalence.
The multiplication readback retains both original equivalence functions.
-/

@[expose] public section

noncomputable section

universe u v

namespace EquivTransport

/-- Transport the actual source group through the full original equivalence. -/
@[instance_reducible]
def group {A : Type u} {B : Type v} [Group B] (e : A ≃ B) : Group A :=
  fast_instance% e.group

/-- The complete original forward function preserves the transported multiplication. -/
theorem apply_mul {A : Type u} {B : Type v} [Group B] (e : A ≃ B) (a b : A) :
    letI := group e
    e (a * b) = e a * e b := by
  let := group e
  change e (e.symm (e a * e b)) = _
  exact e.apply_symm_apply _

/-- A proved square with the two original equivalences transports the actual group map. -/
def map {A B A' B' : Type*} [Group B] [Group B'] (e : A ≃ B) (e' : A' ≃ B')
    (f : A → A') (h : B →* B') (hf : ∀ a, e' (f a) = h (e a)) :
    letI := group e
    letI := group e'
    A →* A' := by
  letI := group e
  letI := group e'
  exact MonoidHom.mk' f (fun a b => by
    apply e'.injective
    rw [hf, apply_mul, h.map_mul, ← hf, ← hf, apply_mul])

/-- The entire transported map function remains the original source-side function of that square. -/
theorem map_apply {A B A' B' : Type*} [Group B] [Group B'] (e : A ≃ B) (e' : A' ≃ B')
    (f : A → A') (h : B →* B') (hf : ∀ a, e' (f a) = h (e a)) (a : A) :
    map e e' f h hf a = f a := rfl

end EquivTransport
