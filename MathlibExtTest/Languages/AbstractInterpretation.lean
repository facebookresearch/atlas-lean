/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Languages.AbstractInterpretation

@[expose] public section

/-- Boundary check: the trivial top domain is sound for the
identity transformer on a two-element state space. -/
example : ∀ a : PUnit, (fun _ => PUnit.unit) ((fun s : Set (Fin 2) => s) (Set.univ)) ≤ a :=
  top_domain_sound (fun s : Set (Fin 2) => s)

/-- Boundary check: fixpoint soundness through the identity
Galois connection (concrete and abstract domains coincide). -/
example :
    (fun s : Set (Fin 2) => s)
        (OrderHom.lfp ⟨fun s : Set (Fin 2) => s, fun _ _ h => h⟩)
      ≤ OrderHom.lfp ⟨fun s : Set (Fin 2) => s, fun _ _ h => h⟩ :=
  abs_lfp_sound (fun s : Set (Fin 2) => s) (fun s : Set (Fin 2) => s)
    (fun a b => Iff.rfl)
    (fun s : Set (Fin 2) => s) (fun _ _ h => h)
    (fun s : Set (Fin 2) => s) (fun _ _ h => h) (fun a => le_refl _)
