/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.FixedPoints
import Mathlib.Order.OrderIsoNat

/-!
# Kleene iteration under the ascending chain condition

In a complete lattice with no infinite strictly ascending chain, the iterates
`⊥ ≤ f ⊥ ≤ f (f ⊥) ≤ ⋯` of a monotone map `f` from the least element become constant, and the
value they reach is the least fixed point of `f`. The lattice may have chains of every finite
length, and `f` need not be continuous; for ω-Scott-continuous maps, Mathlib's
`fixedPoints.lfp_eq_sSup_iterate` gives the same formula without the chain condition.

## Main results

- `OrderHom.lfp_eq_iSup_iterate_of_wellFoundedGT`: `f.lfp = ⨆ n, f^[n] ⊥`, and some iterate
  `f^[k] ⊥` equals `f.lfp`.

## References

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University,
  version of October 15, 2026, Section 4.4.
-/

@[expose] public section

namespace OrderHom

variable {α : Type*} [CompleteLattice α] [WellFoundedGT α]

/-- **Kleene iteration reaches the least fixed point under the ascending chain condition.** Let `α`
be a complete lattice with no infinite strictly ascending chain, such as a lattice of finite height,
and let `f : α →o α` be monotone. Then the least fixed point of `f` is the supremum
`⨆ n, f^[n] ⊥` of the iterates of `f` from the least element, and it is one of these iterates: the
increasing chain `⊥ ≤ f ⊥ ≤ f (f ⊥) ≤ ⋯` reaches it after finitely many steps. No continuity of
`f` is assumed, and `α` may have chains of every finite length. (Møller and Schwartzbach, *Static
Program Analysis*, Section 4.4, for lattices of finite height) -/
theorem lfp_eq_iSup_iterate_of_wellFoundedGT (f : α →o α) :
    f.lfp = ⨆ n, f^[n] ⊥ ∧ ∃ k, f^[k] ⊥ = f.lfp := by
  have hle : ∀ n, f^[n] ⊥ ≤ f.lfp := fun n => by
    induction n with
    | zero => exact bot_le
    | succ n ih => rw [Function.iterate_succ_apply']; exact f.map_le_lfp ih
  obtain ⟨k, hk⟩ := WellFoundedGT.monotone_chain_condition
    ⟨fun n => f^[n] ⊥, f.monotone.monotone_iterate_of_le_map bot_le⟩
  have hfix : f (f^[k] ⊥) ≤ f^[k] ⊥ := by
    rw [← Function.iterate_succ_apply' f k]
    exact (hk (k + 1) k.le_succ).ge
  have hlfp : f^[k] ⊥ = f.lfp := le_antisymm (hle k) (f.lfp_le hfix)
  exact ⟨le_antisymm (hlfp ▸ le_iSup (fun n => f^[n] ⊥) k) (iSup_le hle), k, hlfp⟩

end OrderHom
