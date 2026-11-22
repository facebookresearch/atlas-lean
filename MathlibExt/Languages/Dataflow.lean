/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.FixedPoints
import Mathlib.Tactic.Push

@[expose] public section

/-- Kildall iteration core of VER-15 (framework level; the CFG
worklist algorithm and the live-variables instance are downstream
parts of the roadmap package). On a finite partial order with a
bottom element, iterating a monotone transfer function from `⊥`
stabilizes at a fixpoint. -/
theorem kildall_stabilizes {A : Type*} [PartialOrder A] [OrderBot A]
    [Finite A] (F : A → A) (hF : Monotone F) :
    ∃ k, F^[k] (⊥ : A) = F (F^[k] (⊥ : A)) := by
  by_contra hcon
  push Not at hcon
  have hchain : ∀ k : ℕ, F^[k] (⊥ : A) ≤ F^[k.succ] (⊥ : A) := by
    intro k
    induction k with
    | zero => exact bot_le
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hF ih
  have hlt : ∀ n : ℕ, F^[n] (⊥ : A) < F^[n + 1] (⊥ : A) := by
    intro n
    rw [show n + 1 = n.succ from rfl]
    apply lt_of_le_of_ne (hchain n)
    rw [Function.iterate_succ_apply']
    exact hcon n
  have hmono : StrictMono (fun k : ℕ => F^[k] (⊥ : A)) :=
    strictMono_nat_of_lt_succ hlt
  exact not_injective_infinite_finite _ hmono.injective

/-- On any complete lattice, finite or not, an iterate of a monotone `F`
from `⊥` that is a fixpoint of `F` is the least fixpoint of `F`. -/
theorem kildall_eq_lfp {A : Type*} [CompleteLattice A]
    (F : A → A) (hF : Monotone F) (k : ℕ)
    (hstab : F^[k] (⊥ : A) = F (F^[k] (⊥ : A))) :
    F^[k] (⊥ : A) = OrderHom.lfp ⟨F, hF⟩ := by
  have hle : ∀ j : ℕ, F^[j] (⊥ : A) ≤ OrderHom.lfp ⟨F, hF⟩ := by
    intro j
    induction j with
    | zero => exact bot_le
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hfix : F (OrderHom.lfp ⟨F, hF⟩) = OrderHom.lfp ⟨F, hF⟩ :=
        OrderHom.map_lfp ⟨F, hF⟩
      calc F (F^[n] (⊥ : A)) ≤ F (OrderHom.lfp ⟨F, hF⟩) := hF ih
        _ = OrderHom.lfp ⟨F, hF⟩ := hfix
  refine le_antisymm (hle k) ?_
  apply OrderHom.lfp_le
  change F (F^[k] (⊥ : A)) ≤ F^[k] (⊥ : A)
  exact le_of_eq hstab.symm
