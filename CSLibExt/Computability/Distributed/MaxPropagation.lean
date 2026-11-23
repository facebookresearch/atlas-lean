/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic

/-!
# Synchronous maximum propagation

Nodes `Fin n` hold natural-number values. In each synchronous round, every node `i` replaces its
value by the maximum of its own value and the value at the node `ρ i` it hears from (`maxStep`);
on a unidirectional ring, `ρ` is the predecessor map. This is the max-propagation update of the
FloodMax algorithm (Lynch, Chapter 4) on a network in which every node hears from exactly one
node. It is not a leader-election protocol: there is no leader decision, no assumption that the
values are distinct, and no message counting.

* `maxStep_iterate_apply`: after `k` rounds, node `i` holds the maximum of the values at the
  nodes `ρ^[t] i` for `t ≤ k`.
* `maxStep_iterate_eq_sup`: if from every node `i` every node `j` is reached as `ρ^[k] i` for
  some `k ≤ n`, then after `n` rounds every node holds the maximum of all values. For `n = 0`
  there are no nodes and the statement is vacuous.

## References

* N. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 4.
-/

@[expose] public section

namespace Cslib.Distributed.MaxPropagation

/-- One synchronous round of maximum propagation on the nodes `Fin n`: node `i` replaces its
value by the maximum of its own value and the value at the node `ρ i` it hears from. On a
unidirectional ring, `ρ` is the predecessor map; no property of `ρ` is assumed here. -/
def maxStep {n : ℕ} (ρ : Fin n → Fin n) (s : Fin n → ℕ) (i : Fin n) : ℕ :=
  max (s i) (s (ρ i))

/-- After `k` rounds, node `i` holds the maximum of the values at the `k + 1` nodes
`ρ^[t] i`, `t ≤ k` (not necessarily distinct). -/
theorem maxStep_iterate_apply {n : ℕ} (ρ : Fin n → Fin n)
    (v : Fin n → ℕ) (k : ℕ) (i : Fin n) :
    ((maxStep ρ)^[k] v) i
      = (Finset.range (k + 1)).sup (fun t => v (ρ^[t] i)) := by
  induction k generalizing i with
  | zero =>
    simp
  | succ k ih =>
    have hstep : ((maxStep ρ)^[k + 1] v) i
        = max (((maxStep ρ)^[k] v) i) (((maxStep ρ)^[k] v) (ρ i)) := by
      rw [Function.iterate_succ_apply']
      rfl
    have hshift : ∀ t, v (ρ^[t] (ρ i)) = v (ρ^[t + 1] i) := by
      intro t
      exact congrArg v (Function.iterate_succ_apply ρ t i).symm
    rw [hstep, ih i, ih (ρ i)]
    simp only [hshift]
    apply le_antisymm
    · rw [max_le_iff]
      constructor
      · rw [Finset.sup_le_iff]
        intro t ht
        rw [Finset.mem_range] at ht
        exact Finset.le_sup (f := fun t => v (ρ^[t] i))
          (Finset.mem_range.mpr (by omega))
      · rw [Finset.sup_le_iff]
        intro t ht
        rw [Finset.mem_range] at ht
        exact Finset.le_sup (f := fun t => v (ρ^[t] i))
          (Finset.mem_range.mpr (by omega))
    · rw [Finset.sup_le_iff]
      intro t ht
      rw [Finset.mem_range] at ht
      by_cases htk : t < k + 1
      · calc v (ρ^[t] i)
            ≤ (Finset.range (k + 1)).sup (fun t => v (ρ^[t] i)) :=
              Finset.le_sup (f := fun t => v (ρ^[t] i))
                (Finset.mem_range.mpr htk)
          _ ≤ max ((Finset.range (k + 1)).sup (fun t => v (ρ^[t] i)))
              ((Finset.range (k + 1)).sup (fun t => v (ρ^[t + 1] i))) :=
              le_max_left _ _
      · have htk1 : t = k + 1 := by omega
        subst htk1
        calc v (ρ^[k + 1] i)
            ≤ (Finset.range (k + 1)).sup (fun t => v (ρ^[t + 1] i)) :=
              Finset.le_sup (f := fun t => v (ρ^[t + 1] i))
                (Finset.mem_range.mpr (Nat.lt_succ_self k))
          _ ≤ max ((Finset.range (k + 1)).sup (fun t => v (ρ^[t] i)))
              ((Finset.range (k + 1)).sup (fun t => v (ρ^[t + 1] i))) :=
              le_max_right _ _

/-- After `n` rounds every node holds the maximum `Finset.univ.sup v` of all values, provided
that from every node `i` every node `j` is reached as `ρ^[k] i` for some `k ≤ n` (hypothesis
`hρ`, with the non-strict bound `k ≤ n`). For `n = 0` there are no nodes and the conclusion
holds vacuously. -/
theorem maxStep_iterate_eq_sup {n : ℕ} (ρ : Fin n → Fin n)
    (v : Fin n → ℕ)
    (hρ : ∀ i j, ∃ k ≤ n, ρ^[k] i = j) :
    ∀ i, ((maxStep ρ)^[n] v) i = Finset.univ.sup v := by
  intro i
  rw [maxStep_iterate_apply]
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro t _
    exact Finset.le_sup (f := v) (Finset.mem_univ (ρ^[t] i))
  · rw [Finset.sup_le_iff]
    intro j _
    obtain ⟨k, hkn, hkj⟩ := hρ i j
    subst hkj
    exact Finset.le_sup (f := fun t => v (ρ^[t] i))
      (Finset.mem_range.mpr (by omega))

end Cslib.Distributed.MaxPropagation
