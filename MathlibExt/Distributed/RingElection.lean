/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Ring election by max propagation

On a ring with predecessor rotation `ρ`, each round every
node adopts the maximum of its own value and its
predecessor's. After `n` rounds every node holds the
global maximum, provided iterates of `ρ` reach every node
within `n` steps. The Hirschberg-Sinclair message bound
is not included here.
-/

@[expose] public section

/-- Hirschberg-Sinclair election on a ring, max-propagation
model (core of DPA-03). Nodes are `Fin n` arranged in a
ring; in each round every node adopts the maximum of its
own value and its predecessor's value (messages move one
step per round in one direction). After `k` rounds the
value at `i` is the maximum of the `k + 1` ids ending at
`i`. Ids are a function `id : Fin n → ℕ`. The predecessor
of `i` is `i - 1` in the cyclic sense, handled by
iterating a shift function on indices: we use the state as
a function and a fixed rotation `ρ : Fin n → Fin n`
(bijective, the predecessor map), kept abstract. -/
def electStep {n : ℕ} (ρ : Fin n → Fin n) (s : Fin n → ℕ) (i : Fin n) : ℕ :=
  max (s i) (s (ρ i))

private theorem electStep_iterate_eq_range_sup {n : ℕ} (ρ : Fin n → Fin n)
    (v : Fin n → ℕ) (k : ℕ) (i : Fin n) :
    ((electStep ρ)^[k] v) i
      = (Finset.range (k + 1)).sup (fun t => v (ρ^[t] i)) := by
  induction k generalizing i with
  | zero =>
    simp
  | succ k ih =>
    have hstep : ((electStep ρ)^[k + 1] v) i
        = max (((electStep ρ)^[k] v) i) (((electStep ρ)^[k] v) (ρ i)) := by
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

/-- After one full set of `n` rounds (state iterated `n`
times), every node holds the global maximum of `id`,
provided `ρ` generates the whole ring in the sense that
iterating `ρ` from any node reaches every node within
`n` steps: hypothesis `hρ : ∀ i j, ∃ k < n, ρ^[k] i = j`
(with `n ≥ 1` so the window covers all nodes). -/
theorem electStep_iterate_eq_max {n : ℕ} (ρ : Fin n → Fin n)
    (id : Fin n → ℕ)
    (hρ : ∀ i j, ∃ k ≤ n, ρ^[k] i = j) :
    ∀ i, ((electStep ρ)^[n] id) i = Finset.univ.sup id := by
  intro i
  rw [electStep_iterate_eq_range_sup]
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro t _
    exact Finset.le_sup (f := id) (Finset.mem_univ (ρ^[t] i))
  · rw [Finset.sup_le_iff]
    intro j _
    obtain ⟨k, hkn, hkj⟩ := hρ i j
    subst hkj
    exact Finset.le_sup (f := fun t => id (ρ^[t] i))
      (Finset.mem_range.mpr (by omega))

#print axioms electStep_iterate_eq_max

end
