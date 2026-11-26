/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Embedding
import MathlibExt.Combinatorics.Additive.ConsecutiveOrthogonal

/-!
# Davenport constant of an elementary abelian 2-group

The nonzero coefficients of a dependence over `ZMod 2` select a nonempty zero-sum
subsequence. In the other direction, a nonempty subset of the coordinate vectors has a
nonzero coordinate in its sum.

## References

- Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants of `ℤ_n`*,
  INTEGERS 24 (2024), Article A38, pp. 1–16, Theorem 4.1.
- John E. Olson, *A combinatorial problem on finite Abelian groups, I*, Journal of Number Theory
  1(1) (1969), pp. 8–10. Theorem 4.1 above is a special case of Olson's result for abelian
  p-groups.
-/

namespace MetaMathlibExt

set_option quotPrecheck false in
/-- The set of positive `k` such that every length-`k` sequence in `M` has an `A`-weighted
zero-sum subsequence; `D_A(M)` is its least element. -/
local notation "davenportSet" R:max M:max A:max => {k : ℕ | 0 < k ∧ ∀ x : Fin k → M,
  ∃ I : Finset (Fin k), I.Nonempty ∧
    ∃ a : Fin k → R, (∀ i ∈ I, a i ∈ A) ∧ ∑ i ∈ I, a i • x i = 0}

/-- **Davenport constant of $\mathbb{Z}_2^a$.** Let $\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$. For
every natural number $a$, the least positive integer $k$ such that every sequence of $k$ elements
of the group $\mathbb{Z}_2^a$ has a nonempty subsequence with sum zero is $a + 1$; that is, the
Davenport constant of $\mathbb{Z}_2^a$ is $a + 1$.

The paper states this for positive $a$; for $a = 0$ both sides equal $1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 4.1 (`integers-2024-A38-thm-4-1`). -/
public theorem davenport_zmod_two_pow (a : ℕ) :
    IsLeast (davenportSet (ZMod 2) (Fin a → ZMod 2) ({1} : Set (ZMod 2))) (a + 1) := by
  refine ⟨⟨Nat.succ_pos a, fun x => ?_⟩, ?_⟩
  · -- Apply the independently proved orthogonality lemma to the coordinate rows of `x`.
    obtain ⟨w, hw, horth⟩ := exists_ne_zero_orthogonal le_rfl (fun j i => x i j)
    have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    refine ⟨Finset.univ.filter (fun i => w i = 1), ?_, fun _ => 1, fun _ _ => rfl, ?_⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, (h01 (w i)).resolve_left hi⟩⟩
    · funext j
      simp only [one_smul, Finset.sum_apply, Pi.zero_apply, Finset.sum_filter]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans (horth j)
      rcases h01 (w i) with h | h <;> simp [h]
  · intro k hk
    by_contra! hlt
    -- The first `k` coordinate vectors cannot have a nonempty zero-sum subsequence.
    let e : Fin k ↪ Fin a := Fin.castLEEmb (Nat.le_of_lt_succ hlt)
    let x (i : Fin k) (j : Fin a) : ZMod 2 := if j = e i then 1 else 0
    obtain ⟨I, ⟨i, hi⟩, w, hw, hsum⟩ := hk.2 x
    have hcoord := congrFun hsum (e i)
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hcoord
    rw [Finset.sum_eq_single_of_mem i hi] at hcoord
    · have hwi : w i = 1 := hw i hi
      simp [x, hwi] at hcoord
    · intro j _ hji
      simp [x, Ne.symm (e.injective.ne hji)]

end MetaMathlibExt
