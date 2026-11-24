/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max
import MathlibExt.Combinatorics.Ramsey

@[expose] public section

namespace MetaMathlibExt

section

/-- The maximum minus the minimum of a pair `{a, b}` with `a < b` is `b - a`. -/
private theorem schur_pair_sub {N : ℕ} {a b : Fin N} (hab : a < b)
    (h : ({a, b} : Finset (Fin N)).Nonempty) :
    ((({a, b} : Finset (Fin N)).max' h : ℕ) - (({a, b} : Finset (Fin N)).min' h : ℕ)) =
      (b : ℕ) - a := by
  rw [Finset.max'_insert a {b} (Finset.singleton_nonempty b),
    Finset.min'_insert a {b} (Finset.singleton_nonempty b), Finset.max'_singleton,
    Finset.min'_singleton, max_eq_right hab.le, min_eq_left hab.le]

/-- **Schur's theorem.** For every integer $r \ge 1$ there is a natural number $S$ such that for
every coloring of the natural numbers with $r$ colors there are $x, y, z \in \{1, \dots, S\}$,
not necessarily distinct, with the same color and $x + y = z$.

The bound comes from Ramsey's theorem for pairs, by coloring each pair with the color of its
difference; it is not the Schur number $S(r)$, the largest $S$ for which some $r$-coloring of
$\{1, \dots, S\}$ has no such solution.

Proves `Wanted` entry `schur_ramsey`.

Source: https://en.wikipedia.org/wiki/Schur%27s_theorem (statement schur-ramsey-s1).
-/
theorem schur_ramsey : ∀ r : ℕ, 1 ≤ r →
    ∃ S : ℕ, ∀ c : ℕ → Fin r, ∃ x y z : ℕ,
      x ∈ Finset.Icc 1 S ∧ y ∈ Finset.Icc 1 S ∧ z ∈ Finset.Icc 1 S ∧
        c x = c y ∧ c x = c z ∧ x + y = z := by
  intro r hr
  obtain ⟨N, hN⟩ := MathlibExt.Combinatorics.Ramsey.ramsey_two_uniform (k := 3) (by omega : 0 < r)
  refine ⟨N, fun c => ?_⟩
  obtain ⟨S, hS, col, hcol⟩ := hN fun T =>
    if h : T.Nonempty then c ((T.max' h : ℕ) - (T.min' h : ℕ)) else c 0
  set f := S.orderEmbOfFin hS
  have hpair : ∀ i j : Fin 3, i < j → c ((f j : ℕ) - f i) = col := by
    intro i j hij
    have hlt : f i < f j := f.strictMono hij
    have hmem : ({f i, f j} : Finset (Fin N)) ∈ S.powersetCard 2 := by
      rw [Finset.mem_powersetCard, Finset.card_pair hlt.ne, Finset.insert_subset_iff,
        Finset.singleton_subset_iff]
      exact ⟨⟨S.orderEmbOfFin_mem hS i, S.orderEmbOfFin_mem hS j⟩, rfl⟩
    have h := hcol _ hmem
    rwa [dite_eq_left (Finset.insert_nonempty _ _), schur_pair_sub hlt] at h
  have l01 : (f 0 : ℕ) < f 1 := f.strictMono (by decide)
  have l12 : (f 1 : ℕ) < f 2 := f.strictMono (by decide)
  have hN2 : (f 2 : ℕ) < N := (f 2).isLt
  have h01 := hpair 0 1 (by decide)
  refine ⟨(f 1 : ℕ) - f 0, (f 2 : ℕ) - f 1, (f 2 : ℕ) - f 0, ?_, ?_, ?_,
    h01.trans (hpair 1 2 (by decide)).symm, h01.trans (hpair 0 2 (by decide)).symm, by omega⟩ <;>
    rw [Finset.mem_Icc] <;> omega

end

end MetaMathlibExt
