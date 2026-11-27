/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedHofstadterOrder
import Mathlib.Order.Iterate

/-!
# Basic properties of the iterates of the Hofstadter image length

This module proves the substitution-length identity, successor formula, initial values,
recurrence, and strict growth properties of the iterates of `hofL`.

Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3
(arXiv:2410.00529; TeX source read for the definitions), Proposition 2.3.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem prefix_one (k : ℕ) : hofPrefix k 1 = [k] := by
  simp [hofPrefix_eq_map, hofWord, hofGrow, hofGrowAux]

private theorem iterate_length (k j n : ℕ) :
    (hofL k)^[j] n = ((hofTauList k)^[j] (hofPrefix k n)).length := by
  induction j with
  | zero => simp [hofPrefix_eq_map]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    change (hofTauList k (hofPrefix k _)).length = _
    exact congrArg (fun w => (hofTauList k w).length)
      (hofCount_one_succ_le.iterate_prefix (k := k) (j := j) (n := n)).symm

private theorem iterate_zero (k j : ℕ) : (hofL k)^[j] 0 = 0 := by
  rw [iterate_length]
  exact hofCount_one_succ_le.image_zero k j

private theorem iterate_succ (k j n : ℕ) :
    (hofL k)^[j] (n + 1) =
      (hofL k)^[j] n + ((hofTauList k)^[j] [hofWord k n]).length := by
  rw [iterate_length, iterate_length]
  exact hofCount_one_succ_le.image_succ k j n

private theorem hofL_strictMono (k : ℕ) : StrictMono (hofL k) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h : hofL k (n + 1) = hofL k n + (hofTau k (hofWord k n)).length := by
    simpa [hofTauList] using iterate_succ k 1 n
  have hpos := one_le_length_hofTau k (hofWord k n)
  omega

private theorem lt_hofL (k : ℕ) {n : ℕ} (hn : 1 ≤ n) : n < hofL k n := by
  have h := (hofL_strictMono k).add_le_nat (n - 1) 1
  have h₁ : hofL k 1 = 2 := by simp [hofL, prefix_one, hofTauList, hofTau]
  rw [h₁, Nat.sub_add_cancel hn] at h
  omega

/-- **Basic properties of the iterates of $L_k$.** Let $k \ge 1$, let $x_k$ be the fixed point of
the substitution $\tau_k$, with letters $x_k[0], x_k[1], \dots$ and prefixes
$x_k[0:n) = x_k[0] \cdots x_k[n-1]$, let $L_k(n) = |\tau_k(x_k[0:n))|$, and write $f^j$ for the
$j$-fold iterate of a map $f$ (so $f^0$ is the identity). Then for every $j \ge 0$:
(1) $L_k^j(n) = |\tau_k^j(x_k[0:n))|$ for every $n$;
(2) $L_k^j(0) = 0$, and $L_k^j(n+1) = L_k^j(n) + |\tau_k^j(x_k[n])|$ for every $n$;
(3) $L_k^j(1) = j + 1$ if $j \le k$, and $L_k^j(1) = L_k^{j-1}(1) + L_k^{j-k}(1)$ if $j \ge k$;
(4) $n \mapsto L_k^j(n)$ is strictly increasing;
(5) $L_k^j(n) \ge n$ for every $n$, with equality if and only if $j = 0$ or $n = 0$;
(6) for every $n \ge 1$, the sequence $i \mapsto L_k^i(n)$ is strictly increasing.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 2.3 (`jis-2026-26.3.3-prop-4`). -/
public theorem hofL_iterate_basic {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (∀ n, (hofL k)^[j] n = ((hofTauList k)^[j] (hofPrefix k n)).length) ∧
      (hofL k)^[j] 0 = 0 ∧
      (∀ n, (hofL k)^[j] (n + 1) =
        (hofL k)^[j] n + ((hofTauList k)^[j] [hofWord k n]).length) ∧
      (j ≤ k → (hofL k)^[j] 1 = j + 1) ∧
      (k ≤ j → (hofL k)^[j] 1 = (hofL k)^[j - 1] 1 + (hofL k)^[j - k] 1) ∧
      StrictMono (hofL k)^[j] ∧
      (∀ n, n ≤ (hofL k)^[j] n ∧ ((hofL k)^[j] n = n ↔ j = 0 ∨ n = 0)) ∧
      (∀ n, 1 ≤ n → StrictMono fun i => (hofL k)^[i] n)
    := by
  refine ⟨iterate_length k j, iterate_zero k j, iterate_succ k j, ?_, ?_,
    (hofL_strictMono k).iterate j, ?_,
    fun n hn => StrictMono.strictMono_iterate_of_lt_map (hofL_strictMono k) (lt_hofL k hn)⟩
  · intro hj
    rw [iterate_length, prefix_one, (hofTauList_iterate_self hk j).1 hj, List.length_cons,
      List.length_range']
  · intro hj
    rw [iterate_length, prefix_one, (hofTauList_iterate_self hk j).2 hj, List.length_append,
      iterate_length, iterate_length, prefix_one]
  · intro n
    refine ⟨(by
      simpa only [iterate_zero, Nat.add_zero] using
        ((hofL_strictMono k).iterate j).add_le_nat n 0), ?_⟩
    constructor
    · intro he
      by_contra! h
      have hlt : n < (hofL k)^[j] n :=
        StrictMono.strictMono_iterate_of_lt_map (hofL_strictMono k) (lt_hofL k (by omega))
          (by omega : 0 < j)
      exact (Nat.ne_of_lt hlt) he.symm
    · rintro (rfl | rfl)
      · rfl
      · exact iterate_zero k j

end

end MetaMathlibExt
