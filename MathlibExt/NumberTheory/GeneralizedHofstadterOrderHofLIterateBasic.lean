/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedHofstadterOrder

/-!
# Basic properties of the iterates of the Hofstadter image length

This module proves the substitution-length identity, successor formula, initial values,
recurrence, and strict growth properties of the iterates of `hofL`.

Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3
(arXiv:2410.00529; TeX source read for the definitions), Proposition 4.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem prefix_succ (k n : ℕ) :
    hofPrefix k (n + 1) = hofPrefix k n ++ [hofWord k n] := by
  simp [hofPrefix_eq_map, List.range_succ]

private theorem prefix_one (k : ℕ) : hofPrefix k 1 = [k] := by
  simp [hofPrefix_eq_map, hofWord, hofGrow, hofGrowAux]

private theorem iterate_append (k j : ℕ) (u v : List ℕ) :
    (hofTauList k)^[j] (u ++ v) = (hofTauList k)^[j] u ++ (hofTauList k)^[j] v := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, hofTauList, List.flatMap_append]

private theorem iterate_prefix (k j n : ℕ) :
    (hofTauList k)^[j] (hofPrefix k n) =
      hofPrefix k (((hofTauList k)^[j] (hofPrefix k n)).length) := by
  obtain ⟨r, hr, _⟩ := exists_hofGrow_eq k n
  have h : hofPrefix k n <+: (hofTauList k)^[r] [k] := by
    rw [hofPrefix, hr]
    exact List.take_prefix _ _
  have h' : (hofTauList k)^[j] (hofPrefix k n) <+: (hofTauList k)^[j + r] [k] := by
    rw [Function.iterate_add_apply]
    induction j with
    | zero => exact h
    | succ j ih => simpa only [Function.iterate_succ_apply'] using hofTauList_isPrefix ih
  conv_rhs => rw [hofPrefix_eq_map]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range]
    rw [hofWord_eq_getElem k i (j + r) (lt_of_lt_of_le hi h'.length_le)]
    exact h'.getElem hi

private theorem iterate_length (k j n : ℕ) :
    (hofL k)^[j] n = ((hofTauList k)^[j] (hofPrefix k n)).length := by
  induction j with
  | zero => simp [hofPrefix_eq_map]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    change (hofTauList k (hofPrefix k _)).length = _
    exact congrArg (fun w => (hofTauList k w).length) (iterate_prefix k j n).symm

private theorem iterate_zero (k j : ℕ) : (hofL k)^[j] 0 = 0 := by
  exact Function.iterate_fixed (by simp [hofL, hofPrefix_eq_map, hofTauList]) j

private theorem iterate_succ (k j n : ℕ) :
    (hofL k)^[j] (n + 1) =
      (hofL k)^[j] n + ((hofTauList k)^[j] [hofWord k n]).length := by
  rw [iterate_length, iterate_length, prefix_succ, iterate_append, List.length_append]

private theorem iterate_before_top {k a : ℕ} (j : ℕ) (h : a + j ≤ k) :
    (hofTauList k)^[j] [a] = [a + j] := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hne : a + j ≠ k := by omega
    simp only [hofTauList, List.flatMap_singleton, hofTau, ite_eq_right hne, Nat.add_assoc]

private theorem iterate_top_length {k : ℕ} (j : ℕ) (hj : j ≤ k) :
    ((hofTauList k)^[j] [k]).length = j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    have ht : hofTauList k [k] = [k] ++ [1] := by simp [hofTauList, hofTau]
    rw [ht, iterate_append, List.length_append, ih (by omega),
      iterate_before_top j (by omega)]
    simp [Nat.add_assoc]

private theorem iterate_top_recurrence {k j : ℕ} (hk : 1 ≤ k) (hj : k ≤ j) :
    (hofTauList k)^[j] [k] =
      (hofTauList k)^[j - 1] [k] ++ (hofTauList k)^[j - k] [k] := by
  have hj₁ : 1 ≤ j := hk.trans hj
  have ht : hofTauList k [k] = [k] ++ [1] := by simp [hofTauList, hofTau]
  have hsplit : j - 1 = (j - k) + (k - 1) := by omega
  have hreach : (hofTauList k)^[k - 1] [1] = [k] := by
    have he : 1 + (k - 1) = k := by omega
    simpa only [he] using iterate_before_top (k := k) (a := 1) (k - 1) he.le
  calc
    (hofTauList k)^[j] [k] = (hofTauList k)^[j - 1] (hofTauList k [k]) := by
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hj₁]
    _ = (hofTauList k)^[j - 1] [k] ++ (hofTauList k)^[j - 1] [1] := by
      rw [ht, iterate_append]
    _ = (hofTauList k)^[j - 1] [k] ++ (hofTauList k)^[j - k] [k] := by
      congr 1
      rw [hsplit, Function.iterate_add_apply, hreach]

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

private theorem iterate_index_strictMono (k n : ℕ) (hn : 1 ≤ n) :
    StrictMono fun i => (hofL k)^[i] n := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [Function.iterate_succ_apply']
  exact lt_hofL k (hn.trans (by
    simpa only [iterate_zero, Nat.add_zero] using ((hofL_strictMono k).iterate i).add_le_nat n 0))

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
Proposition 4 (`jis-2026-26.3.3-prop-4`). -/
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
    (hofL_strictMono k).iterate j, ?_, iterate_index_strictMono k⟩
  · intro hj
    rw [iterate_length, prefix_one, iterate_top_length j hj]
  · intro hj
    rw [iterate_length, prefix_one, iterate_top_recurrence hk hj, List.length_append,
      iterate_length, iterate_length, prefix_one]
  · intro n
    refine ⟨(by
      simpa only [iterate_zero, Nat.add_zero] using
        ((hofL_strictMono k).iterate j).add_le_nat n 0), ?_⟩
    constructor
    · intro he
      by_contra! h
      have hlt : n < (hofL k)^[j] n :=
        iterate_index_strictMono k n (by omega) (by omega : 0 < j)
      exact (Nat.ne_of_lt hlt) he.symm
    · rintro (rfl | rfl)
      · rfl
      · exact iterate_zero k j

end

end MetaMathlibExt
