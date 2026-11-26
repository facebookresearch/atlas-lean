/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.Sequences.ThrowbackSequences

/-!
# Recursive bound on throwback leader times

For an injective sequence of positive integers, the time to become leader at position `n`
is bounded recursively by the times at position `n - 1` and at the number of values below `n`.
-/

namespace MetaMathlibExt

namespace throwback_leader_time_le

private abbrev row (X : ℕ → ℕ) (t : ℕ) : ℕ → ℕ := (throwback id)^[t] X

/-- The permutation taking each position after a throwback to its previous position. -/
private def prefixCycle (l : ℕ) : Equiv.Perm ℕ where
  toFun i := if i < l then i + 1 else if i = l then 0 else i
  invFun i := if i = 0 then l else if i ≤ l then i - 1 else i
  left_inv := by
    intro i
    dsimp
    rcases lt_trichotomy i l with h | rfl | h
    · simp [h, show i + 1 ≤ l by omega]
    · simp
    · simp [h.not_gt, h.ne', h.not_ge, show i ≠ 0 by omega]
  right_inv := by
    intro i
    dsimp
    split_ifs <;> omega

private theorem row_succ (X : ℕ → ℕ) (t : ℕ) :
    row X (t + 1) = row X t ∘ prefixCycle (row X t 0) := by
  rw [row, Function.iterate_succ_apply']
  funext i
  simp [throwback, prefixCycle]
  split_ifs <;> rfl

private theorem row_order (X : ℕ → ℕ) (t : ℕ) :
    ∃ e : Equiv.Perm ℕ, row X t = X ∘ e := by
  induction t with
  | zero => exact ⟨Equiv.refl _, rfl⟩
  | succ t ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨(prefixCycle (row X t 0)).trans e, ?_⟩
    rw [row_succ, Equiv.coe_trans, ← Function.comp_assoc, ← he]

/-- Until a leader of value at least `n` appears, any such entry stays ahead of, or
coincides with, an entry that started at or behind it. -/
private theorem ordered_until_large_leader (X : ℕ → ℕ) {m n i j : ℕ}
    (hij : i ≤ j) (hi : n ≤ row X m i) (k : ℕ)
    (hsmall : ∀ t < k, row X (m + t) 0 < n) :
    ∃ p q, p ≤ q ∧ n ≤ row X (m + k) p ∧ row X (m + k) q = row X m j := by
  induction k with
  | zero => exact ⟨i, j, hij, hi, rfl⟩
  | succ k ih =>
    obtain ⟨p, q, hpq, hp, hq⟩ := ih fun t ht => hsmall t (Nat.lt_succ_of_lt ht)
    let e := prefixCycle (row X (m + k) 0)
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact (hsmall k (Nat.lt_succ_self _)).not_ge hp
    have hq0 : q ≠ 0 := by omega
    have hmove (u : ℕ) : row X (m + (k + 1)) (e.symm u) = row X (m + k) u := by
      rw [← Nat.add_assoc, row_succ, Function.comp_apply]
      exact congrArg (row X (m + k)) (e.apply_symm_apply u)
    refine ⟨e.symm p, e.symm q, ?_, (hmove p).symm ▸ hp, (hmove q).trans hq⟩
    dsimp [e, prefixCycle]
    rw [ite_eq_right hp0, ite_eq_right hq0]
    split_ifs <;> omega

end throwback_leader_time_le

open throwback_leader_time_le in
/-- **Recursive bound on the time to become leader.** Let $X = (x_0, x_1, \dots)$ be a sequence
of pairwise distinct positive integers, with positions numbered from $0$, the leader being at
position $0$. Let $\tau$ be the throwback and $T(X) = (t_0, t_1, \dots)$ the throwback
sequence, so $t_k$ is the leader of $\tau^k(X)$. Let $n \ge 1$, and let $N$ be the number of
indices $i$ with $x_i < n$. Suppose $a$ and $b$ are natural numbers such that for every
$m \ge 0$, the term at position $n - 1$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le a$, and
the term at position $N$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le b$. Then for every
$m \ge 0$, the term at position $n$ of $\tau^m(X)$ equals $t_{m+k}$ for some $k \le a + b + 1$.

This is the bound $M(n) \le M(n - 1) + M(N) + 1$ of the source, stated for upper bounds, where
$M(n)$ is the largest number of throwbacks the term at position $n$ of any $\tau^m(X)$ needs to
become leader.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 3 (`jis-2025-25.5.1-lem-3`). -/
public theorem throwback_leader_time_le (X : ℕ → ℕ) (hX : ∀ n, 0 < X n)
    (hinj : Function.Injective X) (n : ℕ) (hn : 0 < n) (a b : ℕ)
    (ha : ∀ m, ∃ k ≤ a, throwbackSequence X (m + k) = ((throwback id)^[m] X) (n - 1))
    (hb : ∀ m, ∃ k ≤ b,
      throwbackSequence X (m + k) = ((throwback id)^[m] X) (Set.ncard {i | X i < n})) :
    ∀ m, ∃ k ≤ a + b + 1, throwbackSequence X (m + k) = ((throwback id)^[m] X) n := by
  classical
  intro m
  let N := Set.ncard {i | X i < n}
  obtain ⟨e, he⟩ := row_order X m
  have hfinite : {i | X i < n}.Finite :=
    ((Set.finite_Ico 1 n).preimage hinj.injOn).subset fun i hi => ⟨hX i, hi⟩
  obtain ⟨i, hiN, hi⟩ : ∃ i ≤ N, n ≤ row X m i := by
    by_contra! h
    have hcard : N + 1 ≤ N :=
      Set.le_ncard_of_inj_on_range e (fun j hj => by
        change (X ∘ e) j < n
        rw [← he]
        exact h j (Nat.le_of_lt_succ hj)) (fun _ _ _ _ hEq => e.injective hEq) hfinite
    omega
  -- The entry at position `N` cannot reach the front before a large entry ahead of it.
  obtain ⟨k, hkb, hk⟩ := hb m
  have hlarge : ∃ d, d ≤ k ∧ n ≤ row X (m + d) 0 := by
    by_contra! h
    obtain ⟨p, q, hpq, hp, hq⟩ :=
      ordered_until_large_leader X hiN hi k fun t ht => h t ht.le
    obtain ⟨f, hf⟩ := row_order X (m + k)
    have hinj' : Function.Injective (row X (m + k)) := hf ▸ hinj.comp f.injective
    have hq0 : 0 = q := hinj' (hk.trans hq.symm)
    have hp0 : p = 0 := by omega
    exact (h k le_rfl).not_ge (hp0 ▸ hp)
  -- Position `n` is fixed until the first large leader shifts its entry left.
  let d := Nat.find hlarge
  obtain ⟨hdk, hd⟩ : d ≤ k ∧ n ≤ row X (m + d) 0 := Nat.find_spec hlarge
  have fixed (r : ℕ) (hr : r ≤ d) : row X (m + r) n = row X m n := by
    induction r with
    | zero => rfl
    | succ r ih =>
      have hlt : row X (m + r) 0 < n := by
        by_contra! h
        exact Nat.find_min hlarge (show r < d by omega) ⟨by omega, h⟩
      rw [← Nat.add_assoc, row_succ]
      simpa [prefixCycle, hlt.not_gt, hlt.ne'] using ih (by omega)
  obtain ⟨l, hla, hl⟩ := ha (m + d + 1)
  refine ⟨d + 1 + l, by omega, ?_⟩
  rw [show m + (d + 1 + l) = m + d + 1 + l by omega, hl]
  change row X (m + d + 1) (n - 1) = row X m n
  rw [row_succ]
  simpa [prefixCycle, show n - 1 < row X (m + d) 0 by omega, Nat.sub_add_cancel hn]
    using fixed d le_rfl

end MetaMathlibExt
