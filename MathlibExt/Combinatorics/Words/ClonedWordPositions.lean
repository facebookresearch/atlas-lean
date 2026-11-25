/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords

/-! # Position functions of a cloned binary word -/

namespace MetaMathlibExt

/-- A prefix of the cloned predicate has `q` complete blocks and `r` entries of the next block. -/
private theorem count_clone_add (p : ℕ → Prop) [DecidablePred p] {k : ℕ} (hk : 0 < k)
    (q : ℕ) {r : ℕ} (hr : r ≤ k) :
    Nat.count (fun i => p (i / k)) (k * q + r) = k * Nat.count p q + if p q then r else 0 := by
  have block (q r : ℕ) (hr : r ≤ k) :
      Nat.count (fun i => p ((k * q + i) / k)) r = if p q then r else 0 := by
    have div_block (i : ℕ) (hi : i < r) : (k * q + i) / k = q := by
      rw [Nat.mul_add_div hk, Nat.div_eq_of_lt (hi.trans_le hr), Nat.add_zero]
    by_cases hp : p q
    · rw [ite_eq_left hp]
      exact Nat.count_iff_forall.mpr fun i hi => by rwa [div_block i hi]
    · rw [ite_eq_right hp]
      exact Nat.count_iff_forall_not.mpr fun i hi => by rwa [div_block i hi]
  have boundary (q : ℕ) : Nat.count (fun i => p (i / k)) (k * q) = k * Nat.count p q := by
    induction q with
    | zero => simp [Nat.count_zero]
    | succ q ih =>
      rw [Nat.mul_succ, Nat.count_add, block q k le_rfl, ih, Nat.count_succ, Nat.mul_add]
      split_ifs <;> simp
  rw [Nat.count_add, block q r hr, boundary]

/-- **Position functions of a cloned word.** Let $w$ be an infinite binary word over the
letters $a$ and $b$ in which both letters occur infinitely often, let $k$ be a natural number,
and let $\varphi_k(w)$ be the word whose letter at position $i$ is the letter of $w$ at position
$\lfloor i/k \rfloor$ (for $k \ge 1$, the word obtained from $w$ by repeating each letter $k$
times). For a word $v$ and a letter $\alpha$, let $p_{\alpha,v}(n)$ be the position (counting
from $0$) of the $n$-th occurrence of $\alpha$ in $v$, and let $r_v(n) = p_{b,v}(n) - p_{a,v}(n)$.
Then for all natural numbers $m$ and $j$ with $1 \le j \le k$,
$p_{a,\varphi_k(w)}(mk+j) = k\,p_{a,w}(m+1) + j - 1$,
$p_{b,\varphi_k(w)}(mk+j) = k\,p_{b,w}(m+1) + j - 1$ and
$r_{\varphi_k(w)}(mk+j) = k\,r_w(m+1)$.

The paper takes $k \ge 2$; the identities hold for $k = 1$ ($\varphi_1$ is the identity) and are
vacuous for $k = 0$, so no bound on $k$ is assumed.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 24
(`jis-2025-25.1.5-lem-24`). -/
public theorem letterPosition_clone {w : ℕ → Bool} (hw : BothLettersInfinite w)
    (k m j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    letterPosition (fun i => w (i / k)) true (m * k + j) =
        k * letterPosition w true (m + 1) + j - 1 ∧
      letterPosition (fun i => w (i / k)) false (m * k + j) =
        k * letterPosition w false (m + 1) + j - 1 ∧
      relativePosition (fun i => w (i / k)) (m * k + j) = k * relativePosition w (m + 1) := by
  have hk : 0 < k := by omega
  have hr : j - 1 < k := by omega
  have pos (α : Bool) (hα : {i | w i = α}.Infinite) :
      letterPosition (fun i => w (i / k)) α (m * k + j) =
        k * letterPosition w α (m + 1) + (j - 1) := by
    let p (i : ℕ) : Prop := w i = α
    let q := Nat.nth p m
    have hq : p q := Nat.nth_mem_of_infinite hα m
    have hqcount : Nat.count p q = m := Nat.count_nth_of_infinite hα m
    have hcount := count_clone_add p hk q hr.le
    rw [hqcount, ite_eq_left hq] at hcount
    have hmem : p ((k * q + (j - 1)) / k) := by
      rwa [Nat.mul_add_div hk, Nat.div_eq_of_lt hr, Nat.add_zero]
    simp only [letterPosition, Nat.add_sub_cancel]
    change Nat.nth (fun i => p (i / k)) (m * k + j - 1) = k * q + (j - 1)
    rw [Nat.add_sub_assoc hj, Nat.mul_comm m k, ← hcount]
    exact Nat.nth_count (p := fun i => p (i / k)) hmem
  have ha := pos true hw.1
  have hb := pos false hw.2
  refine ⟨by simpa only [Nat.add_sub_assoc hj] using ha,
    by simpa only [Nat.add_sub_assoc hj] using hb, ?_⟩
  simp only [relativePosition, ha, hb, Int.natCast_add, Int.natCast_mul, Int.mul_sub]
  omega

end MetaMathlibExt
