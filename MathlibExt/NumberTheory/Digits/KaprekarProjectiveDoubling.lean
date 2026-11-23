/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Order.Lattice.Nat

/-!
# Projective order of 2 and doubling on pairs of projective classes

For a natural number `n`, the projective order of `2` modulo `n` is the least `m > 0` with
`2 ^ m ≡ ±1 (mod n)` (`MetaMathlibExt.projectiveOrderTwo`), and `0` when there is no such `m`.

Let `B > 3` be odd and write `[x] = {x, -x}` for the projective class of a residue `x` modulo
`B`. Doubling sends a pair `{[r], [s]}` of distinct nonzero classes to `{[2r], [2s]}`. Every such
pair is periodic under doubling, with minimal period at most `λ(B) = projectiveOrderTwo B`: as `2`
is a unit modulo the odd number `B`, some power of `2` is `1`, so `λ(B) > 0` and
`2 ^ λ(B) ≡ ±1 (mod B)`; the `λ(B)`-th iterate of doubling then multiplies every class by `±1`,
which fixes it.

## Main statements

* `MetaMathlibExt.projectiveOrderTwo_eq_of`: `λ(n) = m` when `m` is the least positive exponent
  with `2 ^ m ≡ ±1 (mod n)`.
* `MetaMathlibExt.projective_doubling_minimalPeriod_le_projectiveOrderTwo`: pairs of projective
  classes are periodic under doubling, with minimal period at most `λ(B)`.

## References

* Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh S. Thakur, *Four-digit Kaprekar dynamics in
  odd bases*, arXiv:2606.20439v3 (2026), Section 4: the definition of `λ(B)` in display (13) and
  Lemma 4.1. The docstrings below cite the numbering of the version in the Journal of Integer
  Sequences.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Projective order of 2.** For a natural number $n$, the projective order of $2$ modulo $n$ is
the least $m > 0$ with $2^m \equiv 1$ or $2^m \equiv -1 \pmod{n}$,
$$\lambda(n) = \min \{m > 0 : 2^m \equiv \pm 1 \pmod{n}\},$$
and $\lambda(n) = 0$ when no such $m$ exists, which happens exactly when $n$ is even (including
$n = 0$, where congruence modulo $0$ is equality of integers). For odd $n$ these are the terms of
OEIS A003558, which lists $\lambda(2k + 1)$ at index $k$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Definition 19, display (13). -/
public noncomputable def projectiveOrderTwo (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ((2 : ZMod n) ^ m = 1 ∨ (2 : ZMod n) ^ m = -1)}

/-- **Characterization of the projective order of 2.** Let $n$ and $m$ be natural numbers with
$m > 0$. Suppose that $2^m \equiv 1$ or $2^m \equiv -1 \pmod{n}$, and that for every $k$ with
$0 < k < m$ neither $2^k \equiv 1$ nor $2^k \equiv -1 \pmod{n}$. Then the projective order of $2$
modulo $n$ is $\lambda(n) = m$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Definition 19, display (13). -/
public theorem projectiveOrderTwo_eq_of {n m : ℕ} (hm : 0 < m)
    (h : (2 : ZMod n) ^ m = 1 ∨ (2 : ZMod n) ^ m = -1)
    (hmin : ∀ k < m, 0 < k → (2 : ZMod n) ^ k ≠ 1 ∧ (2 : ZMod n) ^ k ≠ -1) :
    projectiveOrderTwo n = m := by
  unfold projectiveOrderTwo
  refine le_antisymm (Nat.sInf_le ⟨hm, h⟩) (le_csInf ⟨m, hm, h⟩ ?_)
  rintro k ⟨hk, hk2⟩
  by_contra hlt
  have hne := hmin k (lt_of_not_ge hlt) hk
  rcases hk2 with h' | h'
  · exact hne.1 h'
  · exact hne.2 h'

/-- **Values of the projective order of 2.** Writing $\lambda(n)$ for the projective order of $2$
modulo $n$, we have $\lambda(7) = 3$, $\lambda(9) = 3$, $\lambda(11) = 5$ and $\lambda(17) = 4$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7,
Examples 7-10 and 23. -/
public theorem projectiveOrderTwo_examples :
    projectiveOrderTwo 7 = 3 ∧ projectiveOrderTwo 9 = 3 ∧ projectiveOrderTwo 11 = 5 ∧
      projectiveOrderTwo 17 = 4 :=
  ⟨projectiveOrderTwo_eq_of (by omega) (by decide) (by decide),
    projectiveOrderTwo_eq_of (by omega) (by decide) (by decide),
    projectiveOrderTwo_eq_of (by omega) (by decide) (by decide),
    projectiveOrderTwo_eq_of (by omega) (by decide) (by decide)⟩

namespace projective_doubling_minimalPeriod_le_projectiveOrderTwo

/-- For odd $n > 0$, the projective order $\lambda(n)$ of $2$ modulo $n$ is positive and
$2^{\lambda(n)} \equiv \pm 1 \pmod{n}$: the unit $2$ of the finite ring $\mathbb{Z}/n\mathbb{Z}$
has finite order, so the set defining $\lambda(n)$ is nonempty. -/
private theorem projectiveOrderTwo_pos_and_pow {n : ℕ} [NeZero n] (hn : Odd n) :
    0 < projectiveOrderTwo n ∧
      ((2 : ZMod n) ^ projectiveOrderTwo n = 1 ∨ (2 : ZMod n) ^ projectiveOrderTwo n = -1) := by
  change projectiveOrderTwo n ∈
    {m : ℕ | 0 < m ∧ ((2 : ZMod n) ^ m = 1 ∨ (2 : ZMod n) ^ m = -1)}
  refine Nat.sInf_mem ?_
  obtain ⟨k, hk, hk1⟩ := (isOfFinOrder_of_finite
    (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hn))).exists_pow_eq_one
  refine ⟨k, hk, Or.inl ?_⟩
  simpa [ZMod.coe_unitOfCoprime] using congrArg Units.val hk1

/-- The $k$-th iterate of the doubling map $T \mapsto \{2C : C \in T\}$ is
$T \mapsto \{2^k C : C \in T\}$. -/
private theorem iterate_doubling (n k : ℕ) (T : Finset (Finset (ZMod n))) :
    (fun T : Finset (Finset (ZMod n)) => T.image fun C => C.image (· * 2))^[k] T =
      T.image fun C => C.image (· * 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Finset.image_image]
    refine Finset.image_congr fun C _ => ?_
    simp only [Function.comp_apply, Finset.image_image]
    congr 1
    funext x
    simp [pow_succ, mul_assoc]

end projective_doubling_minimalPeriod_le_projectiveOrderTwo

/-- **Cycle lengths of doubling on pairs of projective classes.** Let $B > 3$ be odd. For
$x \in \mathbb{Z}/B\mathbb{Z}$ write $[x] = \{x, -x\}$ and $2C = \{2c : c \in C\}$ for a subset
$C$ of $\mathbb{Z}/B\mathbb{Z}$, and let $D$ be the doubling map sending a set $T$ of subsets of
$\mathbb{Z}/B\mathbb{Z}$ to $\{2C : C \in T\}$. If $S = \{[r], [s]\}$ for nonzero
$r, s \in \mathbb{Z}/B\mathbb{Z}$ with $[r] \ne [s]$, then $S$ is a periodic point of $D$ and
its minimal period is at most $\lambda(B)$, the projective order of $2$ modulo $B$.

Source: Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar
Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7, Lemma 20
(`jis-2026-26.4.7-lem-20`). -/
public theorem projective_doubling_minimalPeriod_le_projectiveOrderTwo (B : ℕ)
    (hB : Odd B) (hB3 : 3 < B) (S : Finset (Finset (ZMod B)))
    (hS : S.card = 2 ∧ ∀ C ∈ S, ∃ x : ZMod B, x ≠ 0 ∧ C = {x, -x}) :
    0 < Function.minimalPeriod
        (fun T : Finset (Finset (ZMod B)) => T.image fun C => C.image (· * 2)) S ∧
      Function.minimalPeriod
        (fun T : Finset (Finset (ZMod B)) => T.image fun C => C.image (· * 2)) S ≤
        projectiveOrderTwo B := by
  have : NeZero B := ⟨by omega⟩
  obtain ⟨hpos, hpow⟩ :=
    projective_doubling_minimalPeriod_le_projectiveOrderTwo.projectiveOrderTwo_pos_and_pow hB
  -- The `λ(B)`-th iterate multiplies each class `{x, -x}` of `S` by `2 ^ λ(B) = ±1`.
  have hper : Function.IsPeriodicPt
      (fun T : Finset (Finset (ZMod B)) => T.image fun C => C.image (· * 2))
      (projectiveOrderTwo B) S := by
    change _ = S
    rw [projective_doubling_minimalPeriod_le_projectiveOrderTwo.iterate_doubling]
    conv_rhs => rw [← Finset.image_id' (s := S)]
    refine Finset.image_congr fun C hC => ?_
    obtain ⟨x, -, rfl⟩ := hS.2 C hC
    rcases hpow with h | h <;> simp [h, Finset.pair_comm]
  exact ⟨hper.minimalPeriod_pos hpos, hper.minimalPeriod_le hpos⟩

end

end MetaMathlibExt
