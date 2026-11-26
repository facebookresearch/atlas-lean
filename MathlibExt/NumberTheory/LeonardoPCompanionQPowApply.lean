/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LeonardoP
public import MathlibExt.NumberTheory.LeonardoPFibonacciSum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Matrix.Mul

/-!
# Entries of the powers of the companion matrix `Q_p`

The forward and backward evaluators `hSeqForward` and `hSeqBackward`, the two-sided
extension `hSeqZ`, the sequences `seqAZ` and `seqBZ`, the companion matrix `companionQ`,
its power entry formula `qPowEntry`, and the proof `companionQ_pow_apply` that the formula
gives the entries of `Q_p ^ n`.

Statements from Kantaphon Kuhapatanakul and Pongpol Ruankong
as presented in "On Generalized Leonardo `p`-Numbers",
*Journal of Integer Sequences* 27 (2024), Article 24.4.6
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Kuhapatanakul/kuha13.pdf>),
Theorem 9.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.LeonardoPWanted

/-- **Forward evaluation of the $H(p)$ recurrence.** For a natural number $p$, a function
$s : \mathbb{Z} \to \mathbb{Z}$ and $n \in \mathbb{N}$, this is the list of the $2p + n + 1$
values at $-p, -p+1, \dots, p+n$ (the entry at position $i$ is the value at $i - p$) of the
sequence $H$ that equals $s$ on $[-p, p]$ and continues by the $H(p)$ recurrence
$H(t) = H(t-1) + H(t-p) - H(t-2p-1)$ for $t > p$. Each step appends one value to the previous
list, so evaluation takes polynomial time.

For $p = 0$, where this rule is circular, every appended value is $0$. -/
def hSeqForward (seedA : ℤ → ℤ) (p : ℕ) : ℕ → List ℤ
  | 0 => (List.range (2 * p + 1)).map fun i => seedA ((i : ℤ) - p)
  | n + 1 =>
      let prev := hSeqForward seedA p n
      prev ++ [prev.getD (2 * p + n) 0 + prev.getD (p + 1 + n) 0 -
        prev.getD n 0]

/-- **Backward evaluation of the $H(p)$ recurrence.** For a natural number $p$, a function
$s : \mathbb{Z} \to \mathbb{Z}$ and $n \in \mathbb{N}$, this is the list of the values at
$-p-n, \dots, p$ of the sequence $H$ that equals $s$ on $[-p, p]$ and continues to the left by
$H(t) = H(t+2p) + H(t+p+1) - H(t+2p+1)$ for $t < -p$, which is the $H(p)$ recurrence
$H(u) = H(u-1) + H(u-p) - H(u-2p-1)$ at $u = t+2p+1$ solved for $H(t)$. Each step prepends one
value to the previous list.

For $p = 0$, where this rule is circular, every prepended value equals $s(0)$. -/
def hSeqBackward (seedA : ℤ → ℤ) (p : ℕ) : ℕ → List ℤ
  | 0 => (List.range (2 * p + 1)).map fun i => seedA ((i : ℤ) - p)
  | n + 1 =>
      let prev := hSeqBackward seedA p n
      (prev.getD (2 * p - 1) 0 + prev.getD p 0 - prev.getD (2 * p) 0) ::
        prev

/-- **Two-sided extension of initial values by the $H(p)$ recurrence.** For a natural number
$p \ge 1$ and a function $s : \mathbb{Z} \to \mathbb{Z}$, this is the unique function
$H : \mathbb{Z} \to \mathbb{Z}$ that agrees with $s$ on $[-p, p]$ and satisfies
$H(t) = H(t-1) + H(t-p) - H(t-2p-1)$ for every integer $t$: its values at $t > p$ are computed
forward and its values at $t < -p$ backward from this recurrence. For $p = 0$ its value is $s(0)$
at every $t \le 0$ and $0$ at every $t > 0$. -/
def hSeqZ (seedA : ℤ → ℤ) (p : ℕ) (z : ℤ) : ℤ :=
  if -(p : ℤ) ≤ z then
    (hSeqForward seedA p (z + p).toNat).getD (z + p).toNat 0
  else
    (hSeqBackward seedA p (-(z + p)).toNat).getD 0 0

/-- **The sequence $A_p$.** For a natural number $p \ge 1$, $A_p : \mathbb{Z} \to \mathbb{Z}$ is
the unique sequence with $A_p(n) = 0$ for $-p \le n \le 0$ and $A_p(n) = 1$ for $1 \le n \le p$
that satisfies $A_p(n) = A_p(n-1) + A_p(n-p) - A_p(n-2p-1)$ for every integer $n$. For $p = 0$
it is the zero sequence. -/
def seqAZ (p : ℕ) (z : ℤ) : ℤ :=
  hSeqZ (fun w => if w ≤ 0 then 0 else 1) p z

/-- **The two-sided sequence $B_p$.** For a natural number $p \ge 1$, the sequence $B_p$ of
integers indexed by $\mathbb{Z}$ is the unique solution of the recurrence
$B_p(n) = B_p(n-1) + B_p(n-p) - B_p(n-2p-1)$ for every integer $n$ (the defining recurrence of
the paper's class $H(p)$) with initial values $B_p(n) = 1$ for $1 \le n \le p$,
$B_p(-p+1) = 1$, and $B_p(n) = 0$ for the other integers $n$ with $-p \le n \le 0$.

The definition also accepts $p = 0$, where the recurrence is trivial and the construction has no
mathematical meaning. -/
def seqBZ (p : ℕ) (z : ℤ) : ℤ :=
  hSeqZ (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then 1 else 0)
    else 1) p z

/-- **The companion matrix $Q_p$.** For a natural number $p$, $Q_p$ is the $(2p+1) \times (2p+1)$
integer matrix with rows and columns indexed by $0, 1, \dots, 2p$. For $p = 0$ it is the
$1 \times 1$ matrix $[-1]$. For $p \ge 1$ its entry $(2p, 0)$ is $-1$, its entries $(0, 0)$,
$(p-1, 0)$ and $(i, i+1)$ for $0 \le i < 2p$ are $1$, and its remaining entries are $0$. -/
def companionQ (p : ℕ) : Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℤ :=
  Matrix.of fun i j =>
    if j.val = 0 ∧ i.val = 2 * p then -1
    else if (j.val = 0 ∧ (i.val = 0 ∨ i.val = p - 1)) ∨
        j.val = i.val + 1 then 1
    else 0

/-- **Entry formula for the powers of $Q_p$.** For natural numbers $p$ and $n$ and indices
$a, b \in \{0, 1, \dots, 2p\}$, the value is the integer $A_p(n + 1 - b)$ if $a = 0$, the integer
$B_p(n - p + 1 + a - b)$ if $1 \le a \le p - 1$, and the integer $-A_p(n - 2p + a - b)$ otherwise,
where $A_p$ and $B_p$ are the two-sided auxiliary sequences of the generalized Leonardo
$p$-numbers.

This is the formula of Theorem 9 of the source for the $(a, b)$ entry of $Q_p^n$, where $p \ge 2$
and $Q_p$ is the $(2p+1) \times (2p+1)$ companion matrix of the source, with two corrections to
the source's display: the index direction along the $B_p$ rows (the display reverses it after the
first entry), and the minus sign on the $A_p$ terms of rows $p$ to $2p$ (the display omits it; for
example it prints the bottom-right entry as $A_p(n-2p)$, which at $p = 2$, $n = 0$ is
$A_2(-4) = -1$, whereas the identity matrix has entry $1$). -/
def qPowEntry (p n : ℕ) (a b : Fin (2 * p + 1)) : ℤ :=
  if a.val = 0 then seqAZ p ((n : ℤ) + 1 - b.val)
  else if a.val ≤ p - 1 then seqBZ p ((n : ℤ) - p + 1 + a.val - b.val)
  else -seqAZ p ((n : ℤ) - (2 * p - a.val) - b.val)

private theorem length_forward (seedA : ℤ → ℤ) (p n : ℕ) :
    (hSeqForward seedA p n).length = 2 * p + 1 + n := by
  induction n with
  | zero => simp [hSeqForward]
  | succ n ih => simp [hSeqForward, ih, Nat.add_assoc]

private theorem length_backward (seedA : ℤ → ℤ) (p n : ℕ) :
    (hSeqBackward seedA p n).length = 2 * p + 1 + n := by
  induction n with
  | zero => simp [hSeqBackward]
  | succ n ih => simp [hSeqBackward, ih, Nat.add_assoc]

private theorem getD_forward_le (seedA : ℤ → ℤ) (p m n i : ℕ) (hmn : m ≤ n)
    (hi : i < 2 * p + 1 + m) :
    (hSeqForward seedA p n).getD i 0 = (hSeqForward seedA p m).getD i 0 := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
    have hlen : i < (hSeqForward seedA p n).length := by
      rw [length_forward]; omega
    rw [hSeqForward, List.getD_append _ _ _ _ hlen]
    exact ih

private theorem getD_backward_le (seedA : ℤ → ℤ) (p m n i : ℕ) (hmn : m ≤ n)
    (_hi : i < 2 * p + 1 + m) :
    (hSeqBackward seedA p n).getD (i + (n - m)) 0 =
      (hSeqBackward seedA p m).getD i 0 := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have h1 : i + (n + 1 - m) = (i + (n - m)) + 1 := by omega
    rw [h1]
    have hEq : hSeqBackward seedA p (n + 1) =
        (((hSeqBackward seedA p n).getD (2 * p - 1) 0 +
          (hSeqBackward seedA p n).getD p 0 -
          (hSeqBackward seedA p n).getD (2 * p) 0) ::
        hSeqBackward seedA p n) := rfl
    rw [hEq, List.getD_cons_succ]
    exact ih

private theorem base_getD (seedA : ℤ → ℤ) (p i : ℕ) (hi : i < 2 * p + 1) :
    ((List.range (2 * p + 1)).map fun i => seedA ((i : ℤ) - p)).getD i 0 =
      seedA ((i : ℤ) - p) := by
  have hlen : i < (((List.range (2 * p + 1)).map
      fun i => seedA ((i : ℤ) - p)).length) := by
    simpa using hi
  rw [List.getD_eq_getElem _ _ hlen]
  simp [← List.map_eq_flatMap]

private theorem hSeqZ_of_mem (seedA : ℤ → ℤ) (p : ℕ) (z : ℤ)
    (hz1 : -(p : ℤ) ≤ z) (hz2 : z ≤ p) : hSeqZ seedA p z = seedA z := by
  unfold hSeqZ
  simp only [hz1, ↓reduceIte]
  have hN : (((z + p).toNat : ℕ) : ℤ) = z + p :=
    Int.toNat_of_nonneg (by omega)
  have hNlt : (z + p).toNat < 2 * p + 1 := by omega
  have hpre := getD_forward_le seedA p 0 (z + p).toNat (z + p).toNat
    (Nat.zero_le _) (by omega)
  have hbase := base_getD seedA p (z + p).toNat hNlt
  have h0 : hSeqForward seedA p 0 =
      ((List.range (2 * p + 1)).map fun i => seedA ((i : ℤ) - p)) := rfl
  rw [hpre, h0]
  have hz : (((z + p).toNat : ℕ) : ℤ) - p = z := by omega
  rw [hbase, hz]

private theorem forward_succ_getD (seedA : ℤ → ℤ) (p m : ℕ) :
    (hSeqForward seedA p (m + 1)).getD (2 * p + 1 + m) 0 =
      (hSeqForward seedA p m).getD (2 * p + m) 0 +
        (hSeqForward seedA p m).getD (p + 1 + m) 0 -
        (hSeqForward seedA p m).getD m 0 := by
  have hEq : hSeqForward seedA p (m + 1) =
      hSeqForward seedA p m ++
        [(hSeqForward seedA p m).getD (2 * p + m) 0 +
          (hSeqForward seedA p m).getD (p + 1 + m) 0 -
          (hSeqForward seedA p m).getD m 0] := rfl
  rw [hEq]
  have hlen : (hSeqForward seedA p m).length ≤ 2 * p + 1 + m := by
    rw [length_forward]
  rw [List.getD_append_right _ _ _ _ hlen]
  have hsub : 2 * p + 1 + m - (hSeqForward seedA p m).length = 0 := by
    rw [length_forward]; omega
  rw [hsub]
  rfl

private theorem hSeqZ_forward_rec (seedA : ℤ → ℤ) (p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) (ht : (p : ℤ) < t) :
    hSeqZ seedA p t = hSeqZ seedA p (t - 1) + hSeqZ seedA p (t - p) -
      hSeqZ seedA p (t - 2 * p - 1) := by
  have hz0 : -(p : ℤ) ≤ t := by omega
  have hz1 : -(p : ℤ) ≤ t - 1 := by omega
  have hz2 : -(p : ℤ) ≤ t - p := by omega
  have hz3 : -(p : ℤ) ≤ t - 2 * p - 1 := by omega
  unfold hSeqZ
  simp only [hz0, hz1, hz2, hz3, ↓reduceIte]
  have hN : ((((t + p).toNat : ℕ)) : ℤ) = t + p :=
    Int.toNat_of_nonneg (by omega)
  have hN1 : ((((t - 1 + p).toNat : ℕ)) : ℤ) = t - 1 + p :=
    Int.toNat_of_nonneg (by omega)
  have hN2 : ((((t - p + p).toNat : ℕ)) : ℤ) = t - p + p :=
    Int.toNat_of_nonneg (by omega)
  have hN3 : ((((t - 2 * p - 1 + p).toNat : ℕ)) : ℤ) = t - 2 * p - 1 + p :=
    Int.toNat_of_nonneg (by omega)
  have hM_eq : (t - 2 * p - 1 + p).toNat + 2 * p + 1 = (t + p).toNat := by omega
  have hN1_eq : (t - 1 + p).toNat + 1 = (t + p).toNat := by omega
  have hN2_eq : (t - p + p).toNat = (t - 2 * p - 1 + p).toNat + p + 1 := by omega
  have hN_eq : (t + p).toNat = 2 * p + 1 + (t - 2 * p - 1 + p).toNat := by omega
  have hN1_eq2 : (t - 1 + p).toNat = 2 * p + (t - 2 * p - 1 + p).toNat := by omega
  have hN2_eq2 : (t - p + p).toNat = p + 1 + (t - 2 * p - 1 + p).toNat := by omega
  have hHt : (hSeqForward seedA p (t + p).toNat).getD (t + p).toNat 0 =
      (hSeqForward seedA p ((t - 2 * p - 1 + p).toNat + 1)).getD
        (2 * p + 1 + (t - 2 * p - 1 + p).toNat) 0 := by
    have hle : (t - 2 * p - 1 + p).toNat + 1 ≤ (t + p).toNat := by omega
    have hpre := getD_forward_le seedA p ((t - 2 * p - 1 + p).toNat + 1)
      (t + p).toNat (t + p).toNat hle (by omega)
    rw [hpre, hN_eq]
  have hstep := forward_succ_getD seedA p (t - 2 * p - 1 + p).toNat
  rw [hHt, hstep]
  have hHt1 : (hSeqForward seedA p (t - 1 + p).toNat).getD (t - 1 + p).toNat 0 =
      (hSeqForward seedA p (t - 2 * p - 1 + p).toNat).getD
        (2 * p + (t - 2 * p - 1 + p).toNat) 0 := by
    have hle1 : (t - 1 + p).toNat ≤ (t + p).toNat := by omega
    have hpre1 := getD_forward_le seedA p (t - 1 + p).toNat (t + p).toNat
      (t - 1 + p).toNat hle1 (by omega)
    have hle2 : (t - 2 * p - 1 + p).toNat ≤ (t + p).toNat := by omega
    have hpre2 := getD_forward_le seedA p (t - 2 * p - 1 + p).toNat (t + p).toNat
      (t - 1 + p).toNat hle2 (by omega)
    rw [← hpre1, hpre2, hN1_eq2]
  have hHtp : (hSeqForward seedA p (t - p + p).toNat).getD (t - p + p).toNat 0 =
      (hSeqForward seedA p (t - 2 * p - 1 + p).toNat).getD
        (p + 1 + (t - 2 * p - 1 + p).toNat) 0 := by
    have hle1 : (t - p + p).toNat ≤ (t + p).toNat := by omega
    have hpre1 := getD_forward_le seedA p (t - p + p).toNat (t + p).toNat
      (t - p + p).toNat hle1 (by omega)
    have hle2 : (t - 2 * p - 1 + p).toNat ≤ (t + p).toNat := by omega
    have hpre2 := getD_forward_le seedA p (t - 2 * p - 1 + p).toNat (t + p).toNat
      (t - p + p).toNat hle2 (by omega)
    rw [← hpre1, hpre2, hN2_eq2]
  rw [hHt1, hHtp]

private theorem backward_correct (seedA : ℤ → ℤ) (p m i : ℕ)
    (hi : i < 2 * p + 1 + m) :
    (hSeqBackward seedA p m).getD i 0 =
      hSeqZ seedA p ((i : ℤ) - m - p) := by
  induction m generalizing i with
  | zero =>
    have hbase := base_getD seedA p i (by omega)
    have h0 : hSeqBackward seedA p 0 =
        ((List.range (2 * p + 1)).map fun i => seedA ((i : ℤ) - p)) := rfl
    rw [h0, hbase]
    have hz1 : -(p : ℤ) ≤ (i : ℤ) - 0 - p := by omega
    have hz2 : (i : ℤ) - 0 - p ≤ p := by omega
    have hmem := hSeqZ_of_mem seedA p ((i : ℤ) - 0 - p) hz1 hz2
    have heq : (i : ℤ) - 0 - p = (i : ℤ) - p := by simp
    rw [heq] at hmem
    exact hmem.symm
  | succ m ih =>
    cases i with
    | zero =>
      have hEq : hSeqBackward seedA p (m + 1) =
          (((hSeqBackward seedA p m).getD (2 * p - 1) 0 +
            (hSeqBackward seedA p m).getD p 0 -
            (hSeqBackward seedA p m).getD (2 * p) 0) ::
          hSeqBackward seedA p m) := rfl
      rw [hEq, List.getD_cons_zero]
      have hneg : ¬ (-(p : ℤ) ≤ ((0 : ℕ) : ℤ) - (m + 1 : ℕ) - p) := by omega
      unfold hSeqZ
      simp only [hneg, ↓reduceIte]
      have htoNat : (-(((0 : ℕ) : ℤ) - (m + 1 : ℕ) - p + p)).toNat = m + 1 := by
        have heq2 : -(((0 : ℕ) : ℤ) - (m + 1 : ℕ) - p + p) = ((m + 1 : ℕ) : ℤ) := by
          omega
        rw [heq2, Int.toNat_natCast]
      rw [htoNat]
      rw [hEq, List.getD_cons_zero]
    | succ j =>
      have hEq : hSeqBackward seedA p (m + 1) =
          (((hSeqBackward seedA p m).getD (2 * p - 1) 0 +
            (hSeqBackward seedA p m).getD p 0 -
            (hSeqBackward seedA p m).getD (2 * p) 0) ::
          hSeqBackward seedA p m) := rfl
      rw [hEq, List.getD_cons_succ]
      have hj : j < 2 * p + 1 + m := by omega
      have hih := ih j hj
      have heq3 : (((j + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) - p) =
          ((j : ℕ) : ℤ) - (m : ℕ) - p := by
        omega
      rw [heq3]
      exact hih

private theorem hSeqZ_backward_rec (seedA : ℤ → ℤ) (p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) (ht : t ≤ (p : ℤ)) :
    hSeqZ seedA p t = hSeqZ seedA p (t - 1) + hSeqZ seedA p (t - p) -
      hSeqZ seedA p (t - 2 * p - 1) := by
  have hs_lt : t - 2 * p - 1 < -(p : ℤ) := by omega
  have hs_le : ¬ (-(p : ℤ) ≤ t - 2 * p - 1) := by omega
  have hM_nonneg : (0 : ℤ) ≤ -(t - 2 * p - 1 + p) := by omega
  have hM : ((((-(t - 2 * p - 1 + p)).toNat : ℕ)) : ℤ) = -(t - 2 * p - 1 + p) :=
    Int.toNat_of_nonneg hM_nonneg
  have hM_ge : 1 ≤ (-(t - 2 * p - 1 + p)).toNat := by omega
  have hM1 : (-(t - 2 * p - 1 + p)).toNat - 1 + 1 =
      (-(t - 2 * p - 1 + p)).toNat :=
    Nat.sub_add_cancel hM_ge
  have hM1_cast : (↑((-(t - 2 * p - 1 + p)).toNat - 1) : ℤ) =
      (↑((-(t - 2 * p - 1 + p)).toNat) : ℤ) - 1 := by omega
  have hs_eq : hSeqZ seedA p (t - 2 * p - 1) =
      (hSeqBackward seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)).getD (2 * p - 1) 0 +
        (hSeqBackward seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)).getD p 0 -
        (hSeqBackward seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)).getD (2 * p) 0 := by
    unfold hSeqZ
    simp only [hs_le, ↓reduceIte]
    have hMEq : (-(t - 2 * p - 1 + p)).toNat =
        ((-(t - 2 * p - 1 + p)).toNat - 1) + 1 := by omega
    conv_lhs => rw [hMEq]
    have hEq : hSeqBackward seedA p (((-(t - 2 * p - 1 + p)).toNat - 1) + 1) =
        (((hSeqBackward seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)).getD (2 * p - 1) 0 +
          (hSeqBackward seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)).getD p 0 -
          (hSeqBackward seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)).getD (2 * p) 0) ::
        hSeqBackward seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)) := rfl
    rw [hEq, List.getD_cons_zero]
  have h1 : (hSeqBackward seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)).getD (2 * p - 1) 0 =
      hSeqZ seedA p (t - 1) := by
    have hcorr := backward_correct seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)
      (2 * p - 1) (by omega)
    have heq : (((2 * p - 1 : ℕ)) : ℤ) - (((-(t - 2 * p - 1 + p)).toNat - 1 : ℕ) : ℤ) - p =
        t - 1 := by omega
    rw [heq] at hcorr
    exact hcorr
  have h2 : (hSeqBackward seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)).getD p 0 =
      hSeqZ seedA p (t - p) := by
    have hcorr := backward_correct seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)
      p (by omega)
    have heq : ((p : ℕ) : ℤ) - (((-(t - 2 * p - 1 + p)).toNat - 1 : ℕ) : ℤ) - p =
        t - p := by omega
    rw [heq] at hcorr
    exact hcorr
  have h3 : (hSeqBackward seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)).getD (2 * p) 0 =
      hSeqZ seedA p t := by
    have hcorr := backward_correct seedA p ((-(t - 2 * p - 1 + p)).toNat - 1)
      (2 * p) (by omega)
    have heq : (((2 * p : ℕ)) : ℤ) - (((-(t - 2 * p - 1 + p)).toNat - 1 : ℕ) : ℤ) - p =
        t := by omega
    rw [heq] at hcorr
    exact hcorr
  rw [hs_eq, h1, h2, h3] at *
  omega

private theorem hSeqZ_rec (seedA : ℤ → ℤ) (p : ℕ) (hp : 1 ≤ p) (t : ℤ) :
    hSeqZ seedA p t = hSeqZ seedA p (t - 1) + hSeqZ seedA p (t - p) -
      hSeqZ seedA p (t - 2 * p - 1) := by
  by_cases ht : (p : ℤ) < t
  · exact hSeqZ_forward_rec seedA p hp t ht
  · have hle : t ≤ (p : ℤ) := not_lt.mp ht
    exact hSeqZ_backward_rec seedA p hp t hle

private theorem hSeqZ_backward_step (seedA : ℤ → ℤ) (p : ℕ) (hp : 1 ≤ p)
    (t : ℤ) (ht : t < -(p : ℤ)) :
    hSeqZ seedA p t = hSeqZ seedA p (t + 2 * p) +
      hSeqZ seedA p (t + p + 1) - hSeqZ seedA p (t + 2 * p + 1) := by
  have hs_le : ¬ (-(p : ℤ) ≤ t) := by omega
  have hM_nonneg : (0 : ℤ) ≤ -(t + p) := by omega
  have hM : ((((-(t + p)).toNat : ℕ)) : ℤ) = -(t + p) :=
    Int.toNat_of_nonneg hM_nonneg
  have hM_ge : 1 ≤ (-(t + p)).toNat := by omega
  have hM1_cast : (↑((-(t + p)).toNat - 1) : ℤ) =
      (↑((-(t + p)).toNat) : ℤ) - 1 := by omega
  have hs_eq : hSeqZ seedA p t =
      (hSeqBackward seedA p ((-(t + p)).toNat - 1)).getD (2 * p - 1) 0 +
        (hSeqBackward seedA p ((-(t + p)).toNat - 1)).getD p 0 -
        (hSeqBackward seedA p ((-(t + p)).toNat - 1)).getD (2 * p) 0 := by
    unfold hSeqZ
    simp only [hs_le, ↓reduceIte]
    have hMEq : (-(t + p)).toNat =
        ((-(t + p)).toNat - 1) + 1 := by omega
    conv_lhs => rw [hMEq]
    have hEq : hSeqBackward seedA p (((-(t + p)).toNat - 1) + 1) =
        (((hSeqBackward seedA p ((-(t + p)).toNat - 1)).getD (2 * p - 1) 0 +
          (hSeqBackward seedA p ((-(t + p)).toNat - 1)).getD p 0 -
          (hSeqBackward seedA p ((-(t + p)).toNat - 1)).getD (2 * p) 0) ::
        hSeqBackward seedA p ((-(t + p)).toNat - 1)) := rfl
    rw [hEq, List.getD_cons_zero]
  have h1 : (hSeqBackward seedA p ((-(t + p)).toNat - 1)).getD (2 * p - 1) 0 =
      hSeqZ seedA p (t + 2 * p) := by
    have hcorr := backward_correct seedA p ((-(t + p)).toNat - 1)
      (2 * p - 1) (by omega)
    have heq : (((2 * p - 1 : ℕ)) : ℤ) - (((-(t + p)).toNat - 1 : ℕ) : ℤ) - p =
        t + 2 * p := by omega
    rw [heq] at hcorr
    exact hcorr
  have h2 : (hSeqBackward seedA p ((-(t + p)).toNat - 1)).getD p 0 =
      hSeqZ seedA p (t + p + 1) := by
    have hcorr := backward_correct seedA p ((-(t + p)).toNat - 1)
      p (by omega)
    have heq : ((p : ℕ) : ℤ) - (((-(t + p)).toNat - 1 : ℕ) : ℤ) - p =
        t + p + 1 := by omega
    rw [heq] at hcorr
    exact hcorr
  have h3 : (hSeqBackward seedA p ((-(t + p)).toNat - 1)).getD (2 * p) 0 =
      hSeqZ seedA p (t + 2 * p + 1) := by
    have hcorr := backward_correct seedA p ((-(t + p)).toNat - 1)
      (2 * p) (by omega)
    have heq : (((2 * p : ℕ)) : ℤ) - (((-(t + p)).toNat - 1 : ℕ) : ℤ) - p =
        t + 2 * p + 1 := by omega
    rw [heq] at hcorr
    exact hcorr
  rw [hs_eq, h1, h2, h3]

private theorem seqAZ_rec (p : ℕ) (hp : 1 ≤ p) (t : ℤ) :
    seqAZ p t = seqAZ p (t - 1) + seqAZ p (t - p) - seqAZ p (t - 2 * p - 1) :=
  hSeqZ_rec _ p hp t

private theorem seqBZ_rec (p : ℕ) (hp : 1 ≤ p) (t : ℤ) :
    seqBZ p t = seqBZ p (t - 1) + seqBZ p (t - p) - seqBZ p (t - 2 * p - 1) :=
  hSeqZ_rec _ p hp t

private theorem seqAZ_of_mem_zero (p : ℕ) (z : ℤ)
    (hz1 : -(p : ℤ) ≤ z) (hz2 : z ≤ 0) : seqAZ p z = 0 := by
  unfold seqAZ
  rw [hSeqZ_of_mem _ p z hz1 (by omega)]
  simp [hz2]

private theorem seqAZ_of_mem_one (p : ℕ) (z : ℤ)
    (hz1 : 1 ≤ z) (hz2 : z ≤ p) : seqAZ p z = 1 := by
  unfold seqAZ
  rw [hSeqZ_of_mem _ p z (by omega) (by omega)]
  simp [show ¬ (z ≤ 0) by omega]

private theorem seqBZ_of_mem_one_mid (p : ℕ) (z : ℤ)
    (hz1 : 1 ≤ z) (hz2 : z ≤ p) : seqBZ p z = 1 := by
  unfold seqBZ
  rw [hSeqZ_of_mem _ p z (by omega) (by omega)]
  simp [show ¬ (z ≤ 0) by omega]

private theorem seqBZ_of_mem_special (p : ℕ) (hp : 1 ≤ p) :
    seqBZ p (-(p : ℤ) + 1) = 1 := by
  unfold seqBZ
  have hz1 : -(p : ℤ) ≤ -(p : ℤ) + 1 := by omega
  have hz2 : -(p : ℤ) + 1 ≤ (p : ℤ) := by omega
  rw [hSeqZ_of_mem _ p _ hz1 hz2]
  have hle : (-(p : ℤ) + 1) ≤ 0 := by omega
  simp [hle]

private theorem seqBZ_of_mem_zero (p : ℕ) (z : ℤ)
    (hz1 : -(p : ℤ) ≤ z) (hz2 : z ≤ 0) (hne : z ≠ -(p : ℤ) + 1) :
    seqBZ p z = 0 := by
  unfold seqBZ
  rw [hSeqZ_of_mem _ p z hz1 (by omega)]
  simp [hz2, hne]

private theorem seqAZ_zero_backward_one (p : ℕ) (hp : 2 ≤ p) (t : ℤ)
    (ht1 : 1 - 2 * p ≤ t) (ht2 : t ≤ -(p : ℤ) - 1) : seqAZ p t = 0 := by
  have hlt : t < -(p : ℤ) := by omega
  have hstep := hSeqZ_backward_step (fun w => if w ≤ 0 then (0 : ℤ) else 1)
    p (by omega) t hlt
  unfold seqAZ at hstep ⊢
  rw [hstep]
  have h1 : hSeqZ (fun w => if w ≤ 0 then (0 : ℤ) else 1) p (t + 2 * p) = 1 := by
    have hz1 : (1 : ℤ) ≤ t + 2 * p := by omega
    have hz2 : t + 2 * p ≤ (p : ℤ) := by omega
    have hzmem1 : -(p : ℤ) ≤ t + 2 * p := by omega
    rw [hSeqZ_of_mem _ p _ hzmem1 (by omega)]
    simp [show ¬ (t + 2 * p ≤ 0) by omega]
  have h2 : hSeqZ (fun w => if w ≤ 0 then (0 : ℤ) else 1) p (t + p + 1) = 0 := by
    have hz1 : -(p : ℤ) ≤ t + p + 1 := by omega
    have hz2 : t + p + 1 ≤ (0 : ℤ) := by omega
    rw [hSeqZ_of_mem _ p _ hz1 (by omega)]
    simp [hz2]
  have h3 : hSeqZ (fun w => if w ≤ 0 then (0 : ℤ) else 1) p (t + 2 * p + 1) = 1 := by
    have hz1 : (1 : ℤ) ≤ t + 2 * p + 1 := by omega
    have hz2 : t + 2 * p + 1 ≤ (p : ℤ) := by omega
    have hzmem1 : -(p : ℤ) ≤ t + 2 * p + 1 := by omega
    rw [hSeqZ_of_mem _ p _ hzmem1 (by omega)]
    simp [show ¬ (t + 2 * p + 1 ≤ 0) by omega]
  rw [h1, h2, h3]
  rfl

private theorem seqAZ_neg_two_p (p : ℕ) (hp : 2 ≤ p) :
    seqAZ p (-2 * (p : ℤ)) = -1 := by
  have hlt : (-2 * (p : ℤ)) < -(p : ℤ) := by omega
  have hstep := hSeqZ_backward_step (fun w => if w ≤ 0 then (0 : ℤ) else 1)
    p (by omega) (-2 * p) hlt
  unfold seqAZ at hstep ⊢
  rw [hstep]
  have h1 : hSeqZ (fun w => if w ≤ 0 then (0 : ℤ) else 1) p (-2 * p + 2 * p) = 0 := by
    have heq : (-2 * (p : ℤ) + 2 * p) = 0 := by ring
    rw [heq]
    have hz1 : -(p : ℤ) ≤ (0 : ℤ) := by omega
    rw [hSeqZ_of_mem _ p _ hz1 (by omega)]
    simp
  have h2 : hSeqZ (fun w => if w ≤ 0 then (0 : ℤ) else 1) p (-2 * p + p + 1) = 0 := by
    have heq : (-2 * (p : ℤ) + p + 1) = -(p : ℤ) + 1 := by ring
    rw [heq]
    have hz1 : -(p : ℤ) ≤ -(p : ℤ) + 1 := by omega
    have hz2 : -(p : ℤ) + 1 ≤ (0 : ℤ) := by omega
    rw [hSeqZ_of_mem _ p _ hz1 (by omega)]
    simp [hz2]
  have h3 : hSeqZ (fun w => if w ≤ 0 then (0 : ℤ) else 1) p (-2 * p + 2 * p + 1) = 1 := by
    have heq : (-2 * (p : ℤ) + 2 * p + 1) = 1 := by ring
    rw [heq]
    have hz1 : -(p : ℤ) ≤ (1 : ℤ) := by omega
    have hz2 : (1 : ℤ) ≤ (p : ℤ) := by omega
    rw [hSeqZ_of_mem _ p _ hz1 hz2]
    simp [show ¬ ((1 : ℤ) ≤ 0) by omega]
  rw [h1, h2, h3]
  rfl

private theorem seqAZ_zero_backward_two (p : ℕ) (hp : 2 ≤ p) (t : ℤ)
    (ht1 : -3 * p ≤ t) (ht2 : t ≤ -2 * (p : ℤ) - 1) : seqAZ p t = 0 := by
  have hlt : t < -(p : ℤ) := by omega
  have hstep := hSeqZ_backward_step (fun w => if w ≤ 0 then (0 : ℤ) else 1)
    p (by omega) t hlt
  unfold seqAZ at hstep ⊢
  rw [hstep]
  have h1 : hSeqZ (fun w => if w ≤ 0 then (0 : ℤ) else 1) p (t + 2 * p) = 0 := by
    have hz1 : -(p : ℤ) ≤ t + 2 * p := by omega
    have hz2 : t + 2 * p ≤ (0 : ℤ) := by omega
    rw [hSeqZ_of_mem _ p _ hz1 (by omega)]
    simp [hz2]
  have h3 : hSeqZ (fun w => if w ≤ 0 then (0 : ℤ) else 1) p (t + 2 * p + 1) = 0 := by
    have hz1 : -(p : ℤ) ≤ t + 2 * p + 1 := by omega
    have hz2 : t + 2 * p + 1 ≤ (0 : ℤ) := by omega
    rw [hSeqZ_of_mem _ p _ hz1 (by omega)]
    simp [hz2]
  have h2 : hSeqZ (fun w => if w ≤ 0 then (0 : ℤ) else 1) p (t + p + 1) = 0 := by
    by_cases heq : t + p + 1 = -(p : ℤ)
    · rw [heq]
      have hz1 : -(p : ℤ) ≤ -(p : ℤ) := le_rfl
      rw [hSeqZ_of_mem _ p _ hz1 (by omega)]
      simp [show (-(p : ℤ) ≤ 0) by omega]
    · have hle : t + p + 1 ≤ -(p : ℤ) - 1 := by omega
      have hge : (1 : ℤ) - 2 * p ≤ t + p + 1 := by omega
      have h0 : seqAZ p (t + p + 1) = 0 :=
        seqAZ_zero_backward_one p hp _ hge hle
      unfold seqAZ at h0
      exact h0
  rw [h1, h2, h3]
  rfl

private theorem seqBZ_zero_backward_one (p : ℕ) (hp : 2 ≤ p) (t : ℤ)
    (ht1 : 1 - 2 * p ≤ t) (ht2 : t ≤ -(p : ℤ) - 1) : seqBZ p t = 0 := by
  have hlt : t < -(p : ℤ) := by omega
  have hstep := hSeqZ_backward_step
    (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
    p (by omega) t hlt
  unfold seqBZ at hstep ⊢
  rw [hstep]
  have h1 : hSeqZ
      (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
      p (t + 2 * p) = 1 := by
    have hz1 : (1 : ℤ) ≤ t + 2 * p := by omega
    have hz2 : t + 2 * p ≤ (p : ℤ) := by omega
    have h0 : seqBZ p (t + 2 * p) = 1 := seqBZ_of_mem_one_mid p _ hz1 hz2
    unfold seqBZ at h0
    exact h0
  have h2 : hSeqZ
      (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
      p (t + p + 1) = 0 := by
    have hz1 : -(p : ℤ) ≤ t + p + 1 := by omega
    have hz2 : t + p + 1 ≤ (0 : ℤ) := by omega
    have hne : t + p + 1 ≠ -(p : ℤ) + 1 := by omega
    have h0 : seqBZ p (t + p + 1) = 0 := seqBZ_of_mem_zero p _ hz1 hz2 hne
    unfold seqBZ at h0
    exact h0
  have h3 : hSeqZ
      (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
      p (t + 2 * p + 1) = 1 := by
    have hz1 : (1 : ℤ) ≤ t + 2 * p + 1 := by omega
    have hz2 : t + 2 * p + 1 ≤ (p : ℤ) := by omega
    have h0 : seqBZ p (t + 2 * p + 1) = 1 := seqBZ_of_mem_one_mid p _ hz1 hz2
    unfold seqBZ at h0
    exact h0
  rw [h1, h2, h3]
  rfl

private theorem seqBZ_zero_backward_two (p : ℕ) (hp : 2 ≤ p) (t : ℤ)
    (ht1 : 2 - 3 * p ≤ t) (ht2 : t ≤ -(p : ℤ) - 1) : seqBZ p t = 0 := by
  by_cases hge : (1 : ℤ) - 2 * p ≤ t
  · exact seqBZ_zero_backward_one p hp t hge ht2
  · have hle : t ≤ -2 * (p : ℤ) := by omega
    have hlt : t < -(p : ℤ) := by omega
    have hstep := hSeqZ_backward_step
      (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
      p (by omega) t hlt
    unfold seqBZ at hstep ⊢
    rw [hstep]
    by_cases heq0 : t = -2 * (p : ℤ)
    · have h1 : hSeqZ
          (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
          p (t + 2 * p) = 0 := by
        have heq1 : t + 2 * p = (0 : ℤ) := by omega
        rw [heq1]
        have hz1 : -(p : ℤ) ≤ (0 : ℤ) := by omega
        have hne : (0 : ℤ) ≠ -(p : ℤ) + 1 := by omega
        have h0 : seqBZ p 0 = 0 := seqBZ_of_mem_zero p 0 hz1 le_rfl hne
        unfold seqBZ at h0
        exact h0
      have h2 : hSeqZ
          (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
          p (t + p + 1) = 1 := by
        have heq2 : t + p + 1 = -(p : ℤ) + 1 := by omega
        rw [heq2]
        have h0 : seqBZ p (-(p : ℤ) + 1) = 1 := seqBZ_of_mem_special p (by omega)
        unfold seqBZ at h0
        exact h0
      have h3 : hSeqZ
          (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
          p (t + 2 * p + 1) = 1 := by
        have heq3 : t + 2 * p + 1 = (1 : ℤ) := by omega
        rw [heq3]
        have h0 : seqBZ p 1 = 1 := seqBZ_of_mem_one_mid p 1 le_rfl (by omega)
        unfold seqBZ at h0
        exact h0
      rw [h1, h2, h3]
      rfl
    · have hle2 : t ≤ -2 * (p : ℤ) - 1 := by omega
      have h1 : hSeqZ
          (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
          p (t + 2 * p) = 0 := by
        have hz1 : -(p : ℤ) ≤ t + 2 * p := by omega
        have hz2 : t + 2 * p ≤ (0 : ℤ) := by omega
        have hne : t + 2 * p ≠ -(p : ℤ) + 1 := by omega
        have h0 : seqBZ p (t + 2 * p) = 0 := seqBZ_of_mem_zero p _ hz1 hz2 hne
        unfold seqBZ at h0
        exact h0
      have h3 : hSeqZ
          (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
          p (t + 2 * p + 1) = 0 := by
        have hz1 : -(p : ℤ) ≤ t + 2 * p + 1 := by omega
        have hz2 : t + 2 * p + 1 ≤ (0 : ℤ) := by omega
        have hne : t + 2 * p + 1 ≠ -(p : ℤ) + 1 := by omega
        have h0 : seqBZ p (t + 2 * p + 1) = 0 := seqBZ_of_mem_zero p _ hz1 hz2 hne
        unfold seqBZ at h0
        exact h0
      have h2 : hSeqZ
          (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then (1 : ℤ) else 0) else 1)
          p (t + p + 1) = 0 := by
        by_cases heq2 : t + p + 1 = -(p : ℤ)
        · rw [heq2]
          have hz1 : -(p : ℤ) ≤ -(p : ℤ) := le_rfl
          have hne : (-(p : ℤ)) ≠ -(p : ℤ) + 1 := by omega
          have h0 : seqBZ p (-(p : ℤ)) = 0 :=
            seqBZ_of_mem_zero p _ hz1 (by omega) hne
          unfold seqBZ at h0
          exact h0
        · have hle3 : t + p + 1 ≤ -(p : ℤ) - 1 := by omega
          have hge3 : (1 : ℤ) - 2 * p ≤ t + p + 1 := by omega
          have h0 : seqBZ p (t + p + 1) = 0 :=
            seqBZ_zero_backward_one p hp _ hge3 hle3
          unfold seqBZ at h0
          exact h0
      rw [h1, h2, h3]
      rfl

private theorem companionQ_apply (p : ℕ) (i j : Fin (2 * p + 1)) :
    companionQ p i j =
      (if j.val = 0 ∧ i.val = 2 * p then (-1 : ℤ)
      else if (j.val = 0 ∧ (i.val = 0 ∨ i.val = p - 1)) ∨
          j.val = i.val + 1 then 1
      else 0) := by
  simp [companionQ, Matrix.of_apply]

private theorem companionQ_col_ne_zero (p : ℕ) (k b : Fin (2 * p + 1))
    (hb : b.val ≠ 0) :
    companionQ p k b = (if b.val = k.val + 1 then (1 : ℤ) else 0) := by
  simp [companionQ_apply, hb]

private theorem companionQ_col_zero (p : ℕ) (k b : Fin (2 * p + 1))
    (hb : b.val = 0) :
    companionQ p k b =
      (if k.val = 2 * p then (-1 : ℤ)
      else if k.val = 0 ∨ k.val = p - 1 then 1
      else 0) := by
  simp [companionQ_apply, hb]

private theorem pow_succ_col_ne_zero (p n : ℕ) (a b : Fin (2 * p + 1))
    (hb : b.val ≠ 0) :
    ((companionQ p ^ (n + 1)) a b) =
      ((companionQ p ^ n) a ⟨b.val - 1, by
        have hb_lt := b.isLt
        omega⟩) := by
  rw [pow_succ, Matrix.mul_apply]
  have hb_ge : 1 ≤ b.val := Nat.pos_of_ne_zero hb
  have hk0_eq : (⟨b.val - 1, by omega⟩ : Fin (2 * p + 1)).val = b.val - 1 := rfl
  have hsum := Finset.sum_eq_single (⟨b.val - 1, by omega⟩ : Fin (2 * p + 1))
    (f := fun k => (companionQ p ^ n) a k * companionQ p k b)
    (s := Finset.univ)
    (fun k _ hk => by
      have hval : k.val ≠ b.val - 1 := by
        intro heq
        apply hk
        apply Fin.ext
        simpa using heq
      have hcond : ¬ (b.val = k.val + 1) := by
        intro heq
        apply hval
        omega
      have hq : companionQ p k b = 0 := by
        rw [companionQ_col_ne_zero p k b hb]
        simp [hcond]
      simp [hq])
    (fun h => False.elim (h (Finset.mem_univ _)))
  rw [hsum]
  have hq0 : companionQ p ⟨b.val - 1, by omega⟩ b = 1 := by
    rw [companionQ_col_ne_zero p _ b hb]
    have hcond0 : b.val = (⟨b.val - 1, by omega⟩ : Fin (2 * p + 1)).val + 1 := by
      simp
      omega
    exact ite_eq_left hcond0
  rw [hq0, mul_one]

private theorem pow_succ_col_zero (p n : ℕ) (hp : 2 ≤ p)
    (a b : Fin (2 * p + 1)) (hb : b.val = 0) :
    ((companionQ p ^ (n + 1)) a b) =
      ((companionQ p ^ n) a ⟨0, by omega⟩) +
        ((companionQ p ^ n) a ⟨p - 1, by omega⟩) -
        ((companionQ p ^ n) a ⟨2 * p, by omega⟩) := by
  rw [pow_succ, Matrix.mul_apply]
  set z0 : Fin (2 * p + 1) := ⟨0, by omega⟩ with hz0
  set zpred : Fin (2 * p + 1) := ⟨p - 1, by omega⟩ with hzpred
  set z2p : Fin (2 * p + 1) := ⟨2 * p, by omega⟩ with hz2p
  have hz0_val : z0.val = 0 := rfl
  have hzpred_val : zpred.val = p - 1 := rfl
  have hz2p_val : z2p.val = 2 * p := rfl
  have hne01 : z0 ≠ zpred := by
    apply Fin.ne_of_val_ne
    simp [hz0_val, hzpred_val]
    omega
  have hne02 : z0 ≠ z2p := by
    apply Fin.ne_of_val_ne
    simp [hz0_val, hz2p_val]
    omega
  have hne12 : zpred ≠ z2p := by
    apply Fin.ne_of_val_ne
    simp [hzpred_val, hz2p_val]
    omega
  have hnotin0 : z0 ∉ ({zpred, z2p} : Finset (Fin (2 * p + 1))) := by
    simp [hne01, hne02]
  have hnotin1 : zpred ∉ ({z2p} : Finset (Fin (2 * p + 1))) := by
    simp [hne12]
  have hsub : (∑ x ∈ ({z0, zpred, z2p} : Finset (Fin (2 * p + 1))),
      (companionQ p ^ n) a x * companionQ p x b) =
      ∑ x ∈ (Finset.univ : Finset (Fin (2 * p + 1))),
        (companionQ p ^ n) a x * companionQ p x b := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hknotin
    have hk0 : k ≠ z0 := by
      intro heq
      apply hknotin
      simp [heq]
    have hk1 : k ≠ zpred := by
      intro heq
      apply hknotin
      simp [heq]
    have hk2 : k ≠ z2p := by
      intro heq
      apply hknotin
      simp [heq]
    have hval0 : k.val ≠ 0 := by
      intro heq
      apply hk0
      apply Fin.ext
      simpa [hz0_val] using heq
    have hval1 : k.val ≠ p - 1 := by
      intro heq
      apply hk1
      apply Fin.ext
      simpa [hzpred_val] using heq
    have hval2 : k.val ≠ 2 * p := by
      intro heq
      apply hk2
      apply Fin.ext
      simpa [hz2p_val] using heq
    have hq : companionQ p k b = 0 := by
      rw [companionQ_col_zero p k b hb]
      simp [hval2, hval0, hval1]
    simp [hq]
  rw [← hsub]
  rw [Finset.sum_insert hnotin0, Finset.sum_insert hnotin1, Finset.sum_singleton]
  have hq0 : companionQ p z0 b = 1 := by
    rw [companionQ_col_zero p z0 b hb]
    simp [hz0_val]
    omega
  have hq1 : companionQ p zpred b = 1 := by
    rw [companionQ_col_zero p zpred b hb]
    simp [hzpred_val]
    omega
  have hq2 : companionQ p z2p b = -1 := by
    rw [companionQ_col_zero p z2p b hb]
    simp [hz2p_val]
  rw [hq0, hq1, hq2]
  ring

private theorem qPowEntry_shift (p n : ℕ) (a b : Fin (2 * p + 1))
    (hb : b.val ≠ 0) :
    qPowEntry p (n + 1) a b =
      qPowEntry p n a ⟨b.val - 1, by
        have hb_lt := b.isLt
        omega⟩ := by
  have hb_ge : 1 ≤ b.val := Nat.pos_of_ne_zero hb
  have hcast : ((((b.val - 1 : ℕ)) : ℤ)) = (b.val : ℤ) - 1 := by
    have h : 1 ≤ b.val := hb_ge
    omega
  by_cases ha0 : a.val = 0
  · simp only [qPowEntry, ha0, ↓reduceIte]
    congr 1
    omega
  · by_cases hamid : a.val ≤ p - 1
    · simp only [qPowEntry, ha0, hamid, ↓reduceIte]
      congr 1
      omega
    · simp only [qPowEntry, ha0, hamid, ↓reduceIte]
      congr 1
      congr 1
      omega

private theorem qPowEntry_rec_zero (p n : ℕ) (hp : 2 ≤ p)
    (a b : Fin (2 * p + 1)) (hb : b.val = 0) :
    qPowEntry p (n + 1) a b =
      qPowEntry p n a ⟨0, by omega⟩ +
        qPowEntry p n a ⟨p - 1, by omega⟩ -
        qPowEntry p n a ⟨2 * p, by omega⟩ := by
  set z0 : Fin (2 * p + 1) := ⟨0, by omega⟩ with hz0
  set zpred : Fin (2 * p + 1) := ⟨p - 1, by omega⟩ with hzpred
  set z2p : Fin (2 * p + 1) := ⟨2 * p, by omega⟩ with hz2p
  have hz0_val : z0.val = 0 := rfl
  have hzpred_val : zpred.val = p - 1 := rfl
  have hz2p_val : z2p.val = 2 * p := rfl
  by_cases ha0 : a.val = 0
  · simp only [qPowEntry, ha0, ↓reduceIte]
    have hrec := seqAZ_rec p (by omega) (((n + 1 : ℕ) : ℤ) + 1 - b.val)
    have e1 : ((n : ℕ) : ℤ) + 1 - z0.val =
        ((((n + 1 : ℕ) : ℤ) + 1 - b.val) - 1) := by omega
    have e2 : ((n : ℕ) : ℤ) + 1 - zpred.val =
        ((((n + 1 : ℕ) : ℤ) + 1 - b.val) - p) := by omega
    have e3 : ((n : ℕ) : ℤ) + 1 - z2p.val =
        ((((n + 1 : ℕ) : ℤ) + 1 - b.val) - 2 * p - 1) := by omega
    rw [e1, e2, e3]
    exact hrec
  · by_cases hamid : a.val ≤ p - 1
    · simp only [qPowEntry, ha0, hamid, ↓reduceIte]
      have hrec := seqBZ_rec p (by omega)
        (((n + 1 : ℕ) : ℤ) - p + 1 + a.val - b.val)
      have e1 : ((n : ℕ) : ℤ) - p + 1 + a.val - z0.val =
          ((((n + 1 : ℕ) : ℤ) - p + 1 + a.val - b.val) - 1) := by omega
      have e2 : ((n : ℕ) : ℤ) - p + 1 + a.val - zpred.val =
          ((((n + 1 : ℕ) : ℤ) - p + 1 + a.val - b.val) - p) := by omega
      have e3 : ((n : ℕ) : ℤ) - p + 1 + a.val - z2p.val =
          ((((n + 1 : ℕ) : ℤ) - p + 1 + a.val - b.val) - 2 * p - 1) := by omega
      rw [e1, e2, e3]
      exact hrec
    · simp only [qPowEntry, ha0, hamid, ↓reduceIte]
      have hrec := seqAZ_rec p (by omega)
        (((n + 1 : ℕ) : ℤ) - (2 * p - a.val) - b.val)
      have hneg : -seqAZ p (((n + 1 : ℕ) : ℤ) - (2 * p - a.val) - b.val) =
          -seqAZ p ((((n + 1 : ℕ) : ℤ) - (2 * p - a.val) - b.val) - 1) +
            -seqAZ p ((((n + 1 : ℕ) : ℤ) - (2 * p - a.val) - b.val) - p) -
            -seqAZ p ((((n + 1 : ℕ) : ℤ) - (2 * p - a.val) - b.val) - 2 * p - 1) := by
        rw [hrec]
        ring
      have e1 : ((n : ℕ) : ℤ) - (2 * p - a.val) - z0.val =
          ((((n + 1 : ℕ) : ℤ) - (2 * p - a.val) - b.val) - 1) := by omega
      have e2 : ((n : ℕ) : ℤ) - (2 * p - a.val) - zpred.val =
          ((((n + 1 : ℕ) : ℤ) - (2 * p - a.val) - b.val) - p) := by omega
      have e3 : ((n : ℕ) : ℤ) - (2 * p - a.val) - z2p.val =
          ((((n + 1 : ℕ) : ℤ) - (2 * p - a.val) - b.val) - 2 * p - 1) := by omega
      rw [e1, e2, e3]
      exact hneg

private theorem qPowEntry_zero_eq_one (p : ℕ) (hp : 2 ≤ p)
    (a b : Fin (2 * p + 1)) :
    qPowEntry p 0 a b = (if a = b then (1 : ℤ) else 0) := by
  by_cases hab : a = b
  · have hrhs : (if a = b then (1 : ℤ) else 0) = 1 := ite_eq_left hab
    rw [hrhs]
    have hval : a.val = b.val := Fin.ext_iff.mp hab
    by_cases ha0 : a.val = 0
    · simp only [qPowEntry, ha0, ↓reduceIte]
      have hb0 : b.val = 0 := by omega
      have harg : ((0 : ℕ) : ℤ) + 1 - b.val = 1 := by omega
      rw [harg]
      exact seqAZ_of_mem_one p 1 le_rfl (by omega)
    · by_cases hamid : a.val ≤ p - 1
      · simp only [qPowEntry, ha0, hamid, ↓reduceIte]
        have harg : ((0 : ℕ) : ℤ) - p + 1 + a.val - b.val = -(p : ℤ) + 1 := by omega
        rw [harg]
        exact seqBZ_of_mem_special p (by omega)
      · simp only [qPowEntry, ha0, hamid, ↓reduceIte]
        have harg : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val = -2 * (p : ℤ) := by omega
        rw [harg]
        have hneg : -seqAZ p (-2 * (p : ℤ)) = 1 := by
          rw [seqAZ_neg_two_p p hp]
          rfl
        exact hneg
  · have hrhs : (if a = b then (1 : ℤ) else 0) = 0 := ite_eq_right hab
    rw [hrhs]
    have hval_ne : a.val ≠ b.val := fun heq => hab (Fin.ext heq)
    by_cases ha0 : a.val = 0
    · simp only [qPowEntry, ha0, ↓reduceIte]
      have hb_ne : b.val ≠ 0 := by omega
      have hb_le : b.val ≤ 2 * p := by
        have hlt := b.isLt
        omega
      have hb_ge : 1 ≤ b.val := Nat.pos_of_ne_zero hb_ne
      by_cases hble : b.val ≤ p + 1
      · have hz1 : -(p : ℤ) ≤ ((0 : ℕ) : ℤ) + 1 - b.val := by omega
        have hz2 : ((0 : ℕ) : ℤ) + 1 - b.val ≤ 0 := by omega
        exact seqAZ_of_mem_zero p _ hz1 hz2
      · have hge : (1 : ℤ) - 2 * p ≤ ((0 : ℕ) : ℤ) + 1 - b.val := by omega
        have hle : ((0 : ℕ) : ℤ) + 1 - b.val ≤ -(p : ℤ) - 1 := by omega
        exact seqAZ_zero_backward_one p hp _ hge hle
    · by_cases hamid : a.val ≤ p - 1
      · simp only [qPowEntry, ha0, hamid, ↓reduceIte]
        have ha_ge : 1 ≤ a.val := by omega
        have ha_le : a.val ≤ p - 1 := hamid
        have hb_le : b.val ≤ 2 * p := by
          have hlt := b.isLt
          omega
        have hne : ((0 : ℕ) : ℤ) - p + 1 + a.val - b.val ≠ -(p : ℤ) + 1 := by omega
        by_cases hge : -(p : ℤ) ≤ ((0 : ℕ) : ℤ) - p + 1 + a.val - b.val
        · by_cases hle0 : ((0 : ℕ) : ℤ) - p + 1 + a.val - b.val ≤ 0
          · exact seqBZ_of_mem_zero p _ hge hle0 hne
          · have hle0' : ((0 : ℕ) : ℤ) - p + 1 + a.val - b.val ≤ 0 := by omega
            exact False.elim (hle0 hle0')
        · have hlt : ((0 : ℕ) : ℤ) - p + 1 + a.val - b.val < -(p : ℤ) := by omega
          have hle : ((0 : ℕ) : ℤ) - p + 1 + a.val - b.val ≤ -(p : ℤ) - 1 := by omega
          have hge2 : (2 : ℤ) - 3 * p ≤ ((0 : ℕ) : ℤ) - p + 1 + a.val - b.val := by omega
          exact seqBZ_zero_backward_two p hp _ hge2 hle
      · simp only [qPowEntry, ha0, hamid, ↓reduceIte]
        have ha_ge : p ≤ a.val := by omega
        have ha_le : a.val ≤ 2 * p := by
          have hlt := a.isLt
          omega
        have hb_le : b.val ≤ 2 * p := by
          have hlt := b.isLt
          omega
        have hne : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val ≠ -2 * (p : ℤ) := by omega
        have hneg : -seqAZ p (((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val) = 0 ↔
            seqAZ p (((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val) = 0 := by
          omega
        rw [hneg]
        by_cases hge : -(p : ℤ) ≤ ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val
        · by_cases hle0 : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val ≤ 0
          · exact seqAZ_of_mem_zero p _ hge hle0
          · have hle0' : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val ≤ 0 := by omega
            exact False.elim (hle0 hle0')
        · by_cases hge2 : (1 : ℤ) - 2 * p ≤ ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val
          · by_cases hle2 : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val ≤ -(p : ℤ) - 1
            · by_cases heq2p : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val = -2 * (p : ℤ)
              · exact False.elim (hne heq2p)
              · exact seqAZ_zero_backward_one p hp _ hge2 hle2
            · have hlt : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val < -(p : ℤ) := by omega
              have hle2' : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val ≤ -(p : ℤ) - 1 := by omega
              exact False.elim (hle2 hle2')
          · have hle3 : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val ≤ -2 * (p : ℤ) := by omega
            by_cases heq2p : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val = -2 * (p : ℤ)
            · exact False.elim (hne heq2p)
            · have hle4 : ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val ≤ -2 * (p : ℤ) - 1 := by omega
              have hge4 : (-3 : ℤ) * p ≤ ((0 : ℕ) : ℤ) - (2 * p - a.val) - b.val := by omega
              exact seqAZ_zero_backward_two p hp _ hge4 hle4

private theorem companionQ_pow_apply_aux (p : ℕ) (hp : 2 ≤ p) (n : ℕ)
    (a b : Fin (2 * p + 1)) :
    (companionQ p ^ n) a b = qPowEntry p n a b := by
  induction n generalizing a b with
  | zero =>
    rw [pow_zero]
    have hone : ((1 : Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℤ)) a b =
        (if a = b then (1 : ℤ) else 0) := Matrix.one_apply
    rw [hone]
    exact (qPowEntry_zero_eq_one p hp a b).symm
  | succ n ih =>
    by_cases hb : b.val = 0
    · have hpow := pow_succ_col_zero p n hp a b hb
      have hrec := qPowEntry_rec_zero p n hp a b hb
      rw [hpow, hrec]
      rw [ih _ _, ih _ _, ih _ _]
    · have hpow := pow_succ_col_ne_zero p n a b hb
      have hshift := qPowEntry_shift p n a b hb
      rw [hpow]
      rw [ih _ _]
      exact hshift.symm

/-- **Entries of the powers of the companion matrix $Q_p$.** Let $p \ge 2$ and $n$ be natural
numbers, and index the rows and columns of the $(2p+1) \times (2p+1)$ companion matrix $Q_p$ by
$0, 1, \dots, 2p$. Then for all indices $a$ and $b$, the entry $(a, b)$ of $Q_p^n$ equals
$A_p(n + 1 - b)$ if $a = 0$, equals $B_p(n - p + 1 + a - b)$ if $1 \le a \le p - 1$, and equals
$-A_p(n - (2p - a) - b)$ if $p \le a \le 2p$. Here $A_p, B_p : \mathbb{Z} \to \mathbb{Z}$ are the
sequences satisfying $S(t) = S(t-1) + S(t-p) - S(t-2p-1)$ for every integer $t$, with
$A_p(t) = 1$ for $1 \le t \le p$ and $A_p(t) = 0$ for $-p \le t \le 0$, and with $B_p(t) = 1$ for
$1 \le t \le p$ and for $t = -p+1$ and $B_p(t) = 0$ for the other $-p \le t \le 0$.

This corrects two misprints in the source's display of Theorem 9: there the index direction along
the $B_p$ rows is reversed after the first entry, and the $A_p$ terms of rows $p$ to $2p$ lack
their minus sign (the printed bottom-right entry $A_p(n-2p)$ is $A_2(-4) = -1$ at $p = 2$,
$n = 0$, whereas the identity matrix has entry $1$).

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 9. -/
public theorem companionQ_pow_apply (p n : ℕ) (hp : 2 ≤ p)
    (a b : Fin (2 * p + 1)) :
    (companionQ p ^ n) a b = qPowEntry p n a b
    := by exact companionQ_pow_apply_aux p hp n a b

end MathlibExt.NumberTheory.LeonardoPWanted
