/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Residue walks for Göbel sequences

Once a Göbel residue walk meets the diagonal at a positive index, it follows the diagonal
through the prime modulus. The walk also defines the boundaries used in non-integrality
results for Göbel sequences.

For any natural numbers $l,s$, the reflection laws of a periodic sign sequence $b_{l,s}$ can
be expressed using negation of an index and translation by $2s+1$.

## References

* Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*,
  Journal of Integer Sequences **29** (2026), Article 26.3.8, pp. 1–25. Section 2 defines the
  residue walk and zigzag order, Lemma 8 gives diagonal persistence, the proof of Theorem 1
  uses the boundaries, and Propositions 17 and 20 give the conditions for the sign sequences.
* The forward reindexings of the $b_{l,s}$ reflections also appear in the proofs of
  `existsUnique_gobelBSequence` and `gobelBSequence_complement` in
  `MathlibExt.NumberTheory.GobelBSequence`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The residue walk $\tilde g_l$.** For natural numbers $p$ and $l$, write
$\left(\frac{a}{p}\right)$ for the Jacobi symbol. The residue walk
$\tilde g_l \colon \mathbb{N} \to \mathbb{N}$ of $p$ starting at $l$ is defined by
$\tilde g_l(0) = 0$, $\tilde g_l(1) = l$ and, for every $n \ge 1$,
$\tilde g_l(n+1) = \tilde g_l(n) + \left(\frac{n}{p}\right)\left(\frac{\tilde g_l(n)}{p}\right)$
if $0 < \tilde g_l(n) < p$, and $\tilde g_l(n+1) = \tilde g_l(n)$ otherwise.

The sum in the first case is never negative, since $\tilde g_l(n) \ge 1$ there. The paper only
uses the indices $1 \le n \le p$; the value at $0$ and the values beyond $p$ totalize the walk.
For an odd prime $p$ the Jacobi symbol is the Legendre symbol.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the
(k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2
definition of `tilde g_l`. -/
public def gobelResidueWalk (p l : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => l
  | n + 2 =>
      let x := gobelResidueWalk p l (n + 1)
      if 0 < x ∧ x < p then
        Int.toNat ((x : ℤ) + jacobiSym (n + 1 : ℤ) p * jacobiSym (x : ℤ) p)
      else
        x

/-- **Initial value of the residue walk.** For all natural numbers $p$ and $l$, the residue walk
$\tilde g_l$ of $p$ starting at $l$ satisfies $\tilde g_l(1) = l$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition of
`tilde g_l`. -/
public theorem gobelResidueWalk_one (p l : ℕ) : gobelResidueWalk p l 1 = l := by
  rfl

/-- **Recurrence of the residue walk at interior values.** Let $p$, $l$ and $n$ be natural numbers
with $n \ge 1$, write $\tilde g_l$ for the residue walk of $p$ starting at $l$, and write
$\left(\frac{a}{p}\right)$ for the Jacobi symbol. If $0 < \tilde g_l(n) < p$, then

$$\tilde g_l(n+1) = \max\bigl(0, \tilde g_l(n) + (\tfrac{n}{p})(\tfrac{\tilde g_l(n)}{p})\bigr).$$

The maximum with $0$ records the conversion of the integer sum back to a natural number; the sum
is never negative because $\tilde g_l(n) \ge 1$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the
(k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2
definition of `tilde g_l`. -/
public theorem gobelResidueWalk_succ_of_between (p l n : ℕ) (hn : 1 ≤ n)
    (hbetween : 0 < gobelResidueWalk p l n ∧ gobelResidueWalk p l n < p) :
    gobelResidueWalk p l (n + 1) =
      Int.toNat ((gobelResidueWalk p l n : ℤ) +
        jacobiSym (n : ℤ) p * jacobiSym (gobelResidueWalk p l n : ℤ) p) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m] at hbetween ⊢
  change (if 0 < gobelResidueWalk p l (m + 1) ∧ gobelResidueWalk p l (m + 1) < p then
      Int.toNat ((gobelResidueWalk p l (m + 1) : ℤ) +
        jacobiSym (m + 1 : ℤ) p * jacobiSym (gobelResidueWalk p l (m + 1) : ℤ) p)
    else gobelResidueWalk p l (m + 1)) = _
  simp [hbetween]

/-- **The residue walk stays at $0$.** Let $p$, $l$ and $n$ be natural numbers with $n \ge 1$,
and write $\tilde g_l$ for the residue walk of $p$ starting at $l$. If $\tilde g_l(n) = 0$, then
$\tilde g_l(n+1) = 0$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition of
`tilde g_l`. -/
public theorem gobelResidueWalk_succ_of_eq_zero (p l n : ℕ) (hn : 1 ≤ n)
    (hzero : gobelResidueWalk p l n = 0) :
    gobelResidueWalk p l (n + 1) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m] at hzero ⊢
  change (if 0 < gobelResidueWalk p l (m + 1) ∧ gobelResidueWalk p l (m + 1) < p then _
    else gobelResidueWalk p l (m + 1)) = 0
  simp [hzero]

/-- **The residue walk stays at $p$.** Let $p$, $l$ and $n$ be natural numbers with $n \ge 1$,
and write $\tilde g_l$ for the residue walk of $p$ starting at $l$. If $\tilde g_l(n) = p$, then
$\tilde g_l(n+1) = p$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition of
`tilde g_l`. -/
public theorem gobelResidueWalk_succ_of_eq_prime (p l n : ℕ) (hn : 1 ≤ n)
    (hprime : gobelResidueWalk p l n = p) :
    gobelResidueWalk p l (n + 1) = p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m] at hprime ⊢
  change (if 0 < gobelResidueWalk p l (m + 1) ∧ gobelResidueWalk p l (m + 1) < p then _
    else gobelResidueWalk p l (m + 1)) = p
  simp [hprime]

-- Oddness and the bounds on the starting data are part of the source statement.
set_option linter.unusedVariables false in
/-- **The residue walk stays on the diagonal.** Let $p$ be an odd prime, let $l \le p - 1$ be a
natural number, and let $\tilde g_l$ be the residue walk of $l$ for $p$. If $1 \le m \le p$ and
$\tilde g_l(m) = m$, then $\tilde g_l(n) = n$ for every $n$ with $m \le n \le p$.

Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, Lemma 8. -/
public theorem gobelResidueWalk_eq_index_of_eq_index
    (p l m : ℕ) (hp : p.Prime) (hpodd : Odd p) (hl : l ≤ p - 1)
    (hm1 : 1 ≤ m) (hmp : m ≤ p) (hmeq : gobelResidueWalk p l m = m) :
    ∀ n, m ≤ n → n ≤ p → gobelResidueWalk p l n = n := by
  intro n hmn hnp
  induction n, hmn using Nat.le_induction with
  | base => exact hmeq
  | succ n hmn ih =>
    have hn : 0 < n := hm1.trans hmn
    have hlt : n < p := hnp
    have heq := ih hlt.le
    have hcop : (n : ℤ).gcd p = 1 := (Nat.coprime_of_lt_prime hn.ne' hlt hp).symm
    have hbetween : 0 < gobelResidueWalk p l n ∧ gobelResidueWalk p l n < p := by
      simpa only [heq] using And.intro hn hlt
    rw [gobelResidueWalk_succ_of_between p l n hn hbetween, heq,
      ← sq, jacobiSym.sq_one hcop]
    rfl

/-- **Zigzag order on integer sequences.** For a natural number $p$ and functions
$a, b : \mathbb{N} \to \mathbb{Z}$, $a$ lies zigzag-below $b$ up to $p$, written $a \preceq b$,
when there is a natural number $m \le p$ such that $a(n) < b(n)$ for all $1 \le n \le m$ and
$a(n) = b(n)$ for all $m < n \le p$.

The paper's point sets are represented by their integer-valued coordinate functions; values
outside $1 \le n \le p$ play no role.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition
of `⪯`. -/
public def IsZigzagBelow (p : ℕ) (a b : ℕ → ℤ) : Prop :=
  ∃ m ≤ p,
    (∀ n, 1 ≤ n → n ≤ m → a n < b n) ∧
    (∀ n, m < n → n ≤ p → a n = b n)

/-- **The sign sequence $a_{p,l}$.** For natural numbers $p$ and $l$, a function
$a : \mathbb{N} \to \mathbb{Z}$ is an $a_{p,l}$-sequence when all of the following hold:
$a(n) \in \{1, -1\}$ for $1 \le n \le p-1$; $a(n) = 0$ for $n = 0$ and for every $n \ge p$;
$a(1) = 1$; $a(n) = a(p-n)$ for $1 \le n \le \lfloor (p-1)/2 \rfloor$; $a(n) = -a(l+1-n)$ for
$1 \le n \le \lfloor l/2 \rfloor$; and $a(n) = a(l+1+n)$ for $1 \le n \le p-l-2$.

The values outside $1 \le n \le p-1$ are fixed to $0$ so that uniqueness of the paper's finite
sequence becomes uniqueness of the function.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of
the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8,
Proposition 17. -/
public def IsGobelASequence (p l : ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ n, 1 ≤ n → n ≤ p - 1 → a n = 1 ∨ a n = -1) ∧
  (∀ n, n = 0 ∨ p ≤ n → a n = 0) ∧
  a 1 = 1 ∧
  (∀ n, 1 ≤ n → n ≤ (p - 1) / 2 → a n = a (p - n)) ∧
  (∀ n, 1 ≤ n → n ≤ l / 2 → a n = -a (l + 1 - n)) ∧
  (∀ n, 1 ≤ n → n ≤ p - l - 2 → a n = a (l + 1 + n))

/-- **The periodic sign sequence $b_{l,s}$.** For natural numbers $l$ and $s$, a function
$b : \mathbb{Z} \to \mathbb{Z}$ is a $b_{l,s}$-sequence when all of the following hold:
$b(n) \in \{1, -1\}$ for every integer $n$; $b(n + l + 1) = b(n)$ for every integer $n$;
$b(1) = 1$; $b(n) = -b(l+1-n)$ for every integer $n$ not divisible by $l+1$; and
$b(s-n) = b(s+1+n)$ for every integer $n$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality
of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8,
Proposition 20. -/
public def IsGobelBSequence (l s : ℕ) (b : ℤ → ℤ) : Prop :=
  (∀ n, b n = 1 ∨ b n = -1) ∧
  (∀ n, b (n + (l + 1 : ℤ)) = b n) ∧
  b 1 = 1 ∧
  (∀ n, Int.emod n (l + 1 : ℤ) ≠ 0 → b n = -b ((l + 1 : ℤ) - n)) ∧
  (∀ n, b ((s : ℤ) - n) = b ((s : ℤ) + 1 + n))

/-- **Reflection characterization of the periodic Göbel sign sequence.** For natural numbers
$l,s$ and a function $b : \mathbb{Z} \to \mathbb{Z}$, $b$ is a $b_{l,s}$-sequence if and only if it
has period $l+1$, satisfies $b(1)=1$, takes values in $\{1,-1\}$, satisfies $b(n)=-b(-n)$ for
all integers $n$ not divisible by $l+1$, and satisfies $b(n+2s+1)=b(-n)$ for all integers $n$.
-/
public theorem isGobelBSequence_iff {l s : ℕ} {b : ℤ → ℤ} :
    IsGobelBSequence l s b ↔
      (∀ n, b n = 1 ∨ b n = -1) ∧ Function.Periodic b (l + 1 : ℤ) ∧ b 1 = 1 ∧
      (∀ n, ¬ (l + 1 : ℤ) ∣ n → b n = -b (-n)) ∧
      (∀ n, b (n + (2 * s + 1 : ℤ)) = b (-n)) := by
  constructor
  · rintro ⟨hsign, hperiod, hone, hanti, hreflect⟩
    have hp : Function.Periodic b (l + 1 : ℤ) := hperiod
    refine ⟨hsign, hp, hone, fun n hn => ?_, fun n => ?_⟩
    · rw [← hp.sub_eq' (x := n)]
      exact hanti n (Int.dvd_iff_emod_eq_zero.not.mp hn)
    · simpa only [show (s : ℤ) - ((s : ℤ) + n) = -n by omega,
        show (s : ℤ) + 1 + ((s : ℤ) + n) = n + (2 * s + 1 : ℤ) by omega]
        using (hreflect ((s : ℤ) + n)).symm
  · rintro ⟨hsign, hperiod, hone, hanti, hreflect⟩
    refine ⟨hsign, hperiod, hone, fun n hn => ?_, fun n => ?_⟩
    · rw [hperiod.sub_eq']
      exact hanti n (Int.dvd_iff_emod_eq_zero.not.mpr hn)
    · simpa only [show n - (s : ℤ) + (2 * s + 1 : ℤ) = s + 1 + n by omega, neg_sub]
        using (hreflect (n - (s : ℤ))).symm

/-- **Left boundary of the even Göbel residue walks.** Fix a natural number $p$ and, for each
natural number $l$, let $\tilde g_l$ denote the Göbel residue walk for $p$ starting at $l$. A
natural number $l_L$ is the left boundary for $p$ when there is an even natural number $l_0 < p$
with $\tilde g_{l_0}(p) = 0$ and $l_L = l_0 + 2$ such that every even natural number $l < p$
with $\tilde g_l(p) = 0$ satisfies $l \le l_0$. In other words, the set of even $l < p$ with
$\tilde g_l(p) = 0$ is nonempty and $l_L$ is its maximum plus $2$.

Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, proof of Theorem 1. -/
public def IsGobelLeftBoundary (p lL : ℕ) : Prop :=
  ∃ l0, Even l0 ∧ l0 < p ∧ gobelResidueWalk p l0 p = 0 ∧ lL = l0 + 2 ∧
    ∀ l, Even l → l < p → gobelResidueWalk p l p = 0 → l ≤ l0

/-- **Right boundary of the even Göbel residue walks.** Fix a natural number $p$ and, for each
natural number $l$, let $\tilde g_l$ denote the Göbel residue walk for $p$ starting at $l$. A
natural number $l_R$ is the right boundary for $p$ when $l_R$ is even, $l_R < p$,
$\tilde g_{l_R}(p) = p$, and every even natural number $l < p$ with $\tilde g_l(p) = p$
satisfies $l_R \le l$. In other words, $l_R$ is the least even $l < p$ with $\tilde g_l(p) = p$.

Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, proof of Theorem 1. -/
public def IsGobelRightBoundary (p lR : ℕ) : Prop :=
  Even lR ∧ lR < p ∧ gobelResidueWalk p lR p = p ∧
    ∀ l, Even l → l < p → gobelResidueWalk p l p = p → lR ≤ l

end

end MetaMathlibExt
