/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeInterval.Breusch.Lower
import MathlibExt.NumberTheory.PrimeInterval.Breusch.Theta
import MathlibExt.NumberTheory.PrimeInterval.Breusch.Upper
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Breusch's prime-interval theorem

Every real `x ≥ 48` admits a prime strictly between `x` and `(9 / 8) * x`.

Provenance: R. Breusch, *Zur Verallgemeinerung des Bertrandschen Postulates,
daß zwischen x und 2x stets Primzahlen liegen*, Math. Z. 34 (1932), 505–526,
conclusion on p. 515; Göttingen scan `PPN266833020_0034`, SHA-256
`0a95f2b4f7c9535740d4f88924fb5576dc31a409cfaaf524b802489804fc18f1`.
-/

namespace MathlibExt.NumberTheory.BreuschWanted

namespace Internal

/-- **Breusch's endgame upper-bound inequality.** For a natural number $n$ write
$L(n) = \sum_{d \mid 210} \mu(d) \log \binom{2100n/d}{210n/d}$, where $\mu$ is the Möbius function;
this is the logarithm of Breusch's product $F_9(n)$. The endgame upper-bound inequality at $n$ is
the statement

$$L(n) \le \left(\frac{18900}{279} + \frac{18900}{657} + \frac{18900}{963}\right)
n \log 3.4 + \sqrt{2100n}\,\log(2100n).$$ -/
def upper_ineq (n : ℕ) : Prop :=
  logF9 n ≤ (18900/279 + 18900/657 + 18900/963 : ℝ) * n
    * Real.log 3.4 + Real.sqrt ((2100:ℝ)*n) * Real.log ((2100:ℝ)*n)

/-- **Breusch's prime chain.** The chain is the list of the following 111 natural numbers, in
order:

53, 59, 61, 67, 73, 79, 83, 89, 97, 109, 113, 127, 139, 151, 167, 181, 199, 223, 241, 271, 293,
317, 353, 397, 443, 491, 547, 613, 683, 761, 853, 953, 1069, 1201, 1327, 1489, 1669, 1877, 2111,
2371, 2663, 2971, 3331, 3739, 4201, 4723, 5309, 5953, 6691, 7523, 8461, 9511, 10691, 12011, 13499,
15173, 17053, 19183, 21577, 24251, 27281, 30689, 34519, 38833, 43669, 49123, 55259, 62143, 69899,
78623, 88427, 99469, 111893, 125863, 141587, 159233, 179119, 201499, 226669, 254993, 286859,
322709, 363047, 408427, 459479, 516911, 581521, 654209, 735983, 827969, 931421, 1047841, 1178809,
1326151, 1491913, 1678399, 1888193, 2124197, 2389721, 2688421, 3024457, 3402473, 3827767, 4306231,
4844501, 5450041, 6131239, 6897643, 7759831, 8729801, 9820997.

Every entry is prime, and each entry after the first is less than $\frac{9}{8}$ times the entry
before it. -/
def chain : List ℕ :=
  [53, 59, 61, 67, 73, 79,
  83, 89, 97, 109, 113, 127,
  139, 151, 167, 181, 199, 223,
  241, 271, 293, 317, 353, 397,
  443, 491, 547, 613, 683, 761,
  853, 953, 1069, 1201, 1327, 1489,
  1669, 1877, 2111, 2371, 2663, 2971,
  3331, 3739, 4201, 4723, 5309, 5953,
  6691, 7523, 8461, 9511, 10691, 12011,
  13499, 15173, 17053, 19183, 21577, 24251,
  27281, 30689, 34519, 38833, 43669, 49123,
  55259, 62143, 69899, 78623, 88427, 99469,
  111893, 125863, 141587, 159233, 179119, 201499,
  226669, 254993, 286859, 322709, 363047, 408427,
  459479, 516911, 581521, 654209, 735983, 827969,
  931421, 1047841, 1178809, 1326151, 1491913, 1678399,
  1888193, 2124197, 2389721, 2688421, 3024457, 3402473,
  3827767, 4306231, 4844501, 5450041, 6131239, 6897643,
  7759831, 8729801, 9820997]

/-- **Entries of Breusch's prime chain are prime.** Every entry of the chain is a prime number. -/
theorem chain_prime : ∀ p ∈ chain, p.Prime := by
  intro p hp
  fin_cases hp <;> norm_num

/-- **Breusch's prime chain is strictly increasing.** Each entry of the chain is less than every
later entry. -/
theorem chain_sorted : chain.Pairwise (· < ·) := by decide

/-- **Consecutive entries of Breusch's prime chain are within a factor $9/8$.** If $b$ immediately
follows $a$ in the chain, then $8b < 9a$. -/
theorem chain_ratio : ∀ pr ∈ chain.zip chain.tail, 8 * pr.2 < 9 * pr.1 := by
  decide

/-- **Last entry of Breusch's prime chain.** The last entry of the chain is $9820997$. -/
theorem chain_getLast : chain.getLast (by decide : chain ≠ []) = 9820997 := rfl

-- Bracketing: X between prev and the last element lies in some
-- consecutive pair interval.
/-- **Bracketing a real number in an increasing list.** Let $X$ be a real number and let
$c_0 < c_1 < \dots < c_k$ be natural numbers with $c_0 \le X < c_k$. Then there is an index
$i < k$ with $c_i \le X < c_{i+1}$. -/
lemma bracket (X : ℝ) : ∀ (l : List ℕ) (prev : ℕ),
    List.Pairwise (· < ·) (prev :: l) → (prev:ℝ) ≤ X →
    ∀ (hne : prev :: l ≠ []), (X:ℝ) < ((((prev :: l).getLast hne : ℕ)):ℝ) →
    ∃ (l1 : List ℕ) (a b : ℕ) (l2 : List ℕ),
      prev :: l = l1 ++ [a, b] ++ l2 ∧ (a:ℝ) ≤ X ∧ (X:ℝ) < (b:ℝ) := by
  intro l
  induction l with
  | nil =>
    intro prev hs hlo hne hhi
    rw [List.getLast_singleton] at hhi
    linarith [hlo, hhi]
  | cons q qs ih =>
    intro prev hs hlo hne hhi
    have hsq : List.Pairwise (· < ·) (q :: qs) := (List.pairwise_cons.mp hs).2
    have hne2 : q :: qs ≠ [] := by simp
    have hget : (prev :: q :: qs).getLast hne = (q :: qs).getLast hne2 :=
      List.getLast_cons hne2
    by_cases hXq : (X:ℝ) < (q:ℝ)
    · exact ⟨[], prev, q, qs, by simp, hlo, hXq⟩
    · have hXq' : (q:ℝ) ≤ X := le_of_not_gt hXq
      obtain ⟨l1, a, b, l2, heq, haX, hXb⟩ :=
        ih q hsq hXq' hne2 (by rwa [hget] at hhi)
      exact ⟨prev :: l1, a, b, l2, by
        rw [show (prev :: l1) ++ [a, b] ++ l2 = prev :: (l1 ++ [a, b] ++ l2) by simp,
          ← heq], haX, hXb⟩

/-- **Consecutive pairs survive prepending.** Let $R$ be a list of natural numbers and let
$a, b, d$ be natural numbers. If $(a, b)$ is a pair of consecutive entries of $R$ (an element
of the list obtained by zipping $R$ with its tail), then $(a, b)$ is also a pair of consecutive
entries of the list obtained by prepending $d$ to $R$. -/
lemma zip_cons_mem {R : List ℕ} {d a b : ℕ}
    (h : (a, b) ∈ R.zip R.tail) : (a, b) ∈ (d :: R).zip (d :: R).tail := by
  have etail : (d :: R).tail = R := rfl
  rw [etail]
  cases R with
  | nil => simp at h
  | cons r0 R' =>
    have etail2 : (r0 :: R').tail = R' := rfl
    rw [etail2] at h
    rw [List.zip_cons_cons]
    exact List.mem_cons_of_mem _ h

/-- **Adjacent entries form a consecutive pair.** Let $l$, $l_1$, $l_2$ be lists of natural
numbers and let $a, b$ be natural numbers. If $l$ is the concatenation of $l_1$, the two-entry
list $a, b$, and $l_2$, then $(a, b)$ is a pair of consecutive entries of $l$ (an element of the
list obtained by zipping $l$ with its tail). -/
lemma zip_mem_of_consec {l : List ℕ} {a b : ℕ} {l1 l2 : List ℕ}
    (h : l = l1 ++ [a, b] ++ l2) : (a, b) ∈ l.zip l.tail := by
  subst h
  induction l1 with
  | nil =>
    have e : (([] : List ℕ) ++ [a, b] ++ l2) = a :: b :: l2 := rfl
    rw [e]
    have etail : (a :: b :: l2).tail = b :: l2 := rfl
    rw [etail, List.zip_cons_cons]
    exact List.mem_cons.mpr (Or.inl rfl)
  | cons c cs ih =>
    have e : ((c :: cs) ++ [a, b] ++ l2) = c :: (cs ++ [a, b] ++ l2) := rfl
    rw [e]
    exact zip_cons_mem ih

/-- **Primes in $(X, 9X/8)$ for $53 \le X < 9820997$.** For every real number $X$ with
$53 \le X < 9820997$ there is a prime $p$ with $X < p < \frac{9}{8}X$. -/
theorem chain_cover (X : ℝ) (hlo : (53 : ℝ) ≤ X) (hhi : X < (9820997 : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ (X : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * X := by
  have hchain : chain = 53 :: chain.tail := rfl
  have hsorted : List.Pairwise (· < ·) (53 :: chain.tail) := by
    rw [← hchain]; exact chain_sorted
  have hne53 : 53 :: chain.tail ≠ [] := by simp
  have hlast : (53 :: chain.tail).getLast hne53 = 9820997 := rfl
  have hhi2 : X < (((9820997 : ℕ)) : ℝ) := by exact_mod_cast hhi
  obtain ⟨l1, a, b, l2, heq, haX, hXb⟩ :=
    bracket X chain.tail 53 hsorted hlo hne53 (by rwa [← hlast] at hhi2)
  have heq' : chain = l1 ++ [a, b] ++ l2 := by rw [hchain]; exact heq
  have hmem : (a, b) ∈ chain.zip chain.tail := zip_mem_of_consec heq'
  have hratio := chain_ratio (a, b) hmem
  have hb : b ∈ chain := by rw [heq']; simp
  have hprime := chain_prime b hb
  refine ⟨b, hprime, hXb, ?_⟩
  have hratioR : (8:ℝ)*b < 9*a := by exact_mod_cast hratio
  have haR : (a : ℝ) ≤ X := haX
  linarith [hratioR, haR]

-- Overlap: every X ≥ 5600*4762/3 sits in some [5600n/3, 1890n] with n ≥ 4762.
/-- **Every large real lies in a window $[5600n/3, 1890n]$.** For every real number
$X \ge 5600 \cdot 4762 / 3$ there is a natural number $n \ge 4762$ with
$5600n/3 \le X \le 1890n$. -/
lemma overlap (X : ℝ) (hX : (5600 * 4762 / 3 : ℝ) ≤ X) :
    ∃ n : ℕ, 4762 ≤ n ∧ (5600 : ℝ) * n / 3 ≤ X ∧ X ≤ (1890 : ℝ) * n := by
  set n := ⌊3 * X / 5600⌋₊ with hn
  have hXnn : (0 : ℝ) ≤ 3 * X / 5600 := by linarith [hX]
  refine ⟨n, ?_, ?_, ?_⟩
  · apply Nat.le_floor
    push_cast
    linarith [hX]
  · have hle : (n : ℝ) ≤ 3 * X / 5600 := Nat.floor_le hXnn
    linarith [hle]
  · have hlt := Nat.lt_floor_add_one (3 * X / 5600)
    linarith [hlt, hX]

-- Main contradiction at level n.
/-- **Endgame contradiction in Breusch's theorem.** Let $n \ge 4762$ be a natural number. If
there is no prime $p$ with $1890n < p \le 2100n$ and $n$ satisfies the endgame upper-bound
inequality, then we have a contradiction. -/
lemma main_contra (n : ℕ) (hn : 4762 ≤ n)
    (_hA : ∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False)
    (hupper : upper_ineq n) : False := by
  unfold upper_ineq at hupper
  have hn1 : 1 ≤ n := by omega
  have hlower := logF9_lower n hn1
  have hgap := gap_pos n hn
  have hmargin := T03c_eqmain_margin
  have h34 : Real.log (34/10:ℝ) = Real.log 3.4 := by congr 1; norm_num
  rw [h34] at hmargin
  have hcast : (((2100 * n : ℕ)) : ℝ) = (2100 : ℝ) * (n : ℝ) := by push_cast; ring
  rw [hcast] at hlower
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmargin_n := mul_lt_mul_of_pos_right hmargin hn0
  linarith [hlower, hupper, hgap, hmargin_n]

/-- **Primes in $(X, 9X/8)$ for large $X$, assuming the upper bound.** For a natural number $n$
write $L(n) = \sum_{m \mid 210} \mu(m) \log \binom{2100n/m}{210n/m}$, where $\mu$ is the Möbius
function. Let $X \ge 5600 \cdot 4762 / 3$ be a real number, and suppose that every natural number
$n \ge 1$ such that no prime $p$ satisfies $1890n < p \le 2100n$ also satisfies
$L(n) \le \left(\frac{18900}{279} + \frac{18900}{657} + \frac{18900}{963}\right) n \log 3.4 +
\sqrt{2100n}\,\log(2100n)$. Then there is a prime $p$ with $X < p < \frac{9}{8}X$. -/
theorem analytic_at_X (X : ℝ) (hX : (5600 * 4762 / 3 : ℝ) ≤ X)
    (hU : ∀ n : ℕ, 1 ≤ n →
      (∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) → upper_ineq n) :
    ∃ p : ℕ, p.Prime ∧ (X : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * X := by
  obtain ⟨n, hn0, hnlo, hnhi⟩ := overlap X hX
  by_contra hcon
  have hA : ∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False := by
    intro p hp hlo hhi
    apply hcon
    have h1 : (X : ℝ) < (p : ℝ) := by
      have h : ((1890 * n : ℕ):ℝ) < (p : ℝ) := by exact_mod_cast hlo
      have hcast : ((1890 * n : ℕ):ℝ) = (1890 : ℝ) * (n : ℝ) := by push_cast; ring
      rw [hcast] at h
      linarith [hnhi, h]
    have h2 : (p : ℝ) < (9 / 8 : ℝ) * X := by
      -- 2100 * n is composite, so the prime p is strictly below it.
      have hne : p ≠ 2100 * n := by
        intro heq
        have h2dvd : 2 ∣ p := by rw [heq]; exact ⟨1050 * n, by ring⟩
        have h2lt : 2 < p := by
          have hlo' := hlo
          have hn1 : 1 ≤ n := by omega
          omega
        have hdis := hp.eq_one_or_self_of_dvd 2 h2dvd
        omega
      have hhiR : (p : ℝ) < ((2100 * n : ℕ):ℝ) :=
        by exact_mod_cast (lt_of_le_of_ne hhi hne)
      have hcast : ((2100 * n : ℕ):ℝ) = (2100 : ℝ) * (n : ℝ) := by push_cast; ring
      rw [hcast] at hhiR
      have hle : (2100 : ℝ) * (n : ℝ) ≤ (9 / 8 : ℝ) * X := by linarith [hnlo]
      linarith [hhiR, hle]
    exact ⟨p, hp, h1, h2⟩
  exact main_contra n hn0 hA (hU n (by omega) hA)

/-- **Breusch's theorem from the upper bound.** For a natural number $n$ write
$L(n) = \sum_{m \mid 210} \mu(m) \log \binom{2100n/m}{210n/m}$, where $\mu$ is the Möbius function.
Let $x \ge 48$ be a real number, and suppose that every natural number $n \ge 1$ such that no
prime $p$ satisfies $1890n < p \le 2100n$ also satisfies
$L(n) \le \left(\frac{18900}{279} + \frac{18900}{657} + \frac{18900}{963}\right) n \log 3.4 +
\sqrt{2100n}\,\log(2100n)$. Then there is a prime $p$ with $x < p < \frac{9}{8}x$. -/
theorem breusch_prime_interval_of_upper (x : ℝ) (hx : 48 ≤ x)
    (hU : ∀ n : ℕ, 1 ≤ n →
      (∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) → upper_ineq n) :
    ∃ p : ℕ, p.Prime ∧ (x : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * x := by
  by_cases hX0 : x < (5600 * 4762 / 3 : ℝ)
  · by_cases h53 : x < 53
    · refine ⟨53, by norm_num, h53, ?_⟩
      linarith [hx]
    · have h53' : (53 : ℝ) ≤ x := le_of_not_gt h53
      have hlast : x < (9820997 : ℝ) := by
        have hle : (5600 * 4762 / 3 : ℝ) ≤ (9820997 : ℝ) := by norm_num
        linarith [hX0, hle]
      exact chain_cover x h53' hlast
  · have hX0' : (5600 * 4762 / 3 : ℝ) ≤ x := le_of_not_gt hX0
    exact analytic_at_X x hX0' hU

end Internal

/-- **Breusch's theorem on primes between $x$ and $9x/8$.** For every real number $x \ge 48$
there is a prime $p$ with $x < p < \frac{9}{8}x$.

Source: R. Breusch, *Zur Verallgemeinerung des Bertrandschen Postulates*,
Math. Z. 34 (1932), 505–526, conclusion on p. 515. -/
theorem breusch_prime_interval : ∀ x : ℝ, 48 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * x := by
  intro x hx
  exact Internal.breusch_prime_interval_of_upper x hx
    (fun n hn hA => Internal.logF9_upper n hn hA)

end MathlibExt.NumberTheory.BreuschWanted
