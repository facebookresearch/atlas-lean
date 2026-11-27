/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.LehmerBoundsFormula
public import MathlibExt.NumberTheory.LehmerBoundsMonotonicity
public import MathlibExt.NumberTheory.SpoofLehmerFactorization
public import MathlibExt.NumberTheory.SpoofLehmerResidues
public import MathlibExt.NumberTheory.SpoofLehmerFactorizationSpoofLehmerBaseNotModEqOnePrime
public import MathlibExt.NumberTheory.SpoofLehmerFactorizationLehmerEquationSolutionsFinite
public import MathlibExt.NumberTheory.SpoofLehmerFactorizationSpoofLehmerLowerLeLeUpper

/-!
# Spoof Lehmer factorizations (wanted statements)

Statements from Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26
(2026), Article A33. The statement `spoofLehmer_lower_le_le_upper` is in
`MathlibExt.NumberTheory.SpoofLehmerFactorizationSpoofLehmerLowerLeLeUpper`. A spoof
factorization `x_1^{a_1} ⋯ x_r^{a_r}` is a multiset of pairs
`(x_i, a_i)` of positive integers; `x_1 ⋯ x_r` denotes the factorization with all exponents `1`,
encoded as `Multiset.map (fun a => (a, 1)) x`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Nontrivial spoof Lehmer factorizations have all exponents $1$.** If $F$ is a nontrivial spoof
$k$-Lehmer factorization for some integer $k$, then every exponent of $F$ is $1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 3 (`integers-2026-A33-thm-3`). -/
public theorem_wanted spoofLehmer_exponents_eq_one (F : Multiset (ℕ × ℕ))
    (k : ℤ) (hL : IsSpoofLehmer k F) (hnt : ¬ IsTrivialSpoof F) : ∀ p ∈ F, p.2 = 1

/-- **Bases of a nontrivial spoof Lehmer factorization are not $1$ modulo one another.** Let
$x_1, \dots, x_r$ be natural numbers and let $F = x_1 \cdots x_r$ be the spoof factorization with
these bases, all with exponent $1$. If $F$ is a nontrivial spoof $k$-Lehmer factorization for some
integer $k$, then $x_i \not\equiv 1 \pmod{x_j}$ for all $i$ and $j$, including $i = j$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Corollary 1 (`integers-2026-A33-cor-1`). -/
public theorem_wanted spoofLehmer_base_not_modEq_one_base (x : Multiset ℕ) (k : ℤ)
    (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) :
    ∀ a ∈ x, ∀ b ∈ x, ¬ a ≡ 1 [MOD b]

/-- **Solutions of the Lehmer equation with at most six variables.** Call a finite multiset
$\{x_1, \dots, x_r\}$ of natural numbers a solution of the Lehmer equation if $x_i \ge 2$ for
every $i$ and $k (x_1 - 1) \cdots (x_r - 1) = x_1 \cdots x_r - 1$ for some integer $k > 0$.
There are exactly $76$ solutions with $2 \le r \le 6$ (counted over all such $r$ together).
Exactly $31$ of them have every $x_i$ odd, and exactly $45$ have every $x_i$ even.

Solutions are counted as multisets, that is, up to the order of the $x_i$, as in Tables 1 and 2.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 2 (`integers-2026-A33-thm-2`). -/
public theorem_wanted lehmerEquation_solutions_count :
    Set.ncard {x : Multiset ℕ | 2 ≤ Multiset.card x ∧ Multiset.card x ≤ 6 ∧
      IsLehmerEquationSolution x} = 76 ∧
    Set.ncard {x : Multiset ℕ | 2 ≤ Multiset.card x ∧ Multiset.card x ≤ 6 ∧
      IsLehmerEquationSolution x ∧ ∀ a ∈ x, Odd a} = 31 ∧
    Set.ncard {x : Multiset ℕ | 2 ≤ Multiset.card x ∧ Multiset.card x ≤ 6 ∧
      IsLehmerEquationSolution x ∧ ∀ a ∈ x, Even a} = 45

/-- **Finitely many nontrivial spoof Lehmer factorizations with $r$ factors.** For every natural
number $r$, there are only finitely many finite multisets $F$ of pairs (base, exponent) of natural
numbers with exactly $r$ elements such that $F$ is a nontrivial spoof $k$-Lehmer factorization for
some integer $k$.

The source also asserts that these factorizations can be computed explicitly and verifiably; that
claim is not part of this statement.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 6 (`integers-2026-A33-thm-6`). -/
public theorem_wanted spoofLehmer_finite (r : ℕ) :
    {F : Multiset (ℕ × ℕ) | Multiset.card F = r ∧
      (∃ k : ℤ, IsSpoofLehmer k F) ∧ ¬ IsTrivialSpoof F}.Finite

/-- **Spoof Lehmer factorizations with at most six factors.** Let $F$ be a finite multiset of pairs
(base, exponent) of natural numbers with at most $6$ elements. Then $F$ is a nontrivial odd spoof
$k$-Lehmer factorization for some integer $k$ if and only if every exponent of $F$ is $1$ and the
multiset of bases of $F$ is one of the following $31$, written as tuples: $(3, 3)$, $(3, 5, 15)$,
$(3, 5, 17, 255)$, $(3, 3, 3, 3)$, $(3, 5, 17, 257, 65535)$, $(3, 5, 17, 285, 2507)$,
$(5, 5, 5, 43, 5375)$, $(5, 5, 9, 9, 89)$, $(3, 5, 17, 257, 65537, 4294967295)$,
$(3, 5, 17, 257, 65555, 226112997)$, $(3, 5, 17, 257, 65717, 23794275)$,
$(3, 5, 17, 257, 68975, 1314417)$, $(3, 5, 17, 353, 929, 83623935)$, $(3, 5, 17, 377, 1217, 2295)$,
$(3, 5, 17, 395, 1059, 2303)$, $(3, 5, 33, 53, 69, 8343)$, $(3, 9, 9, 23, 131, 732159)$,
$(5, 5, 5, 43, 5377, 28901375)$, $(5, 5, 5, 43, 5387, 2632285)$, $(5, 5, 5, 43, 5407, 937505)$,
$(5, 5, 5, 43, 5477, 291475)$, $(5, 5, 5, 43, 5717, 90115)$, $(5, 5, 5, 43, 6215, 39817)$,
$(5, 5, 5, 43, 6487, 31385)$, $(5, 5, 5, 43, 8507, 14605)$, $(5, 5, 5, 45, 807, 267023)$,
$(5, 5, 5, 47, 453, 2661375)$, $(5, 5, 5, 47, 457, 50659)$, $(5, 5, 5, 65, 129, 2325)$,
$(5, 7, 7, 7, 133, 228095)$ and $(3, 3, 5, 5, 9, 89)$. Also, $F$ is a nontrivial spoof $k$-Lehmer
factorization for some integer $k$ and $F$ is even (some base is even) if and only if every exponent
of $F$ is $1$ and the multiset of bases of $F$ is one of the following $45$, written as tuples:
$(2, 2)$, $(2, 4, 8)$, $(2, 2, 4)$, $(2, 2, 2)$, $(2, 4, 10, 80)$, $(2, 2, 6, 24)$, $(2, 2, 4, 4)$,
$(2, 2, 2, 8)$, $(2, 2, 2, 2)$, $(2, 4, 10, 82, 6560)$, $(2, 4, 10, 92, 670)$,
$(2, 4, 10, 100, 422)$, $(2, 4, 10, 112, 290)$, $(2, 2, 6, 26, 624)$, $(2, 2, 8, 12, 384)$,
$(2, 2, 2, 10, 80)$, $(2, 2, 2, 4, 32)$, $(2, 2, 2, 2, 16)$, $(2, 2, 2, 2, 6)$, $(2, 2, 2, 2, 4)$,
$(2, 2, 2, 2, 2)$, $(2, 4, 10, 82, 6562, 43046720)$, $(2, 4, 10, 82, 12440, 13882)$,
$(2, 4, 10, 88, 1120, 9944)$, $(2, 4, 26, 26, 26, 8272)$, $(2, 8, 8, 8, 206, 210944)$,
$(2, 2, 6, 26, 626, 390624)$, $(2, 2, 6, 42, 62, 2156)$, $(2, 2, 8, 12, 386, 148224)$,
$(2, 2, 8, 12, 404, 8166)$, $(2, 2, 8, 12, 416, 5154)$, $(2, 2, 8, 12, 636, 974)$,
$(2, 2, 12, 14, 18, 206)$, $(2, 2, 2, 10, 82, 6560)$, $(2, 2, 2, 10, 92, 670)$,
$(2, 2, 2, 10, 100, 422)$, $(2, 2, 2, 10, 112, 290)$, $(2, 2, 2, 4, 34, 1088)$,
$(2, 2, 2, 4, 38, 244)$, $(2, 2, 2, 6, 8, 384)$, $(2, 2, 2, 4, 8, 16)$, $(2, 2, 2, 2, 18, 288)$,
$(2, 2, 2, 2, 6, 6)$, $(2, 2, 2, 2, 2, 32)$ and $(2, 2, 2, 2, 2, 2)$.

The source further attributes $11$ of the odd and $27$ of the even factorizations to the families of
its Examples 2–5, leaving $20$ and $18$ sporadic ones; that attribution is not part of this
statement.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 7 (`integers-2026-A33-thm-7`). -/
public theorem_wanted spoofLehmer_atMostSix_tables :
    {F : Multiset (ℕ × ℕ) | Multiset.card F ≤ 6 ∧
      (∃ k : ℤ, IsSpoofLehmer k F) ∧ ¬ IsTrivialSpoof F ∧ IsOddSpoof F} =
      {F | ∃ l ∈ ([
      [3, 3], [3, 5, 15], [3, 5, 17, 255], [3, 3, 3, 3], [3, 5, 17, 257, 65535],
      [3, 5, 17, 285, 2507], [5, 5, 5, 43, 5375], [5, 5, 9, 9, 89],
      [3, 5, 17, 257, 65537, 4294967295], [3, 5, 17, 257, 65555, 226112997],
      [3, 5, 17, 257, 65717, 23794275], [3, 5, 17, 257, 68975, 1314417],
      [3, 5, 17, 353, 929, 83623935], [3, 5, 17, 377, 1217, 2295], [3, 5, 17, 395, 1059, 2303],
      [3, 5, 33, 53, 69, 8343], [3, 9, 9, 23, 131, 732159], [5, 5, 5, 43, 5377, 28901375],
      [5, 5, 5, 43, 5387, 2632285], [5, 5, 5, 43, 5407, 937505], [5, 5, 5, 43, 5477, 291475],
      [5, 5, 5, 43, 5717, 90115], [5, 5, 5, 43, 6215, 39817], [5, 5, 5, 43, 6487, 31385],
      [5, 5, 5, 43, 8507, 14605], [5, 5, 5, 45, 807, 267023], [5, 5, 5, 47, 453, 2661375],
      [5, 5, 5, 47, 457, 50659], [5, 5, 5, 65, 129, 2325], [5, 7, 7, 7, 133, 228095],
      [3, 3, 5, 5, 9, 89]] : List (List ℕ)),
        F = spoofOfBases (l : Multiset ℕ)} ∧
    {F : Multiset (ℕ × ℕ) | Multiset.card F ≤ 6 ∧
      (∃ k : ℤ, IsSpoofLehmer k F) ∧ ¬ IsTrivialSpoof F ∧ ¬ IsOddSpoof F} =
      {F | ∃ l ∈ ([
      [2, 2], [2, 4, 8], [2, 2, 4], [2, 2, 2], [2, 4, 10, 80], [2, 2, 6, 24], [2, 2, 4, 4],
      [2, 2, 2, 8], [2, 2, 2, 2], [2, 4, 10, 82, 6560], [2, 4, 10, 92, 670], [2, 4, 10, 100, 422],
      [2, 4, 10, 112, 290], [2, 2, 6, 26, 624], [2, 2, 8, 12, 384], [2, 2, 2, 10, 80],
      [2, 2, 2, 4, 32], [2, 2, 2, 2, 16], [2, 2, 2, 2, 6], [2, 2, 2, 2, 4], [2, 2, 2, 2, 2],
      [2, 4, 10, 82, 6562, 43046720], [2, 4, 10, 82, 12440, 13882], [2, 4, 10, 88, 1120, 9944],
      [2, 4, 26, 26, 26, 8272], [2, 8, 8, 8, 206, 210944], [2, 2, 6, 26, 626, 390624],
      [2, 2, 6, 42, 62, 2156], [2, 2, 8, 12, 386, 148224], [2, 2, 8, 12, 404, 8166],
      [2, 2, 8, 12, 416, 5154], [2, 2, 8, 12, 636, 974], [2, 2, 12, 14, 18, 206],
      [2, 2, 2, 10, 82, 6560], [2, 2, 2, 10, 92, 670], [2, 2, 2, 10, 100, 422],
      [2, 2, 2, 10, 112, 290], [2, 2, 2, 4, 34, 1088], [2, 2, 2, 4, 38, 244], [2, 2, 2, 6, 8, 384],
      [2, 2, 2, 4, 8, 16], [2, 2, 2, 2, 18, 288], [2, 2, 2, 2, 6, 6], [2, 2, 2, 2, 2, 32],
      [2, 2, 2, 2, 2, 2]] : List (List ℕ)),
        F = spoofOfBases (l : Multiset ℕ)}

end

end MetaMathlibExt
