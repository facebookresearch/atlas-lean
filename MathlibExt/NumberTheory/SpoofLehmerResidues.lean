/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.SpoofLehmerFactorization
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-! # Residues of bases of spoof Lehmer factorizations -/

namespace MetaMathlibExt

-- Keep the original named `hnt` argument: the equation alone suffices for this obstruction.
set_option linter.unusedVariables false in
/-- **Bases of a spoof Lehmer factorization modulo divisors of its evaluation.** Let
$x_1, \dots, x_r$ be natural numbers and let $F = x_1 \cdots x_r$ be the spoof factorization with
these bases, all with exponent $1$. Suppose $F$ is a nontrivial spoof $k$-Lehmer factorization for
some integer $k$. If $n$ is an integer with $n \ne \pm 1$ that divides the spoof evaluation
$\tilde e(F)$, then $x_i \not\equiv 1 \pmod n$ for every $i$.

The source states this for every integer $n$ dividing $\tilde e(F)$, but the hypothesis
$n \ne \pm 1$ cannot be dropped: $3 \cdot 3$ is a nontrivial spoof $2$-Lehmer factorization
($2 \cdot 4 = 9 - 1$), $1$ divides $\tilde e(3 \cdot 3) = 9$, and $3 \equiv 1 \pmod 1$. The source's
proof reaches $0 \equiv -1 \pmod n$, which is a contradiction only when $n \nmid 1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 4 (`integers-2026-A33-thm-4`). -/
public theorem spoofLehmer_base_not_modEq_one (x : Multiset ℕ) (k : ℤ)
    (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) (n : ℤ)
    (hn : n ∣ spoofEval (spoofOfBases x)) (hunit : ¬ IsUnit n) :
    ∀ a ∈ x, ¬ (a : ℤ) ≡ 1 [ZMOD n] := by
  intro a ha hmod
  have hfactor : (a : ℤ) - 1 ∣ spoofTotient (spoofOfBases x) := by
    apply Multiset.dvd_prod
    exact Multiset.mem_map.mpr ⟨(a, 1), Multiset.mem_map_of_mem _ ha, by simp⟩
  have htot : n ∣ spoofTotient (spoofOfBases x) := hmod.symm.dvd.trans hfactor
  have hdiff : n ∣ spoofEval (spoofOfBases x) - 1 := by
    rw [← hL.2.1]
    exact dvd_mul_of_dvd_right htot k
  exact hunit (isUnit_of_dvd_one (by simpa using dvd_sub hn hdiff))

end MetaMathlibExt
