/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.Schroder
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
public import MathlibExt.Combinatorics.Enumerative.ZagierNumber
public import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
public import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusGeometricGrowth
public import MathlibExt.NumberTheory.DoldPrimePowerCongruences
public import MathlibExt.NumberTheory.HelouTerjanianLargePrime
public import MathlibExt.NumberTheory.HelouTerjanianThree
public import MathlibExt.NumberTheory.HelouTerjanianTwo
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.RealizableCombinatorialSequencesNotIsAlmostRealizableSeqCatalanMotzkinSchroder

namespace MetaMathlibExt

@[expose] public section

/-- **The zero sequence is almost realizable.** The constant sequence $a(n) = 0$ is almost
realizable.

It is realized by the self-map of the empty set, with multiplier $m = 1$.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 3. -/
theorem isAlmostRealizableSeq_zero : IsAlmostRealizableSeq fun _ => 0 :=
  ⟨1, one_pos, fun n _ => by simp⟩

/-- **Binomial-power sequences are almost realizable.** For all natural numbers $r \ge 1$ and $s$,
the binomial-power sequence $n \mapsto \sum_{k=0}^{n} \binom{n}{k}^r \binom{n+k}{k}^s$ is almost
realizable.

Every Dold realizable sequence is almost realizable (take the multiplier $m = 1$), and the
binomial-power sequences are Dold realizable.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 3 and Theorem 13. -/
theorem isAlmostRealizableSeq_binomialPowerSeq (r s : ℕ) (hr : 0 < r) :
    IsAlmostRealizableSeq fun n => binomialPowerSeq r s n :=
  ⟨1, one_pos, by simpa using binomial_power_sequence_dold_realizable r s hr⟩

/-- **Domb-type sums are Dold realizable.** For all natural numbers $r \ge 1$, $s$ and $t$, the
integer sequence $(D(n, r, s, t))_{n \ge 0}$ of Domb-type sums
$D(n, r, s, t) = \sum_{k=0}^{n} \binom{n}{k}^r \binom{2k}{k}^s \binom{2(n-k)}{n-k}^t$ is Dold
realizable.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Theorem 15 (`jis-2024-24.3.3-thm-15`). -/
public theorem_wanted doldRealizable_dombTypeSum (r s t : ℕ) (hr : 1 ≤ r) :
    doldRealizable fun n => ((dombTypeSum n r s t : ℕ) : ℤ)

/-- **Even-binomial-type sums are Dold realizable.** Let $r \ge 1$, $s$, $t$ and $u$ be natural
numbers with $t + u \ge 1$, and let

$$T(n) = \sum_{k=0}^{n} \binom{n}{2k}^r \binom{n+k}{k}^s \binom{2k}{k}^t \binom{2(n-k)}{n-k}^u.$$

Then the integer sequence $(T(n))_{n \ge 0}$ is Dold realizable.

The hypothesis $t + u \ge 1$ is added to the source: for $t = u = 0$ the Möbius transform at
$n = 2$ is $T(2) - T(1) = 3^s$, which is odd, so the sequence is not Dold realizable.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Theorem 18 (`jis-2024-24.3.3-thm-18`). -/
public theorem_wanted doldRealizable_evenBinomialTypeSum (r s t u : ℕ) (hr : 1 ≤ r)
    (htu : 1 ≤ t + u) :
    doldRealizable fun n => ((∑ k ∈ Finset.range (n + 1),
      n.choose (2 * k) ^ r * (n + k).choose k ^ s * (2 * k).choose k ^ t *
        (2 * (n - k)).choose (n - k) ^ u : ℕ) : ℤ)

end

end MetaMathlibExt
