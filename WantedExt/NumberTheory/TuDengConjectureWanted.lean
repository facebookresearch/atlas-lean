/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tu-Deng conjecture
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.DigitalBinomialTheorem
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.TuDengConjectureWanted

open MetaMathlibExt (binDigitSum)

def tuDengConjecture : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ t : ZMod (2 ^ k - 1), t ≠ 0 →
    {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
      p.1 + p.2 = t ∧ binDigitSum p.1.val + binDigitSum p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

/-- **Tu–Deng conjecture.** For every integer $k \ge 2$ and every nonzero residue $t$ modulo
$2^k - 1$, the number of pairs $(a, b)$ of residues modulo $2^k - 1$ with $a + b = t$ and
$w(a) + w(b) \le k - 1$ is at most $2^{k-1}$, where $w(a)$ is the binary digit sum of the
representative of $a$ in $\{0, 1, \dots, 2^k - 2\}$.

Source: T. W. Cusick, Proof of the Tu-Deng
Conjecture, arXiv:2608.14821 (2026), https://arxiv.org/abs/2608.14821. Moved from
`OpenConjectures/NumberTheory/TuDengConjecture`.
-/
public theorem_wanted tuDengConjecture_holds : tuDengConjecture

end MathlibExt.NumberTheory.TuDengConjectureWanted
