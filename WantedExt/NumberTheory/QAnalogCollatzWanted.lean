/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.NumberTheory.QAnalogCollatz
public import MathlibExt.NumberTheory.QCollatzConjugacy
public import MathlibExt.NumberTheory.QCollatzParityCongruence
public import MathlibExt.NumberTheory.QCollatzParityFlip
public import MathlibExt.NumberTheory.QCollatzPerturbation
public import MathlibExt.NumberTheory.QAnalogCollatzQCollatzFixedPointsAndTwoCycle
public import MathlibExt.NumberTheory.QAnalogCollatzQCollatzOneOneAddXSqPolynomial

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

/-- **Parity vectors induce bijections modulo $q^n$.** Let $A, B \in \mathbb{F}_2[[q]]$ be odd
(constant term $1$), let $\mathrm{PV}_{A,B}$ be the parity vector map of the $q$-analog $T_{A,B}$
of the $3x+1$ map, and let $n \ge 1$ be an integer. Then there is a bijection
$e : \mathbb{F}_2[[q]]/(q^n) \to \mathbb{Z}/2^n\mathbb{Z}$ such that, for every
$a \in \mathbb{F}_2[[q]]$, $e$ sends the class of $a$ to the residue of $\mathrm{PV}_{A,B}(a)$
modulo $2^n$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 12 (`jis-2025-25.6.8-cor-12`). -/
public theorem_wanted qCollatzParityVector_quotient_bijection (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : (PowerSeries (ZMod 2) ⧸ Ideal.span {(X : PowerSeries (ZMod 2)) ^ n}) ≃ ZMod (2 ^ n),
      ∀ a, e (Ideal.Quotient.mk _ a) = PadicInt.toZModPow n (qCollatzParityVector A B a)

end

end MetaMathlibExt
