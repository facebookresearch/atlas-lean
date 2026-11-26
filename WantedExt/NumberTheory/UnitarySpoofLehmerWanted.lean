/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.NielsenBound
public import MathlibExt.NumberTheory.UnitarySpoofLehmer
public import MathlibExt.NumberTheory.UnitarySpoofLehmerReplicate
public import WantedExt.NumberTheory.SpoofLehmerFactorizationWanted
public import MathlibExt.NumberTheory.UnitarySpoofLehmerSpoofEvalLeOfIsSpoofLehmerSpoofOfBases

/-!
# Unitary spoof Lehmer factorizations (wanted statements)

Statements from Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26
(2026), Article A100. Hasanalizade's spoof factorization `x_1 ⋯ x_r` is a multiset of positive
integers; it is encoded as `spoofOfBases x` (all exponents `1`) from the Molnar–Singh module, so
that the spoof evaluation `ε̃(x_1 ⋯ x_r) = ∏ x_i` is `spoofEval (spoofOfBases x)` and the spoof
unitary totient `φ̃*(x_1 ⋯ x_r) = ∏ (x_i - 1)` is `spoofTotient (spoofOfBases x)`
(`spoofTotient_spoofOfBases`). A unitary `k`-Lehmer factorization (Equation (2)) is then
`IsSpoofLehmer k (spoofOfBases x)`: `k φ̃*(F) = ε̃(F) - 1` with at least two factors.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Spoof totient of a unitary factorization.** For natural numbers $x_1, \dots, x_r$, the spoof
totient of the spoof factorization $x_1 \cdots x_r$ with every exponent $1$ is
$\prod_{i=1}^{r} (x_i - 1)$, computed in the integers. This is Hasanalizade's spoof unitary
totient $\tilde{\varphi}^*(x_1 \cdots x_r)$.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Section 1 (definition of `φ̃*`). -/
theorem spoofTotient_spoofOfBases (x : Multiset ℕ) :
    spoofTotient (spoofOfBases x) = (x.map fun a : ℕ => (a : ℤ) - 1).prod := by
  simp [spoofTotient, spoofOfBases, Multiset.map_map]

end

end MetaMathlibExt
