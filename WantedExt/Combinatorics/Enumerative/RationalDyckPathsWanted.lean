/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.RationalDyckPaths

/-!
# Correspondence between rational Dyck path families
-/

namespace MetaMathlibExt

/-- **$Q$-bonacci and rational-run paths correspond exactly when $s \equiv 1 \pmod r$.** Let
$r, s \ge 1$ be coprime natural numbers and let $t = \lfloor (s - 1)/r \rfloor$, so that
$t r + 1 \le s \le (t + 1) r$. For $m \in \mathbb{N}$ write $Q_m^{r/s}$ for the set of $Q$-bonacci
paths of semilength $m$ and $\tilde R_m^{r/s}$ for the set of Dyck paths of semilength $m$ and
height at most $2$ whose block word's maximal runs satisfy the rational run condition for
$q = r/s$. Then $\tilde R_{n+t+1}^{r/s}$ and $Q_n^{r/s}$ are in bijection for every $n \ge 0$ if
and only if $s = t r + 1$.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Proposition 7
(`jis-2025-25.3.2-prop-7`). -/
public theorem_wanted forall_nonempty_equiv_qBonacci_tildeRational_iff {r s : ℕ} (hr : 0 < r)
    (hs : 0 < s) (hrs : Nat.Coprime r s) :
    (∀ n : ℕ, Nonempty (tildeRationalDyckPaths r s (n + (s - 1) / r + 1) ≃
      qBonacciDyckPaths r s n)) ↔ s = (s - 1) / r * r + 1

end MetaMathlibExt
