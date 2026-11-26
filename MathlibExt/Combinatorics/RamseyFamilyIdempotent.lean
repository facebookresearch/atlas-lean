/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.RamseyFamily

import Mathlib.Topology.Algebra.Semigroup

/-!
# Idempotent ultrafilters in Ramsey families

A Ramsey family's ultrafilters form a nonempty compact set. If this set is closed under
multiplication, the Ellis idempotent theorem applies using continuity of right translations.

## References

* Dibyendu De and Pintu Debnath, *Abundance of Arithmetic Progressions in CR-Sets*,
  INTEGERS **25** (2025), Article A4, pp. 1–8, Section 2, p. 4, after Theorem 3.
* Neil Hindman and Dona Strauss, *Algebra in the Stone-Čech Compactification: Theory and
  Applications*, 2nd revised and extended edition, De Gruyter, 2012, p. 40, Theorem 2.5 (the
  Ellis idempotent theorem).
-/

namespace MetaMathlibExt

attribute [local instance] Ultrafilter.semigroup

variable {S : Type*}

/-- **β(F) contains an idempotent when it is a subsemigroup.** Let $S$ be a semigroup and
$\mathcal F$ a family of subsets of $S$ with the Ramsey property, and multiply ultrafilters on
$S$ by $E \in pq$ iff $\{x \in S : \{y \in S : xy \in E\} \in q\} \in p$. If
$pq \in \beta(\mathcal F)$ for all $p, q \in \beta(\mathcal F)$, then there is
$p \in \beta(\mathcal F)$ with $pp = p$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, immediately after Theorem 3 (`integers-2025-A4-thm-3`). -/
public theorem exists_idempotent_mem_betaFamily [Semigroup S] {F : Set (Set S)}
    (hF : IsRamseyFamily F) (hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) :
    ∃ p ∈ betaFamily F, p * p = p := by
  obtain ⟨A, hA⟩ := hF.1
  obtain ⟨p, hp, -⟩ := (mem_iff_exists_mem_betaFamily hF A).mp hA
  exact exists_idempotent_in_compact_subsemigroup Ultrafilter.continuous_mul_left
    (betaFamily F) ⟨p, hp⟩ (isClosed_betaFamily hF).isCompact hsub

end MetaMathlibExt
