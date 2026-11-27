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
# Idempotents from decreasing sequences in Ramsey families

Intersect the closed sets of ultrafilters in a Ramsey family that contain each successive
term of the sequence. The shift condition makes the resulting compact set a subsemigroup.

## References

* Dibyendu De and Pintu Debnath, *Abundance of Arithmetic Progressions in CR-Sets*,
  INTEGERS **25** (2025), Article A4, pp. 1–8, Theorem 6(d) ⇒ (a).
  <https://math.colgate.edu/~integers/z4/z4.pdf>
* Dibyendu De, Pintu Debnath and Sayan Goswami, *Elementary characterization of essential
  $\mathcal{F}$-sets and its combinatorial consequences*, Semigroup Forum **104** (2022),
  pp. 45–57, Theorem 5, the source cited for the characterization.
* Neil Hindman and Dona Strauss, *Algebra in the Stone-Čech Compactification: Theory and
  Applications*, 2nd revised and extended edition, De Gruyter, 2012, p. 40, Theorem 2.5.
* Robert Ellis, *Distal transformation groups*, Pacific Journal of Mathematics **8** (1958),
  pp. 401–405, Lemma 1, for existence of an idempotent with one-sided continuity.
-/

namespace MetaMathlibExt

attribute [local instance] Ultrafilter.semigroup

variable {S : Type*}

/-- **Decreasing shift-closed sequences give essential sets.** Let $S$ be a semigroup and let $F$
be a family of subsets of $S$ with the Ramsey property, and write $\beta(F)$ for the set of
ultrafilters on $S$ all of whose members lie in $F$. For $x \in S$ and $E \subseteq S$ write
$x^{-1}E = \{y \in S : xy \in E\}$, and multiply ultrafilters on $S$ by the rule that
$E \in p \cdot q$ if and only if $\{x \in S : x^{-1}E \in q\} \in p$. Suppose that
$p \cdot q \in \beta(F)$ whenever $p, q \in \beta(F)$. Let $A \subseteq S$, and let
$C_0 \supseteq C_1 \supseteq C_2 \supseteq \cdots$ be members of $F$ contained in $A$ such that
for every $n$ and every $x \in C_n$ there is an $m$ with $C_m \subseteq x^{-1}C_n$. Then some
$p \in \beta(F)$ satisfies $p \cdot p = p$ and $A \in p$; that is, $A$ is an essential $F$-set.

This is the implication (d) ⇒ (a) of the paper's Theorem 6; statements (b) (trees of functions)
and (c) (downward directed families) are omitted. The sequence is indexed from $0$ rather
than $1$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 6 (`integers-2025-A4-thm-6`). -/
public theorem exists_idempotent_mem_of_decreasing_sequence [Semigroup S]
    {F : Set (Set S)} (hF : IsRamseyFamily F)
    (hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) {A : Set S}
    (C : ℕ → Set S) (hanti : Antitone C) (hCA : ∀ n, C n ⊆ A)
    (hshift : ∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : S | x * y ∈ C n}) (hCF : ∀ n, C n ∈ F) :
    ∃ p ∈ betaFamily F, p * p = p ∧ A ∈ p := by
  let K (n : ℕ) : Set (Ultrafilter S) := betaFamily F ∩ {p | C n ∈ p}
  have hclosed (n : ℕ) : IsClosed (K n) :=
    (isClosed_betaFamily hF).inter (ultrafilter_isClosed_basic _)
  have hnonempty (n : ℕ) : (K n).Nonempty := (mem_iff_exists_mem_betaFamily hF _).mp (hCF n)
  have hinter : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
      (fun n _ hp => ⟨hp.1, Filter.mem_of_superset hp.2 (hanti (Nat.le_succ n))⟩)
      hnonempty (hclosed 0).isCompact hclosed
  have hmul : ∀ p ∈ (⋂ n, K n), ∀ q ∈ (⋂ n, K n), p * q ∈ (⋂ n, K n) := by
    intro p hp q hq
    have hp' := Set.mem_iInter.mp hp
    have hq' := Set.mem_iInter.mp hq
    refine Set.mem_iInter.mpr fun n => ⟨hsub p (hp' n).1 q (hq' n).1, ?_⟩
    apply (Ultrafilter.eventually_mul p q (· ∈ C n)).2
    filter_upwards [(hp' n).2] with x hx
    obtain ⟨m, hm⟩ := hshift n x hx
    exact Filter.mem_of_superset (hq' m).2 hm
  obtain ⟨p, hp, hpp⟩ := exists_idempotent_in_compact_subsemigroup
    Ultrafilter.continuous_mul_left _ hinter (isClosed_iInter hclosed).isCompact hmul
  have hp₀ := Set.mem_iInter.mp hp 0
  exact ⟨p, hp₀.1, hpp, Filter.mem_of_superset hp₀.2 (hCA 0)⟩

end MetaMathlibExt
