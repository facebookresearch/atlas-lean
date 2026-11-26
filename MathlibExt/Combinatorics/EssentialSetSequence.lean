/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.RamseyFamily
import Mathlib.Logic.Equiv.List
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Decreasing sequences in essential sets

In a countable semigroup, every essential F-set contains a decreasing sequence of F-sets
such that, for each element of a term, left multiplication by that element sends a later
term into it.
-/

namespace MetaMathlibExt

open Filter

variable {S : Type*}

attribute [local instance] Ultrafilter.semigroup

set_option linter.unusedVariables false in
/-- **Essential F-sets contain shift-closed decreasing sequences (countable case).** Let $S$ be
a countable semigroup and $\mathcal F$ a family of subsets of $S$ with the Ramsey property. For
$x \in S$ and $E \subseteq S$ write $x^{-1}E = \{y \in S : xy \in E\}$, multiply ultrafilters on
$S$ by $E \in pq$ iff $\{x \in S : x^{-1}E \in q\} \in p$, and assume $pq \in \beta(\mathcal F)$
for all $p, q \in \beta(\mathcal F)$. If $A \subseteq S$ belongs to some $p \in \beta(\mathcal F)$
with $pp = p$ (an essential $\mathcal F$-set), then there are sets $C_0 \supseteq C_1 \supseteq
C_2 \supseteq \cdots$ in $\mathcal F$, all contained in $A$, such that for every $n$ and every
$x \in C_n$ there is $m$ with $C_m \subseteq x^{-1}C_n$.

Statements (b) (trees of functions) and (c) (downward directed families) of the paper are
omitted. The sequence is indexed from $0$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 6 (`integers-2025-A4-thm-6`). -/
public theorem exists_decreasing_sequence_of_idempotent_mem [Semigroup S] [Countable S]
    {F : Set (Set S)} (hF : IsRamseyFamily F)
    (hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) {A : Set S}
    (hA : ∃ p ∈ betaFamily F, p * p = p ∧ A ∈ p) :
    ∃ C : ℕ → Set S, Antitone C ∧ (∀ n, C n ⊆ A) ∧
      (∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : S | x * y ∈ C n}) ∧ ∀ n, C n ∈ F := by
  classical
  obtain ⟨p, hpF, hpp, hAp⟩ := hA
  let B := {t : S | (t * ·) ⁻¹' A ∈ p}
  let D := A ∩ B
  have hB : B ∈ p := by
    change A ∈ p * p
    rwa [hpp]
  have hD : D ∈ p := inter_mem hAp hB
  -- Every shift indexed by B carries D back to a member of p.
  have hshift (t : S) (ht : t ∈ B) : (t * ·) ⁻¹' D ∈ p := by
    simp only [D, Set.preimage_inter]
    apply inter_mem ht
    change ∀ᶠ y in p, ∀ᶠ z in p, (t * y) * z ∈ A
    simp only [mul_assoc]
    change (t * ·) ⁻¹' A ∈ p * p
    rw [hpp]
    exact ht
  obtain ⟨K, hmono, hcofinal⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset S)
  -- Each stage imposes only the shift conditions indexed by K n ∩ B.
  let C (n : ℕ) := D ∩ {y | ∀ t ∈ K n, t ∈ B → t * y ∈ D}
  refine ⟨C, fun i j hij y hy => ⟨hy.1, fun t ht => hy.2 t (hmono hij ht)⟩,
    fun n y hy => hy.1.1, ?_, ?_⟩
  · intro n x hx
    -- Testing x and all t * x at stage m tests every constraint of C n at x * y.
    obtain ⟨m, hm⟩ := hmono.tendsto_atTop_atTop_iff.mp hcofinal (insert x ((K n).image (· * x)))
    refine ⟨m, fun y hy => ⟨hy.2 x (hm (Finset.mem_insert_self ..)) hx.1.2, ?_⟩⟩
    intro t ht htB
    have htx := hm (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (· * x) ht))
    simpa only [mul_assoc] using hy.2 (t * x) htx (hx.2 t ht htB).2
  · intro n
    apply hpF _ (inter_mem hD ((K n).eventually_all.mpr ?_))
    exact fun t _ => eventually_imp_distrib_left.mpr (hshift t)

end MetaMathlibExt
