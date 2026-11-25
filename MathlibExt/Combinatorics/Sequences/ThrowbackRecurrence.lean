/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Sequences.ThrowbackSequences
import MathlibExt.Combinatorics.Sequences.ThrowbackFrequency
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field

/-!
# Recurrence of terms in throwback sequences

Every entry in a sequence of distinct positive integers becomes the leader infinitely often.
A finite set of leader times would give the entry limiting frequency zero.
-/

namespace MetaMathlibExt

/-- **Every term recurs in the throwback sequence.** Let $X = (x_0, x_1, \dots)$ be a sequence of
pairwise distinct positive integers, and let $T(X) = (t_0, t_1, \dots)$ be its throwback
sequence. Then every term $x_j$ of $X$ appears infinitely often in $T(X)$: there are infinitely
many $k$ with $t_k = x_j$.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 2 (`jis-2025-25.5.1-thm-2`). -/
public theorem throwbackSequence_infinite_eq (X : ℕ → ℕ) (hX : ∀ n, 0 < X n)
    (hinj : Function.Injective X) (j : ℕ) :
    {k | throwbackSequence X k = X j}.Infinite := by
  intro hfin
  obtain ⟨c, hc, hlim⟩ := throwbackSequence_limiting_frequency_ne_zero X hX hinj j
  apply hc
  apply tendsto_nhds_unique hlim
  apply tendsto_bdd_div_atTop_nhds_zero (b := 0) (B := (hfin.toFinset.card : ℝ)) _ _
    tendsto_natCast_atTop_atTop
  · exact .of_forall fun _ => Nat.cast_nonneg _
  · refine .of_forall fun _ => Nat.cast_le.mpr (Finset.card_le_card ?_)
    exact fun k hk => hfin.mem_toFinset.mpr (Finset.mem_filter.mp hk).2

end MetaMathlibExt
