/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.JosephusFunction
import MathlibExt.NumberTheory.JosephusFixedSuccCases

/-!
# Josephus fixed points and their next values

## References

* Yunier Bello-Cruz and Roy Quintero-Contreras,
  *Analytical Study and Efficient Evaluation of the Josephus Function*, Journal of Integer
  Sequences **27** (2024), Article 24.3.8, pp. 1–19, Proposition 4 (pp. 4–5).
* Leonhard Euler, *Observationes circa novum et singulare progressionum genus*,
  Novi Commentarii academiae scientiarum Petropolitanae **20** (1776), pp. 123–139,
  especially pp. 130–131. Bello-Cruz and Quintero-Contreras credit this work for the recurrence
  they recall in Theorem 2 and use in Proposition 4.
-/

namespace MathlibExt.NumberTheory.JosephusWanted

/-- **Josephus fixed points detected by the next value.** Let $k \ge 2$ and $n_p$ be natural
numbers with $n_p \ge k - 1$, and let $J_k$ be the Josephus function. Then $J_k(n_p) = n_p$ if
and only if $J_k(n_p + 1) = k - 1$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Proposition 4. -/
public theorem josephus_eq_self_iff (k np : ℕ) (hk : 2 ≤ k)
    (hnp : k - 1 ≤ np) :
    MetaMathlibExt.josephus k np = np ↔
      MetaMathlibExt.josephus k (np + 1) = k - 1 := by
  have hn : 1 ≤ np := by omega
  constructor
  · intro hfix
    exact (josephus_fixed_succ_cases k np hk hn hfix).1 (by omega)
  · intro hnext
    obtain ⟨hpos, hle⟩ := MetaMathlibExt.josephus_range k np hk hn
    rw [MetaMathlibExt.josephus_succ k np hk hn] at hnext
    by_cases hlt : MetaMathlibExt.josephus k np + k - 1 < np + 1
    · rw [Nat.mod_eq_of_lt hlt] at hnext
      omega
    · have hmod : np + 1 ≤ MetaMathlibExt.josephus k np + k - 1 := by omega
      have hrem : MetaMathlibExt.josephus k np + k - 1 - (np + 1) < np + 1 := by omega
      rw [Nat.mod_eq_sub_mod hmod, Nat.mod_eq_of_lt hrem] at hnext
      omega

end MathlibExt.NumberTheory.JosephusWanted
