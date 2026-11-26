/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Notation
public import MathlibExt.Combinatorics.Additive.Sidon
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.MinMax

/-!
# Sidon sets meeting every infinite progression

The sequence `s n = (n + 1)! + n` grows by more than a factor of two at each step, so its range is
Sidon. For any starting point `a` and positive step `d`, the index `n = a + d` gives a term of the
progression: `d` divides `(n + 1)!`.

## Record carried over from the retired wanted module

From `WantedExt/Combinatorics/SidonSetComplementProgressionErdosProblem198Wanted.lean`:

Source: T. F. Bloom, Erdős Problems, Problem #198, https://www.erdosproblems.com/198 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006760 (`EP-198`), dataset ulamai/UnsolvedMath v1.8.0.

Sidon sets are the canonical `Set.IsSidon` of MathlibExt (`a + b = c + d` forces `{a, b} = {c, d}`,
repeated summands included); an infinite progression is `a, a + d, a + 2d, …` with `d ≥ 1`. Compared
with the formal-conjectures statement `ErdosProblems/198.lean` (equivalent; no code imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SidonSetComplementProgressionErdosProblem198Wanted

/-- **Erdős Problem 198.** The proposition that the complement of every Sidon set
$A \subseteq \mathbb{N}$ contains an infinite arithmetic progression: for every Sidon set
$A \subseteq \mathbb{N}$ there are natural numbers $a$ and $d \ge 1$ such that $a + kd \notin A$
for every natural number $k$. -/
def sidonComplementContainsProgression : Prop :=
  ∀ A : Set ℕ, A.IsSidon → ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∉ A

private def term (n : ℕ) : ℕ := (n + 1).factorial + n

private lemma double_lt_term_succ (n : ℕ) : 2 * term n < term (n + 1) := by
  have h := Nat.mul_le_mul_left n (Nat.factorial_pos (n + 1))
  simp only [Nat.mul_one] at h
  simp only [term, Nat.factorial_succ (n + 1), Nat.add_mul, Nat.one_mul]
  omega

/-- A sum of two terms determines the larger index and hence both summands. -/
private lemma isSidon_range_of_double_lt {f : ℕ → ℕ} (hgap : ∀ n, 2 * f n < f (n + 1)) :
    (Set.range f).IsSidon := by
  have hmono : Monotone f := (strictMono_nat_of_lt_succ fun n ↦ by
    have := hgap n
    omega).monotone
  have index_le {i j k : ℕ} (h : f i ≤ f j + f k) : i ≤ max j k := by
    by_contra! hlt
    have hj := hmono (le_max_left j k)
    have hk := hmono (le_max_right j k)
    have hi := (hgap (max j k)).trans_le (hmono hlt)
    omega
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ heq
  have hmax : max i j = max k l := le_antisymm
    (max_le (index_le (by omega)) (index_le (by omega)))
    (max_le (index_le (by omega)) (index_le (by omega)))
  have hmaxValue := congrArg f hmax
  simp only [hmono.map_max] at hmaxValue
  omega

/--
**Erdős Problem 198 is false.** It is not the case that the complement of every Sidon set
$A \subseteq \mathbb{N}$ contains an infinite arithmetic progression: there is a Sidon set
$A \subseteq \mathbb{N}$ such that for all natural numbers $a$ and $d \ge 1$ some term $a + kd$,
$k \in \mathbb{N}$, lies in $A$. Here $A$ is Sidon when $w + x = y + z$ with $w, x, y, z \in A$
forces $\{w, x\} = \{y, z\}$.

To construct such a set, enumerate the infinite progressions $P_1, P_2, \ldots$ and pick
$a_n \in P_n$ with $a_n > 2 a_{n-1}$; the resulting lacunary set is Sidon and meets every infinite
progression. erdosproblems.com/198 records this construction (implicit in Baumgartner's paper) and
the explicit example $\{(n + 1)! + n : n \ge 0\}$.

Source: T. F. Bloom, Erdős Problems, Problem #198,
https://www.erdosproblems.com/198 (status DISPROVED (LEAN)); resolution: J. E. Baumgartner,
Partitioning vector spaces, J. Combin. Theory Ser. A 18 (1975), 231-233; construction recorded on
erdosproblems.com/198, erdosproblems.com/198: answered no; a lacunary set with one element in each
infinite progression (implicit in [Ba75]), or explicitly A = {(n + 1)! + n : n ≥ 0},
https://www.erdosproblems.com/198.
-/
public theorem sidonComplementContainsProgression_refuted :
    ¬ sidonComplementContainsProgression := by
  intro h
  obtain ⟨a, d, hd, hmiss⟩ := h (Set.range term) (isSidon_range_of_double_lt double_lt_term_succ)
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hd (show d ≤ a + d + 1 by omega)
  apply hmiss (q + 1)
  refine ⟨a + d, ?_⟩
  simp only [term, hq, Nat.succ_mul, Nat.mul_comm d q]
  omega

end MathlibExt.Combinatorics.SidonSetComplementProgressionErdosProblem198Wanted
