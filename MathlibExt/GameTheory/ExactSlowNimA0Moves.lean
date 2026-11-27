/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ExactSlowNimRemoteness
import all MathlibExt.GameTheory.ExactSlowNimRemoteness

/-!
# Moves supported by type (A0) basic vectors in exact slow Nim

A legal move from an (A0)-supported position strictly lowers its basic-vector value and leaves
an odd value. If a pile below the value in the support can stay unchanged under the move, a
new (A1) support shows that the loss is exactly one.

## References

* Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi,
  *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024),
  Article G1, Lemma 2 (Section 2, pp. 9–11).
* C. A. B. Smith, *Graphs and composite games*, Journal of Combinatorial Theory 1 (1966),
  pp. 51–81, for the remoteness function discussed in Section 1.3 of the first reference.
-/

namespace MetaMathlibExt

open exactSlowNim_critical_of_even

/-- **Moves at a position supported by an (A0) basic vector (Lemma 2).** Let $k \ge 1$, let
$B$ be the basic-vector value on $\mathbb{N}^{k+1}$, and let $x, z \in \mathbb{N}^{k+1}$ with
$z \le x$ componentwise, where $z$ is a basic vector of type (A0) with parameter $B(x)$. Let $j$
be a pile with $x_i > 0$ for every $i \ne j$, and let $x'$ be obtained from $x$ by removing one
token from every pile other than $j$. Then $B(x') \le B(x) - 1$ and $B(x')$ is odd. Moreover, if
$z_j < B(x)$, or if $z_j = B(x)$ and $z_i < \min(B(x), x_i)$ for some $i$, then
$B(x') = B(x) - 1$. Here $B(x) - 1$ is truncated subtraction in $\mathbb{N}$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 2. -/
public theorem exactSlowNimBasicValue_of_supports_basicA0 {k : ℕ} (hk : 0 < k)
    (x z : Fin (k + 1) → ℕ) (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA0 k (exactSlowNimBasicValue k x) z) (j : Fin (k + 1))
    (hj : ∀ i, i ≠ j → 0 < x i) :
    exactSlowNimBasicValue k (slowANimAfter x (Finset.univ.erase j)) ≤
        exactSlowNimBasicValue k x - 1 ∧
      Odd (exactSlowNimBasicValue k (slowANimAfter x (Finset.univ.erase j))) ∧
      (z j < exactSlowNimBasicValue k x ∨
          (z j = exactSlowNimBasicValue k x ∧
            ∃ i, z i < min (exactSlowNimBasicValue k x) (x i)) →
        exactSlowNimBasicValue k (slowANimAfter x (Finset.univ.erase j)) =
          exactSlowNimBasicValue k x - 1) := by
  have hmove : after x j ∈ slowANimMoves {k} x := (mem_moves_iff hk).mpr ⟨j, hj, rfl⟩
  -- A legal move supplies a type (A1) support at value one.
  let w (i : Fin (k + 1)) := if i = j then 0 else 1
  have hwx : w ≤ x := by
    intro i
    by_cases hi : i = j
    · simp [w, hi]
    · simpa [w, hi] using Nat.succ_le_of_lt (hj i hi)
  have hw : IsExactSlowNimBasicA1 k 1 w := by
    refine ⟨?_, ?_, by decide, j, by simp [w], ?_⟩
    · have hsum : ∑ i, (w i + if i = j then 1 else 0) = k + 1 := by
        calc
          _ = ∑ _i : Fin (k + 1), (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i = j <;> simp [w, hi]
          _ = _ := by simp
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Nat.mul_one] at hsum ⊢
      omega
    · intro i
      by_cases hi : i = j <;> simp [w, hi]
    · intro i hi
      by_contra hij
      simp [w, hij] at hi
  have hb := le_value hk hwx (Or.inr (Or.inl hw))
  have he := hz.2.2.1
  obtain ⟨hodd, hlt⟩ := (option_profile hk x hb).2.1 he _ hmove
  refine ⟨Nat.le_pred_of_lt hlt, hodd, fun h => ?_⟩
  obtain ⟨i, hi, hiy⟩ : ∃ i, z i < exactSlowNimBasicValue k x ∧ z i ≤ after x j i := by
    rcases h with hjlt | ⟨-, i, hi⟩
    · exact ⟨j, hjlt, by simpa [after_apply] using hzx j⟩
    · obtain ⟨hi, hix⟩ := lt_min_iff.mp hi
      refine ⟨i, hi, ?_⟩
      rw [after_apply]
      split_ifs <;> omega
  obtain ⟨hA, hle⟩ := a1_of_a0_after hzx hz j i hi hiy
  exact value_eq_pred_of_a1_after hk he hmove (le_value hk hle (Or.inr (Or.inl hA)))

end MetaMathlibExt
