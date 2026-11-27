/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.JosephusHighExtremal

/-!
# Extremal points of the Josephus function near `2k - 2`

The theorem `extremal_two_mul_sub` shows that `2k - 2` is always a low or a high
extremal point of the Josephus function: if `J_k(2k - 2) ≤ k - 1` then `2k - 3` is high
extremal and `2k - 2` is low extremal, while if `J_k(2k - 2) > k - 1` then `2k - 2` is high
extremal and `2k - 1` is low extremal.

Statements from Yunier Bello-Cruz and Roy
Quintero-Contreras, "Analytical Study and Efficient
Evaluation of the Josephus Function", *Journal of Integer
Sequences* 27 (2024), Article 24.3.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Cruz/cruz4.html>).
-/

@[expose] public section

namespace MathlibExt.NumberTheory.JosephusWanted

/-- **Extremal points of the Josephus function near $2k - 2$.** Let $k \ge 2$ be a natural
number and let $J_k$ be the Josephus function; call $m$ low extremal if $1 \le J_k(m) \le k - 1$,
and high extremal if $m + 1$ is low extremal. If $J_k(2k - 2) \le k - 1$, then $2k - 3$ is high
extremal and $2k - 2$ is low extremal. If $J_k(2k - 2) > k - 1$, then $2k - 2$ is high extremal
and $2k - 1$ is low extremal. In particular, $2k - 2$ is always a low or a high extremal point.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Corollary 7. -/
public theorem extremal_two_mul_sub (k : ℕ) (hk : 2 ≤ k) :
    (MetaMathlibExt.josephus k (2 * k - 2) ≤ k - 1 →
      IsHighExtremal k (2 * k - 3) ∧
        IsLowExtremal k (2 * k - 2)) ∧
    (k - 1 < MetaMathlibExt.josephus k (2 * k - 2) →
      IsHighExtremal k (2 * k - 2) ∧
        IsLowExtremal k (2 * k - 1)) := by
  have h1k : 1 ≤ 2 * k - 2 := by omega
  have hrng := MetaMathlibExt.josephus_range k (2 * k - 2) hk h1k
  refine ⟨fun hle => ?_, fun hlt => ?_⟩
  · have hlow : IsLowExtremal k (2 * k - 2) := ⟨hrng.1, hle⟩
    have hshift : 2 * k - 3 + 1 = 2 * k - 2 := by omega
    have hhigh : IsHighExtremal k (2 * k - 3) := by
      change IsLowExtremal k (2 * k - 3 + 1)
      rw [hshift]
      exact hlow
    exact ⟨hhigh, hlow⟩
  · have hkle : k ≤ MetaMathlibExt.josephus k (2 * k - 2) := by omega
    have h2k : 2 * k - 1 = (2 * k - 2) + 1 := by omega
    have hJ := MetaMathlibExt.josephus_succ k (2 * k - 2) hk h1k
    have hmod : (MetaMathlibExt.josephus k (2 * k - 2) + k - 1) % (2 * k - 1)
        = MetaMathlibExt.josephus k (2 * k - 2) - k := by
      have e : MetaMathlibExt.josephus k (2 * k - 2) + k - 1
          = (2 * k - 1) + (MetaMathlibExt.josephus k (2 * k - 2) - k) := by omega
      have hlt2 : MetaMathlibExt.josephus k (2 * k - 2) - k < 2 * k - 1 := by omega
      rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt hlt2]
    have hval : MetaMathlibExt.josephus k (2 * k - 1)
        = MetaMathlibExt.josephus k (2 * k - 2) - k + 1 := by
      rw [h2k, hJ, ← h2k, hmod]
    have hlow : IsLowExtremal k (2 * k - 1) := by
      refine ⟨?_, ?_⟩
      · rw [hval]
        omega
      · rw [hval]
        omega
    have hshift : 2 * k - 2 + 1 = 2 * k - 1 := by omega
    have hhigh : IsHighExtremal k (2 * k - 2) := by
      change IsLowExtremal k (2 * k - 2 + 1)
      rw [hshift]
      exact hlow
    exact ⟨hhigh, hlow⟩

end MathlibExt.NumberTheory.JosephusWanted
