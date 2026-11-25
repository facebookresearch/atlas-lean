/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CleanLatticeParallelogram

/-!
# A determinant of three convergent vectors

`convergentVec_det_three` expresses the oriented double area of the triangle on three
alternate convergent vectors as a signed product of partial quotients.
-/

namespace MetaMathlibExt
namespace convergentVec_det_three

open GenContFract
open GenContFract (of)

-- Include the two initial vectors so the recurrence also applies at indices zero and one.
private theorem step (x : ℚ) {m : ℕ} (hm : IsLeast {k | (of x).TerminatedAt k} m)
    (j : ℕ) (hj : j ≤ m) :
    convergentVec x j = convergentVec x ((j : ℤ) - 2) +
      (partialQuotient x j : ℝ) • convergentVec x ((j : ℤ) - 1) := by
  cases j with
  | zero =>
    obtain ⟨h₂, h₁, h₀, hq⟩ := convergentVec_initial x
    simp [h₂, h₁, h₀, hq, Prod.mk_add_mk, Prod.smul_mk]
  | succ j =>
    have hn : ¬(of x).TerminatedAt j := fun h => (Nat.not_le_of_lt hj) (hm.2 h)
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (mt terminatedAt_iff_partDen_none.mpr hn)
    cases j with
    | zero =>
      obtain ⟨gp, hs, rfl⟩ := exists_s_b_of_partDen hb
      have ha := of_partNum_eq_one (partNum_eq_s_a hs)
      norm_num [convergentVec, partialQuotient, hb, first_num_eq hs, first_den_eq hs, ha,
        Prod.mk_add_mk, Prod.smul_mk, add_comm]
    | succ j =>
      obtain ⟨hv, hq⟩ := convergentVec_recurrence x j hb
      simpa [Nat.cast_succ, hq, add_assoc, show (j : ℤ) + 2 - 1 = j + 1 by omega] using hv

end convergentVec_det_three

set_option linter.unusedVariables false in
/-- **A determinant of three convergent vectors.** Let $1 \le a < n$ be integers, let
$n / a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction of $n / a$, where $m$ is the
least index at which it terminates, and let $v_j = (B_j, A_j)$ be its convergent vectors. Then
for every natural number $i$ with $i + 2 \le m$, the determinant of the $3 \times 3$ matrix with
rows $(1, B_{i-2}, A_{i-2})$, $(1, B_i, A_i)$ and $(1, B_{i+2}, A_{i+2})$ equals
$(-1)^{i+1} q_i q_{i+1} q_{i+2}$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 10 (`integers-2026-A10-lem-10`). -/
public theorem convergentVec_det_three {a n m : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m) {i : ℕ}
    (him : i + 2 ≤ m) :
    let v := convergentVec ((n : ℚ) / a)
    let q := partialQuotient ((n : ℚ) / a)
    Matrix.det !![1, (v ((i : ℤ) - 2)).1, (v ((i : ℤ) - 2)).2;
        1, (v i).1, (v i).2;
        1, (v ((i : ℤ) + 2)).1, (v ((i : ℤ) + 2)).2] =
      (-1) ^ (i + 1) * ((q i * q (i + 1) * q (i + 2) : ℚ) : ℝ) := by
  intro v q
  let x := (n : ℚ) / a
  have hi : ¬(GenContFract.of x).TerminatedAt i := fun h => by
    have := hm.2 h
    omega
  have hdet := (SimpContFract.of x).determinant hi
  change (GenContFract.of x).nums i * (GenContFract.of x).dens (i + 1) -
    (GenContFract.of x).dens i * (GenContFract.of x).nums (i + 1) = (-1 : ℚ) ^ (i + 1) at hdet
  have hsign : (v i).2 * (v ((i : ℤ) + 1)).1 - (v i).1 * (v ((i : ℤ) + 1)).2 =
      (-1 : ℝ) ^ (i + 1) := by
    have hv (j : ℕ) :
        v j = (((GenContFract.of x).dens j : ℝ), ((GenContFract.of x).nums j : ℝ)) := by
      simp [v, x, convergentVec, show (j : ℤ) ≠ -2 by omega, show (j : ℤ) ≠ -1 by omega]
    rw [← Nat.cast_succ, hv, hv]
    dsimp only
    exact_mod_cast hdet
  have hstep (j : ℕ) (hj : j ≤ m) :
      v j = v ((j : ℤ) - 2) + (q j : ℝ) • v ((j : ℤ) - 1) :=
    convergentVec_det_three.step x hm j hj
  have h₁ : v ((i : ℤ) + 1) = v ((i : ℤ) - 1) + (q (i + 1) : ℝ) • v i := by
    simpa [Nat.cast_add, show (i : ℤ) + 1 - 2 = i - 1 by omega] using hstep (i + 1) (by omega)
  have h₂ : v ((i : ℤ) + 2) = v i + (q (i + 2) : ℝ) • v ((i : ℤ) + 1) := by
    simpa [Nat.cast_add, show (i : ℤ) + 2 - 1 = i + 1 by omega] using hstep (i + 2) him
  rw [← hsign, Matrix.det_fin_three, h₂, h₁, hstep i (by omega)]
  simp [Prod.smul_fst, Prod.smul_snd]
  ring

end MetaMathlibExt
