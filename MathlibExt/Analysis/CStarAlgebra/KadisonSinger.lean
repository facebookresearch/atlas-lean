/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian

import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.Paving
import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.MSS

@[expose] public section

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger

/-- **Paving projection.** Given a colouring $c$ of the indices $\{0, \dots, n-1\}$ with the
colours $\{0, \dots, r-1\}$ and a colour $j$, the paving projection of $c$ onto colour $j$ is the
diagonal complex $n \times n$ matrix whose $i$-th diagonal entry is $1$ if $c(i) = j$ and $0$
otherwise. -/
noncomputable def pavingProj (n r : ℕ) (c : Fin n → Fin r) (j : Fin r) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => if c i = j then (1 : ℂ) else 0)

private lemma ksExists_paving_rate (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧
      2 * (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1 ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (6 / ε))
  have hN1 : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNe : 6 / ε < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : 0 < (N : ℝ) := lt_trans (by norm_num) hN1
  have hNnat : 0 < N := by exact_mod_cast hNpos
  refine ⟨N * N, Nat.mul_pos hNnat hNnat, ?_⟩
  have hsqrt : Real.sqrt ((N * N : ℕ) : ℝ) = N := by
    rw [Nat.cast_mul, ← pow_two, Real.sqrt_sq (Nat.cast_nonneg N)]
  rw [hsqrt]
  let x : ℝ := 1 / N
  let y : ℝ := Real.sqrt (1 / 2 : ℝ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hsix : 6 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hNe
  have hxe : x < ε / 6 := by
    dsimp [x]
    rw [div_lt_iff₀ hNpos]
    nlinarith
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy1 : y ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
  have hy2 : y ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hxx : x * x ≤ x := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hxy : x * y ≤ x := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hy1)]
  change 2 * (x + y) ^ 2 - 1 ≤ ε
  nlinarith

private theorem ksKadisonSingerPaving_of_finiteMSS
    (hMSS : FiniteMSSBound.{0}) (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℕ), 0 < r ∧
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.IsHermitian → (∀ i : Fin n, A i i = 0) → ‖A‖ ≤ 1 →
        ∃ (c : Fin n → Fin r), ∀ (j : Fin r),
          ‖pavingProj n r c j * A * pavingProj n r c j‖ ≤ ε := by
  obtain ⟨q, hq, hqε⟩ := ksExists_paving_rate ε hε
  refine ⟨q * q, Nat.mul_pos hq hq, ?_⟩
  intro n A hA hdiag hnorm
  obtain ⟨c, hc⟩ := andersonPaving_of_finiteMSS hMSS hq A hA hdiag hnorm
  refine ⟨c, ?_⟩
  intro j
  apply le_trans ?_ hqε
  simpa only [pavingProj] using hc j

/--
**Anderson paving theorem.** For every real $\varepsilon > 0$ there is a positive integer $r$ such
that for every $n \in \mathbb{N}$ and every Hermitian complex $n \times n$ matrix $A$ with zero
diagonal and $\|A\| \le 1$, where $\|\cdot\|$ is the operator norm for the Euclidean norm on
$\mathbb{C}^n$, there is a colouring $c$ of the indices $\{0, \dots, n-1\}$ with the $r$ colours
$\{0, \dots, r-1\}$ such that $\|P_j A P_j\| \le \varepsilon$ for every colour $j$, where $P_j$ is
the paving projection of $c$ onto colour $j$.

Proof: We formalize the Marcus--Spielman--Srivastava mixed-characteristic-polynomial bound via
real stability, interlacing families, and the barrier argument, then use Timotin's projection
dilation reduction to derive Anderson paving.

Proves `Wanted` entry `kadison_singer_paving`.

Source: Anderson paving formulation equivalent to Kadison–Singer conjecture; proved
by Marcus–Spielman–Srivastava, Ann. of Math. 182 (2015), 327–350; original Kadison–Singer, Amer.
J. Math. 81 (1959) and Anderson, Trans. Amer. Math. Soc. 249 (1979); Lean is finite-dimensional
Hermitian zero-diagonal paving with r(ε) independent of n.
-/
theorem kadison_singer_paving
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℕ), 0 < r ∧
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.IsHermitian → (∀ i : Fin n, A i i = 0) → ‖A‖ ≤ 1 →
        ∃ (c : Fin n → Fin r), ∀ (j : Fin r),
          ‖pavingProj n r c j * A * pavingProj n r c j‖ ≤ ε := by
  exact ksKadisonSingerPaving_of_finiteMSS finiteMSSBound.{0} ε hε

end MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted
