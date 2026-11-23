/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Monatomic chain normal modes

Textbook dispersion relation of a periodic monatomic chain.

## i. Overview

The textbook dispersion relation of a periodic monatomic chain (`N` masses `m`, springs `K`) is
taken as a model input and not derived from dynamics. Its physical domain is enforced by its
arguments: `0 < m`, `0 ≤ K`, and `[NeZero N]` (so `N` is positive); outside that domain the bare
algebraic expression is not offered as a physical angular frequency. Only the finite periodic
case is treated: no continuous Fourier transform is claimed.

The module's `K` is the spring constant, `m` the mass, `N` the number of masses and `j` the mode
index. In N. W. Ashcroft and N. D. Mermin, Chapter 22, the one-dimensional monatomic Bravais
lattice with Born–von Karman periodic boundary conditions has `ω(k) = 2 √(K/M) |sin(k a / 2)|`
with allowed `k = 2π n / (N a)`, so `k a / 2 = π n / N`; here `K` is Ashcroft and Mermin's `K`,
`m` their `M`, `N` their `N` and `j` their `n`. In C. Kittel, Chapter 4,
`ω = (4C/M)^{1/2} |sin(K a / 2)|`, where Kittel writes `C` for the spring constant and `M` for
the mass; here `K` is Kittel's `C`, `m` his `M`, and `j` the mode index with `K a / 2 = π j / N`.

Provenance: atlas roadmap R09 and R11; task MF15, target MF15.3.

## ii. Key results

- `PhyslibExt.CondensedMatter.LatticeDynamics.MonatomicChain.chainNormalModeAngularFrequency` :
  textbook normal-mode angular frequency `ω_j = 2 √(K/m) |sin(π j / N)|`.
- `PhyslibExt.CondensedMatter.LatticeDynamics.MonatomicChain.chainNormalModeAngularFrequency_zero`
  : the `j = 0` mode has angular frequency `0`.
- `PhyslibExt.CondensedMatter.LatticeDynamics.MonatomicChain.chainNormalModeAngularFrequency_nonneg`
  : angular frequencies are nonnegative on the physical domain.
- `PhyslibExt.CondensedMatter.LatticeDynamics.MonatomicChain.chainNormalModeAngularFrequency_symm`
  : mode `N - j` has the same angular frequency as mode `j`.

## iii. Table of contents

- A. Dispersion relation
- B. Basic properties

## iv. References

* N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Holt, Rinehart and Winston (1976),
  Chapter 22, for the one-dimensional monatomic Bravais lattice with Born–von Karman periodic
  boundary conditions: `ω(k) = 2 √(K/M) |sin(k a / 2)|` with allowed `k = 2π n / (N a)`, so
  `k a / 2 = π n / N`.
* C. Kittel, *Introduction to Solid State Physics*, 8th ed., Wiley (2005), Chapter 4, for
  `ω = (4C/M)^{1/2} |sin(K a / 2)|` (Kittel writes `C` for the spring constant and `M` for the
  mass).

-/

@[expose] public section

noncomputable section

namespace PhyslibExt.CondensedMatter.LatticeDynamics.MonatomicChain

/-! ## A. Dispersion relation -/

/-- Textbook finite-chain normal-mode angular frequency (model input, not derived here):
`ω_j = 2 * sqrt(K / m) * |sin (π j / N)|`, valid for `0 < m`, `0 ≤ K`,
and positive `N`. The proof arguments gate the physical domain; they do not
enter the value. The ordinary frequency is `ν_j = ω_j / (2π)`, i.e.
`frequency` from the wave-conventions module. -/
noncomputable def chainNormalModeAngularFrequency (K m : ℝ) (_hm : 0 < m) (_hK : 0 ≤ K)
    (N : ℕ) [NeZero N] (j : ℕ) : ℝ :=
  2 * Real.sqrt (K / m) * |Real.sin (Real.pi * j / N)|

/-! ## B. Basic properties -/

/-- The `j = 0` chain mode has angular frequency `0`. -/
lemma chainNormalModeAngularFrequency_zero (K m : ℝ) (hm : 0 < m) (hK : 0 ≤ K)
    (N : ℕ) [NeZero N] :
    chainNormalModeAngularFrequency K m hm hK N 0 = 0 := by
  simp only [chainNormalModeAngularFrequency, Nat.cast_zero, mul_zero, zero_div,
    Real.sin_zero, abs_zero]

/-- Chain-mode angular frequencies are nonnegative on the physical domain. -/
lemma chainNormalModeAngularFrequency_nonneg (K m : ℝ) (hm : 0 < m) (hK : 0 ≤ K)
    (N : ℕ) [NeZero N] (j : ℕ) :
    0 ≤ chainNormalModeAngularFrequency K m hm hK N j := by
  unfold chainNormalModeAngularFrequency
  positivity

/-- Chain-mode symmetry: mode `N - j` has the same angular frequency as mode `j`. -/
lemma chainNormalModeAngularFrequency_symm (K m : ℝ) (hm : 0 < m) (hK : 0 ≤ K)
    {N : ℕ} [NeZero N] {j : ℕ} (hj : j ≤ N) :
    chainNormalModeAngularFrequency K m hm hK N (N - j) =
      chainNormalModeAngularFrequency K m hm hK N j := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have harg : Real.pi * ((N - j : ℕ) : ℝ) / N = Real.pi - Real.pi * j / N := by
    rw [Nat.cast_sub hj]
    field_simp
  simp only [chainNormalModeAngularFrequency, harg, Real.sin_pi_sub]

end PhyslibExt.CondensedMatter.LatticeDynamics.MonatomicChain
