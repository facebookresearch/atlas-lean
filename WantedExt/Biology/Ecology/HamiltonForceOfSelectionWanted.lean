/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hamilton's force of selection on age-specific survival and fecundity

Discrete ages `x = 1, …, N`, survivorship `l_x = ∏_{a < x} p_a` from age-specific survival
probabilities `p_a > 0`, fecundities `m_x ≥ 0` (some positive), and intrinsic rate `r`, the
unique real root of `∑_x e^{-rx} l_x m_x = 1`. With the generation time
`T = ∑_x x e^{-rx} l_x m_x`, Hamilton (1966) showed
`∂r/∂ ln p_a = (∑_{x = a+1}^N e^{-rx} l_x m_x) / T` and `∂r/∂m_a = e^{-ra} l_a / T`. The
survival indicator equals `1/T` at every age before first reproduction, never increases with
age, and drops from age `a` to `a + 1` exactly when `m_{a+1} > 0`. The maximum age `N` is
finite, as in Hamilton's life tables.

Sources: W. D. Hamilton, "The moulding of senescence by natural selection", J. Theor. Biol. 12
(1966) 12–45, eq. (8); A. Baudisch, "Hamilton's indicators of the force of selection", Proc.
Natl. Acad. Sci. USA 102 (2005) 8263–8268, eqs. (4a) and (9); J. H. Jones, "Notes on Hamilton
(1966)", Stanford lecture notes.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace WantedExt.Biology.Ecology.HamiltonForceOfSelectionWanted

open Finset Filter Topology Real

/-- **Survivorship** to age `x`: `l_x = ∏_{a < x} p_a`. -/
def survivorship (p : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∏ a ∈ range x, p a

/-- The **discrete Euler–Lotka sum** `∑_{x=1}^N e^{-rx} l_x m_x`. -/
noncomputable def lotkaSum (N : ℕ) (p m : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ x ∈ Icc 1 N, exp (-(r * x)) * survivorship p x * m x

/-- The **generation time** `T = ∑_{x=1}^N x e^{-rx} l_x m_x`. -/
noncomputable def generationTime (N : ℕ) (p m : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ x ∈ Icc 1 N, (x : ℝ) * exp (-(r * x)) * survivorship p x * m x

/-- **Hamilton's survival indicator** at age `a`: `(∑_{x=a+1}^N e^{-rx} l_x m_x) / T`. -/
noncomputable def survivalIndicator (N : ℕ) (p m : ℕ → ℝ) (r : ℝ) (a : ℕ) : ℝ :=
  (∑ x ∈ Icc (a + 1) N, exp (-(r * x)) * survivorship p x * m x) / generationTime N p m r

/-- Survival probabilities with `p_a` multiplied by `e^u` (a shift of `ln p_a` by `u`). -/
noncomputable def scaleSurvival (p : ℕ → ℝ) (a : ℕ) (u : ℝ) : ℕ → ℝ :=
  Function.update p a (exp u * p a)

/-- **Hamilton's survival sensitivity** (Hamilton 1966, eq. (8)). With `p_a > 0`, `m_x ≥ 0`,
some `m_x > 0` for `1 ≤ x ≤ N`, and `r` a root of the Euler–Lotka equation, the root `R(u)` of
the equation after shifting `ln p_a` by `u` exists near `u = 0`, equals `r` at `0`, and has
derivative `(∑_{x=a+1}^N e^{-rx} l_x m_x) / T` there.

Sources: Hamilton (1966), eq. (8); Baudisch (2005), eq. (4a). -/
public theorem_wanted hasDerivAt_root_log_survival (N : ℕ) (p m : ℕ → ℝ)
    (hp : ∀ a, 0 < p a) (hm : ∀ x, 0 ≤ m x) (hrep : ∃ x ∈ Icc 1 N, 0 < m x) (r : ℝ)
    (hr : lotkaSum N p m r = 1) (a : ℕ) :
    ∃ R : ℝ → ℝ, R 0 = r ∧ (∀ᶠ u in 𝓝 0, lotkaSum N (scaleSurvival p a u) m (R u) = 1) ∧
      HasDerivAt R (survivalIndicator N p m r a) 0

/-- **Hamilton's fecundity sensitivity** (Hamilton 1966). With `p_a > 0` for all `a`, `m_x ≥ 0`
for all `x`, some `m_x > 0` with `1 ≤ x ≤ N`, and `r` solving the discrete Euler–Lotka equation
`lotkaSum N p m r = 1`, for an age `1 ≤ a ≤ N` the root `R(ε)` after changing `m_a` to `m_a + ε`
exists near `ε = 0`, equals `r` at `0`, and has derivative `e^{-ra} l_a / T` there.

Sources: Hamilton (1966); Baudisch (2005), eq. (9). -/
public theorem_wanted hasDerivAt_root_fecundity (N : ℕ) (p m : ℕ → ℝ)
    (hp : ∀ a, 0 < p a) (hm : ∀ x, 0 ≤ m x) (hrep : ∃ x ∈ Icc 1 N, 0 < m x) (r : ℝ)
    (hr : lotkaSum N p m r = 1) (a : ℕ) (ha : a ∈ Icc 1 N) :
    ∃ R : ℝ → ℝ, R 0 = r ∧
      (∀ᶠ ε in 𝓝 0, lotkaSum N p (Function.update m a (m a + ε)) (R ε) = 1) ∧
      HasDerivAt R (exp (-(r * a)) * survivorship p a / generationTime N p m r) 0

/-- **The force of selection on survival declines with age** (Hamilton 1966). With `p_a > 0` for
all `a`, `m_x ≥ 0` for all `x`, some `m_x > 0` with `1 ≤ x ≤ N`, and `r` solving the discrete
Euler–Lotka equation `lotkaSum N p m r = 1`: the survival indicator equals `1/T` at every age
`a` with no reproduction at ages `1, …, a`; it never increases from `a` to `a + 1`; and it
strictly decreases from `a` to `a + 1` whenever `a + 1 ≤ N` and `m_{a+1} > 0`.

Sources: Hamilton (1966); Jones, "Notes on Hamilton (1966)". -/
public theorem_wanted survivalIndicator_antitone (N : ℕ) (p m : ℕ → ℝ)
    (hp : ∀ a, 0 < p a) (hm : ∀ x, 0 ≤ m x) (hrep : ∃ x ∈ Icc 1 N, 0 < m x) (r : ℝ)
    (hr : lotkaSum N p m r = 1) :
    (∀ a, (∀ x ∈ Icc 1 a, m x = 0) →
        survivalIndicator N p m r a = (generationTime N p m r)⁻¹) ∧
      (∀ a, survivalIndicator N p m r (a + 1) ≤ survivalIndicator N p m r a) ∧
      ∀ a, a + 1 ≤ N → 0 < m (a + 1) →
        survivalIndicator N p m r (a + 1) < survivalIndicator N p m r a

end WantedExt.Biology.Ecology.HamiltonForceOfSelectionWanted
