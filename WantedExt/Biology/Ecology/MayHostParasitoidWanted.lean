/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# May's negative-binomial host–parasitoid model: local stability if and only if `k < 1`

May (1978) replaced the Poisson encounter law of the Nicholson–Bailey model by a negative
binomial with clumping parameter `k > 0`:
`H_{t+1} = F H_t (1 + a P_t / k)^{-k}` and `P_{t+1} = H_t - H_{t+1} / F` (eqs. 3–4), with host
growth factor `F > 1` and searching efficiency `a > 0`. The positive equilibrium is
`a P* = k (F^{1/k} - 1)` and `H* = (F / (F - 1)) P*` (eqs. 5–6); as `k → ∞` it tends to the
Nicholson–Bailey value `a P* = ln F`. The equilibrium "is stable against small disturbances if,
and only if, `k < 1`", whatever `F` and `a`; for `k > 1` arbitrarily small disturbances lead to
diverging oscillations (p. 839 and Appendix 2, by linearization).

Recorded here: the equilibrium and its `k → ∞` limit, local asymptotic stability for `k < 1`
and instability for `k > 1`, both for the nonlinear map on the open positive quadrant. The case
`k = 1` (eigenvalues of modulus `1`) and May's numerical global remarks are not claimed.

Sources: R. M. May, "Host-parasitoid systems in patchy environments: a phenomenological model",
J. Anim. Ecol. 47 (1978) 833–844, doi:10.2307/3674, eqs. 3–7 and Appendix 2.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

namespace WantedExt.Biology.Ecology.MayHostParasitoidWanted

open Filter Topology

/-- One step of **May's host–parasitoid map** with host growth factor `F`, searching efficiency
`a` and clumping parameter `k`: `(H, P) ↦ (F H (1 + a P / k)^{-k}, H - F H (1 + a P / k)^{-k} / F)`,
i.e. the parasitoids of the next generation are the parasitized hosts. -/
noncomputable def step (F a k : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (F * z.1 * (1 + a * z.2 / k) ^ (-k), z.1 - F * z.1 * (1 + a * z.2 / k) ^ (-k) / F)

/-- The equilibrium parasitoid density `P* = k (F^{1/k} - 1) / a` (May 1978, eq. 5). -/
noncomputable def parasitoidEq (F a k : ℝ) : ℝ := k * (F ^ (1 / k) - 1) / a

/-- The equilibrium host density `H* = (F / (F - 1)) P*` (May 1978, eq. 6). -/
noncomputable def hostEq (F a k : ℝ) : ℝ := F / (F - 1) * parasitoidEq F a k

/-- The equilibrium point `(H*, P*)`. -/
noncomputable def equilibrium (F a k : ℝ) : ℝ × ℝ := (hostEq F a k, parasitoidEq F a k)

/-- A fixed point `z*` of a map `T` of `ℝ × ℝ` is **locally asymptotically stable on the open
positive quadrant**: for every `ε > 0` there is `δ > 0` such that every `z` with both coordinates
positive and `dist z z* < δ` has `dist (Tⁿ z) z* < ε` for every `n`, and there is `δ₀ > 0` such
that every such `z` with `dist z z* < δ₀` has `Tⁿ z → z*`. -/
def IsLocallyAsymptoticallyStable (T : ℝ × ℝ → ℝ × ℝ) (zs : ℝ × ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ × ℝ, 0 < z.1 → 0 < z.2 → dist z zs < δ →
      ∀ n : ℕ, dist (T^[n] z) zs < ε) ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ z : ℝ × ℝ, 0 < z.1 → 0 < z.2 → dist z zs < δ₀ →
      Tendsto (fun n : ℕ => T^[n] z) atTop (𝓝 zs)

/-- A fixed point `z*` of `T` is **Lyapunov unstable on the open positive quadrant**: there is
`ε > 0` such that for every `δ > 0` some `z` with both coordinates positive and `dist z z* < δ`
has `dist (Tⁿ z) z* ≥ ε` for some `n`. -/
def IsUnstable (T : ℝ × ℝ → ℝ × ℝ) (zs : ℝ × ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ∃ z : ℝ × ℝ, 0 < z.1 ∧ 0 < z.2 ∧ dist z zs < δ ∧
    ∃ n : ℕ, ε ≤ dist (T^[n] z) zs

/-- **The positive equilibrium and its Nicholson–Bailey limit** (May 1978, eqs. 5–6): let
`F > 1`, `a > 0` and `k > 0`. Then `(H*, P*)`, with `P* = k (F^{1/k} - 1) / a` and
`H* = (F / (F - 1)) P*`, has both coordinates positive, is a fixed point of May's map, and is the
only fixed point with both coordinates positive; moreover, for fixed `F > 1` and `a > 0`,
`a P*` tends to `ln F` as `k → ∞`.

Source: May (1978), eqs. 5–6. -/
public theorem_wanted equilibrium_spec (F a k : ℝ) (hF : 1 < F) (ha : 0 < a) (hk : 0 < k) :
    0 < hostEq F a k ∧ 0 < parasitoidEq F a k ∧ step F a k (equilibrium F a k) = equilibrium F a k ∧
      (∀ z : ℝ × ℝ, 0 < z.1 → 0 < z.2 → step F a k z = z → z = equilibrium F a k) ∧
      Tendsto (fun κ : ℝ => a * parasitoidEq F a κ) atTop (𝓝 (Real.log F))

/-- **May's stability criterion, stable side** (May 1978, eq. 7 and Appendix 2): let `F > 1`,
`a > 0` and `0 < k < 1`. Then the positive equilibrium `(H*, P*)` is locally asymptotically
stable for May's map on the open positive quadrant.

Source: May (1978), p. 839 and Appendix 2. -/
public theorem_wanted stable_of_lt_one (F a k : ℝ) (hF : 1 < F) (ha : 0 < a) (hk₀ : 0 < k)
    (hk₁ : k < 1) :
    IsLocallyAsymptoticallyStable (step F a k) (equilibrium F a k)

/-- **May's stability criterion, unstable side** (May 1978, eq. 7 and Appendix 2): let `F > 1`,
`a > 0` and `k > 1`. Then the positive equilibrium `(H*, P*)` is Lyapunov unstable for May's map
on the open positive quadrant (arbitrarily small positive disturbances move a fixed distance
away).

Source: May (1978), p. 839 and Appendix 2. -/
public theorem_wanted unstable_of_one_lt (F a k : ℝ) (hF : 1 < F) (ha : 0 < a) (hk : 1 < k) :
    IsUnstable (step F a k) (equilibrium F a k)

end WantedExt.Biology.Ecology.MayHostParasitoidWanted
