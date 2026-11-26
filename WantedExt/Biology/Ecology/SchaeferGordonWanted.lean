/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Schaefer's maximum sustainable yield and Gordon's bionomic equilibrium

Schaefer (1954) models a fished stock by `dP/dt = f(P) - k₂ F P` with natural increase
`f(P) = k₁ P (L - P)`, maximum population `L` and fishing intensity `F`; at equilibrium the
catch equals `f(P)`, a parabola with axis `P = L / 2`, so the maximum equilibrium catch is
`k₁ L² / 4`, attained only at `P = L / 2`. In `(r, K)` notation (`r = k₁ L`, `K = L`) the
maximum sustainable yield is `r K / 4` at `P = K / 2`. Gordon (1954) showed that under open
access fishing effort expands until total revenue equals total cost, so the net economic yield
of the bionomic equilibrium is zero.

Recorded here: Schaefer's maximum equilibrium catch, and Gordon's zero-rent equilibrium in the
standard Gordon–Schaefer form (harvest `q E P`, price `π`, cost `c` per unit effort, logistic
growth): an equilibrium with positive stock and effort and zero net revenue exists if and only if
`c / (π q) < K`, and it is `P∞ = c / (π q)`, `E∞ = (r / q) (1 - c / (π q K))`. The
Gordon–Schaefer form is derived (Gordon's argument is graphical).

Sources: M. B. Schaefer, "Some aspects of the dynamics of populations important to the
management of the commercial marine fisheries", Bull. Inter-Am. Trop. Tuna Comm. 1 (1954)
25–56; H. S. Gordon, "The economic theory of a common-property resource: the fishery", J. Polit.
Econ. 62 (1954) 124–142, doi:10.1086/257497.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.SchaeferGordonWanted

/-- **Natural increase.** Schaefer's natural increase `f(P) = k₁ P (L - P)`. -/
def naturalIncrease (k₁ L P : ℝ) : ℝ := k₁ * P * (L - P)

/-- **Schaefer's maximum equilibrium catch.** Let `k₁ > 0` and `L > 0`. For every stock level `P`,
the equilibrium catch `f(P) = k₁ P (L - P)` satisfies `f(P) ≤ k₁ L² / 4`, with equality if and only
if `P = L / 2`.

Source: Schaefer (1954). -/
public theorem_wanted naturalIncrease_le (k₁ L : ℝ) (hk₁ : 0 < k₁) (hL : 0 < L) (P : ℝ) :
    naturalIncrease k₁ L P ≤ k₁ * L ^ 2 / 4 ∧ (naturalIncrease k₁ L P = k₁ * L ^ 2 / 4 ↔ P = L / 2)

/-- **Bionomic equilibrium.** `(P, E)` is a bionomic equilibrium of the Gordon–Schaefer fishery with
intrinsic growth rate `r`, carrying capacity `K`, catchability `q`, price `π` and cost `c` per unit
effort: stock and effort are positive, the stock is at equilibrium, `r P (1 - P / K) = q E P`, and
the net revenue vanishes, `π q E P - c E = 0`. -/
def IsBionomicEquilibrium (r K q π c P E : ℝ) : Prop :=
  0 < P ∧ 0 < E ∧ r * P * (1 - P / K) = q * E * P ∧ π * q * E * P - c * E = 0

/-- **Gordon's bionomic equilibrium.** In the Gordon–Schaefer form of Gordon's (1954) model
(derived), let `r, K, q, π, c > 0`. A bionomic equilibrium exists if and only if `c / (π q) < K`; in
that case it is unique, with stock `P∞ = c / (π q)` and effort `E∞ = (r / q) (1 - c / (π q K))`.

Sources: Gordon (1954); Schaefer (1954). -/
public theorem_wanted bionomicEquilibrium_iff (r K q π c : ℝ) (hr : 0 < r) (hK : 0 < K)
    (hq : 0 < q) (hπ : 0 < π) (hc : 0 < c) :
    ((∃ P E, IsBionomicEquilibrium r K q π c P E) ↔ c / (π * q) < K) ∧
      ∀ P E, IsBionomicEquilibrium r K q π c P E →
        P = c / (π * q) ∧ E = r / q * (1 - c / (π * q * K))

end WantedExt.Biology.Ecology.SchaeferGordonWanted
