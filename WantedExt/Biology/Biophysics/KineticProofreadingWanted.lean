/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hopfield kinetic proofreading

Hopfield (1974) compares the error fraction `f` (incorrect over correct product formation rate,
at equal substrate concentrations) of two pseudo-first-order mass-action schemes on one
recognition site `c` with a correct substrate `C` and an incorrect substrate `D`.

* Scheme [1]: `S + c ⇌ Sc` (on `k'_S`, off `k_S`) and `Sc → product` (rate `W`), for
  `S ∈ {C, D}`. With `k'_C = k'_D` the steady-state error fraction is
  `f = (W + k_C) / (W + k_D)` (Eq. [3]); when `k_C ≤ k_D` it is at least `f₀ = k_C / k_D`, the
  source's minimum error fraction, which it approaches as `W → 0`.
* Scheme [4]: `S + c ⇌ Sc` (on `k'_S`, off `k_S`), `Sc ⇌ Sc*` (forward `m'`, backward `m`,
  nonspecific), `Sc* → S + c` (rate `l_S`) with reverse `S + c → Sc*` (rate `l'_S`), and
  `Sc* → product` (rate `W`). For the full scheme, with every rate positive, the steady-state
  error fraction is Eq. [5]; under the equilibrium constraint [6] it is never below `f₀` (for
  `f₀ < 1`).

Not stated here: the source's driven scheme [9], where the back reaction `m` and the direct
entry `l'_S` are negligible and the error fraction is `f ≈ f₀²` (text after Eq. [9], with the
driving condition Eq. [10]), since the source gives it only as an approximation; and
multi-stage proofreading (`f₀^{n+1}`).

Sources: J. J. Hopfield, "Kinetic proofreading: a new mechanism for reducing errors in
biosynthetic processes requiring high specificity", Proc. Natl. Acad. Sci. USA 71 (1974)
4135–4139, Eqs. [1]–[6]; Eqs. [9]–[10] for the driven scheme, which is not stated.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace WantedExt.Biology.Biophysics.KineticProofreadingWanted

/-- The steady-state equations of scheme [1] for one substrate: with free site concentration
`c`, the complex `Sc` (concentration `x`) is formed at rate `k' c` and lost at rate
`(k + W) x`. -/
def OneStageSteady (kOn kOff W c x : ℝ) : Prop :=
  kOn * c - (kOff + W) * x = 0

/-- The steady-state equations of scheme [4] for one substrate `S`: the complexes `Sc`
(concentration `x`) and `Sc*` (concentration `y`) satisfy
`k'_S c - k_S x - m' x + m y = 0` and `m' x - m y - l_S y + l'_S c - W y = 0`. -/
def TwoStageSteady (kOn kOff m' m l l' W c x y : ℝ) : Prop :=
  kOn * c - kOff * x - m' * x + m * y = 0 ∧ m' * x - m * y - l * y + l' * c - W * y = 0

/-- The error fraction of scheme [4] (Eq. [5]). -/
noncomputable def errorFraction (kC kD kOnC kOnD m' m lC lD l'C l'D W : ℝ) : ℝ :=
  (l'D * (kD + m') + m' * kOnD) * ((kC + m') * (W + lC) + kC * m) /
    (((kD + m') * (W + lD) + kD * m) * (l'C * (kC + m') + m' * kOnC))

/-- **One-stage error fraction** (Hopfield 1974, Eqs. [1]–[3]). Let all rates
`k'_C = k'_D = k' > 0`, `k_C, k_D, W > 0` and the free site concentration `c > 0`, and let `x_C`,
`x_D` satisfy the steady-state equations of scheme [1]. Then the product flux ratio is
`W x_D / (W x_C) = (W + k_C) / (W + k_D)`.

Source: Hopfield (1974), Eq. [3]. -/
theorem_wanted oneStage_errorFraction (kOn kC kD W c xC xD : ℝ) (hkOn : 0 < kOn) (hkC : 0 < kC)
    (hkD : 0 < kD) (hW : 0 < W) (hc : 0 < c) (hC : OneStageSteady kOn kC W c xC)
    (hD : OneStageSteady kOn kD W c xD) :
    W * xD / (W * xC) = (W + kC) / (W + kD)

/-- **Two-stage error fraction** (Hopfield 1974, Eqs. [4]–[5]). Let all rates
`k'_C, k'_D, k_C, k_D, m', m, l_C, l_D, l'_C, l'_D, W > 0` and the free site concentration
`c > 0`: the full scheme [4], with every step present. Let `(x_C, y_C)` and `(x_D, y_D)` satisfy
the steady-state equations of scheme [4] for `C` and `D`. Then the product flux ratio
`W y_D / (W y_C)` equals Eq. [5], which the source gives as the error fraction of "the full
reaction of Eq. [4]", with no special supposition about the on-rates.

Source: Hopfield (1974), Eq. [5]. -/
theorem_wanted twoStage_errorFraction (kC kD kOnC kOnD m' m lC lD l'C l'D W c xC yC xD yD : ℝ)
    (hkC : 0 < kC) (hkD : 0 < kD) (hkOnC : 0 < kOnC) (hkOnD : 0 < kOnD) (hm' : 0 < m')
    (hm : 0 < m) (hlC : 0 < lC) (hlD : 0 < lD) (hl'C : 0 < l'C) (hl'D : 0 < l'D) (hW : 0 < W)
    (hc : 0 < c) (hC : TwoStageSteady kOnC kC m' m lC l'C W c xC yC)
    (hD : TwoStageSteady kOnD kD m' m lD l'D W c xD yD) :
    W * yD / (W * yC) = errorFraction kC kD kOnC kOnD m' m lC lD l'C l'D W

/-- **No proofreading at equilibrium** (Hopfield 1974, Eq. [6]). Let `k' , k_C, k_D, m', l_C,
l_D, l', W > 0` with `k'_C = k'_D = k'`, `l'_C = l'_D = l'`, `l_C / l_D = k_C / k_D = f₀ < 1`
(the correct substrate `C` dissociates more slowly), and let `m` be fixed by the equilibrium
constraint `m'/m = l' k_C / (l_C k')`, that is `m = m' l_C k' / (l' k_C)`. Then the error
fraction of Eq. [5] is at least `f₀ = k_C / k_D`.

Source: Hopfield (1974), Eqs. [5]–[6]. -/
theorem_wanted le_errorFraction_of_equilibrium (kOn kC kD m' lC lD l' W : ℝ) (hkOn : 0 < kOn)
    (hkC : 0 < kC) (hkD : 0 < kD) (hm' : 0 < m') (hlC : 0 < lC) (hlD : 0 < lD) (hl' : 0 < l')
    (hW : 0 < W) (hratio : lC / lD = kC / kD) (hf₀ : kC / kD < 1) :
    kC / kD ≤ errorFraction kC kD kOn kOn m' (m' * lC * kOn / (l' * kC)) lC lD l' l' W

end WantedExt.Biology.Biophysics.KineticProofreadingWanted
