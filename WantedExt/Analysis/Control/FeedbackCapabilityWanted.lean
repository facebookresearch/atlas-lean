/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Wanted: the critical uncertainty `3/2 + √2` for feedback stabilisation

Xie and Guo (*How much uncertainty can be dealt with by feedback?*, IEEE Trans. Automat. Control
45 (2000)) determined exactly how much nonparametric uncertainty feedback can handle for the
first-order system `y_{t+1} = f(y_t) + u_t + w_{t+1}` with bounded noise: measured by the
generalized Lipschitz quasi-norm of the unknown `f`, the critical radius is `3/2 + √2`. The
statement is taken from Guo's ICM 2002 lecture (*Exploring the capability and limits of the
feedback mechanism*, Proc. ICM 2002, Vol. III; arXiv:math/0305011, Theorem 4.1), read in place of
the original paper.

A function `f : ℝ → ℝ` has quasi-norm
`‖f‖ = lim_{a → ∞} sup_{x, x'} |f x - f x'| / (|x - x'| + a)`, and `‖f‖ ≤ L` holds exactly when
for every `L' > L` there is `a` with `|f x - f x'| ≤ L' (|x - x'| + a)` for all `x, x'`; this is
the form used below. In the source a feedback law is a sequence of Lebesgue measurable maps
`h_t : ℝ^{t+1} → ℝ`, applied as `u_t = h_t(y_0, …, y_t)`. Both statements below use exactly this
notion: `NullMeasurable (h t) volume`, for Lebesgue measure `volume` on
`ℝ^{t+1} = Fin (t + 1) → ℝ`, says that preimages of Borel sets are Lebesgue measurable. Every
Borel measurable law is Lebesgue measurable (`Measurable.nullMeasurable`), and for real-valued
maps Lebesgue measurability is the same as almost-everywhere measurability
(`AEMeasurable.nullMeasurable`, `NullMeasurable.aemeasurable`).
-/

open Set MeasureTheory

@[expose] public section

namespace MathlibExt.Analysis.Control.FeedbackCapabilityWanted

/-- **Feedback can stabilise every system with uncertainty below `3/2 + √2`** (Xie and Guo,
IEEE Trans. Automat. Control 45 (2000); stated as Guo, Proc. ICM 2002, arXiv:math/0305011,
Theorem 4.1(i)). Let `L < 3/2 + √2`. There is a feedback law `u_t = h_t(y_0, …, y_t)`, with
each `h_t` Lebesgue measurable as in the source, such that for every noise bound `W > 0`, every
`f : ℝ → ℝ` with generalized Lipschitz quasi-norm `‖f‖ ≤ L`, every noise sequence with
`|w_t| ≤ W` and every initial value `y_0`, the closed loop `y_{t+1} = f(y_t) + u_t + w_{t+1}`
satisfies `sup_t (|y_t| + |u_t|) < ∞`. As in the source, one law serves every noise bound, which
it does not know. -/
theorem_wanted exists_feedback_bddAbove_of_lt (L : ℝ) (hL : L < 3 / 2 + √2) :
    ∃ h : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ, (∀ t, NullMeasurable (h t) volume) ∧
      ∀ W : ℝ, 0 < W →
      ∀ f : ℝ → ℝ, (∀ L' > L, ∃ a : ℝ, ∀ x x', |f x - f x'| ≤ L' * (|x - x'| + a)) →
      ∀ w : ℕ → ℝ, (∀ t, |w t| ≤ W) →
      ∀ y u : ℕ → ℝ, (∀ t, u t = h t (fun i => y i)) →
        (∀ t, y (t + 1) = f (y t) + u t + w (t + 1)) →
        BddAbove (range fun t => |y t| + |u t|)

/-- **No feedback stabilises every system with uncertainty at least `3/2 + √2`** (Xie and Guo,
IEEE Trans. Automat. Control 45 (2000); stated as Guo, Proc. ICM 2002, arXiv:math/0305011,
Theorem 4.1(ii)). Let `L ≥ 3/2 + √2` and `W > 0`. For every feedback law
`u_t = h_t(y_0, …, y_t)` with each `h_t` Lebesgue measurable, as in the source (so in
particular every Borel measurable law), and every initial value `y_0`, there are `f : ℝ → ℝ`
with generalized Lipschitz quasi-norm `‖f‖ ≤ L` and a noise sequence with `|w_t| ≤ W` such that
the closed loop `y_{t+1} = f(y_t) + u_t + w_{t+1}` is unbounded: `sup_t |y_t| = ∞`. The source
does not say how the noise is chosen, so letting the adversary choose it, as here, is the
weakest reading. -/
theorem_wanted exists_unbounded_of_le (L : ℝ) (hL : 3 / 2 + √2 ≤ L) (W : ℝ) (hW : 0 < W)
    (h : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ) (hh : ∀ t, NullMeasurable (h t) volume) (y₀ : ℝ) :
    ∃ f : ℝ → ℝ, (∀ L' > L, ∃ a : ℝ, ∀ x x', |f x - f x'| ≤ L' * (|x - x'| + a)) ∧
      ∃ w : ℕ → ℝ, (∀ t, |w t| ≤ W) ∧
      ∃ y u : ℕ → ℝ, y 0 = y₀ ∧ (∀ t, u t = h t (fun i => y i)) ∧
        (∀ t, y (t + 1) = f (y t) + u t + w (t + 1)) ∧
        ¬ BddAbove (range fun t => |y t|)

end MathlibExt.Analysis.Control.FeedbackCapabilityWanted
