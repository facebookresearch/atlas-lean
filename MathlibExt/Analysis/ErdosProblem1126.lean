/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1126
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

@[expose] public section

open Filter MeasureTheory

namespace MathlibExt.Analysis.ErdosProblem1126Wanted

/-! Source record `FC-ErdosProblem1126`, ported from FormalConjectures
`ErdosProblems/1126.lean` (`theorem erdos_1126`) and checked against
erdosproblems.com/1126. The `answer(True)` wrapper is dropped. Status:
resolved true (de Bruijn; Jurkat). -/

/-- **Erdős Problem 1126 on almost additive functions.** This is the statement that for every
function $f : \mathbb{R} \to \mathbb{R}$ with $f(x + y) = f(x) + f(y)$ for almost every
$(x, y) \in \mathbb{R}^2$ with respect to Lebesgue measure on $\mathbb{R}^2$, there is a function
$h : \mathbb{R} \to \mathbb{R}$ with $h(x + y) = h(x) + h(y)$ for all $x, y \in \mathbb{R}$ and
$f(x) = h(x)$ for almost every $x \in \mathbb{R}$.

Source: erdosproblems.com/1126 (record FC-ErdosProblem1126). -/
def conjecture : Prop :=
  ∀ (f : ℝ → ℝ),
    (∀ᵐ (p : ℝ × ℝ) ∂(MeasureTheory.volume.prod MeasureTheory.volume),
      f (p.1 + p.2) = f p.1 + f p.2) →
    ∃ h : ℝ → ℝ,
      (∀ x y, h (x + y) = h x + h y) ∧ (∀ᵐ x ∂MeasureTheory.volume, f x = h x)

/--
**Almost additive functions agree almost everywhere with additive functions.** Let
$f : \mathbb{R} \to \mathbb{R}$ satisfy $f(x + y) = f(x) + f(y)$ for almost every
$(x, y) \in \mathbb{R}^2$ with respect to Lebesgue measure on $\mathbb{R}^2$. Then there is a
function $h : \mathbb{R} \to \mathbb{R}$ with $h(x + y) = h(x) + h(y)$ for all
$x, y \in \mathbb{R}$ and $f(x) = h(x)$ for almost every $x \in \mathbb{R}$.

Source: de Bruijn [dB66] and Jurkat [Ju65], independently, per
erdosproblems.com/1126, https://www.erdosproblems.com/1126. Moved from
`OpenConjectures/Analysis/ErdosProblem1126`.
-/
theorem conjecture_holds : conjecture := by
  intro f hf
  have translate (c : ℝ) {p : ℝ → Prop} (hp : ∀ᵐ x ∂volume, p x) :
      ∀ᵐ x ∂volume, p (c + x) :=
    (measurePreserving_add_left volume c).quasiMeasurePreserving.ae hp
  let inc (x c : ℝ) : Prop := ∀ᵐ t ∂volume, f (x + t) = c + f t
  have hgood : ∀ᵐ x ∂volume, inc x (f x) := Measure.ae_ae_of_ae_prod hf
  -- Two good sections at `u` and `x + u` determine the increment at any offset `x`.
  have hex (x : ℝ) : ∃ c, inc x c := by
    obtain ⟨u, hu, hxu⟩ := (hgood.and (translate x hgood)).exists
    refine ⟨f (x + u) - f u, ?_⟩
    change ∀ᵐ t ∂volume, f (x + t) = f (x + u) - f u + f t
    change ∀ᵐ t ∂volume, f (u + t) = f u + f t at hu
    change ∀ᵐ t ∂volume, f (x + u + t) = f (x + u) + f t at hxu
    filter_upwards [translate (-u) hu, translate (-u) hxu] with t ht ht'
    rw [show u + (-u + t) = t by abel] at ht
    rw [show x + u + (-u + t) = x + t by abel] at ht'
    linarith
  have h_unique {x a b : ℝ} (ha : inc x a) (hb : inc x b) : a = b := by
    obtain ⟨t, ht, ht'⟩ := (ha.and hb).exists
    change f (x + t) = a + f t at ht
    change f (x + t) = b + f t at ht'
    linarith
  -- Uniqueness makes these increments additive and identifies them with `f` a.e.
  choose h hh using hex
  refine ⟨h, ?_, hgood.mono (fun x hx => h_unique hx (hh x))⟩
  intro x y
  apply h_unique (hh (x + y))
  have hx : ∀ᵐ t ∂volume, f (x + t) = h x + f t := hh x
  have hy : ∀ᵐ t ∂volume, f (y + t) = h y + f t := hh y
  change ∀ᵐ t ∂volume, f (x + y + t) = h x + h y + f t
  filter_upwards [translate y hx, hy] with t hxt hyt
  rw [add_assoc, hxt, hyt, add_assoc]

end MathlibExt.Analysis.ErdosProblem1126Wanted
