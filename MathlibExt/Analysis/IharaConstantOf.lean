/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abstract Ihara-type limsup constants
-/
module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Order.LiminfLimsup

@[expose] public section

open Filter
open scoped ENNReal

namespace MathlibExt.Analysis

/-!
# Abstract Ihara-type limsup constants

For an arbitrary sequence `N : ℕ → ℕ`, `iharaConstantOf N` is the extended
nonnegative real limsup of the ratios `N g / g`.

This is deliberately only the numerical layer used by the Ihara constant.
It does not identify `N` with a maximum number of rational points on curves
of genus `g`; that geometric input remains a separate formalization step.
Using `ENNReal` makes an unbounded ratio sequence — the normalized ratios
`N g / g` themselves unbounded — have value `⊤` rather than a junk finite
value. Unboundedness of `N` alone does not suffice: the identity sequence is
unbounded but has `iharaConstantOf N = 1`, since its ratios are `0` at
`g = 0` and `1` at every positive genus.
-/

/-- The normalized ratio `N g / g`, with the value at `g = 0` set to `0`. -/
noncomputable def iharaRatio (N : ℕ → ℕ) (g : ℕ) : ENNReal :=
  if g = 0 then 0 else (N g : ENNReal) / (g : ENNReal)

/-- The limsup of the normalized ratios associated with `N`. -/
noncomputable def iharaConstantOf (N : ℕ → ℕ) : ENNReal :=
  Filter.limsup (iharaRatio N) atTop

@[simp]
theorem iharaRatio_zero (N : ℕ → ℕ) : iharaRatio N 0 = 0 := rfl

theorem iharaRatio_of_pos (N : ℕ → ℕ) {g : ℕ} (hg : 0 < g) :
    iharaRatio N g = (N g : ENNReal) / (g : ENNReal) := by
  rw [iharaRatio, ite_eq_right hg.ne']

/-- An eventual bound on the normalized ratios bounds their limsup. -/
theorem iharaConstantOf_le_of_eventually_ratio_le (N : ℕ → ℕ) {c : ENNReal}
    (h : ∀ᶠ g in atTop, iharaRatio N g ≤ c) :
    iharaConstantOf N ≤ c :=
  Filter.limsup_le_of_le (h := h)

/-- A frequently attained lower bound on the ratios bounds the limsup below. -/
theorem le_iharaConstantOf_of_frequently_ratio_le (N : ℕ → ℕ) {c : ENNReal}
    (h : ∃ᶠ g in atTop, c ≤ iharaRatio N g) :
    c ≤ iharaConstantOf N :=
  Filter.le_limsup_of_frequently_le h

/-- A pointwise multiplicative upper bound controls one normalized ratio. -/
theorem iharaRatio_le_of_le_mul (N : ℕ → ℕ) {c : ENNReal} {g : ℕ}
    (h : (N g : ENNReal) ≤ c * (g : ENNReal)) :
    iharaRatio N g ≤ c := by
  by_cases hg : g = 0
  · simp [iharaRatio, hg]
  · rw [iharaRatio, ite_eq_right hg]
    exact ENNReal.div_le_of_le_mul h

/-- A pointwise multiplicative lower bound controls one normalized ratio. -/
theorem le_iharaRatio_of_mul_le (N : ℕ → ℕ) {c : ENNReal} {g : ℕ}
    (hg : 0 < g) (h : c * (g : ENNReal) ≤ (N g : ENNReal)) :
    c ≤ iharaRatio N g := by
  have hg0 : (g : ENNReal) ≠ 0 := by
    exact_mod_cast hg.ne'
  rw [iharaRatio_of_pos N hg]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hg0)
    (Or.inl (ENNReal.natCast_ne_top g))).2 h

/-- An eventual linear upper bound gives the corresponding limsup bound. -/
theorem iharaConstantOf_le_of_eventually_le (N : ℕ → ℕ) {c : ENNReal}
    (h : ∀ᶠ g in atTop, (N g : ENNReal) ≤ c * (g : ENNReal)) :
    iharaConstantOf N ≤ c :=
  iharaConstantOf_le_of_eventually_ratio_le N
    (h.mono fun _g hg => iharaRatio_le_of_le_mul N hg)

/-- An eventual affine upper bound `N g ≤ c * g + d`, with finite additive
error `d`, gives the corresponding limsup bound. -/
theorem iharaConstantOf_le_of_eventually_le_add (N : ℕ → ℕ) {c d : ENNReal}
    (hd : d ≠ ⊤)
    (h : ∀ᶠ g : ℕ in atTop, (N g : ENNReal) ≤ c * (g : ENNReal) + d) :
    iharaConstantOf N ≤ c := by
  rcases eq_or_ne c ⊤ with rfl | _hc
  · exact le_top
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hcTop
  apply iharaConstantOf_le_of_eventually_le
  have hε0 : (ε : ENNReal) ≠ 0 := by
    exact_mod_cast hε.ne'
  have hεTop : (ε : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  obtain ⟨G, hG⟩ := ENNReal.exists_nat_gt
    (ENNReal.div_ne_top hd hε0)
  have hdle : ∀ᶠ g : ℕ in atTop, d ≤ (ε : ENNReal) * (g : ENNReal) := by
    refine Filter.eventually_atTop.2 ⟨G, fun g hg => ?_⟩
    have hdg : d / (ε : ENNReal) ≤ (g : ENNReal) :=
      hG.le.trans (by exact_mod_cast hg)
    calc
      d = (ε : ENNReal) * (d / (ε : ENNReal)) :=
        (ENNReal.mul_div_cancel hε0 hεTop).symm
      _ ≤ (ε : ENNReal) * (g : ENNReal) := by
        exact mul_le_mul_right hdg _
  filter_upwards [h, hdle] with g hg hdg
  calc
    (N g : ENNReal) ≤ c * (g : ENNReal) + d := hg
    _ ≤ c * (g : ENNReal) + (ε : ENNReal) * (g : ENNReal) :=
      add_le_add_right hdg _
    _ = (c + (ε : ENNReal)) * (g : ENNReal) := by rw [add_mul]

/-- A frequently attained linear lower bound gives a limsup lower bound. -/
theorem le_iharaConstantOf_of_frequently_le (N : ℕ → ℕ) {c : ENNReal}
    (h : ∃ᶠ g : ℕ in atTop, 0 < g ∧ c * (g : ENNReal) ≤ (N g : ENNReal)) :
    c ≤ iharaConstantOf N :=
  le_iharaConstantOf_of_frequently_ratio_le N
    (h.mono fun _g hg => le_iharaRatio_of_mul_le N hg.1 hg.2)

/-- The normalized ratio is monotone in the underlying counting sequence. -/
theorem iharaRatio_mono {N M : ℕ → ℕ} {g : ℕ} (h : N g ≤ M g) :
    iharaRatio N g ≤ iharaRatio M g := by
  by_cases hg : g = 0
  · simp [iharaRatio, hg]
  · rw [iharaRatio, iharaRatio, ite_eq_right hg, ite_eq_right hg]
    exact ENNReal.div_le_div_right (by exact_mod_cast h) _

/-- The abstract Ihara constant is monotone under eventual domination. -/
theorem iharaConstantOf_mono_of_eventually_le {N M : ℕ → ℕ}
    (h : ∀ᶠ g in atTop, N g ≤ M g) :
    iharaConstantOf N ≤ iharaConstantOf M :=
  Filter.limsup_le_limsup (h.mono fun g hg => iharaRatio_mono hg)

/-- Changing finitely many values of `N` does not change the limsup. -/
theorem iharaConstantOf_congr {N M : ℕ → ℕ} (h : N =ᶠ[atTop] M) :
    iharaConstantOf N = iharaConstantOf M :=
  Filter.limsup_congr (h.mono fun g hg => by simp [iharaRatio, hg])

/-- Agreement from some index onward determines the abstract constant. -/
theorem iharaConstantOf_eq_of_eventually_eq {N M : ℕ → ℕ} {G : ℕ}
    (h : ∀ g ≥ G, N g = M g) :
    iharaConstantOf N = iharaConstantOf M :=
  iharaConstantOf_congr (Filter.eventually_atTop.2 ⟨G, h⟩)

end MathlibExt.Analysis
