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

/-- **Normalized Ihara ratio.** For a sequence $N : \mathbb{N} \to \mathbb{N}$ and
$g \in \mathbb{N}$, the normalized ratio of $N$ at $g$ is the extended nonnegative real $N(g)/g$
when $g > 0$, and $0$ when $g = 0$. -/
noncomputable def iharaRatio (N : ℕ → ℕ) (g : ℕ) : ENNReal :=
  if g = 0 then 0 else (N g : ENNReal) / (g : ENNReal)

/-- **Abstract Ihara constant of a sequence.** For a sequence $N : \mathbb{N} \to \mathbb{N}$,
the abstract Ihara constant of $N$ is $\limsup_{g \to \infty} N(g)/g \in [0, \infty]$, the limit
superior as $g \to \infty$ of the normalized ratios of $N$. -/
noncomputable def iharaConstantOf (N : ℕ → ℕ) : ENNReal :=
  Filter.limsup (iharaRatio N) atTop

@[simp]
theorem iharaRatio_zero (N : ℕ → ℕ) : iharaRatio N 0 = 0 := rfl

theorem iharaRatio_of_pos (N : ℕ → ℕ) {g : ℕ} (hg : 0 < g) :
    iharaRatio N g = (N g : ENNReal) / (g : ENNReal) := by
  rw [iharaRatio, ite_eq_right hg.ne']

/-- **Eventual ratio bounds bound the abstract Ihara constant.** Let
$N : \mathbb{N} \to \mathbb{N}$ and $c \in [0, \infty]$. If the normalized ratio of $N$ at $g$ is
at most $c$ for all sufficiently large $g$, then the abstract Ihara constant of $N$ is at most
$c$. -/
theorem iharaConstantOf_le_of_eventually_ratio_le (N : ℕ → ℕ) {c : ENNReal}
    (h : ∀ᶠ g in atTop, iharaRatio N g ≤ c) :
    iharaConstantOf N ≤ c :=
  Filter.limsup_le_of_le (h := h)

/-- **Lower bound for the Ihara constant from the normalized ratios.** Let
$N : \mathbb{N} \to \mathbb{N}$, let $c \in [0, \infty]$, and for each $g \in \mathbb{N}$ let
$r_N(g) \in [0, \infty]$ be the normalized ratio $N(g)/g$, with $r_N(0) = 0$. If $c \le r_N(g)$
for infinitely many $g$, then $c \le \limsup_{g \to \infty} r_N(g)$, the Ihara constant of $N$. -/
theorem le_iharaConstantOf_of_frequently_ratio_le (N : ℕ → ℕ) {c : ENNReal}
    (h : ∃ᶠ g in atTop, c ≤ iharaRatio N g) :
    c ≤ iharaConstantOf N :=
  Filter.le_limsup_of_frequently_le h

/-- **Linear upper bound on a normalized ratio.** Let $N : \mathbb{N} \to \mathbb{N}$,
$g \in \mathbb{N}$ and $c \in [0, \infty]$. If $N(g) \le c \cdot g$ in $[0, \infty]$, then the
normalized ratio of $N$ at $g$ is at most $c$. -/
theorem iharaRatio_le_of_le_mul (N : ℕ → ℕ) {c : ENNReal} {g : ℕ}
    (h : (N g : ENNReal) ≤ c * (g : ENNReal)) :
    iharaRatio N g ≤ c := by
  by_cases hg : g = 0
  · simp [iharaRatio, hg]
  · rw [iharaRatio, ite_eq_right hg]
    exact ENNReal.div_le_of_le_mul h

/-- **Lower bound for one normalized Ihara ratio.** Let $N : \mathbb{N} \to \mathbb{N}$,
$c \in [0, \infty]$ and $g > 0$ an integer. If $c \cdot g \le N(g)$ in $[0, \infty]$, then
$c \le N(g)/g$, where the normalized ratio $N(g)/g$ is taken in $[0, \infty]$. -/
theorem le_iharaRatio_of_mul_le (N : ℕ → ℕ) {c : ENNReal} {g : ℕ}
    (hg : 0 < g) (h : c * (g : ENNReal) ≤ (N g : ENNReal)) :
    c ≤ iharaRatio N g := by
  have hg0 : (g : ENNReal) ≠ 0 := by
    exact_mod_cast hg.ne'
  rw [iharaRatio_of_pos N hg]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hg0)
    (Or.inl (ENNReal.natCast_ne_top g))).2 h

/-- **Eventual linear upper bound on the abstract Ihara constant.** Let
$N : \mathbb{N} \to \mathbb{N}$ and $c \in [0, \infty]$. If $N(g) \le c \cdot g$ in $[0, \infty]$
for all sufficiently large $g$, then the abstract Ihara constant of $N$ is at most $c$. -/
theorem iharaConstantOf_le_of_eventually_le (N : ℕ → ℕ) {c : ENNReal}
    (h : ∀ᶠ g in atTop, (N g : ENNReal) ≤ c * (g : ENNReal)) :
    iharaConstantOf N ≤ c :=
  iharaConstantOf_le_of_eventually_ratio_le N
    (h.mono fun _g hg => iharaRatio_le_of_le_mul N hg)

/-- **Eventual affine upper bound on the abstract Ihara constant.** Let
$N : \mathbb{N} \to \mathbb{N}$, $c \in [0, \infty]$ and $d \in [0, \infty)$. If
$N(g) \le c \cdot g + d$ in $[0, \infty]$ for all sufficiently large $g$, then the abstract Ihara
constant of $N$ is at most $c$. -/
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

/-- **Lower bound for the Ihara constant from a linear bound.** Let $N : \mathbb{N} \to \mathbb{N}$
and $c \in [0, \infty]$. If there are infinitely many integers $g > 0$ with $c \cdot g \le N(g)$
in $[0, \infty]$, then $c \le \limsup_{g \to \infty} N(g)/g$, the Ihara constant of $N$, where the
ratio $N(g)/g$ is taken in $[0, \infty]$ and set to $0$ at $g = 0$. -/
theorem le_iharaConstantOf_of_frequently_le (N : ℕ → ℕ) {c : ENNReal}
    (h : ∃ᶠ g : ℕ in atTop, 0 < g ∧ c * (g : ENNReal) ≤ (N g : ENNReal)) :
    c ≤ iharaConstantOf N :=
  le_iharaConstantOf_of_frequently_ratio_le N
    (h.mono fun _g hg => le_iharaRatio_of_mul_le N hg.1 hg.2)

/-- **Monotonicity of the normalized ratio.** Let $N, M : \mathbb{N} \to \mathbb{N}$ and
$g \in \mathbb{N}$. If $N(g) \le M(g)$, then the normalized ratio of $N$ at $g$ is at most the
normalized ratio of $M$ at $g$. -/
theorem iharaRatio_mono {N M : ℕ → ℕ} {g : ℕ} (h : N g ≤ M g) :
    iharaRatio N g ≤ iharaRatio M g := by
  by_cases hg : g = 0
  · simp [iharaRatio, hg]
  · rw [iharaRatio, iharaRatio, ite_eq_right hg, ite_eq_right hg]
    exact ENNReal.div_le_div_right (by exact_mod_cast h) _

/-- **Monotonicity of the abstract Ihara constant.** Let $N, M : \mathbb{N} \to \mathbb{N}$. If
$N(g) \le M(g)$ for all sufficiently large $g$, then the abstract Ihara constant of $N$ is at
most that of $M$. -/
theorem iharaConstantOf_mono_of_eventually_le {N M : ℕ → ℕ}
    (h : ∀ᶠ g in atTop, N g ≤ M g) :
    iharaConstantOf N ≤ iharaConstantOf M :=
  Filter.limsup_le_limsup (h.mono fun g hg => iharaRatio_mono hg)

/-- **The abstract Ihara constant ignores finitely many values.** Let
$N, M : \mathbb{N} \to \mathbb{N}$. If $N(g) = M(g)$ for all sufficiently large $g$, then $N$ and
$M$ have the same abstract Ihara constant. In particular, changing finitely many values of $N$
does not change its abstract Ihara constant. -/
theorem iharaConstantOf_congr {N M : ℕ → ℕ} (h : N =ᶠ[atTop] M) :
    iharaConstantOf N = iharaConstantOf M :=
  Filter.limsup_congr (h.mono fun g hg => by simp [iharaRatio, hg])

/-- **Agreement from an index onward preserves the abstract Ihara constant.** Let
$N, M : \mathbb{N} \to \mathbb{N}$ and $G \in \mathbb{N}$. If $N(g) = M(g)$ for every $g \ge G$,
then $N$ and $M$ have the same abstract Ihara constant. -/
theorem iharaConstantOf_eq_of_eventually_eq {N M : ℕ → ℕ} {G : ℕ}
    (h : ∀ g ≥ G, N g = M g) :
    iharaConstantOf N = iharaConstantOf M :=
  iharaConstantOf_congr (Filter.eventually_atTop.2 ⟨G, h⟩)

end MathlibExt.Analysis
