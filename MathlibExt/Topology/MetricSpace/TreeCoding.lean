/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Topology.MetricSpace.GromovHyperbolic

/-!
# Real trees coded by continuous functions

A continuous function `g : ℝ → ℝ` codes a tree: with `m_g(s, t) = min_{r ∈ [s ∧ t, s ∨ t]} g r`,

`d_g(s, t) = g s + g t - 2 m_g(s, t)`

is a pseudometric on `ℝ`, and identifying the points at distance `0` gives the real tree `T_g`
coded by `g`. This is the continuous analogue of the coding of a plane tree by its contour (Dyck)
path, and it is how Aldous's continuum random tree is built from the Brownian excursion and how
Le Gall's random-geometry programme (the Brownian snake, the Brownian map) starts.

This file proves that `d_g` is a pseudometric for every continuous `g`, that it is
`0`-hyperbolic in Gromov's sense (the four-point condition satisfied by every real tree), and that
`g ↦ d_g` is `4`-Lipschitz for the uniform norm, the estimate behind the bound
`d_GH(T_g, T_h) ≤ 2 ‖g - h‖_∞` that transfers invariance principles from coding functions to
trees.

## Main definitions

* `MathlibExt.TreeCoding.treeMin g s t`: the minimum of `g` between `s` and `t`.
* `MathlibExt.TreeCoding.treeDist g s t`: the coded tree distance `g s + g t - 2 treeMin g s t`.
* `MathlibExt.TreeCoding.CodedTree g`: `ℝ` with the pseudometric `treeDist g`
  (for `g` continuous, given as a `Fact`).

## Main results

* `MathlibExt.TreeCoding.treeMin_of_le_of_le`: `m_g(a, c) = min (m_g(a, b)) (m_g(b, c))` for
  `a ≤ b ≤ c`.
* `MathlibExt.TreeCoding.treeDist_triangle`: the triangle inequality.
* `MathlibExt.TreeCoding.treeMin_four_point`: the four-point inequality for `m_g`.
* `MathlibExt.TreeCoding.isDeltaHyperbolic_zero`: the coded tree is `0`-hyperbolic.
* `MathlibExt.TreeCoding.abs_treeDist_sub_le`: `|d_g - d_h| ≤ 4 ε` when `|g - h| ≤ ε`.

## References

* J.-F. Le Gall, *Random trees and applications*, Probability Surveys 2 (2005), 245–311,
  Section 2.2 (Theorem 2.2: `(T_g, d_g)` is a real tree; Lemma 2.4 and its proof:
  `d_GH(T_g, T_{g'}) ≤ 2 ‖g - g'‖`).
* J.-F. Le Gall, *Brownian geometry*, Japanese Journal of Mathematics 14 (2019), Section 3.1.
-/

@[expose] public section

open Set

namespace MathlibExt.TreeCoding

/-- **Minimum of a function between two times.** The minimum of `g` on the interval between `s`
and `t`, `m_g(s, t) = inf g([s ∧ t, s ∨ t])`;
for continuous `g` the infimum is attained (Le Gall, *Random trees and applications*,
Section 2.2). -/
noncomputable def treeMin (g : ℝ → ℝ) (s t : ℝ) : ℝ := sInf (g '' uIcc s t)

/-- **Distance coded by a function.** For `g : ℝ → ℝ`,
`d_g(s, t) = g s + g t - 2 m_g(s, t)`, where `m_g(s, t)` is the minimum of `g` between `s` and
`t`. For continuous `g` this is the pseudometric of the real tree coded by `g` (Le Gall, *Random
trees and applications*, Section 2.2). -/
noncomputable def treeDist (g : ℝ → ℝ) (s t : ℝ) : ℝ := g s + g t - 2 * treeMin g s t

variable {g : ℝ → ℝ}

/-- **Symmetry of the minimum.** `m_g` is symmetric: the interval between `s` and `t` does not
depend on their order. -/
lemma treeMin_comm (g : ℝ → ℝ) (s t : ℝ) : treeMin g s t = treeMin g t s := by
  simp [treeMin, uIcc_comm]

/-- **Symmetry of the coded distance.** `d_g` is symmetric (Le Gall, *Random trees and
applications*, Section 2.2). -/
lemma treeDist_comm (g : ℝ → ℝ) (s t : ℝ) : treeDist g s t = treeDist g t s := by
  simp only [treeDist, treeMin_comm g s t]
  ring

private lemma bddBelow_image (hg : Continuous g) (s t : ℝ) : BddBelow (g '' uIcc s t) :=
  (isCompact_uIcc.image hg).bddBelow

private lemma image_nonempty (s t : ℝ) : (g '' uIcc s t).Nonempty :=
  nonempty_uIcc.image g

/-- **The minimum is a lower bound.** The minimum lies below every value of `g` between `s` and
`t`. -/
lemma treeMin_le (hg : Continuous g) {s t x : ℝ} (hx : x ∈ uIcc s t) : treeMin g s t ≤ g x :=
  csInf_le (bddBelow_image hg s t) ⟨x, hx, rfl⟩

/-- **The minimum is the greatest lower bound.** A lower bound for `g` between `s` and `t` bounds
the minimum. -/
lemma le_treeMin {s t c : ℝ} (h : ∀ x ∈ uIcc s t, c ≤ g x) : c ≤ treeMin g s t :=
  le_csInf (image_nonempty s t) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

/-- **The minimum lies below the left endpoint value.** `m_g(s, t) ≤ g s`. -/
lemma treeMin_le_left (hg : Continuous g) (s t : ℝ) : treeMin g s t ≤ g s :=
  treeMin_le hg left_mem_uIcc

/-- **The minimum lies below the right endpoint value.** `m_g(s, t) ≤ g t`. -/
lemma treeMin_le_right (hg : Continuous g) (s t : ℝ) : treeMin g s t ≤ g t :=
  treeMin_le hg right_mem_uIcc

/-- **Minimum over a single point.** `m_g(s, s) = g s`. -/
lemma treeMin_self (hg : Continuous g) (s : ℝ) : treeMin g s s = g s :=
  le_antisymm (treeMin_le_left hg s s) (le_treeMin fun x hx ↦ by simp_all)

/-- **Monotonicity of the minimum.** A larger interval has a smaller minimum. -/
lemma treeMin_anti (hg : Continuous g) {s t s' t' : ℝ} (h : uIcc s' t' ⊆ uIcc s t) :
    treeMin g s t ≤ treeMin g s' t' :=
  le_treeMin fun _ hx ↦ treeMin_le hg (h hx)

/-- **Splitting the minimum.** For `a ≤ b ≤ c`, `m_g(a, c) = min (m_g(a, b)) (m_g(b, c))`. -/
lemma treeMin_of_le_of_le (hg : Continuous g) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    treeMin g a c = min (treeMin g a b) (treeMin g b c) := by
  refine le_antisymm (le_min (treeMin_anti hg ?_) (treeMin_anti hg ?_)) (le_treeMin ?_)
  · rw [uIcc_of_le hab, uIcc_of_le (hab.trans hbc)]
    exact Icc_subset_Icc_right hbc
  · rw [uIcc_of_le hbc, uIcc_of_le (hab.trans hbc)]
    exact Icc_subset_Icc_left hab
  · intro x hx
    rw [uIcc_of_le (hab.trans hbc)] at hx
    rcases le_total x b with hxb | hxb
    · exact (min_le_left _ _).trans (treeMin_le hg (by rw [uIcc_of_le hab]; exact ⟨hx.1, hxb⟩))
    · exact (min_le_right _ _).trans (treeMin_le hg (by rw [uIcc_of_le hbc]; exact ⟨hxb, hx.2⟩))

/-- **The coded distance is nonnegative.** `d_g` is nonnegative, because
`m_g(s, t) ≤ min (g s) (g t)` (Le Gall, *Random trees and applications*, Section 2.2). -/
lemma treeDist_nonneg (hg : Continuous g) (s t : ℝ) : 0 ≤ treeDist g s t := by
  have := treeMin_le_left hg s t
  have := treeMin_le_right hg s t
  simp only [treeDist]
  linarith

/-- **The coded distance vanishes on the diagonal.** `d_g(s, s) = 0`. -/
lemma treeDist_self (hg : Continuous g) (s : ℝ) : treeDist g s s = 0 := by
  simp only [treeDist, treeMin_self hg]
  ring

/-- **Triangle inequality for the coded distance.** For `d_g`,
`m_g(s, t) + m_g(t, u) ≤ g t + m_g(s, u)` because the larger of the two minima is at most `g t`
and the smaller is at most `m_g(s, u)`, as `[s, u] ⊆ [s, t] ∪ [t, u]`. -/
lemma treeDist_triangle (hg : Continuous g) (s t u : ℝ) :
    treeDist g s u ≤ treeDist g s t + treeDist g t u := by
  have hmin : min (treeMin g s t) (treeMin g t u) ≤ treeMin g s u :=
    le_treeMin fun x hx ↦ by
      rcases uIcc_subset_uIcc_union_uIcc hx with hx | hx
      · exact (min_le_left _ _).trans (treeMin_le hg hx)
      · exact (min_le_right _ _).trans (treeMin_le hg hx)
  have hmax : max (treeMin g s t) (treeMin g t u) ≤ g t :=
    max_le (treeMin_le_right hg s t) (treeMin_le_left hg t u)
  have := min_add_max (treeMin g s t) (treeMin g t u)
  simp only [treeDist]
  linarith

/-- **Ultrametric inequality for the minimum.** `min (m_g(a, b)) (m_g(b, c)) ≤ m_g(a, c)`, since
`[a, c] ⊆ [a, b] ∪ [b, c]`. -/
lemma min_treeMin_le (hg : Continuous g) (a b c : ℝ) :
    min (treeMin g a b) (treeMin g b c) ≤ treeMin g a c :=
  le_treeMin fun x hx ↦ by
    rcases uIcc_subset_uIcc_union_uIcc hx with hx | hx
    · exact (min_le_left _ _).trans (treeMin_le hg hx)
    · exact (min_le_right _ _).trans (treeMin_le hg hx)

/-- The real-number core of the four-point inequality: four ultrametric bounds on the diagonals
`X, Y` of a quadrilateral with sides `A, B, C, D` give `min (A + C) (B + D) ≤ X + Y`. -/
private lemma min_add_le_of_ultra {A B C D X Y : ℝ} (h1 : min A B ≤ X) (h2 : min D C ≤ X)
    (h3 : min A D ≤ Y) (h4 : min B C ≤ Y) : min (A + C) (B + D) ≤ X + Y := by
  simp only [min_def] at *
  split_ifs at * <;> linarith

/-- **Four-point inequality for the minimum.** For the minimum function `m_g`, for all `x, y, z, w`,
`min (m_g(x, y) + m_g(z, w)) (m_g(y, z) + m_g(x, w)) ≤ m_g(x, z) + m_g(y, w)`. With
`d_g = g + g - 2 m_g`, this is the four-point condition satisfied by the distance of a real tree
(Le Gall, *Random trees and applications*, Theorem 2.2). -/
lemma treeMin_four_point (hg : Continuous g) (x y z w : ℝ) :
    min (treeMin g x y + treeMin g z w) (treeMin g y z + treeMin g x w) ≤
      treeMin g x z + treeMin g y w := by
  have h1 := min_treeMin_le hg x y z
  have h2 := min_treeMin_le hg x w z
  have h3 := min_treeMin_le hg y x w
  have h4 := min_treeMin_le hg y z w
  rw [treeMin_comm g w z] at h2
  rw [treeMin_comm g y x] at h3
  rw [treeMin_comm g x w] at h2 h3 ⊢
  exact min_add_le_of_ultra h1 h2 h3 h4

/-- **The tree coded by a function.** `ℝ` equipped with the pseudometric `d_g` coded by `g`; its
metric quotient is the real tree `T_g` coded by `g` (Le Gall, *Random trees and applications*,
Section 2.2). -/
def CodedTree (_g : ℝ → ℝ) : Type := ℝ

/-- For continuous `g`, `d_g` is a pseudometric on `ℝ`. -/
noncomputable instance (g : ℝ → ℝ) [hg : Fact (Continuous g)] :
    PseudoMetricSpace (CodedTree g) where
  dist s t := treeDist g s t
  dist_self s := treeDist_self hg.out s
  dist_comm s t := treeDist_comm g s t
  dist_triangle s t u := treeDist_triangle hg.out s t u

/-- **Distance in the coded tree.** The distance of the coded tree is `d_g`. -/
lemma CodedTree.dist_eq (g : ℝ → ℝ) [Fact (Continuous g)] (s t : CodedTree g) :
    dist s t = treeDist g s t := rfl

/-- **The tree coded by a continuous function is `0`-hyperbolic.** For continuous `g`, the
pseudometric space `(ℝ, d_g)` satisfies Gromov's four-point condition with constant `0`:
`(x ∣ z)_w ≥ min ((x ∣ y)_w) ((y ∣ z)_w)` for all points, as every real tree does. Le Gall,
*Random trees and applications*, Theorem 2.2, shows that the quotient `(T_g, d_g)` is a real tree;
`0`-hyperbolicity is the metric half of that statement. -/
theorem isDeltaHyperbolic_zero (g : ℝ → ℝ) [hg : Fact (Continuous g)] :
    Metric.IsDeltaHyperbolic (CodedTree g) 0 := by
  refine ⟨le_rfl, fun w x y z ↦ ?_⟩
  simp only [Metric.gromovProduct_eq, CodedTree.dist_eq, treeDist, sub_zero]
  have h := treeMin_four_point hg.out x y z w
  have e1 := treeMin_comm g w x
  have e2 := treeMin_comm g w y
  have e3 := treeMin_comm g w z
  simp only [min_def] at h ⊢
  split_ifs at h ⊢ <;> linarith

/-- **Uniform continuity of the minimum in the coding function.** If `|g - h| ≤ ε` everywhere, then
`|m_g(s, t) - m_h(s, t)| ≤ ε` for all `s, t`. -/
lemma abs_treeMin_sub_le {h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) {ε : ℝ}
    (hε : ∀ x, |g x - h x| ≤ ε) (s t : ℝ) : |treeMin g s t - treeMin h s t| ≤ ε := by
  rw [abs_le]
  constructor
  · have : treeMin h s t - ε ≤ treeMin g s t := le_treeMin fun x hx ↦ by
      have := treeMin_le hh hx
      have := (abs_le.1 (hε x)).1
      linarith
    linarith
  · have : treeMin g s t - ε ≤ treeMin h s t := le_treeMin fun x hx ↦ by
      have := treeMin_le hg hx
      have := (abs_le.1 (hε x)).2
      linarith
    linarith

/-- **The coding is `4`-Lipschitz for the uniform norm.** If `g, h` are continuous and
`|g - h| ≤ ε` everywhere, then `|d_g(s, t) - d_h(s, t)| ≤ 4 ε` for all `s, t`. This is the
estimate in the proof of Le Gall, *Random trees and applications*, Lemma 2.4: the correspondence
`{(p_g(t), p_h(t))}` between `T_g` and `T_h` then has distortion at most `4 ‖g - h‖`, whence
`d_GH(T_g, T_h) ≤ 2 ‖g - h‖`. -/
theorem abs_treeDist_sub_le {h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) {ε : ℝ}
    (hε : ∀ x, |g x - h x| ≤ ε) (s t : ℝ) : |treeDist g s t - treeDist h s t| ≤ 4 * ε := by
  have h1 := abs_le.1 (hε s)
  have h2 := abs_le.1 (hε t)
  have h3 := abs_le.1 (abs_treeMin_sub_le hg hh hε s t)
  rw [abs_le]
  simp only [treeDist]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end MathlibExt.TreeCoding
