/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.MoserWormCover
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The half-disk of diameter one covers every unit arc

`halfSemidiskCovers_holds` places a unit arc in the closed upper half-disk of radius one half.
Rotate the endpoint chord to be horizontal and put a lowest point on the real axis. Center the
endpoints horizontally, so reflecting one endpoint across the real axis gives the negative of the
other. The broken path through a test point and the lowest point bounds the sum of distances
from the test point to a pair of opposite points, and hence bounds twice its norm.
-/

@[expose] public section

open Set ComplexConjugate

namespace MoserConvexWormCoverConstant

/-- **The half-disk of diameter one covers every unit arc (claim).** This proposition asserts
that the closed half-disk $H = \{z \in \mathbb{C} : |z| \le 1/2,\ \operatorname{Im} z \ge 0\}$
covers every unit arc: for every continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length
exactly $1$ there are an angle $\theta \in \mathbb{R}$ and a translation $c \in \mathbb{C}$ such
that $e^{i\theta}\gamma(t) + c \in H$ for every $t \in [0, 1]$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def halfSemidiskCovers : Prop := CoversEveryUnitArc halfSemidisk

/-- The polygonal path along the arc through two ordered parameters has length at most one. -/
private theorem three_chords_le_one (arc : UnitArc) {s t : ArcParameter} (hst : s ≤ t) :
    dist (arc.path 0) (arc.path s) + dist (arc.path s) (arc.path t) +
      dist (arc.path t) (arc.path 1) ≤ 1 := by
  let u : ℕ → ArcParameter
    | 0 => 0
    | 1 => s
    | 2 => t
    | _ => 1
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    rintro (_ | _ | _ | i)
    exacts [s.2.1, hst, t.2.2, le_rfl]
  have h := eVariationOn.sum_le (f := arc.path) (n := 3) hu (fun i => mem_univ (u i))
  rw [arc.length_eq_one] at h
  simpa [Finset.sum_range_succ, u, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
    ← ENNReal.ofReal_add (add_nonneg dist_nonneg dist_nonneg) dist_nonneg,
    ENNReal.ofReal_le_one, dist_comm] using h

/-- Reflect the last chord across the real axis at the point of contact `p`. -/
private theorem norm_le_of_reflected_chords {a z p b : ℂ} (hp : conj p = p)
    (hb : conj b = -a) (hlen : dist a z + dist z p + dist p b ≤ 1) : ‖z‖ ≤ 1 / 2 := by
  have htri := dist_triangle z p (-a)
  have hd : dist p (-a) = dist p b := by rw [← hb, ← Complex.dist_conj_comm p b, hp]
  rw [hd] at htri
  have hmid := dist_midpoint_midpoint_le z z a (-a)
  rw [midpoint_self, midpoint_self_neg, dist_zero_right, dist_comm z a] at hmid
  linarith

/-- **The half-disk of diameter one covers every unit arc.** Let
$H = \{z \in \mathbb{C} : |z| \le 1/2,\ \operatorname{Im} z \ge 0\}$. For every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ there are an angle $\theta \in \mathbb{R}$
and a translation $c \in \mathbb{C}$ such that $e^{i\theta}\gamma(t) + c \in H$ for every
$t \in [0, 1]$.

Source: Optimization Problems, constant 13a, closed claim `halfSemidiskCovers`. -/
theorem halfSemidiskCovers_holds : halfSemidiskCovers := by
  intro arc
  let chord := arc.path 1 - arc.path 0
  let angle := -chord.arg
  let rot := Complex.exp ((angle : ℂ) * Complex.I)
  let q (t : ArcParameter) := rot * arc.path t
  have hchord : rot * chord = (‖chord‖ : ℂ) := by
    dsimp only [rot, angle]
    rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg]
    apply (inv_mul_eq_iff_eq_mul₀ (Complex.exp_ne_zero _)).2
    rw [mul_comm, Complex.norm_mul_exp_arg_mul_I]
  have hend : (q 1).im = (q 0).im := by
    have h : q 1 - q 0 = (‖chord‖ : ℂ) := by
      simpa only [q, chord, mul_sub] using hchord
    simpa [sub_eq_zero] using congrArg Complex.im h
  have hc : Continuous (fun t => (q t).im) :=
    Complex.continuous_im.comp (continuous_const.mul arc.path.continuous)
  obtain ⟨s, _, hs⟩ := isCompact_univ.exists_isMinOn univ_nonempty hc.continuousOn
  let c : ℂ := ⟨-((q 0).re + (q 1).re) / 2, -(q s).im⟩
  let f (t : ArcParameter) := q t + c
  have hsreal : conj (f s) = f s := Complex.conj_eq_iff_im.mpr (by simp [f, c])
  have hreflect : conj (f 1) = -f 0 := by
    apply Complex.ext <;> simp [f, c, hend] <;> ring
  have hlen {u v : ArcParameter} (huv : u ≤ v) :
      dist (f 0) (f u) + dist (f u) (f v) + dist (f v) (f 1) ≤ 1 := by
    have hd (x y : ArcParameter) : dist (f x) (f y) = dist (arc.path x) (arc.path y) :=
      (move_isometry angle c).dist_eq _ _
    simpa only [hd] using three_chords_le_one arc huv
  refine ⟨angle, c, fun t => ?_⟩
  change ‖f t‖ ≤ 1 / 2 ∧ 0 ≤ (f t).im
  refine ⟨?_, by simpa [f, c, sub_eq_add_neg] using sub_nonneg.mpr (hs (mem_univ t))⟩
  rcases le_total t s with h | h
  · exact norm_le_of_reflected_chords hsreal hreflect (hlen h)
  · have hreverse : conj (f 0) = -f 1 := by
      calc
        conj (f 0) = conj (-conj (f 1)) := by rw [hreflect, neg_neg]
        _ = -f 1 := by simp
    apply norm_le_of_reflected_chords hsreal hreverse
    linarith only [hlen h, dist_comm (f 1) (f t), dist_comm (f t) (f s), dist_comm (f s) (f 0)]

end MoserConvexWormCoverConstant
