/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.MoserWormCover

/-!
# The disk of diameter one covers every unit arc

A unit arc is a continuous curve `γ : [0, 1] → ℂ` of length (total variation) exactly `1`. This
module proves that the closed disk `halfDisk` of radius `1/2` centred at `0` covers every unit
arc: a rotation followed by a translation moves each unit arc into it. The radius `1/2` cannot be
lowered, because the endpoints of the straight unit arc are at distance `1`.

## Main statements

* `MoserConvexWormCoverConstant.halfDiskCovers`: the claim that `halfDisk` covers every unit arc.
* `MoserConvexWormCoverConstant.halfDiskCovers_holds`: the claim holds.

## Proof

Let `A = γ 0` and `B = γ 1` be the endpoints of the arc and `M` their midpoint. For every
parameter `t`, the total variation of `γ` on `[0, 1]` is at least its variation on `[0, t]` plus
its variation on `[t, 1]`, so `dist A (γ t) + dist (γ t) B ≤ 1`. Hence
`dist (γ t) M ≤ (dist (γ t) A + dist (γ t) B) / 2 ≤ 1/2`, and the rotation by the angle `0`
followed by the translation by `-M` moves the arc into `halfDisk`.
-/

@[expose] public section

open Set

namespace MoserConvexWormCoverConstant

/-- **The disk of diameter one covers every unit arc (claim).** This proposition asserts that
the closed disk $D = \{z \in \mathbb{C} : |z| \le 1/2\}$ covers every unit arc: for every
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ there are an angle
$\theta \in \mathbb{R}$ and a translation $c \in \mathbb{C}$ such that
$e^{i\theta}\gamma(t) + c \in D$ for every $t \in [0, 1]$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def halfDiskCovers : Prop := CoversEveryUnitArc halfDisk

/-- For parameters `a ≤ t ≤ b` of a unit arc, the distances from `γ a` to `γ t` and from `γ t`
to `γ b` add up to at most the length `1` of the arc. -/
private theorem edist_add_edist_le_one (arc : UnitArc) {a t b : ArcParameter} (hat : a ≤ t)
    (htb : t ≤ b) : edist (arc.path a) (arc.path t) + edist (arc.path t) (arc.path b) ≤ 1 := by
  calc edist (arc.path a) (arc.path t) + edist (arc.path t) (arc.path b)
      ≤ eVariationOn arc.path (Iic t) + eVariationOn arc.path (Ici t) :=
        add_le_add (eVariationOn.edist_le _ (mem_Iic.2 hat) self_mem_Iic)
          (eVariationOn.edist_le _ self_mem_Ici (mem_Ici.2 htb))
    _ ≤ eVariationOn arc.path (Iic t ∪ Ici t) :=
        eVariationOn.add_le_union _ fun _ hx _ hy => le_trans hx hy
    _ ≤ eVariationOn arc.path univ := eVariationOn.mono _ (subset_univ _)
    _ = 1 := arc.length_eq_one

/-- **The disk of diameter one covers every unit arc.** For every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ there are an angle $\theta \in \mathbb{R}$
and a translation $c \in \mathbb{C}$ such that $|e^{i\theta}\gamma(t) + c| \le 1/2$ for every
$t \in [0, 1]$.

Source: Optimization Problems, constant 13a, closed claim `halfDiskCovers`. -/
theorem halfDiskCovers_holds : halfDiskCovers := by
  intro arc
  refine ⟨0, -midpoint ℝ (arc.path 0) (arc.path 1), fun t => ?_⟩
  have hsum := edist_add_edist_le_one arc (a := 0) (b := 1) t.2.1 t.2.2
  rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
    ENNReal.ofReal_le_one] at hsum
  have hmid := dist_midpoint_midpoint_le (arc.path t) (arc.path t) (arc.path 0) (arc.path 1)
  rw [midpoint_self] at hmid
  change ‖move 0 _ (arc.path t)‖ ≤ (1 : ℝ) / 2
  rw [move, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, ← sub_eq_add_neg,
    ← dist_eq_norm]
  linarith [dist_comm (arc.path 0) (arc.path t)]

end MoserConvexWormCoverConstant
