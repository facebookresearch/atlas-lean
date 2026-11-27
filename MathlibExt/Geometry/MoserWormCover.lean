/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Unit planar arcs and Moser universal covers

Continuous unit-length planar arcs, direct rigid motions, actual-area families and
finite area infima for convex and unrestricted universal covers.

Source: Optimization Problems, constant 13a; Panraksa and Wichiramala,
Wetzel's sector covers unit arcs (2021); Fässler and Orponen,
Curve packing and modulus estimates (2018).

The geometric definitions and proved support laws retain the original
`MoserConvexWormCoverConstant` namespace. Literature bounds and missing proofs
are specified in the separate opt-in wishlist library.
-/

@[expose] public section

open MeasureTheory Set

namespace MoserConvexWormCoverConstant

/-- **Parameter interval of unit arcs.** Planar arcs are parametrized by the closed unit interval
$[0, 1]$ of real numbers.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
abbrev ArcParameter := Set.Icc (0 : ℝ) 1

/-- **Unit arc.** A unit arc is a continuous map $\gamma$ from the closed interval $[0, 1]$ to
the complex plane whose length, the total variation of $\gamma$ on $[0, 1]$, equals $1$.

Source: Optimization
Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc adaptation.
-/
structure UnitArc where
  path : C(ArcParameter, ℂ)
  length_eq_one : eVariationOn path Set.univ = 1

/-- **Direct rigid motion of the plane.** For a real angle $\theta$ and a complex number
$\tau$, the motion with angle $\theta$ and translation $\tau$ sends $z \in \mathbb{C}$ to
$e^{i\theta} z + \tau$: a rotation about the origin by $\theta$ followed by translation by
$\tau$, with neither reflection nor rescaling.

Source:
Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc adaptation.
-/
noncomputable def move (angle : ℝ) (translation z : ℂ) : ℂ :=
  Complex.exp (angle * Complex.I) * z + translation

/-- **Direct rigid motions of the plane are isometries.** For every real angle $\theta$ and every
complex number $\tau$, the map $z \mapsto e^{i\theta} z + \tau$ of the complex plane is an
isometry: it preserves the distance $|z - w|$ between any two points $z, w \in \mathbb{C}$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem move_isometry (angle : ℝ) (translation : ℂ) : Isometry (move angle translation) := by
  apply Isometry.of_dist_eq
  intro z w
  simp [move, dist_eq_norm, ← mul_sub]

/-- **Straight path.** The straight path is the continuous map from the interval $[0, 1]$ to
the complex plane that sends each $t \in [0, 1]$ to $t$ viewed as a complex number; it traces
the segment from $0$ to $1$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def straightPath : C(ArcParameter, ℂ) :=
  ⟨fun t => (t.1 : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

/-- **The identity on the unit interval has total variation one.** The total variation of the
inclusion $[0, 1] \to \mathbb{R}$, $t \mapsto t$, over the whole interval $[0, 1]$ equals $1$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem parameter_variation :
    eVariationOn (Subtype.val : ArcParameter → ℝ) Set.univ = 1 := by
  have himage : (Subtype.val : ArcParameter → ℝ) '' Set.univ = Set.Icc 0 1 := by
    ext x
    constructor
    · rintro ⟨t, _, rfl⟩
      exact t.2
    · intro hx
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  have h := eVariationOn.comp_eq_of_monotoneOn (id : ℝ → ℝ) (t := Set.univ)
    (Subtype.val : ArcParameter → ℝ) (fun _ _ _ _ h => h)
  simpa [Function.comp_def, himage, eVariationOn_id_Icc] using h

/-- **The straight segment has length one.** The path $[0, 1] \to \mathbb{C}$, $t \mapsto t$,
which traces the segment from $0$ to $1$ on the real axis, has total variation (length) exactly
$1$ over $[0, 1]$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem straightPath_length : eVariationOn straightPath Set.univ = 1 := by
  apply le_antisymm
  · have h := Complex.isometry_ofReal.lipschitzWith.lipschitzOnWith.comp_eVariationOn_le
      (g := (Subtype.val : ArcParameter → ℝ)) (s := Set.univ) (t := Set.univ)
      (fun _ _ => Set.mem_univ _)
    simpa [Function.comp_def, straightPath, parameter_variation] using h
  · let a : ArcParameter := ⟨0, by constructor <;> norm_num⟩
    let b : ArcParameter := ⟨1, by constructor <;> norm_num⟩
    have h := eVariationOn.edist_le straightPath (s := Set.univ) (x := a) (y := b)
      (Set.mem_univ _) (Set.mem_univ _)
    simpa [a, b, straightPath, edist_dist, Complex.dist_eq] using h

/-- **Straight unit arc.** The straight unit arc is the unit arc whose curve is the straight
path $t \mapsto t$ from $[0, 1]$ to the complex plane, which traces the segment from $0$ to $1$
and has length $1$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def straightUnitArc : UnitArc := ⟨straightPath, straightPath_length⟩

/-- The straight unit arc witnesses nonemptiness of the curve domain.
Source: Optimization Problems, constant 13a (frozen 2c1968cd); interval-arc adaptation.
-/
instance : Nonempty UnitArc := ⟨straightUnitArc⟩

/-- **Sets that cover every unit arc.** A set $\Omega \subseteq \mathbb{C}$ covers every
unit arc when for every unit arc $\gamma : [0, 1] \to \mathbb{C}$, that is, every continuous map
whose total variation (length) is exactly $1$, there are an angle $\theta \in \mathbb{R}$ and a
translation $\tau \in \mathbb{C}$ such that $e^{i\theta} \gamma(t) + \tau \in \Omega$ for every
$t \in [0, 1]$.

Only rotations followed by translations are allowed; reflections and rescalings are not.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def CoversEveryUnitArc (Ω : Set ℂ) : Prop :=
  ∀ arc : UnitArc, ∃ angle : ℝ, ∃ translation : ℂ,
    ∀ t : ArcParameter, move angle translation (arc.path t) ∈ Ω

/-- **Sets covering every unit arc are nonempty.** If a set $\Omega \subseteq \mathbb{C}$
covers every unit arc, that is, contains a rotated and translated copy of every continuous curve
$[0, 1] \to \mathbb{C}$ of length exactly one, then $\Omega$ is nonempty.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem CoversEveryUnitArc.nonempty {Ω : Set ℂ} (h : CoversEveryUnitArc Ω) : Ω.Nonempty := by
  obtain ⟨angle, translation, h⟩ := h straightUnitArc
  let t : ArcParameter := ⟨0, by constructor <;> norm_num⟩
  exact ⟨_, h t⟩

/-- **The empty set does not cover every unit arc.** The empty set
$\emptyset \subseteq \mathbb{C}$ does not cover every unit arc: not every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be mapped into $\emptyset$ by a
rotation followed by a translation.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem empty_not_covers : ¬ CoversEveryUnitArc (∅ : Set ℂ) := by
  intro h
  exact Set.not_nonempty_empty h.nonempty

/-- **Convex universal covers.** A set $\Omega \subseteq \mathbb{C}$ is a convex universal cover
when it is nonempty, convex (as a subset of the real plane $\mathbb{C} \cong \mathbb{R}^2$), and
covers every unit arc: for every continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length
exactly $1$ there are $\theta \in \mathbb{R}$ and $\tau \in \mathbb{C}$ with
$e^{i\theta} \gamma(t) + \tau \in \Omega$ for all $t \in [0, 1]$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def IsConvexUniversalCover (Ω : Set ℂ) : Prop :=
  Ω.Nonempty ∧ Convex ℝ Ω ∧ CoversEveryUnitArc Ω

/-- **Universal covers.** A set $\Omega \subseteq \mathbb{C}$ is a universal cover when it is
nonempty and covers every unit arc: for every continuous curve $\gamma : [0, 1] \to \mathbb{C}$
of length exactly $1$ there are $\theta \in \mathbb{R}$ and $\tau \in \mathbb{C}$ with
$e^{i\theta} \gamma(t) + \tau \in \Omega$ for all $t \in [0, 1]$. Neither convexity nor
measurability of $\Omega$ is required.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def IsUniversalCover (Ω : Set ℂ) : Prop :=
  Ω.Nonempty ∧ CoversEveryUnitArc Ω

/-- **Convex universal covers are null-measurable.** If $\Omega \subseteq \mathbb{C}$ is a
convex universal cover of unit arcs, then $\Omega$ is a null-measurable set for Lebesgue measure
on $\mathbb{C}$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem IsConvexUniversalCover.nullMeasurableSet {Ω : Set ℂ}
    (h : IsConvexUniversalCover Ω) : NullMeasurableSet Ω volume :=
  h.2.1.nullMeasurableSet volume

/-- **Convex universal covers are universal covers.** Every convex universal cover
$\Omega \subseteq \mathbb{C}$ is a universal cover.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem IsConvexUniversalCover.isUniversalCover {Ω : Set ℂ}
    (h : IsConvexUniversalCover Ω) : IsUniversalCover Ω :=
  ⟨h.1, h.2.2⟩

/-- **Areas of convex universal covers.** The set of convex cover areas is the set of all values
$\operatorname{vol}(\Omega) \in [0, \infty]$, where $\Omega \subseteq \mathbb{C}$ ranges over the
convex universal covers and $\operatorname{vol}$ is Lebesgue measure on
$\mathbb{C} \cong \mathbb{R}^2$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def convexCoverAreas : Set ENNReal :=
  {a | ∃ Ω : Set ℂ, IsConvexUniversalCover Ω ∧ volume Ω = a}

/-- **Areas of universal covers.** The set of values $\lambda(\Omega) \in [0, \infty]$, where
$\Omega \subseteq \mathbb{C}$ ranges over the universal covers and $\lambda$ is Lebesgue measure on
$\mathbb{C} \cong \mathbb{R}^2$, applied as an outer measure since $\Omega$ need not be
measurable.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def coverAreas : Set ENNReal :=
  {a | ∃ Ω : Set ℂ, IsUniversalCover Ω ∧ volume Ω = a}

/-- **Infimal area of convex universal covers.** The convex cover area infimum is the infimum in
$[0, \infty]$ of the set of convex cover areas, that is, the infimum of the Lebesgue areas of all
convex universal covers $\Omega \subseteq \mathbb{C}$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def convexCoverAreaInfimum : ENNReal := sInf convexCoverAreas

/-- **Infimal area of a universal cover.** The infimum in $[0, \infty]$ of the areas
$\lambda(\Omega)$ of the universal covers $\Omega \subseteq \mathbb{C}$, where $\lambda$ is
Lebesgue measure on $\mathbb{C} \cong \mathbb{R}^2$, applied as an outer measure since $\Omega$
need not be measurable.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def coverAreaInfimum : ENNReal := sInf coverAreas

/-- **The closed unit disk covers every unit arc.** For every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ there are an angle $\theta \in \mathbb{R}$
and a translation $c \in \mathbb{C}$ such that $|e^{i\theta}\gamma(t) + c| \le 1$ for every
$t \in [0, 1]$; that is, the closed disk of radius $1$ centred at $0$ covers every unit arc.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem closedBall_one_covers : CoversEveryUnitArc (Metric.closedBall (0 : ℂ) 1) := by
  intro arc
  let start : ArcParameter := ⟨0, by constructor <;> norm_num⟩
  refine ⟨0, -arc.path start, ?_⟩
  intro t
  have h := eVariationOn.edist_le arc.path (s := Set.univ) (x := t) (y := start)
    (Set.mem_univ _) (Set.mem_univ _)
  rw [arc.length_eq_one] at h
  have hd := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) h
  have hd' : dist (arc.path t) (arc.path start) ≤ 1 := by
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_one] using hd
  simpa [Metric.mem_closedBall, move, Complex.dist_eq, sub_eq_add_neg] using hd'

/-- **The closed unit disk is a convex universal cover.** The closed disk
$\{z \in \mathbb{C} : |z| \le 1\}$ is a convex universal cover: it is nonempty, convex, and covers
every unit arc.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem closedBall_one_isConvexUniversalCover :
    IsConvexUniversalCover (Metric.closedBall (0 : ℂ) 1) := by
  refine ⟨⟨0, by simp⟩, convex_closedBall _ _, closedBall_one_covers⟩

/-- **The set of convex cover areas is nonempty.** The set of convex cover areas, the Lebesgue
areas of all convex universal covers in $\mathbb{C}$, is nonempty; that is, some convex universal
cover exists.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem convexCoverAreas_nonempty : convexCoverAreas.Nonempty :=
  ⟨volume (Metric.closedBall (0 : ℂ) 1), _, closedBall_one_isConvexUniversalCover, rfl⟩

/-- **The set of universal cover areas is nonempty.** The set of values
$\lambda(\Omega) \in [0, \infty]$, where $\Omega \subseteq \mathbb{C}$ ranges over the universal
covers and $\lambda$ is Lebesgue outer measure on $\mathbb{C} \cong \mathbb{R}^2$, is nonempty.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem coverAreas_nonempty : coverAreas.Nonempty :=
  ⟨volume (Metric.closedBall (0 : ℂ) 1), _,
    closedBall_one_isConvexUniversalCover.isUniversalCover, rfl⟩

/-- **The infimal area of convex universal covers is finite.** The convex cover area infimum, the
infimum in $[0, \infty]$ of the Lebesgue areas of all convex universal covers in $\mathbb{C}$, is
not $\infty$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem convexCoverAreaInfimum_ne_top : convexCoverAreaInfimum ≠ ⊤ := by
  have h : convexCoverAreaInfimum ≤ volume (Metric.closedBall (0 : ℂ) 1) :=
    sInf_le ⟨_, closedBall_one_isConvexUniversalCover, rfl⟩
  exact ne_top_of_le_ne_top (by simp [Complex.volume_closedBall]) h

/-- **The infimal area of universal covers is finite.** The cover area infimum, the infimum in
$[0, \infty]$ of the Lebesgue areas of all universal covers in $\mathbb{C}$ (nonempty sets that
cover every unit arc, not necessarily convex), is not $\infty$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem coverAreaInfimum_ne_top : coverAreaInfimum ≠ ⊤ := by
  have h : coverAreaInfimum ≤ volume (Metric.closedBall (0 : ℂ) 1) :=
    sInf_le ⟨_, closedBall_one_isConvexUniversalCover.isUniversalCover, rfl⟩
  exact ne_top_of_le_ne_top (by simp [Complex.volume_closedBall]) h

/-- **Moser's convex worm cover constant.** The convex worm cover constant is the real number
obtained from the convex cover area infimum, the infimum in $[0, \infty]$ of the Lebesgue areas of
all convex universal covers in $\mathbb{C}$, by the conversion $[0, \infty] \to \mathbb{R}$ that
is the identity on finite values and sends $\infty$ to $0$.

That infimum is finite, so the constant equals the infimal area itself.

Source:
Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc adaptation.
-/
noncomputable def convexWormCoverConstant : ℝ := convexCoverAreaInfimum.toReal

/-- **Nonconvex worm cover constant.** The nonconvex worm cover constant is the real number
obtained from the cover area infimum, the infimum in $[0, \infty]$ of the Lebesgue outer measures
of all universal covers of unit arcs (nonempty sets $\Omega \subseteq \mathbb{C}$ containing a
rotated and translated copy of every continuous curve of length one), by converting it to a
real number. The conversion would send $\infty$ to $0$, but this infimum is finite.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def nonconvexWormCoverConstant : ℝ := coverAreaInfimum.toReal

/-- **The convex worm cover constant is nonnegative.** The convex worm cover constant is at
least $0$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem convexWormCoverConstant_nonneg : 0 ≤ convexWormCoverConstant :=
  ENNReal.toReal_nonneg

/-- **Nonnegativity of the nonconvex worm cover constant.** The nonconvex worm cover constant
is greater than or equal to $0$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem nonconvexWormCoverConstant_nonneg : 0 ≤ nonconvexWormCoverConstant :=
  ENNReal.toReal_nonneg

/-- **The nonconvex worm cover constant is at most the convex one.** The nonconvex worm cover
constant (the infimal area of universal covers of unit arcs) is less than or equal to the convex
worm cover constant (the infimal area of convex universal covers of unit arcs).

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem nonconvex_le_convex : nonconvexWormCoverConstant ≤ convexWormCoverConstant := by
  apply (ENNReal.toReal_le_toReal coverAreaInfimum_ne_top convexCoverAreaInfimum_ne_top).2
  apply le_sInf
  rintro a ⟨Ω, hΩ, rfl⟩
  exact sInf_le ⟨Ω, hΩ.isUniversalCover, rfl⟩

/-- **Disk of radius one half.** The closed disk $\{z \in \mathbb{C} : |z| \le 1/2\}$ of
radius $1/2$ centred at $0$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def halfDisk : Set ℂ :=
  {z | ‖z‖ ≤ (1 : ℝ) / 2}

/-- **Semidisk of radius one half.** The closed upper half-disk
$\{z \in \mathbb{C} : |z| \le 1/2,\ \operatorname{Im} z \ge 0\}$ of radius $1/2$ centred at $0$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def halfSemidisk : Set ℂ :=
  {z | ‖z‖ ≤ (1 : ℝ) / 2 ∧ 0 ≤ z.im}

/-- **Wetzel's sector.** This is the closed circular sector of radius $1$ and opening angle
$30^\circ$ with apex at the origin, placed symmetrically about the positive real axis: the set
of complex numbers $z$ with $|z| \le 1$, $\operatorname{Re} z \ge 0$ and
$|\operatorname{Im} z| \le \tan(\pi/12) \operatorname{Re} z$.

Source: Optimization
Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc adaptation.
-/
noncomputable def wetzelSector : Set ℂ :=
  {z | ‖z‖ ≤ 1 ∧ 0 ≤ z.re ∧ |z.im| ≤ Real.tan (Real.pi / 12) * z.re}

/-- **Covers give upper bounds on the nonconvex worm cover constant.** Let $r \ge 0$ be a real
number. If some set $\Omega \subseteq \mathbb{C}$ is a universal cover of unit arcs whose
Lebesgue outer measure is at most $r$, then the nonconvex worm cover constant is at most $r$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem nonconvexUpperBound_of_cover {r : ℝ} (hr : 0 ≤ r)
    (h : ∃ Ω : Set ℂ, IsUniversalCover Ω ∧ volume Ω ≤ ENNReal.ofReal r) :
    nonconvexWormCoverConstant ≤ r := by
  rcases h with ⟨Ω, hΩ, harea⟩
  have hi : coverAreaInfimum ≤ ENNReal.ofReal r :=
    (sInf_le (s := coverAreas) ⟨Ω, hΩ, rfl⟩).trans harea
  have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal r ≠ ⊤) hi
  simpa [nonconvexWormCoverConstant, ENNReal.toReal_ofReal hr] using hreal

end MoserConvexWormCoverConstant
