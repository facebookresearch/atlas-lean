/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Algebra.Module.ZLattice.Basic

@[expose] public section

open Filter MeasureTheory

namespace MathlibExt.Geometry.SpherePackingDensityFourWanted

/-!
# Sphere-packing density in four dimensions

Source: optimizationproblems `constants/36a.md`, frozen catalogue SHA256
`5be76ae842abb1b5154ab2fd538c4c5c4cebd91ee72b0fc009bd6ba99fd9b89b`;
H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of
Mathematics 157 (2003), 689--714, arXiv:math/0110009, Appendix A and Table 3;
D. de Laat, F. M. de Oliveira Filho and F. Vallentin, *Upper bounds for packings
of spheres of several radii*, Forum of Mathematics, Sigma 2 (2014),
DOI 10.1017/fms.2014.24, arXiv:1206.2608, Section 1.4 and Table 1.

The observation-center supremum is taken before the radius limsup. The region
is the union of closed congruent balls; disjoint open interiors allow tangency.
Positive observation radii exclude a zero-volume denominator. `ENNReal` is
the complete-lattice measure codomain; the proved bound by one makes the
optimized value finite. No optimum-attainment assertion is made.

The three displayed upper decimals and the displayed lower decimal are
approximations to the exact converted expressions, not extra exact bounds.
The primary tables call their center-density numbers bounds. Their numerical
certificates have not been replayed here. The four deep bound statements and
periodic approximation are `theorem_wanted` goals, not proofs or axioms.
The catalogue states no open exact-value conjecture, so this is a WantedExt
entry, not an OpenConjectures entry.
-/

noncomputable section

/-- **Four-dimensional Euclidean space.** The ambient space is $\mathbb{R}^4$, the space of real
$4$-tuples with the standard Euclidean inner product and the distance it induces.

Source: CE2003, the ambient Euclidean space `ℝ⁴`. -/
abbrev Space := EuclideanSpace ℝ (Fin 4)

/-- **Positive radii.** A positive radius is a real number $R$ with $R > 0$; the positive radii
form the set $\{R \in \mathbb{R} : R > 0\}$.

Source: CE2003 Appendix A, positive observation radii tending to infinity. -/
abbrev PositiveRadius := {R : ℝ // 0 < R}

/-- **Packings of congruent balls in $\mathbb{R}^4$.** A packing in $\mathbb{R}^4$ consists of a
real radius $r > 0$ and a set $C \subseteq \mathbb{R}^4$ of centres such that for any two distinct
centres $c, c' \in C$ the open balls of radius $r$ about $c$ and $c'$ are disjoint.

Source: CE2003 introduction, congruent positive-radius balls with disjoint interiors. -/
structure Packing where
  radius : ℝ
  radius_pos : 0 < radius
  centers : Set Space
  interior_disjoint : centers.PairwiseDisjoint (fun c => Metric.ball c radius)

/-- **Packed ball.** For a packing $P$ in $\mathbb{R}^4$ with radius $r$ and a point
$c \in \mathbb{R}^4$, the packed ball of $P$ at $c$ is the closed ball
$\{x \in \mathbb{R}^4 : \|x - c\| \le r\}$, boundary included.

Source: CE2003, the packed closed ball at a center, including its boundary. -/
def packedBall (P : Packing) (c : Space) : Set Space := Metric.closedBall c P.radius

/-- **Region covered by a packing.** For a packing $P$ in $\mathbb{R}^4$ with radius $r$ and set
of centres $C$, the region covered by $P$ is the union, over all centres $c \in C$, of the packed
closed balls $\{x \in \mathbb{R}^4 : \|x - c\| \le r\}$.

Source: CE2003 Appendix A, the union `P` of all packed balls. -/
def packingRegion (P : Packing) : Set Space := ⋃ c ∈ P.centers, packedBall P c

/-- **Density of a packing in a ball.** For a packing $P$ of congruent balls in $\mathbb{R}^4$, a
point $p \in \mathbb{R}^4$ and a radius $R > 0$, the density of $P$ in the open ball $B(p, R)$ of
radius $R$ about $p$ is $\operatorname{vol}(U \cap B(p, R)) / \operatorname{vol}(B(p, R))$, where
$U$ is the union of the closed balls of $P$ and $\operatorname{vol}$ is Lebesgue measure; the
quotient is taken in $[0, \infty]$.

Source: CE2003 Appendix A, `vol(P ∩ B(p,R)) / vol(B(p,R))`. -/
def finiteRadiusDensity (P : Packing) (p : Space) (R : PositiveRadius) : ENNReal :=
  volume (packingRegion P ∩ Metric.ball p (R : ℝ)) / volume (Metric.ball p (R : ℝ))

/-- **Density of a packing at a fixed radius.** For a packing $P$ of congruent balls in
$\mathbb{R}^4$ and a radius $R > 0$, the density of $P$ at radius $R$ is the supremum, over all
centers $p \in \mathbb{R}^4$, of the density of $P$ in the open ball of radius $R$ about $p$;
it is a value in $[0, \infty]$.

Source: CE2003 Appendix A, supremum over all observation centers at fixed radius. -/
def centeredRadiusDensity (P : Packing) (R : PositiveRadius) : ENNReal :=
  ⨆ p : Space, finiteRadiusDensity P p R

/-- **Upper density of a packing.** For a packing $P$ of congruent balls in $\mathbb{R}^4$, let
$U_P$ be the union of the closed balls of the packing, and for $p \in \mathbb{R}^4$ and $R > 0$ let
$B(p, R)$ be the open ball of radius $R$ about $p$. The upper density of $P$ is the extended
nonnegative real number

$$\limsup_{R \to \infty} \sup_{p \in \mathbb{R}^4}
\frac{\operatorname{vol}(U_P \cap B(p, R))}{\operatorname{vol}(B(p, R))},$$

where $\operatorname{vol}$ is Lebesgue measure and the limit superior is taken as the positive
radius $R$ tends to infinity.

Source: CE2003 Appendix A, limsup as positive radii tend to infinity. -/
def upperDensity (P : Packing) : ENNReal :=
  Filter.limsup (centeredRadiusDensity P) Filter.atTop

/-- **Sphere-packing density of $\mathbb{R}^4$.** The sphere-packing density
$\Delta_4 \in [0, \infty]$ is the supremum, over all packings $P$ of congruent balls in
$\mathbb{R}^4$, of the upper density of $P$. Here the upper density of $P$ is the limit superior,
as the real radius $R > 0$ tends to infinity, of the supremum over all points
$p \in \mathbb{R}^4$ of the ratio of the volume of the part of the open ball $B(p, R)$ covered
by $P$ to the volume of $B(p, R)$.

Source: catalogue C36, supremum over all congruent-ball packings in `ℝ⁴`. -/
def spherePackingDensity4 : ENNReal := ⨆ P : Packing, upperDensity P

/-- **Volume of the unit ball in $\mathbb{R}^4$.** The volume of the unit ball in $\mathbb{R}^4$ is
the Lebesgue measure, as an extended nonnegative real number, of the open ball of radius $1$ about
the origin in four-dimensional Euclidean space $\mathbb{R}^4$.

Source: dLOV2014 Section 1.4, volume of a unit ball in `ℝ⁴`. -/
def unitBallVolume4 : ENNReal := volume (Metric.ball (0 : Space) 1)

/-- **Center density in four dimensions.** The center density of sphere packings in
$\mathbb{R}^4$ is $\delta_4 = \Delta_4 / \operatorname{vol}(B)$, where $\Delta_4$ is the
sphere-packing density of $\mathbb{R}^4$ and $B$ is the open unit ball of $\mathbb{R}^4$ centered
at the origin; the quotient is taken in $[0, \infty]$.

Source: dLOV2014 Section 1.4, `δ₄ = Δ₄ / vol(B)` for unit spheres. -/
def centerDensity4 : ENNReal := spherePackingDensity4 / unitBallVolume4

/-- **Periodic packings.** A packing $P$ of congruent balls in $\mathbb{R}^4$ is periodic if there
are a basis $b_1, b_2, b_3, b_4$ of $\mathbb{R}^4$ and a finite set $F \subseteq \mathbb{R}^4$ such
that the set of centers of $P$ equals $\{c + w : c \in F, w \in \Lambda\}$, where $\Lambda$ is the
set of integer linear combinations of $b_1, b_2, b_3, b_4$.

Source: CE2003 introduction, finite union of translates of a full-rank lattice.
The lattice is the integer span of a real basis, not an arbitrary periodicity oracle. -/
def Packing.IsPeriodic (P : Packing) : Prop :=
  ∃ (b : Module.Basis (Fin 4) ℝ Space) (offsets : Finset Space),
    P.centers = ⋃ c ∈ offsets,
      (fun w : Space => c + w) '' (Submodule.span ℤ (Set.range b) : Set Space)

/-- **Trivial upper bound for the sphere-packing density of $\mathbb{R}^4$.** The trivial upper
bound is the statement that the sphere-packing density of $\mathbb{R}^4$ is at most $1$.

Source: catalogue C36, trivial upper-bound row. -/
def upperBound_trivial : Prop := spherePackingDensity4 ≤ 1

/-- **The trivial lower bound for the four-dimensional packing density.** This is the statement
that the sphere-packing density $\Delta_4$ of $\mathbb{R}^4$ satisfies $0 \le \Delta_4$.

Source: catalogue C36, trivial nonnegative lower-bound row. -/
def lowerBound_trivial : Prop := 0 ≤ spherePackingDensity4

/-- **A packing has countably many centers.** For every packing of congruent balls in
$\mathbb{R}^4$, the set of centers of its balls is countable.

Source: packing admission conditions;
disjoint nonempty open balls have countably many centers. -/
theorem centers_countable (P : Packing) : P.centers.Countable :=
  P.interior_disjoint.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    (fun _ _ => Metric.nonempty_ball.mpr P.radius_pos)

/-- **The region covered by a packing is measurable.** For every packing $P$ in $\mathbb{R}^4$,
the region covered by $P$, the union of its packed closed balls, is a Borel set; in
particular it is Lebesgue measurable.

Source: the covered region is Lebesgue measurable, without an extra packing restriction. -/
theorem packingRegion_measurable (P : Packing) : MeasurableSet (packingRegion P) :=
  MeasurableSet.biUnion (centers_countable P) (fun _ _ => measurableSet_closedBall)

/-- **Balls of positive radius in $\mathbb{R}^4$ have nonzero volume.** For every point
$p \in \mathbb{R}^4$ and every real $R > 0$, the open ball of radius $R$ centred at $p$ has nonzero
Lebesgue measure.

Source: positive observation radii give nonzero volume denominators. -/
theorem observationVolume_ne_zero (p : Space) (R : PositiveRadius) :
    volume (Metric.ball p (R : ℝ)) ≠ 0 :=
  ne_of_gt (Metric.measure_ball_pos volume p R.property)

/-- **Balls of positive radius in $\mathbb{R}^4$ have finite volume.** For every point
$p \in \mathbb{R}^4$ and every real $R > 0$, the open ball of radius $R$ centred at $p$ has finite
Lebesgue measure.

Source: every finite-radius observation ball has finite volume. -/
theorem observationVolume_ne_top (p : Space) (R : PositiveRadius) :
    volume (Metric.ball p (R : ℝ)) ≠ ⊤ := measure_ball_ne_top

/-- **The density in a ball is at most one.** For every packing $P$ of congruent balls in
$\mathbb{R}^4$, every point $p \in \mathbb{R}^4$ and every radius $R > 0$, the density of $P$ in
the open ball of radius $R$ about $p$ is at most $1$.

Source: a covered-volume fraction cannot exceed one. -/
theorem finiteRadiusDensity_le_one (P : Packing) (p : Space) (R : PositiveRadius) :
    finiteRadiusDensity P p R ≤ 1 := by
  rw [finiteRadiusDensity, ENNReal.div_le_iff (observationVolume_ne_zero p R)
    (observationVolume_ne_top p R), one_mul]
  exact measure_mono Set.inter_subset_right

/-- **The density at a fixed radius is at most one.** For every packing $P$ of congruent balls
in $\mathbb{R}^4$ and every radius $R > 0$, the density of $P$ at radius $R$ (the supremum over
all centers $p \in \mathbb{R}^4$ of the density of $P$ in the open ball of radius $R$ about $p$)
is at most $1$.

Source: taking the observation-center supremum preserves the bound by one. -/
theorem centeredRadiusDensity_le_one (P : Packing) (R : PositiveRadius) :
    centeredRadiusDensity P R ≤ 1 :=
  iSup_le (fun p => finiteRadiusDensity_le_one P p R)

/-- **The upper density of a packing is at most one.** For every packing $P$ of congruent balls in
$\mathbb{R}^4$, the upper density of $P$ is at most $1$.

Source: taking the radius limsup preserves the bound by one. -/
theorem upperDensity_le_one (P : Packing) : upperDensity P ≤ 1 := by
  exact Filter.limsup_le_of_le (h := Filter.Eventually.of_forall (centeredRadiusDensity_le_one P))

/-- **The sphere-packing density of $\mathbb{R}^4$ is at most one.** The trivial upper bound holds:
the sphere-packing density of $\mathbb{R}^4$ is at most $1$.

Source: catalogue C36 trivial upper bound, proved for the actual optimized constant. -/
theorem upperBound_trivial_proved : upperBound_trivial := iSup_le upperDensity_le_one

/-- **The four-dimensional packing density is nonnegative.** The trivial lower bound holds: the
sphere-packing density $\Delta_4$ of $\mathbb{R}^4$ satisfies $0 \le \Delta_4$.

Source: catalogue C36 trivial lower bound, proved in the measure codomain. -/
theorem lowerBound_trivial_proved : lowerBound_trivial := bot_le

/-- **The unit ball in $\mathbb{R}^4$ has volume $\pi^2/2$.** The Lebesgue measure of the open unit
ball centred at the origin of $\mathbb{R}^4$ equals $\pi^2/2$.

Source: the standard four-dimensional unit-ball volume `π²/2`. -/
theorem unitBallVolume4_eq : unitBallVolume4 = ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  rw [unitBallVolume4, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
  norm_num

/-- **The unit ball in $\mathbb{R}^4$ has nonzero volume.** The Lebesgue volume of the open unit
ball of radius $1$ about the origin in $\mathbb{R}^4$ is not $0$.

Source: the center-density divisor is nonzero. -/
theorem unitBallVolume4_ne_zero : unitBallVolume4 ≠ 0 :=
  ne_of_gt (Metric.measure_ball_pos volume (0 : Space) (by norm_num))

/-- **The unit ball in $\mathbb{R}^4$ has finite volume.** The Lebesgue volume of the open unit
ball of radius $1$ about the origin in $\mathbb{R}^4$ is not $\infty$.

Source: the center-density divisor is finite. -/
theorem unitBallVolume4_ne_top : unitBallVolume4 ≠ ⊤ := measure_ball_ne_top

/-- **Center-density upper bounds as packing-density upper bounds.** For every real number
$a \ge 0$, the center density $\delta_4$ of sphere packings in $\mathbb{R}^4$ is at most $a$ if
and only if the sphere-packing density $\Delta_4$ of $\mathbb{R}^4$ is at most $\pi^2 a / 2$.

Source: exact conversion between a nonnegative center-density upper bound
and its `π²/2`-scaled volume-density bound. -/
theorem centerDensity_upper_iff (a : ℝ) (ha : 0 ≤ a) :
    centerDensity4 ≤ ENNReal.ofReal a ↔
      spherePackingDensity4 ≤ ENNReal.ofReal ((Real.pi ^ 2 / 2) * a) := by
  rw [centerDensity4, ENNReal.div_le_iff unitBallVolume4_ne_zero unitBallVolume4_ne_top,
    unitBallVolume4_eq, ← ENNReal.ofReal_mul ha, mul_comm]


end
end MathlibExt.Geometry.SpherePackingDensityFourWanted
