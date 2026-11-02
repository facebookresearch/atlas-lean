/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Continuous rigid passage through a unit right-angle corridor

The plane is `ℂ` with its canonical Lebesgue measure. A shape is Lebesgue-measurable
and connected, and one continuous rotation/translation path carries its entire set
from the horizontal entrance to the vertical exit while staying in the corridor.
Areas are optimized in `ENNReal`, so finiteness and attainment are not assumptions.

The square and its two-segment translation give an actual area-one example.
These source-independent definitions and proofs were authored by Codex Cedar.
The separately recorded catalogue bounds are not used by this module.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MovingSofa

/-- **Corridor.** The corridor is the L-shaped set of points $z \in \mathbb{C}$ with
$\operatorname{Re} z \le 1$ and $0 \le \operatorname{Im} z \le 1$ (the horizontal arm, extending
to the left) together with the points $z$ with $0 \le \operatorname{Re} z \le 1$ and
$\operatorname{Im} z \ge 0$ (the vertical arm, extending upward): two perpendicular
semi-infinite arms of width one. -/
def corridor : Set ℂ :=
  {z | z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1} ∪
    {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im}

/-- **Entrance of the corridor.** The entrance region of the unit right-angle corridor is
the closed half-strip
$\{z \in \mathbb{C} : \operatorname{Re} z \le 0,\ 0 \le \operatorname{Im} z \le 1\}$,
the part of its horizontal arm to the left of the corner square. -/
def entrance : Set ℂ := {z | z.re ≤ 0 ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- **Exit of the corridor.** The exit region of the unit right-angle corridor is the closed
half-strip $\{z \in \mathbb{C} : 0 \le \operatorname{Re} z \le 1,\ \operatorname{Im} z \ge 1\}$,
the part of its vertical arm above the corner square. -/
def exit : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im}

/-- **Planar rigid motion.** A motion consists of a continuous map $t \mapsto u_t$ from $[0, 1]$
to the unit circle $\{u \in \mathbb{C} : |u| = 1\}$ (the rotation) and a continuous map
$t \mapsto c_t$ from $[0, 1]$ to $\mathbb{C}$ (the translation). -/
structure Motion where
  /-- The orientation-preserving unit complex rotation at each time. -/
  rotation : C(unitInterval, Circle)
  /-- The planar translation at each time. -/
  translation : C(unitInterval, ℂ)

/-- **Position under a rigid motion.** Let $m$ be a motion with rotation $u(t)$ in the unit circle
and translation $c(t) \in \mathbb{C}$ at each time $t \in [0, 1]$. The position at time $t$ of a
point $z \in \mathbb{C}$ is $u(t)\,z + c(t)$. -/
def Motion.position (m : Motion) (t : unitInterval) (z : ℂ) : ℂ :=
  (m.rotation t : ℂ) * z + m.translation t

/-- **Passing the corridor.** A set $K \subseteq \mathbb{C}$ can pass the corridor if there are
continuous maps $u$ from $[0, 1]$ to the unit circle $\{w \in \mathbb{C} : |w| = 1\}$ and $c$
from $[0, 1]$ to $\mathbb{C}$ such that, writing $K_t = \{u(t) z + c(t) : z \in K\}$ for the
position of $K$ at time $t$, $K_0$ lies in the entrance arm, $K_1$ lies in the exit arm, and
$K_t$ lies in the corridor for every $t \in [0, 1]$. -/
def CanPass (K : Set ℂ) : Prop :=
  ∃ m : Motion,
    m.position 0 '' K ⊆ entrance ∧
    m.position 1 '' K ⊆ exit ∧
    ∀ t : unitInterval, m.position t '' K ⊆ corridor

/-- **Sofa shapes.** A set $K \subseteq \mathbb{C}$ is a sofa when it is Lebesgue measurable,
nonempty and connected, and can be moved through the unit right-angle corridor: there is a motion
(a rotation by a unit complex number and a translation, both varying continuously with time
$t \in [0, 1]$) that places $K$ inside the corridor's entrance region at time $0$, inside its exit
region at time $1$, and inside the corridor at every time $t$. -/
def IsSofa (K : Set ℂ) : Prop :=
  NullMeasurableSet K volume ∧ IsConnected K ∧ CanPass K

/-- **Optimal sofa area.** Let the corridor be
$L = \{z \in \mathbb{C} : \operatorname{Re} z \le 1,\ 0 \le \operatorname{Im} z \le 1\} \cup
\{z \in \mathbb{C} : 0 \le \operatorname{Re} z \le 1,\ 0 \le \operatorname{Im} z\}$, with entrance
$E = \{z \in \mathbb{C} : \operatorname{Re} z \le 0,\ 0 \le \operatorname{Im} z \le 1\}$ and exit
$X = \{z \in \mathbb{C} : 0 \le \operatorname{Re} z \le 1,\ 1 \le \operatorname{Im} z\}$. A sofa
is a nonempty connected Lebesgue-measurable set $K \subseteq \mathbb{C}$ for which there are
continuous maps $u : [0, 1] \to \{w \in \mathbb{C} : |w| = 1\}$ and $c : [0, 1] \to \mathbb{C}$
such that, writing $K_t = \{u(t)\,z + c(t) : z \in K\}$, we have $K_0 \subseteq E$,
$K_1 \subseteq X$ and $K_t \subseteq L$ for every $t \in [0, 1]$. The optimal sofa area is the
supremum, taken in $[0, \infty]$, of the Lebesgue measures of all sofas.

Because the supremum is taken in $[0, \infty]$, neither its finiteness nor its attainment is
assumed. -/
noncomputable def optimalArea : ℝ≥0∞ := ⨆ (K : Set ℂ) (_ : IsSofa K), volume K

/-- **Unit square.** The unit square is the set of complex numbers $z$ with
$0 \le \operatorname{Re} z \le 1$ and $0 \le \operatorname{Im} z \le 1$, that is, the square
$[0,1] \times [0,1]$ in the complex plane. -/
def unitSquare : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

/-- **The square's translation through the corner.** The motion with no rotation that sends a
point $z$ at time $t \in [0,1]$ to $z + \tau(t)$, where $\tau(t) = 2t - 1$ for $t \le 1/2$ and
$\tau(t) = (2t - 1)i$ for $t \ge 1/2$: it moves a shape one unit to the right during the first
half of the time interval and then one unit upward. -/
noncomputable def squareMotion : Motion where
  rotation := ContinuousMap.const unitInterval 1
  translation :=
    ⟨fun t ↦ ((min (2 * (t : ℝ) - 1) 0 : ℝ) : ℂ) +
      ((max (2 * (t : ℝ) - 1) 0 : ℝ) : ℂ) * Complex.I, by fun_prop⟩

/-- **Motions preserve distance.** Let $m$ be a motion, $t \in [0, 1]$ a time, and write $m_t(z)$
for the position of a point $z \in \mathbb{C}$ under $m$ at time $t$. Then
$|m_t(z) - m_t(w)| = |z - w|$ for all $z, w \in \mathbb{C}$. -/
theorem motion_preserves_distance (m : Motion) (t : unitInterval) (z w : ℂ) :
    dist (m.position t z) (m.position t w) = dist z w := by
  simp only [Motion.position, dist_eq_norm, add_sub_add_right_eq_sub, ← mul_sub]
  simp

/-- **The unit square is Borel measurable.** The unit square $[0,1] \times [0,1]$ is a measurable
set for the Borel $\sigma$-algebra of the complex plane. -/
theorem square_measurable : MeasurableSet unitSquare :=
  (measurableSet_Icc.prod measurableSet_Icc).preimage
    Complex.measurableEquivRealProd.measurable

/-- **The unit square is connected.** The unit square
$\{z \in \mathbb{C} : 0 \le \operatorname{Re} z \le 1,\ 0 \le \operatorname{Im} z \le 1\}$ is a
nonempty connected subset of $\mathbb{C}$. -/
theorem square_connected : IsConnected unitSquare := by
  have h := (isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num)).prod
    (isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num))
  have hi := h.image Complex.measurableEquivRealProd.symm
    Complex.equivRealProdCLM.symm.continuous.continuousOn
  have heq : Complex.measurableEquivRealProd.symm ''
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = unitSquare := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa [unitSquare] using hp
    · intro hz
      exact ⟨Complex.measurableEquivRealProd z, hz,
        Complex.measurableEquivRealProd.symm_apply_apply z⟩
  rwa [heq] at hi

/-- **The unit square has area one.** The unit square
$\{z \in \mathbb{C} : 0 \le \operatorname{Re} z \le 1,\ 0 \le \operatorname{Im} z \le 1\}$ has
Lebesgue measure $1$. -/
theorem square_area : volume unitSquare = 1 := by
  rw [unitSquare, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet]
  change (volume.prod volume) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1
  rw [Measure.prod_prod]
  norm_num [Real.volume_Icc]

/-- **The unit square passes the corridor.** Let the corridor be
$L = \{z \in \mathbb{C} : \operatorname{Re} z \le 1,\ 0 \le \operatorname{Im} z \le 1\} \cup
\{z \in \mathbb{C} : 0 \le \operatorname{Re} z \le 1,\ 0 \le \operatorname{Im} z\}$, with entrance
$E = \{z \in \mathbb{C} : \operatorname{Re} z \le 0,\ 0 \le \operatorname{Im} z \le 1\}$ and exit
$X = \{z \in \mathbb{C} : 0 \le \operatorname{Re} z \le 1,\ 1 \le \operatorname{Im} z\}$. For the
unit square
$Q = \{z \in \mathbb{C} : 0 \le \operatorname{Re} z \le 1,\ 0 \le \operatorname{Im} z \le 1\}$
there are continuous maps $u : [0, 1] \to \{w \in \mathbb{C} : |w| = 1\}$ and
$c : [0, 1] \to \mathbb{C}$ such that, writing $Q_t = \{u(t)\,z + c(t) : z \in Q\}$, we have
$Q_0 \subseteq E$, $Q_1 \subseteq X$ and $Q_t \subseteq L$ for every $t \in [0, 1]$.

A pure translation, first to the right and then upward, suffices. -/
theorem square_canPass : CanPass unitSquare := by
  refine ⟨squareMotion, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    norm_num [entrance, Motion.position, squareMotion]
    exact ⟨by linarith, him0, him1⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    norm_num [exit, Motion.position, squareMotion]
    exact ⟨hre0, hre1, by linarith⟩
  · intro t
    rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    change ((squareMotion.position t z).re ≤ 1 ∧
      0 ≤ (squareMotion.position t z).im ∧ (squareMotion.position t z).im ≤ 1) ∨
      (0 ≤ (squareMotion.position t z).re ∧ (squareMotion.position t z).re ≤ 1 ∧
        0 ≤ (squareMotion.position t z).im)
    by_cases ht : 2 * (t : ℝ) - 1 ≤ 0
    · left
      have h : z.re + (2 * (t : ℝ) - 1) ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1 :=
        ⟨by linarith, him0, him1⟩
      simpa [Motion.position, squareMotion, min_eq_left ht, max_eq_right ht] using h
    · right
      have ht' : 0 ≤ 2 * (t : ℝ) - 1 := le_of_not_ge ht
      have h : 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im + (2 * (t : ℝ) - 1) :=
        ⟨hre0, hre1, by linarith⟩
      simpa [Motion.position, squareMotion, min_eq_right ht', max_eq_left ht'] using h

/-- **The unit square is a sofa.** The unit square $[0,1] \times [0,1]$ in the complex plane is a
sofa: it is null-measurable for Lebesgue measure, connected, and there are continuous maps
$u \colon [0,1] \to \{w \in \mathbb{C} : |w| = 1\}$ and $v \colon [0,1] \to \mathbb{C}$ such that
the motion $z \mapsto u(t) z + v(t)$ carries the square into the entrance
$\{z : \operatorname{Re} z \le 0,\ 0 \le \operatorname{Im} z \le 1\}$ at $t = 0$, into the exit
$\{z : 0 \le \operatorname{Re} z \le 1,\ 1 \le \operatorname{Im} z\}$ at $t = 1$, and into the
unit right-angle corridor
$\{z : \operatorname{Re} z \le 1,\ 0 \le \operatorname{Im} z \le 1\} \cup
\{z : 0 \le \operatorname{Re} z \le 1,\ 0 \le \operatorname{Im} z\}$ at every time $t \in [0,1]$. -/
theorem square_isSofa : IsSofa unitSquare :=
  ⟨square_measurable.nullMeasurableSet, square_connected, square_canPass⟩

/-- **The optimal sofa area is at least one.** The optimal sofa area, that is, the supremum
in $[0, \infty]$ of the Lebesgue areas of all sofas, is at least $1$.

The unit square, a sofa of area $1$, witnesses the bound. -/
theorem one_le_optimalArea : 1 ≤ optimalArea := by
  rw [← square_area]
  exact le_iSup_of_le unitSquare (le_iSup_of_le square_isSofa le_rfl)

/-- **Mirrored corridor.** The mirrored corridor is the set of points $z \in \mathbb{C}$ with
$\operatorname{Re} z \ge -1$ and $0 \le \operatorname{Im} z \le 1$ (the horizontal arm,
extending to the right) together with the points $z$ with $-1 \le \operatorname{Re} z \le 0$
and $\operatorname{Im} z \ge 0$ (the vertical arm, extending upward). It is the reflection of
the corridor in the imaginary axis, so passing it requires the opposite turn. -/
def corridorOther : Set ℂ :=
  {z | -1 ≤ z.re ∧ 0 ≤ z.im ∧ z.im ≤ 1} ∪
    {z | -1 ≤ z.re ∧ z.re ≤ 0 ∧ 0 ≤ z.im}

/-- **Entrance arm of the mirrored corridor.** The entrance arm of the mirrored corridor is the
set of points $z \in \mathbb{C}$ with $\operatorname{Re} z \ge 0$ and
$0 \le \operatorname{Im} z \le 1$: the part of its horizontal arm beyond the corner square
$-1 \le \operatorname{Re} z \le 0$, $0 \le \operatorname{Im} z \le 1$. -/
def entranceOther : Set ℂ := {z | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- **Exit of the mirrored corridor.** The exit region of the mirrored unit corridor is the
closed half-strip
$\{z \in \mathbb{C} : -1 \le \operatorname{Re} z \le 0,\ \operatorname{Im} z \ge 1\}$,
the part of its vertical arm above its corner square. -/
def exitOther : Set ℂ := {z | -1 ≤ z.re ∧ z.re ≤ 0 ∧ 1 ≤ z.im}

/-- **Passing the mirrored corridor.** A set $K \subseteq \mathbb{C}$ can pass the mirrored
corridor if there are continuous maps $u$ from $[0, 1]$ to the unit circle
$\{w \in \mathbb{C} : |w| = 1\}$ and $c$ from $[0, 1]$ to $\mathbb{C}$ such that, writing
$K_t = \{u(t) z + c(t) : z \in K\}$ for the position of $K$ at time $t$, $K_0$ lies in the
entrance arm of the mirrored corridor, $K_1$ lies in the exit arm of the mirrored corridor, and
$K_t$ lies in the mirrored corridor for every $t \in [0, 1]$. -/
def CanPassOther (K : Set ℂ) : Prop :=
  ∃ m : Motion,
    m.position 0 '' K ⊆ entranceOther ∧
    m.position 1 '' K ⊆ exitOther ∧
    ∀ t : unitInterval, m.position t '' K ⊆ corridorOther


/-- **Z-shaped corridor.** For a real number $d$, the Z-shaped corridor with corner separation
$d$ is the set of points $z \in \mathbb{C}$ lying in at least one of three pieces: the lower
horizontal arm, where $\operatorname{Re} z \le 1$ and $0 \le \operatorname{Im} z \le 1$; the
middle channel, where $0 \le \operatorname{Re} z \le 1$ and $0 \le \operatorname{Im} z \le 2 + d$;
and the upper horizontal arm, where $\operatorname{Re} z \ge 0$ and
$1 + d \le \operatorname{Im} z \le 2 + d$.

The middle channel is bounded: it does not contain the upward ray above the upper arm. For
$d = 1$ the two corner squares are separated by one full corridor width. Passing the corridor
requires one turn in each direction inside a single passage. -/
def corridorZ (d : ℝ) : Set ℂ :=
  {z | z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1} ∪
    {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 2 + d} ∪
    {z | 0 ≤ z.re ∧ 1 + d ≤ z.im ∧ z.im ≤ 2 + d}

/-- **Entrance arm of the Z corridor.** The entrance region of the Z corridor is the closed
half-strip $\{z \in \mathbb{C} : \operatorname{Re} z \le 0,\ 0 \le \operatorname{Im} z \le 1\}$,
the part of its horizontal entrance arm to the left of the middle channel. -/
def entranceZ : Set ℂ := {z | z.re ≤ 0 ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- **Exit arm of the Z corridor.** For a real number $d$ (the corner separation), the exit region
of the Z corridor with separation $d$ is the closed half-strip
$\{z \in \mathbb{C} : \operatorname{Re} z \ge 1,\ 1 + d \le \operatorname{Im} z \le 2 + d\}$,
the part of its horizontal exit arm to the right of the middle channel. -/
def exitZ (d : ℝ) : Set ℂ := {z | 1 ≤ z.re ∧ 1 + d ≤ z.im ∧ z.im ≤ 2 + d}

/-- **Passing the Z corridor at a given separation.** For a real number $d$, a set
$K \subseteq \mathbb{C}$ can pass the Z corridor with corner separation $d$ if there are
continuous maps $u$ from $[0, 1]$ to the unit circle $\{w \in \mathbb{C} : |w| = 1\}$ and $c$
from $[0, 1]$ to $\mathbb{C}$ such that, writing $K_t = \{u(t) z + c(t) : z \in K\}$ for the
position of $K$ at time $t$, $K_0$ lies in the entrance arm of the Z corridor, $K_1$ lies in the
exit arm of the Z corridor with corner separation $d$, and $K_t$ lies in the Z corridor with
corner separation $d$ for every $t \in [0, 1]$.

Such a passage is a single motion that turns once in each direction. -/
def CanPassZAt (K : Set ℂ) (d : ℝ) : Prop :=
  ∃ m : Motion,
    m.position 0 '' K ⊆ entranceZ ∧
    m.position 1 '' K ⊆ exitZ d ∧
    ∀ t : unitInterval, m.position t '' K ⊆ corridorZ d

/-- **Passing the Z corridor for all large separations.** A set $K \subseteq \mathbb{C}$ can pass
the Z corridor if there is a real number $D$ such that, for every real $d \ge D$, $K$ can pass
the Z corridor with corner separation $d$; that is, $K$ passes whenever the corners are
sufficiently separated.

Unlike the mirrored corridor, this is not implied by an ordinary passage: time reversal plus a
rigid motion transports an ordinary passage to the mirrored corridor, but a Z passage couples
both turns in one motion. -/
def CanPassZ (K : Set ℂ) : Prop :=
  ∃ D : ℝ, ∀ d : ℝ, D ≤ d → CanPassZAt K d

/-- **The square's translation through the Z corridor.** For a real number $d$, the motion with no
rotation that sends a point $z$ at time $t \in [0,1]$ to $z + \tau(t)$, where $\tau(t) = 3t - 1$ for
$t \le 1/3$, $\tau(t) = (1 + d)(3t - 1)i$ for $1/3 \le t \le 2/3$, and
$\tau(t) = (3t - 2) + (1 + d)i$ for $t \ge 2/3$: it translates a shape by $1$, then by $(1 + d)i$,
then by $1$, each segment taking a third of the time interval. -/
noncomputable def squareMotionZAt (d : ℝ) : Motion where
  rotation := ContinuousMap.const unitInterval 1
  translation :=
    ⟨fun t ↦ ((-1 + min (3 * (t : ℝ)) 1 + max (3 * (t : ℝ) - 2) 0 : ℝ) : ℂ) +
      (((1 + d) * min (max (3 * (t : ℝ) - 1) 0) 1 : ℝ) : ℂ) * Complex.I,
      by fun_prop⟩

/-- **Z-corridor passage of the unit square.** For every real $d \ge 0$, the unit square passes
the Z corridor with corner separation $d$. -/
theorem square_canPassZAt (d : ℝ) (hd : 0 ≤ d) : CanPassZAt unitSquare d := by
  refine ⟨squareMotionZAt d, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    norm_num [entranceZ, Motion.position, squareMotionZAt]
    exact ⟨by linarith, him0, him1⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    norm_num [exitZ, Motion.position, squareMotionZAt]
    exact ⟨by linarith, by linarith, by linarith⟩
  · intro t
    rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    change ((((squareMotionZAt d).position t z).re ≤ 1 ∧
      0 ≤ ((squareMotionZAt d).position t z).im ∧
      ((squareMotionZAt d).position t z).im ≤ 1) ∨
      (0 ≤ ((squareMotionZAt d).position t z).re ∧
        ((squareMotionZAt d).position t z).re ≤ 1 ∧
        0 ≤ ((squareMotionZAt d).position t z).im ∧
        ((squareMotionZAt d).position t z).im ≤ 2 + d)) ∨
      (0 ≤ ((squareMotionZAt d).position t z).re ∧
        1 + d ≤ ((squareMotionZAt d).position t z).im ∧
        ((squareMotionZAt d).position t z).im ≤ 2 + d)
    by_cases h1 : 3 * (t : ℝ) ≤ 1
    · refine Or.inl (Or.inl ?_)
      have hx : -1 + min (3 * (t : ℝ)) 1 + max (3 * (t : ℝ) - 2) 0 =
          -1 + 3 * (t : ℝ) := by
        rw [min_eq_left h1, max_eq_right (by linarith)]; ring
      have hy : min (max (3 * (t : ℝ) - 1) 0) 1 = (0 : ℝ) := by
        rw [max_eq_right (by linarith)]; exact min_eq_left (by norm_num)
      have h : z.re + (-1 + 3 * (t : ℝ)) ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1 :=
        ⟨by linarith, him0, him1⟩
      simpa [Motion.position, squareMotionZAt, hx, hy] using h
    · by_cases h2 : 3 * (t : ℝ) ≤ 2
      · refine Or.inl (Or.inr ?_)
        have hx : -1 + min (3 * (t : ℝ)) 1 + max (3 * (t : ℝ) - 2) 0 = (0 : ℝ) := by
          rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
        have hy : min (max (3 * (t : ℝ) - 1) 0) 1 = 3 * (t : ℝ) - 1 := by
          rw [max_eq_left (by linarith), min_eq_left (by linarith)]
        have hprod0 : 0 ≤ (1 + d) * (3 * (t : ℝ) - 1) :=
          mul_nonneg (by linarith) (by linarith)
        have hprod1 : (1 + d) * (3 * (t : ℝ) - 1) ≤ 1 + d :=
          mul_le_of_le_one_right (by linarith) (by linarith)
        have h : 0 ≤ z.re ∧ z.re ≤ 1 ∧
            0 ≤ z.im + (1 + d) * (3 * (t : ℝ) - 1) ∧
            z.im + (1 + d) * (3 * (t : ℝ) - 1) ≤ 2 + d :=
          ⟨hre0, hre1, by linarith, by linarith⟩
        simpa [Motion.position, squareMotionZAt, hx, hy] using h
      · refine Or.inr ?_
        have hx : -1 + min (3 * (t : ℝ)) 1 + max (3 * (t : ℝ) - 2) 0 =
            3 * (t : ℝ) - 2 := by
          rw [min_eq_right (by linarith), max_eq_left (by linarith)]; ring
        have hy : min (max (3 * (t : ℝ) - 1) 0) 1 = (1 : ℝ) := by
          rw [min_eq_right]
          have hle := le_max_left (3 * (t : ℝ) - 1) (0 : ℝ)
          linarith
        have h : 0 ≤ z.re + (3 * (t : ℝ) - 2) ∧
            1 + d ≤ z.im + (1 + d) * 1 ∧ z.im + (1 + d) * 1 ≤ 2 + d :=
          ⟨by linarith, by linarith, by linarith⟩
        simpa [Motion.position, squareMotionZAt, hx, hy] using h

/-- **The square's translation through the Z corridor at separation one.** The square's
translation through the Z corridor at separation $d = 1$: the motion with no rotation that sends a
point $z$ at time $t \in [0,1]$ to $z + \tau(t)$, where $\tau(t) = 3t - 1$ for $t \le 1/3$,
$\tau(t) = 2(3t - 1)i$ for $1/3 \le t \le 2/3$, and $\tau(t) = (3t - 2) + 2i$ for $t \ge 2/3$. -/
noncomputable def squareMotionZ : Motion := squareMotionZAt 1

/-- **Z-corridor passage of the unit square at separation one.** The unit square passes the Z
corridor with corner separation $1$. -/
theorem square_canPassZAt_one : CanPassZAt unitSquare 1 :=
  square_canPassZAt 1 (by norm_num)

/-- **Z-corridor passage of the unit square for large separations.** There is a real $D$ such
that for every $d \ge D$ the unit square passes the Z corridor with corner separation $d$. -/
theorem square_canPassZ : CanPassZ unitSquare :=
  ⟨0, fun d hd => square_canPassZAt d hd⟩

/-- **Ambidextrous sofa shapes.** A set $K \subseteq \mathbb{C}$ is an ambidextrous sofa when it is
a sofa and there is a real number $D$ such that, for every corner separation $d \ge D$, a single
motion places $K$ inside the entrance arm of the Z corridor with separation $d$ at time $0$, inside
its exit arm at time $1$, and inside that corridor at every time; such a passage turns once in
each direction.

(Two independent passages, one through each mirrored L corridor, would not suffice: an ordinary
passage transports to the mirrored corridor by time reversal plus a rigid motion, so that
formulation would collapse to the ordinary sofa condition.) -/
def IsAmbidextrousSofa (K : Set ℂ) : Prop :=
  IsSofa K ∧ CanPassZ K

/-- **Optimal area of ambidextrous sofas.** The ambidextrous optimal area is the supremum, taken
in $[0, \infty]$, of the Lebesgue areas of all ambidextrous sofas $K \subseteq \mathbb{C}$. -/
noncomputable def ambidextrousOptimalArea : ℝ≥0∞ :=
  ⨆ (K : Set ℂ) (_ : IsAmbidextrousSofa K), volume K

/-- **The ambidextrous optimal area is at most the optimal area.** The supremum, in $[0, \infty]$,
of the Lebesgue areas of all ambidextrous sofas is at most the supremum of the Lebesgue areas of
all sofas. This holds because every ambidextrous sofa is a sofa. -/
theorem ambidextrousOptimalArea_le_optimalArea :
    ambidextrousOptimalArea ≤ optimalArea := by
  apply iSup_le
  intro K
  apply iSup_le
  intro hK
  exact le_iSup_of_le K (le_iSup_of_le hK.1 le_rfl)

/-- **The square's translation through the mirrored corner.** The motion with no rotation that
sends a point $z$ at time $t \in [0,1]$ to $z + \tau(t)$, where $\tau(t) = -2t$ for $t \le 1/2$ and
$\tau(t) = -1 + (2t - 1)i$ for $t \ge 1/2$: it moves a shape one unit to the left during the first
half of the time interval and then one unit upward. -/
noncomputable def squareMotionOther : Motion where
  rotation := ContinuousMap.const unitInterval 1
  translation :=
    ⟨fun t ↦ ((-1 - min (2 * (t : ℝ) - 1) 0 : ℝ) : ℂ) +
      ((max (2 * (t : ℝ) - 1) 0 : ℝ) : ℂ) * Complex.I, by fun_prop⟩

/-- **The unit square passes the mirrored corridor.** Let the mirrored corridor be
$L' = \{z \in \mathbb{C} : -1 \le \operatorname{Re} z,\ 0 \le \operatorname{Im} z \le 1\} \cup
\{z \in \mathbb{C} : -1 \le \operatorname{Re} z \le 0,\ 0 \le \operatorname{Im} z\}$, with entrance
$E' = \{z \in \mathbb{C} : 0 \le \operatorname{Re} z,\ 0 \le \operatorname{Im} z \le 1\}$ and exit
$X' = \{z \in \mathbb{C} : -1 \le \operatorname{Re} z \le 0,\ 1 \le \operatorname{Im} z\}$. For the
unit square
$Q = \{z \in \mathbb{C} : 0 \le \operatorname{Re} z \le 1,\ 0 \le \operatorname{Im} z \le 1\}$
there are continuous maps $u : [0, 1] \to \{w \in \mathbb{C} : |w| = 1\}$ and
$c : [0, 1] \to \mathbb{C}$ such that, writing $Q_t = \{u(t)\,z + c(t) : z \in Q\}$, we have
$Q_0 \subseteq E'$, $Q_1 \subseteq X'$ and $Q_t \subseteq L'$ for every $t \in [0, 1]$. -/
theorem square_canPassOther : CanPassOther unitSquare := by
  refine ⟨squareMotionOther, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, _hre1⟩, ⟨him0, him1⟩⟩
    norm_num [entranceOther, Motion.position, squareMotionOther]
    exact ⟨hre0, him0, him1⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, _him1⟩⟩
    norm_num [exitOther, Motion.position, squareMotionOther]
    exact ⟨by linarith, by linarith, by linarith⟩
  · intro t
    rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    change (-1 ≤ (squareMotionOther.position t z).re ∧
      0 ≤ (squareMotionOther.position t z).im ∧
      (squareMotionOther.position t z).im ≤ 1) ∨
      (-1 ≤ (squareMotionOther.position t z).re ∧
        (squareMotionOther.position t z).re ≤ 0 ∧
        0 ≤ (squareMotionOther.position t z).im)
    by_cases ht : 2 * (t : ℝ) - 1 ≤ 0
    · left
      have h : -1 ≤ z.re + (-1 - (2 * (t : ℝ) - 1)) ∧ 0 ≤ z.im ∧ z.im ≤ 1 :=
        ⟨by linarith, him0, him1⟩
      simpa [Motion.position, squareMotionOther, min_eq_left ht,
        max_eq_right ht] using h
    · right
      have ht' : 0 ≤ 2 * (t : ℝ) - 1 := le_of_not_ge ht
      have h : -1 ≤ z.re + -1 ∧ z.re + -1 ≤ 0 ∧
          0 ≤ z.im + (2 * (t : ℝ) - 1) :=
        ⟨by linarith, by linarith, by linarith⟩
      simpa [Motion.position, squareMotionOther, min_eq_right ht',
        max_eq_left ht'] using h

/-- **The unit square is an ambidextrous sofa.** The unit square $[0,1] \times [0,1]$ in the
complex plane is an ambidextrous sofa. -/
theorem square_isAmbidextrousSofa : IsAmbidextrousSofa unitSquare :=
  ⟨square_isSofa, square_canPassZ⟩

/-- **The ambidextrous sofa constant is at least one.** The supremum of the Lebesgue areas of all
ambidextrous sofas, taken in $[0, \infty]$, is at least $1$.

The unit square $[0, 1] \times [0, 1]$ is an ambidextrous sofa of area $1$. -/
theorem one_le_ambidextrousOptimalArea : 1 ≤ ambidextrousOptimalArea := by
  rw [← square_area]
  exact le_iSup_of_le unitSquare
    (le_iSup_of_le square_isAmbidextrousSofa le_rfl)

end MovingSofa
