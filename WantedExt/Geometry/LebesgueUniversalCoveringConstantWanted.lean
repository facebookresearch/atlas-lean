/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Lebesgue universal covering constant

The constant is the infimal area of a nonempty convex planar set containing a
congruent copy of every nonempty convex planar set of diameter exactly one.
Area is planar Lebesgue measure; congruences include reflections.

The bounds and reductions below are known results requested as `theorem_wanted`,
not assumptions or proofs. Source: optimization catalogue, constant 13b.
-/

open MeasureTheory

namespace MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

noncomputable section

/-- **The Euclidean plane of Lebesgue's covering problem.** The ambient space is the Euclidean
plane $\mathbb{R}^2$, with the Euclidean distance. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Convex sets of diameter one.** A set $K$ in the Euclidean plane $\mathbb{R}^2$ is a
unit-diameter convex set when it is nonempty and convex and its diameter
$\sup_{x, y \in K} \lVert x - y \rVert$ is exactly $1$. -/
def IsUnitDiameterConvexSet (K : Set Plane) : Prop :=
  K.Nonempty ∧ Convex ℝ K ∧ Metric.diam K = 1

/-- **Covering a congruent copy.** A planar set $\Omega$ covers a congruent copy of a planar set
$K$ when some isometry $e$ of the plane onto itself satisfies $e(K) \subseteq \Omega$.

Isometries include reflections. -/
def CoversCongruentCopy (Ω K : Set Plane) : Prop :=
  ∃ e : Plane ≃ᵢ Plane, e '' K ⊆ Ω

/-- **Universal convex covers.** A set $\Omega$ in the Euclidean plane $\mathbb{R}^2$ is a universal
convex cover when it is nonempty and convex and, for every nonempty convex set
$K \subseteq \mathbb{R}^2$ of diameter $1$, some isometry $e$ of the plane onto itself satisfies
$e(K) \subseteq \Omega$. -/
def IsUniversalConvexCover (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ Convex ℝ Ω ∧
    ∀ K : Set Plane, IsUnitDiameterConvexSet K → CoversCongruentCopy Ω K

/-- **Planar area.** The area of a set $S$ in the Euclidean plane $\mathbb{R}^2$
is its Lebesgue measure (outer measure if $S$ is not measurable), a value in $[0, \infty]$,
so infinite area is allowed. -/
def planarArea (S : Set Plane) : ENNReal :=
  volume S

/-- **Areas of universal convex covers.** The set of admissible cover areas is the set of all
$a \in [0, \infty]$ for which there is a universal convex cover $\Omega$ in the plane (a nonempty
convex set containing a congruent copy of every nonempty convex planar set of diameter $1$) whose
Lebesgue area is $a$. -/
def admissibleCoverAreas : Set ENNReal :=
  {a | ∃ Ω : Set Plane, IsUniversalConvexCover Ω ∧ planarArea Ω = a}

/--
**Lebesgue universal covering constant.** Call a set $\Omega$ in the Euclidean plane
$\mathbb{R}^2$ a universal convex cover if it is nonempty and convex and, for every nonempty
convex set $K \subseteq \mathbb{R}^2$ of diameter exactly $1$, some isometry of the plane onto
itself maps $K$ into $\Omega$. The Lebesgue universal covering constant is the infimum, taken in
$[0, \infty]$, of the Lebesgue areas of all universal convex covers; the infimum of an empty
family would be $\infty$.

The definition does not assume that a universal convex cover of minimal area exists.
-/
def lebesgueUniversalCoveringConstant : ENNReal :=
  sInf admissibleCoverAreas

/-- **Directional width.** For a planar set $K$ and a vector $u$ in the plane, the width of $K$
in direction $u$ is $\sup_{x \in K} \langle u, x \rangle - \inf_{x \in K} \langle u, x \rangle$,
where the supremum and infimum are taken in $\mathbb{R}$, with the convention that each is $0$
when the set of values $\langle u, x \rangle$ is empty or unbounded on that side.

It is only applied to nonempty compact $K$, where both extrema are attained. -/
def directionalWidth (K : Set Plane) (u : Plane) : ℝ :=
  sSup ((fun x : Plane => inner ℝ u x) '' K) -
    sInf ((fun x : Plane => inner ℝ u x) '' K)

/-- **Sets of constant width one.** A set $K$ in the Euclidean plane $\mathbb{R}^2$ has constant
width $1$ when it is nonempty, compact and convex and, for every unit vector $u$, its width in
direction $u$, namely $\sup_{x \in K} \langle u, x \rangle - \inf_{x \in K} \langle u, x \rangle$,
equals $1$. -/
def IsConstantWidthOne (K : Set Plane) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧
    ∀ u : Plane, ‖u‖ = 1 → directionalWidth K u = 1

/-- **Statement of the existence of a minimal universal convex cover.** This proposition states
that some nonempty convex set $\Omega$ in the Euclidean plane $\mathbb{R}^2$ is a universal convex
cover, that is, for every nonempty convex set $K \subseteq \mathbb{R}^2$ of diameter $1$ some
isometry $e$ of the plane onto itself satisfies $e(K) \subseteq \Omega$, and that the area (planar
Lebesgue measure) of $\Omega$ equals the Lebesgue universal covering constant, the infimum of the
areas of all universal convex covers.

The existence of such a cover follows from the Blaschke selection theorem. -/
def elekes1994MinimalCoverExists : Prop :=
  ∃ Ω : Set Plane,
    IsUniversalConvexCover Ω ∧
      planarArea Ω = lebesgueUniversalCoveringConstant

/-- **Covering sets of constant width one suffices (statement).** The proposition that every
nonempty convex subset $\Omega$ of the Euclidean plane that contains a congruent copy of every
nonempty compact convex planar set of constant width $1$ is a universal convex cover, that is,
contains a congruent copy of every nonempty convex planar set of diameter $1$. -/
def vrecica1981ConstantWidthOneSuffices : Prop :=
  ∀ Ω : Set Plane,
    Ω.Nonempty →
      Convex ℝ Ω →
        (∀ K : Set Plane, IsConstantWidthOne K → CoversCongruentCopy Ω K) →
          IsUniversalConvexCover Ω

/-- **Jung's upper bound for Lebesgue's universal covering constant (statement).** The proposition
that Lebesgue's universal covering constant is at most $\pi/3$.

This is the bound given by Jung's theorem: a closed disk of radius $1/\sqrt{3}$, of area $\pi/3$,
contains a translate of every planar set of diameter $1$. -/
def trivialJungElekes1994UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal (Real.pi / 3)

/-- **Statement of Pál's hexagon bound.** The proposition that the Lebesgue universal covering
constant is at most $\sqrt{3}/2$, the bound given by Pál's regular hexagon. -/
def pal1920HexagonUpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal (Real.sqrt 3 / 2)

/-- **Statement of Pál's truncated hexagon bound.** The proposition that the Lebesgue universal
covering constant is at most $2 - 2/\sqrt{3}$, the bound given by Pál's truncated hexagon. -/
def pal1920TruncatedHexagonUpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤
    ENNReal.ofReal (2 - 2 / Real.sqrt 3)

/-- **Statement of Sprague's bound.** The proposition that the Lebesgue universal covering
constant is at most $0.844137708436$. -/
def sprague1936UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.844137708436

/-- **Statement of Hansen's corrected upper bound.** This proposition states that the Lebesgue
universal covering constant, the infimum of the areas of the nonempty convex sets in the Euclidean
plane that contain a congruent copy of every nonempty convex planar set of diameter $1$, is at most
$0.844137708398$.

This is Hansen's finite-decimal upper bound, as corrected by Baez, Bagdasaryan and Gibbs. -/
def hansen1992CorrectedBBG2015UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.844137708398

/-- **Statement of the Baez–Bagdasaryan–Gibbs upper bound.** This is the proposition that there
is a real number $b$ with $0.844115297128419059 \le b < 0.844115297128419060$ such that the
Lebesgue universal covering constant (the infimum of the areas of universal convex covers) is at
most $b$.

The 18 printed digits are a truncation of the bound, not its exact value. -/
def bbg2015ApproximateUpperBound : Prop :=
  ∃ b : ℝ,
    0.844115297128419059 ≤ b ∧
      b < 0.844115297128419060 ∧
        lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal b

/-- **Statement of Gibbs's upper bound.** This proposition states that the Lebesgue universal
covering constant, the infimum of the areas of the nonempty convex sets in the Euclidean plane that
contain a congruent copy of every nonempty convex planar set of diameter $1$, is at most
$0.8440935944$. -/
def gibbs2018UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.8440935944

/-- **Disk lower bound for Lebesgue's universal covering constant (statement).** The proposition
that Lebesgue's universal covering constant is at least $\pi/4$.

This is the bound given by a disk of radius $1/2$, which has diameter $1$ and area $\pi/4$. -/
def trivialUnitDiskLowerBound : Prop :=
  ENNReal.ofReal (Real.pi / 4) ≤ lebesgueUniversalCoveringConstant

/-- **Statement of Elekes's disk-and-triangle lower bound.** This is the proposition that the
Lebesgue universal covering constant (the infimum of the areas of universal convex covers) is at
least $0.8257$.

The bound comes from simultaneously covering a disk and an equilateral triangle of diameter $1$. -/
def elekes1994DiskTriangleLowerBound : Prop :=
  ENNReal.ofReal 0.8257 ≤ lebesgueUniversalCoveringConstant

/-- **Statement of Elekes's regular-polygon lower bound.** This proposition states that the Lebesgue
universal covering constant, the infimum of the areas of the nonempty convex sets in the Euclidean
plane that contain a congruent copy of every nonempty convex planar set of diameter $1$, is at
least $0.8271$.

This is Elekes's finite-decimal lower bound, obtained using regular $3^j$-gons as well. -/
def elekes1994RegularPolygonLowerBound : Prop :=
  ENNReal.ofReal 0.8271 ≤ lebesgueUniversalCoveringConstant

/-- **Statement of the Brass–Sharifi lower bound.** This is the proposition that the Lebesgue
universal covering constant (the infimum of the areas of universal convex covers) is at least
$0.832$.

Brass and Sharifi obtained this bound by a rigorous computer-aided argument. -/
def brassSharifi2005LowerBound : Prop :=
  ENNReal.ofReal 0.832 ≤ lebesgueUniversalCoveringConstant

/-- **Existence of a minimal universal cover.** There is a universal convex cover $\Omega$ (a
nonempty convex planar set containing a congruent copy of every nonempty convex planar set of
diameter $1$) whose Lebesgue area equals the Lebesgue universal covering constant, the infimum of
the areas of all universal convex covers.

Source: Elekes, Generalized breadths, circular Cantor sets, and the least area UCC (1994). -/
theorem_wanted elekes1994MinimalCoverExists_holds : elekes1994MinimalCoverExists

/-- **Covering sets of constant width one suffices.** Let $\Omega$ be a nonempty convex subset of
the Euclidean plane that contains a congruent copy (an image under an isometry of the plane,
reflections allowed) of every nonempty compact convex planar set of constant width $1$. Then
$\Omega$ contains a congruent copy of every nonempty convex planar set of diameter $1$, that is,
$\Omega$ is a universal convex cover.

Source: Vrećica, A note on sets of constant width (1981). -/
theorem_wanted vrecica1981ConstantWidthOneSuffices_holds : vrecica1981ConstantWidthOneSuffices

/-- **Jung's bound for the Lebesgue covering problem.** The Lebesgue universal covering constant
is at most $\pi/3$.

Source: Jung's theorem, quoted in Elekes (1994), catalogue constant 13b. -/
theorem_wanted trivialJungElekes1994UpperBound_holds : trivialJungElekes1994UpperBound

/-- **Pál's hexagon bound.** The Lebesgue universal covering constant is at most $\sqrt{3}/2$.

Source: Pál, Über ein elementares Variationsproblem (1920), hexagon bound. -/
theorem_wanted pal1920HexagonUpperBound_holds : pal1920HexagonUpperBound

/-- **Pál's truncated hexagon bound.** The Lebesgue universal covering constant is at most
$2 - 2/\sqrt{3}$.

Source: Pál, Über ein elementares Variationsproblem (1920), truncated hexagon bound. -/
theorem_wanted pal1920TruncatedHexagonUpperBound_holds : pal1920TruncatedHexagonUpperBound

/-- **Sprague's bound.** The Lebesgue universal covering constant is at most $0.844137708436$.

Source: Sprague, Über ein elementares Variationsproblem (1936). -/
theorem_wanted sprague1936UpperBound_holds : sprague1936UpperBound

/-- **Hansen's upper bound for Lebesgue's covering problem, as corrected.** The Lebesgue universal
covering constant, the infimum of the areas of the nonempty convex sets in the Euclidean plane that
contain a congruent copy of every nonempty convex planar set of diameter $1$, is at most
$0.844137708398$.

Source: Hansen (1992), corrected in Baez, Bagdasaryan and Gibbs (2015). -/
theorem_wanted hansen1992CorrectedBBG2015UpperBound_holds : hansen1992CorrectedBBG2015UpperBound

/-- **Baez–Bagdasaryan–Gibbs upper bound.** There is a real number $b$ with
$0.844115297128419059 \le b < 0.844115297128419060$ such that the Lebesgue universal covering
constant (the infimum of the areas of universal convex covers) is at most $b$.

Source: Baez, Bagdasaryan and Gibbs, The Lebesgue universal covering problem (2015). -/
theorem_wanted bbg2015ApproximateUpperBound_holds : bbg2015ApproximateUpperBound

/-- **Gibbs's upper bound for Lebesgue's covering problem.** The Lebesgue universal covering
constant, the infimum of the areas of the nonempty convex sets in the Euclidean plane that contain a
congruent copy of every nonempty convex planar set of diameter $1$, is at most $0.8440935944$.

Source: Gibbs, An Upper Bound for Lebesgue's Covering Problem (2018). -/
theorem_wanted gibbs2018UpperBound_holds : gibbs2018UpperBound

/-- **Disk lower bound for Lebesgue's universal covering constant.** Lebesgue's universal covering
constant, the infimum of the areas of the nonempty convex planar sets that contain a congruent
copy of every nonempty convex planar set of diameter $1$, is at least $\pi/4$, the area of a disk
of radius $1/2$.

Source: Radius-half disk lower-bound row, optimization catalogue constant 13b. -/
theorem_wanted trivialUnitDiskLowerBound_holds : trivialUnitDiskLowerBound

/-- **Elekes's disk-and-triangle lower bound.** The Lebesgue universal covering constant (the
infimum of the areas of universal convex covers) is at least $0.8257$.

Source: Elekes (1994), disk and equilateral triangle lower bound. -/
theorem_wanted elekes1994DiskTriangleLowerBound_holds : elekes1994DiskTriangleLowerBound

/-- **Elekes's regular-polygon lower bound for Lebesgue's covering problem.** The Lebesgue universal
covering constant, the infimum of the areas of the nonempty convex sets in the Euclidean plane that
contain a congruent copy of every nonempty convex planar set of diameter $1$, is at least $0.8271$.

Source: Elekes (1994), additional regular polygon lower bound. -/
theorem_wanted elekes1994RegularPolygonLowerBound_holds : elekes1994RegularPolygonLowerBound

/-- **Brass–Sharifi lower bound.** The Lebesgue universal covering constant (the infimum of the
areas of universal convex covers) is at least $0.832$.

Source: Brass and Sharifi, A lower bound for Lebesgue's universal cover problem (2005). -/
theorem_wanted brassSharifi2005LowerBound_holds : brassSharifi2005LowerBound

end

end MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted
