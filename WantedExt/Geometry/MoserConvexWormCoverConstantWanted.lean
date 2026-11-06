/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.MoserWormCover

/-!
# Moser's convex worm cover constant: literature requests

Source: Optimization Problems, constant 13a; Panraksa and Wichiramala,
Wetzel's sector covers unit arcs (2021); Fässler and Orponen,
Curve packing and modulus estimates (2018).

The completed geometry is imported from its canonical upstream implementation.
The 20 literature propositions and 20 private proof requests are not assumptions
or proofs. Two conditional witness corollaries stay with their source claims.
There is no source-supplied exact-value conjecture. The PWW2007 polygonal-testing
companion remains an explicit partial-scope gap.
-/

@[expose] public section

open MeasureTheory Set

namespace MoserConvexWormCoverConstant

/-- **Proposition: the convex worm cover constant is at most π/4.** A unit arc is a
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover
constant is the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$
that contain, for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by
a translation. This proposition states that the convex worm cover constant is at most $\pi/4$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundPiOverFour : Prop := convexWormCoverConstant ≤ Real.pi / 4

/-- **Proposition: the convex worm cover constant is at most π/8.** A unit arc is a
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover
constant is the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$
that contain, for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by
a translation. This proposition states that the convex worm cover constant is at most $\pi/8$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundPiOverEight : Prop := convexWormCoverConstant ≤ Real.pi / 8

/-- **Proposition: the convex worm cover constant is at most 0.34501.** A unit arc is a
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover
constant is the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$
that contain, for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by
a translation. This proposition states that the convex worm cover constant is at most $0.34501$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundWetzel1973 : Prop := convexWormCoverConstant ≤ (34501 : ℝ) / 100000

/-- **Statement of Gerriets' upper bound $0.3214$ for convex worm covers.** The proposition that
Moser's convex worm cover constant, the infimum of the areas of convex planar sets containing a
rotated and translated copy of every planar curve of length $1$, is at most $0.3214$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundGerriets1972 : Prop := convexWormCoverConstant ≤ (3214 : ℝ) / 10000

/-- **Statement of the Gerriets–Poole upper bound $0.2861$ for convex worm covers.** The
proposition that Moser's convex worm cover constant, the infimum of the areas of convex planar
sets containing a rotated and translated copy of every planar curve of length $1$, is at most
$0.2861$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundGerrietsPoole1974 : Prop := convexWormCoverConstant ≤ (28610 : ℝ) / 100000

/-- **Statement of the Norwood–Poole–Laidacker upper bound $0.27524$ for convex worm covers.** The
proposition that Moser's convex worm cover constant, the infimum of the areas of convex planar
sets containing a rotated and translated copy of every planar curve of length $1$, is at most
$0.27524$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundNorwoodPooleLaidacker1992 : Prop :=
  convexWormCoverConstant ≤ (27524 : ℝ) / 100000

/-- **Proposition: the convex worm cover constant is at most 0.270911861.** A unit arc is a
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover
constant is the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$
that contain, for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by
a translation. This proposition states that the convex worm cover constant is at most
$0.270911861$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundWang2006 : Prop := convexWormCoverConstant ≤ (270911861 : ℝ) / 1000000000

/-- **Proposition: the convex worm cover constant is at most π/12.** A unit arc is a
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover
constant is the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$
that contain, for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by
a translation. This proposition states that the convex worm cover constant is at most $\pi/12$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundPiOverTwelve : Prop := convexWormCoverConstant ≤ Real.pi / 12

/-- **Wetzel's 1973 lower bound for the convex worm cover constant (claim).** This proposition
asserts that $0.2194 \le \mu$, where $\mu$ is the convex worm cover constant: the infimum of the
areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$ such that every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be moved into $\Omega$ by a rotation
followed by a translation.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def lowerBoundWetzel1973 : Prop := (2194 : ℝ) / 10000 ≤ convexWormCoverConstant

/-- **Khandhawit–Sriswasdi 2009 lower bound for the convex worm cover constant (claim).** This
proposition asserts that $0.227498 \le \mu$, where $\mu$ is the convex worm cover constant: the
infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$ such that every
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be moved into $\Omega$
by a rotation followed by a translation.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def lowerBoundKhandhawitSriswasdi2009 : Prop :=
  (227498 : ℝ) / 1000000 ≤ convexWormCoverConstant

/-- **Khandhawit–Pagonakis–Sriswasdi 2013 lower bound on the convex worm cover constant (claim).**
This proposition asserts that $0.232239 \le \mu$, where $\mu$ is the convex worm cover constant:
the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$ such that every
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be moved into $\Omega$
by a rotation followed by a translation.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def lowerBoundKhandhawitPagonakisSriswasdi2013 : Prop :=
  (232239 : ℝ) / 1000000 ≤ convexWormCoverConstant

/-- **The minimal-convex-cover claim.** Call a nonempty convex set $\Omega \subseteq \mathbb{C}$ a
convex universal cover if every continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length
exactly $1$ can be moved into $\Omega$ by some rotation followed by a translation, and let the
convex worm cover constant be the infimum of the areas (Lebesgue measures) of all convex
universal covers, which is a finite real number. This is the proposition that some convex
universal cover has area equal to the convex worm cover constant.

Attainment of the minimum is a claim to be proved; it is not built into the definition of the
constant.

Source:
Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc adaptation.
-/
def minimalConvexCoverExists : Prop :=
  ∃ Ω : Set ℂ, IsConvexUniversalCover Ω ∧
    volume Ω = ENNReal.ofReal convexWormCoverConstant

/-- **The Norwood–Poole cover claim.** Call a nonempty set $\Omega \subseteq \mathbb{C}$ a
universal cover if every continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$
can be moved into $\Omega$ by some rotation followed by a translation. This is the proposition
that some universal cover has area (Lebesgue outer measure) at most $0.260437$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def nonconvexCoverNorwoodPoole2003 : Prop :=
  ∃ Ω : Set ℂ, IsUniversalCover Ω ∧ volume Ω ≤ ENNReal.ofReal ((2604370 : ℝ) / 10000000)

/-- **The Ploymaklam–Wichiramala cover claim.** Call a nonempty set $\Omega \subseteq \mathbb{C}$
a universal cover if every continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly
$1$ can be moved into $\Omega$ by some rotation followed by a translation. This is the
proposition that some universal cover has area (Lebesgue outer measure) at most $0.26007$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def nonconvexCoverPloymaklamWichiramala2018 : Prop :=
  ∃ Ω : Set ℂ, IsUniversalCover Ω ∧ volume Ω ≤ ENNReal.ofReal ((26007 : ℝ) / 100000)

/-- **Statement of the Norwood–Poole upper bound $0.260437$ for worm covers.** The proposition
that the nonconvex worm cover constant, the infimum of the areas (Lebesgue outer measures) of
planar sets containing a rotated and translated copy of every planar curve of length $1$, is at
most $0.260437$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def nonconvexUpperBoundNorwoodPoole2003 : Prop :=
  nonconvexWormCoverConstant ≤ (2604370 : ℝ) / 10000000

/-- **Statement of the Ploymaklam–Wichiramala upper bound $0.26007$ for worm covers.** The
proposition that the nonconvex worm cover constant, the infimum of the areas (Lebesgue outer
measures) of planar sets containing a rotated and translated copy of every planar curve of length
$1$, is at most $0.26007$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def nonconvexUpperBoundPloymaklamWichiramala2018 : Prop :=
  nonconvexWormCoverConstant ≤ (26007 : ℝ) / 100000

/-- **The positivity claim for the nonconvex worm cover constant.** Call a nonempty set
$\Omega \subseteq \mathbb{C}$ a universal cover if every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be moved into $\Omega$ by some rotation
followed by a translation, and let the nonconvex worm cover constant be the infimum of the areas
(Lebesgue outer measures) of all universal covers, which is a finite real number. This is the
proposition that the nonconvex worm cover constant is strictly positive.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def nonconvexStrictPositivity : Prop := 0 < nonconvexWormCoverConstant

/-- **The disk of diameter one covers every unit arc (claim).** This proposition asserts that
the closed disk $D = \{z \in \mathbb{C} : |z| \le 1/2\}$ covers every unit arc: for every
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ there are an angle
$\theta \in \mathbb{R}$ and a translation $c \in \mathbb{C}$ such that
$e^{i\theta}\gamma(t) + c \in D$ for every $t \in [0, 1]$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def halfDiskCovers : Prop := CoversEveryUnitArc halfDisk

/-- **The half-disk of diameter one covers every unit arc (claim).** This proposition asserts
that the closed half-disk $H = \{z \in \mathbb{C} : |z| \le 1/2,\ \operatorname{Im} z \ge 0\}$
covers every unit arc: for every continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length
exactly $1$ there are an angle $\theta \in \mathbb{R}$ and a translation $c \in \mathbb{C}$ such
that $e^{i\theta}\gamma(t) + c \in H$ for every $t \in [0, 1]$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def halfSemidiskCovers : Prop := CoversEveryUnitArc halfSemidisk

/-- **Wetzel's sector covering claim.** The proposition that the closed circular sector $S$ of
radius $1$ and angle $30^\circ$ with apex $0$ and symmetric about the positive real axis, that is,
the set of complex numbers $z$ with $|z| \le 1$, $\operatorname{Re} z \ge 0$ and
$|\operatorname{Im} z| \le \tan(\pi/12)\operatorname{Re} z$, covers every unit arc: for every
continuous curve $\gamma : [0,1] \to \mathbb{C}$ of length (total variation) exactly $1$ there are
an angle $\theta \in \mathbb{R}$ and a point $c \in \mathbb{C}$ such that
$e^{i\theta}\gamma(t) + c \in S$ for all $t \in [0,1]$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def wetzelSectorCovers : Prop := CoversEveryUnitArc wetzelSector

/-- **A Norwood–Poole cover bounds the nonconvex worm cover constant.** Call a nonempty set
$\Omega \subseteq \mathbb{C}$ a universal cover if every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be moved into $\Omega$ by some rotation
followed by a translation, and let the nonconvex worm cover constant be the infimum of the areas
(Lebesgue outer measures) of all universal covers, which is a finite real number. If some
universal cover has area at most $0.260437$, then the nonconvex worm cover constant is at most
$0.260437$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem nonconvexUpperBoundNorwoodPoole2003_of_cover
    (h : nonconvexCoverNorwoodPoole2003) : nonconvexUpperBoundNorwoodPoole2003 :=
  nonconvexUpperBound_of_cover (by norm_num) h

/-- **Covers of area at most $0.26007$ bound the nonconvex worm cover constant.** If some
nonempty planar set of area (Lebesgue outer measure) at most $0.26007$ contains a rotated and
translated copy of every planar curve of length $1$, then the nonconvex worm cover constant is at
most $0.26007$.

Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem nonconvexUpperBoundPloymaklamWichiramala2018_of_cover
    (h : nonconvexCoverPloymaklamWichiramala2018) :
    nonconvexUpperBoundPloymaklamWichiramala2018 :=
  nonconvexUpperBound_of_cover (by norm_num) h

/-- **The convex worm cover constant is at most π/4.** A unit arc is a continuous
curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover constant,
the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$ that contain,
for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by a translation,
is at most $\pi/4$.

Source: Optimization Problems, constant 13a, closed claim `upperBoundPiOverFour`.
-/
theorem_wanted upperBoundPiOverFour_holds : upperBoundPiOverFour

/-- **The convex worm cover constant is at most π/8.** A unit arc is a continuous
curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover constant,
the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$ that contain,
for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by a translation,
is at most $\pi/8$.

Source: Optimization Problems, constant 13a, closed claim `upperBoundPiOverEight`.
-/
theorem_wanted upperBoundPiOverEight_holds : upperBoundPiOverEight

/-- **The convex worm cover constant is at most 0.34501.** A unit arc is a continuous
curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover constant,
the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$ that contain,
for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by a translation,
is at most $0.34501$.

Source: Optimization Problems, constant 13a, closed claim `upperBoundWetzel1973`.
-/
theorem_wanted upperBoundWetzel1973_holds : upperBoundWetzel1973

/-- **Gerriets' upper bound for the convex worm cover constant.** Moser's convex worm cover
constant, the infimum of the areas of convex planar sets containing a rotated and translated copy
of every planar curve of length $1$, is at most $0.3214$.

Source: Optimization Problems, constant 13a, closed claim `upperBoundGerriets1972`. -/
theorem_wanted upperBoundGerriets1972_holds : upperBoundGerriets1972

/-- **Gerriets–Poole upper bound for the convex worm cover constant.** Moser's convex worm cover
constant, the infimum of the areas of convex planar sets containing a rotated and translated copy
of every planar curve of length $1$, is at most $0.2861$.

Source: Optimization Problems, constant 13a, closed claim `upperBoundGerrietsPoole1974`. -/
theorem_wanted upperBoundGerrietsPoole1974_holds : upperBoundGerrietsPoole1974

/-- **Norwood–Poole–Laidacker upper bound for the convex worm cover constant.** Moser's convex
worm cover constant, the infimum of the areas of convex planar sets containing a rotated and
translated copy of every planar curve of length $1$, is at most $0.27524$.

Source: Optimization Problems, constant 13a, closed claim
`upperBoundNorwoodPooleLaidacker1992`.
-/
theorem_wanted upperBoundNorwoodPooleLaidacker1992_holds : upperBoundNorwoodPooleLaidacker1992

/-- **The convex worm cover constant is at most 0.270911861.** A unit arc is a continuous
curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover constant,
the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$ that contain,
for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by a translation,
is at most $0.270911861$.

Source: Optimization Problems, constant 13a, closed claim `upperBoundWang2006`.
-/
theorem_wanted upperBoundWang2006_holds : upperBoundWang2006

/-- **The convex worm cover constant is at most π/12.** A unit arc is a continuous
curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$. The convex worm cover constant,
the infimum of the areas of the nonempty convex sets $\Omega \subseteq \mathbb{C}$ that contain,
for every unit arc $\gamma$, the image of $\gamma$ under some rotation followed by a translation,
is at most $\pi/12$.

Source: Optimization Problems, constant 13a, closed claim `upperBoundPiOverTwelve`.
-/
theorem_wanted upperBoundPiOverTwelve_holds : upperBoundPiOverTwelve

/-- **Wetzel's 1973 lower bound for the convex worm cover constant.** Let $\mu$ be the convex
worm cover constant, the infimum of the areas of the nonempty convex sets
$\Omega \subseteq \mathbb{C}$ such that every continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of
length exactly $1$ can be moved into $\Omega$ by a rotation followed by a translation. Then
$0.2194 \le \mu$.

Source: Optimization Problems, constant 13a, closed claim `lowerBoundWetzel1973`. -/
theorem_wanted lowerBoundWetzel1973_holds : lowerBoundWetzel1973

/-- **Khandhawit–Sriswasdi 2009 lower bound for the convex worm cover constant.** Let $\mu$ be
the convex worm cover constant, the infimum of the areas of the nonempty convex sets
$\Omega \subseteq \mathbb{C}$ such that every continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of
length exactly $1$ can be moved into $\Omega$ by a rotation followed by a translation. Then
$0.227498 \le \mu$.

Source: Optimization Problems, constant 13a, closed claim
`lowerBoundKhandhawitSriswasdi2009`.
-/
theorem_wanted lowerBoundKhandhawitSriswasdi2009_holds : lowerBoundKhandhawitSriswasdi2009

/-- **Khandhawit–Pagonakis–Sriswasdi 2013 lower bound on the convex worm cover constant.** Let
$\mu$ be the convex worm cover constant, the infimum of the areas of the nonempty convex sets
$\Omega \subseteq \mathbb{C}$ such that every continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of
length exactly $1$ can be moved into $\Omega$ by a rotation followed by a translation. Then
$0.232239 \le \mu$.

Source: Optimization Problems, constant 13a, closed claim
`lowerBoundKhandhawitPagonakisSriswasdi2013`.
-/
theorem_wanted lowerBoundKhandhawitPagonakisSriswasdi2013_holds :
    lowerBoundKhandhawitPagonakisSriswasdi2013

/-- **A minimal convex cover for unit arcs exists.** Call a nonempty convex set
$\Omega \subseteq \mathbb{C}$ a convex universal cover if every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be moved into $\Omega$ by some rotation
followed by a translation, and let the convex worm cover constant be the infimum of the areas
(Lebesgue measures) of all convex universal covers, which is a finite real number. Then some
convex universal cover has area equal to the convex worm cover constant.

Source: Optimization Problems, constant 13a, closed claim `minimalConvexCoverExists`.
-/
theorem_wanted minimalConvexCoverExists_holds : minimalConvexCoverExists

/-- **Norwood–Poole universal cover for unit arcs.** There is a nonempty set
$\Omega \subseteq \mathbb{C}$ of area (Lebesgue outer measure) at most $0.260437$ such that every
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be moved into $\Omega$
by some rotation followed by a translation.

Source: Optimization Problems, constant 13a, closed claim `nonconvexCoverNorwoodPoole2003`.
-/
theorem_wanted nonconvexCoverNorwoodPoole2003_holds : nonconvexCoverNorwoodPoole2003

/-- **Ploymaklam–Wichiramala universal cover for unit arcs.** There is a nonempty set
$\Omega \subseteq \mathbb{C}$ of area (Lebesgue outer measure) at most $0.26007$ such that every
continuous curve $\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be moved into $\Omega$
by some rotation followed by a translation.

Source: Optimization Problems, constant 13a, closed claim
`nonconvexCoverPloymaklamWichiramala2018`.
-/
theorem_wanted nonconvexCoverPloymaklamWichiramala2018_holds :
    nonconvexCoverPloymaklamWichiramala2018

/-- **Norwood–Poole upper bound for the nonconvex worm cover constant.** Call a nonempty set
$\Omega \subseteq \mathbb{C}$ a universal cover if every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be moved into $\Omega$ by some rotation
followed by a translation, and let the nonconvex worm cover constant be the infimum of the areas
(Lebesgue outer measures) of all universal covers, which is a finite real number. Then the
nonconvex worm cover constant is at most $0.260437$.

Source: Optimization Problems, constant 13a, closed claim
`nonconvexUpperBoundNorwoodPoole2003`.
-/
theorem_wanted nonconvexUpperBoundNorwoodPoole2003_holds : nonconvexUpperBoundNorwoodPoole2003

/-- **Ploymaklam–Wichiramala upper bound for the nonconvex worm cover constant.** The nonconvex
worm cover constant, the infimum of the areas (Lebesgue outer measures) of planar sets containing
a rotated and translated copy of every planar curve of length $1$, is at most $0.26007$.

Source: Optimization Problems, constant 13a, closed claim
`nonconvexUpperBoundPloymaklamWichiramala2018`.
-/
theorem_wanted nonconvexUpperBoundPloymaklamWichiramala2018_holds :
    nonconvexUpperBoundPloymaklamWichiramala2018

/-- **The nonconvex worm cover constant is positive.** Call a nonempty set
$\Omega \subseteq \mathbb{C}$ a universal cover if every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ can be moved into $\Omega$ by some rotation
followed by a translation, and let the nonconvex worm cover constant be the infimum of the areas
(Lebesgue outer measures) of all universal covers, which is a finite real number. Then the
nonconvex worm cover constant is strictly positive.

Source: Optimization Problems, constant 13a, closed claim `nonconvexStrictPositivity`.
-/
theorem_wanted nonconvexStrictPositivity_holds : nonconvexStrictPositivity

/-- **The disk of diameter one covers every unit arc.** For every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ there are an angle $\theta \in \mathbb{R}$
and a translation $c \in \mathbb{C}$ such that $|e^{i\theta}\gamma(t) + c| \le 1/2$ for every
$t \in [0, 1]$.

Source: Optimization Problems, constant 13a, closed claim `halfDiskCovers`. -/
theorem_wanted halfDiskCovers_holds : halfDiskCovers

/-- **The half-disk of diameter one covers every unit arc.** Let
$H = \{z \in \mathbb{C} : |z| \le 1/2,\ \operatorname{Im} z \ge 0\}$. For every continuous curve
$\gamma : [0, 1] \to \mathbb{C}$ of length exactly $1$ there are an angle $\theta \in \mathbb{R}$
and a translation $c \in \mathbb{C}$ such that $e^{i\theta}\gamma(t) + c \in H$ for every
$t \in [0, 1]$.

Source: Optimization Problems, constant 13a, closed claim `halfSemidiskCovers`. -/
theorem_wanted halfSemidiskCovers_holds : halfSemidiskCovers

/-- **Wetzel's sector covers every unit arc.** Let $S$ be the closed circular sector of radius $1$
and angle $30^\circ$ with apex $0$ and symmetric about the positive real axis, that is, the set of
complex numbers $z$ with $|z| \le 1$, $\operatorname{Re} z \ge 0$ and
$|\operatorname{Im} z| \le \tan(\pi/12)\operatorname{Re} z$. Then for every continuous curve
$\gamma : [0,1] \to \mathbb{C}$ of length (total variation) exactly $1$ there are an angle
$\theta \in \mathbb{R}$ and a point $c \in \mathbb{C}$ such that $e^{i\theta}\gamma(t) + c \in S$
for all $t \in [0,1]$.

Source: Optimization Problems, constant 13a, closed claim `wetzelSectorCovers`. -/
theorem_wanted wetzelSectorCovers_holds : wetzelSectorCovers

end MoserConvexWormCoverConstant
