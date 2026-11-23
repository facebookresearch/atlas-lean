/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two or infinitely many prime closed geodesics on an irreversible Finsler two-sphere

Burns and Matveev, *Open problems and questions about geodesics*, Conjecture 2.2.1 (Long, Bangert;
Problem 15 of Álvarez Paiva's list): every irreversible Finsler metric on `S²` has either exactly
two or infinitely many distinct prime closed geodesics. Cristofaro-Gardiner, Hryniewicz, Hutchings
and Liu proved it for every Finsler metric on `S²` (J. Amer. Math. Soc. 39 (2026), Corollary 1.4).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import MathlibExt.Geometry.Manifold.Finsler

@[expose] public section

namespace MathlibExt.Geometry.FinslerSphereTwoOrInfinityAMR149Problem0001Wanted

/-!
Source: K. Burns and V. S. Matveev, Open problems and questions about geodesics, Ergodic Theory
Dynam. Systems 41 (2021), 641-684 (arXiv:1308.5417), Section 2.2, Conjecture 2.2.1 (Long, Bangert,
Problem 15 of J. C. Álvarez Paiva, Some problems on Finsler geometry, 2006), stated right after
Bangert and Long's theorem that every irreversible Finsler metric on `S²` has at least two distinct
prime closed geodesics. UnsolvedMath record UM-00800921 (`AMR-149-0001`), dataset
ulamai/UnsolvedMath v1.8.0; the records `AIM-GEOMETRY-0207` and `AIM-GEOMETRY-0208` state the same
conjecture.

`S²` is the unit sphere of `ℝ³` with its standard smooth structure (charts modelled on `𝓡 2`): a
Hausdorff manifold without boundary, the setting in which the metric geodesics of
`MathlibExt.Geometry.Manifold.Finsler` are the geodesics of the smooth Finsler metric. A Finsler
metric is `Manifold.FinslerMetric (𝓡 2) S²` (`C^∞` off the zero section, positively homogeneous of
degree one, strongly convex, possibly irreversible), and irreversible means `¬ F.IsReversible`. A
closed geodesic is `F.IsClosedGeodesic` (a non-constant periodic curve `ℝ → S²` that near every
time realizes the forward Finsler distance at constant speed; forward, since `F` need not be
reversible).

Counting convention: closed geodesics are oriented curves up to orientation-preserving
reparametrization, as in the source, where Katok's irreversible metrics have exactly two prime
closed geodesics, one great circle traversed in the two directions. Every closed geodesic has a
unit-speed parametrization, unique up to a time shift `t ↦ t + s`; its iterates are the same map
`ℝ → S²`. So one class of unit-speed closed geodesics modulo time shifts is one prime closed
geodesic, and a closed geodesic and its reversal (when both are geodesics) are different classes.
The distinct prime closed geodesics of `F` are these classes, `primeClosedGeodesics F`; "exactly
two or infinitely many" is `ncard = 2` or infinite.
-/

open Manifold Set
open scoped Manifold

/-- The unit sphere `S²` of `ℝ³`, a smooth manifold modelled on `𝓡 2`. -/
abbrev TwoSphere : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- `δ` is a time shift of `γ`: `δ t = γ (t + s)` for some `s : ℝ` and all `t`. -/
def IsTimeShift {X : Type*} (γ δ : ℝ → X) : Prop :=
  ∃ s : ℝ, ∀ t, δ t = γ (t + s)

/-- The unit-speed closed geodesics `ℝ → S²` of a Finsler metric `F` on `S²`. -/
def unitSpeedClosedGeodesics (F : FinslerMetric (𝓡 2) TwoSphere) : Set (ℝ → TwoSphere) :=
  {γ | F.IsClosedGeodesic γ ∧ F.IsGeodesicOnWithSpeed γ univ 1}

/-- The distinct prime closed geodesics of `F`: classes of unit-speed closed geodesics modulo
time shifts. -/
def primeClosedGeodesics (F : FinslerMetric (𝓡 2) TwoSphere) :
    Set (Quot (@IsTimeShift TwoSphere)) :=
  Quot.mk _ '' unitSpeedClosedGeodesics F

/-- Burns–Matveev Conjecture 2.2.1: every irreversible Finsler metric `F` on `S²` has either
exactly two or infinitely many distinct prime closed geodesics. -/
def irreversibleTwoOrInfinitelyMany : Prop :=
  ∀ F : FinslerMetric (𝓡 2) TwoSphere, ¬ F.IsReversible →
    (primeClosedGeodesics F).ncard = 2 ∨ (primeClosedGeodesics F).Infinite

/--
Resolved true: every Finsler metric on `S²`, reversible or not, has either two or infinitely many
prime closed geodesics (Cristofaro-Gardiner, Hryniewicz, Hutchings and Liu, Corollary 1.4, which
cites Álvarez Paiva's Problem 15 and Burns–Matveev's Conjecture 2.2.1; their Remark 1.5 calls it the
longstanding conjecture that every irreversible Finsler metric on `S²` has either two or infinitely
many prime closed geodesics). In their proof the prime closed geodesics correspond bijectively to
the simple Reeb orbits of a contact form on the unit tangent bundle, i.e. to the periodic orbits of
the geodesic flow, which are the classes of unit-speed closed geodesics modulo time shifts counted
here. Source: K. Burns and V. S. Matveev, Open problems and questions about geodesics, Ergodic
Theory Dynam. Systems 41 (2021), 641-684, Conjecture 2.2.1; resolution: D. Cristofaro-Gardiner,
U. Hryniewicz, M. Hutchings and H. Liu, Proof of Hofer-Wysocki-Zehnder's two or infinity
conjecture, J. Amer. Math. Soc. 39 (2026), no. 4, 915-983 (published online 2026-06-23;
arXiv:2310.07636v2), Corollary 1.4 and Remark 1.5, https://doi.org/10.1090/jams/1072.
-/
public theorem_wanted irreversibleTwoOrInfinitelyMany_holds : irreversibleTwoOrInfinitelyMany

end MathlibExt.Geometry.FinslerSphereTwoOrInfinityAMR149Problem0001Wanted
