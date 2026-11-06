/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared Conway knot stack

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This neutral helper module is shared by the Piccirillo and
Conway-topologically-slice wanted entries, so both theorems speak about
the same `PLKnot` type and the same concrete `conwayKnot`. The
definitions are the trusted (non-hole) helpers from leanprover/lean-eval
at commit 38361be884302c7edce1908c4aef8296eb2cb27e (modules
`LeanEval.KnotTheory.ConwayKnot`, `LeanEval.KnotTheory.Piccirillo`, and
`LeanEval.Topology.ConwayTopologicallySlice`), distributed under the
Apache License, Version 2.0; unchanged apart from the namespace.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace MathlibExt.Topology.ConwayKnotShared

namespace KnotTheory

/-!
# Smooth knots, links, ambient isotopy, and chirality

Minimal definitions to support the three knot-theory benchmark problems
(`Linking`, `NonIsotopicKnots`, `Chiral`). Mathlib has essentially no knot
theory, so we set up just enough infrastructure to state the questions
faithfully in terms of smooth maps `S¹ → ℝ³` and ambient isotopies of `ℝ³`.

A *knot* is a smooth, 2π-periodic, injective immersion `ℝ → ℝ³`. A
*two-component link* is a pair of knots with disjoint images. An *ambient
isotopy* is a smooth one-parameter family of diffeomorphisms of `ℝ³`
starting at the identity, presented here as a forward map and an inverse
map jointly smooth in `(t, x)`.

The parametrization is part of the data, so each knot or link component
comes with an orientation induced from the standard orientation on `S¹`.
Accordingly, isotopy is understood in the oriented sense: an ambient isotopy
must carry the parametrized components of the source to those of the target,
up to orientation-preserving reparametrization of the source circle. A knot
is *chiral* here in this same orientation-sensitive sense: it is not isotopic
to its mirror image (under reflection through the `xy`-plane).

These definitions trade some Mathlib idiomaticity for being self-contained
and easy to read; in particular, we do not go through `Diffeomorph` or
`ContMDiff` on a manifold structure for `ℝ³`, since `ContDiff ℝ ⊤` over the
ambient normed space says exactly what we need.
-/

/-- **Euclidean space $\mathbb{R}^3$.** The ambient space of the knots here is $\mathbb{R}^3$ with
its standard Euclidean inner product. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- **Oriented smooth knot.** An oriented smooth knot in $\mathbb{R}^3$ is a smooth map
$\gamma : \mathbb{R} \to \mathbb{R}^3$ that is $2\pi$-periodic, injective on $[0, 2\pi)$, and an
immersion, meaning $\gamma'(t) \ne 0$ for every real $t$. The orientation is the one induced by
the parametrization. -/
structure Knot where
  /-- The parametrizing map. -/
  curve : ℝ → R3
  /-- The map is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) curve
  /-- The map has period `2π`. -/
  periodic : ∀ t, curve (t + 2 * Real.pi) = curve t
  /-- The map is injective on a fundamental period. -/
  injOn : Set.InjOn curve (Set.Ico 0 (2 * Real.pi))
  /-- The map is an immersion (its derivative is everywhere nonzero). -/
  immersion : ∀ t, deriv curve t ≠ 0

/-- **Two-component link.** An oriented two-component smooth link in $\mathbb{R}^3$ is a pair
$(K, L)$ of oriented smooth knots whose images in $\mathbb{R}^3$ are disjoint. -/
structure TwoLink where
  /-- The first component. -/
  K : Knot
  /-- The second component. -/
  L : Knot
  /-- The two components have disjoint images in `ℝ³`. -/
  disjoint : Disjoint (Set.range K.curve) (Set.range L.curve)

/-- **Smooth ambient isotopy of $\mathbb{R}^3$.** A smooth ambient isotopy of $\mathbb{R}^3$
consists of two families of maps $H_t, G_t \colon \mathbb{R}^3 \to \mathbb{R}^3$ indexed by
$t \in \mathbb{R}$ such that $(t, x) \mapsto H_t(x)$ and $(t, x) \mapsto G_t(x)$ are smooth
($C^\infty$) maps $\mathbb{R} \times \mathbb{R}^3 \to \mathbb{R}^3$, $G_t$ is a two-sided inverse
of $H_t$ for every $t$, and $H_0$ is the identity. In particular every $H_t$ is a
diffeomorphism of $\mathbb{R}^3$. -/
structure AmbientIsotopy where
  /-- The forward family. -/
  H : ℝ → R3 → R3
  /-- The inverse family. -/
  Hinv : ℝ → R3 → R3
  /-- The forward family is jointly smooth in `(t, x)`. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H)
  /-- The inverse family is jointly smooth in `(t, x)`. -/
  smooth_inv : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry Hinv)
  /-- `Hinv t` is a left inverse of `H t`. -/
  inv_left : ∀ t x, Hinv t (H t x) = x
  /-- `Hinv t` is a right inverse of `H t`. -/
  inv_right : ∀ t x, H t (Hinv t x) = x
  /-- The isotopy starts at the identity. -/
  start : H 0 = id

structure CircleReparam where
  /-- A lift `ℝ → ℝ` of a circle self-map. -/
  f : ℝ → ℝ
  /-- A lifted inverse. -/
  finv : ℝ → ℝ
  /-- The lift is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  /-- The inverse lift is smooth. -/
  smooth_inv : ContDiff ℝ (⊤ : ℕ∞) finv
  /-- `finv` is a left inverse to `f`. -/
  left_inv : ∀ t, finv (f t) = t
  /-- `finv` is a right inverse to `f`. -/
  right_inv : ∀ t, f (finv t) = t
  /-- The lift descends to a map of `S¹ = ℝ / 2πℤ`. -/
  periodic : ∀ t, f (t + 2 * Real.pi) = f t + 2 * Real.pi
  /-- The inverse lift also descends to `S¹`. -/
  periodic_inv : ∀ t, finv (t + 2 * Real.pi) = finv t + 2 * Real.pi
  /-- The induced circle map preserves orientation. -/
  mono : StrictMono f

/-- **Ambient isotopy of oriented knots.** Let $K_1$ and $K_2$ be oriented knots, each given by
its $2\pi$-periodic parametrization. They are ambient-isotopic if there are a smooth ambient
isotopy $(\Phi_t)_{t \in \mathbb{R}}$ of $\mathbb{R}^3$ and an orientation-preserving smooth
reparametrization $\sigma$ of the circle such that $\Phi_1(K_1(t)) = K_2(\sigma(t))$ for every real
$t$. Here an orientation-preserving smooth reparametrization of the circle is a smooth, strictly
increasing bijection $\sigma : \mathbb{R} \to \mathbb{R}$ with smooth inverse such that
$\sigma(t + 2\pi) = \sigma(t) + 2\pi$ for every $t$. -/
def Knot.Isotopic (K₁ K₂ : Knot) : Prop :=
  ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam, ∀ t, Φ.H 1 (K₁.curve t) = K₂.curve (σ.f t)

/-- **Ambient isotopy of oriented two-component links.** Let $L = (K, J)$ and $L' = (K', J')$ be
oriented two-component links, each knot given by its $2\pi$-periodic parametrization. Then $L$
and $L'$ are ambient-isotopic if there are a smooth ambient isotopy $(\Phi_t)_{t \in \mathbb{R}}$
of $\mathbb{R}^3$ and orientation-preserving smooth reparametrizations $\sigma$, $\tau$ of the
circle such that $\Phi_1(K(t)) = K'(\sigma(t))$ and $\Phi_1(J(t)) = J'(\tau(t))$ for every real
$t$. Here an orientation-preserving smooth reparametrization of the circle is a smooth, strictly
increasing bijection $\sigma : \mathbb{R} \to \mathbb{R}$ with smooth inverse such that
$\sigma(t + 2\pi) = \sigma(t) + 2\pi$ for every $t$. -/
def TwoLink.Isotopic (L₁ L₂ : TwoLink) : Prop :=
  ∃ Φ : AmbientIsotopy, ∃ σ τ : CircleReparam,
    (∀ t, Φ.H 1 (L₁.K.curve t) = L₂.K.curve (σ.f t)) ∧
    (∀ t, Φ.H 1 (L₁.L.curve t) = L₂.L.curve (τ.f t))

/-- **Reflection in the $xy$-plane.** The reflection of $\mathbb{R}^3$ through the $xy$-plane is
the map $(x, y, z) \mapsto (x, y, -z)$. -/
def reflectZ (p : R3) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 => if i = 2 then -p.ofLp i else p.ofLp i)

/-- **Chiral knot.** Let $K \colon \mathbb{R} \to \mathbb{R}^3$ be an oriented smooth knot, and
let $\rho(x, y, z) = (x, y, -z)$ be the reflection of $\mathbb{R}^3$ through the $xy$-plane.
Call $\sigma \colon \mathbb{R} \to \mathbb{R}$ an orientation-preserving reparametrization of
the circle if it is a strictly increasing smooth bijection with smooth inverse satisfying
$\sigma(t + 2\pi) = \sigma(t) + 2\pi$ for all $t \in \mathbb{R}$, that is, the lift of an
orientation-preserving diffeomorphism of $\mathbb{R} / 2\pi\mathbb{Z}$. The knot $K$ is chiral
if there is no smooth ambient isotopy $(H_t)$ of $\mathbb{R}^3$ together with such a $\sigma$
satisfying $H_1(K(t)) = \rho(K(\sigma(t)))$ for all $t \in \mathbb{R}$. Equivalently, $K$ is
not ambient isotopic, as an oriented knot, to its mirror image $\rho \circ K$. -/
def Knot.Chiral (K : Knot) : Prop :=
  ¬ ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
    ∀ t, Φ.H 1 (K.curve t) = reflectZ (K.curve (σ.f t))

end KnotTheory

namespace KnotTheory

/-!
# Slice-ness in the smooth `Knot` world, bridged to `PLKnot`

Slice-ness, both smooth and topological, lives most naturally on the smooth
`Knot` of `Prelude`: a smooth knot's image is a smooth `1`-submanifold of
`ℝ³`, so a smooth properly embedded `2`-disk whose smooth boundary lies on
the floor `ℝ³ × {0}` matches the knot image *as a set* without any corner
pathology.

For specific named knots, however, we prefer the PL world: a `PLKnot` is a
concrete `List R3` of polyline vertices, easy to write down for, e.g., the
Conway knot. To state Piccirillo's theorem about the *Conway knot type*, we
bridge: a PL knot is (smoothly / topologically) slice if it has a smooth
representative of the same knot type which is (smoothly / topologically)
slice in the standard smooth sense. "Same knot type" is encoded as
topological ambient isotopy of subsets of `ℝ³`; for tame knots — and PL
polylines are tame — this is classically equivalent to the smooth/PL knot
type relation.
-/

/-! ## Topological ambient isotopy of subsets of `ℝ³` -/

/-- **Topological ambient isotopy.** A topological ambient isotopy of $\mathbb{R}^3$ is a family of
maps $H_t : \mathbb{R}^3 \to \mathbb{R}^3$, indexed by $t \in \mathbb{R}$, together with a family
$G_t : \mathbb{R}^3 \to \mathbb{R}^3$ such that $(t, x) \mapsto H_t(x)$ and $(t, x) \mapsto G_t(x)$
are continuous, $G_t$ is a two-sided inverse of $H_t$ for every $t$ (so each $H_t$ is a
homeomorphism of $\mathbb{R}^3$), and $H_0$ is the identity.

The time domain is all of $\mathbb{R}$, but only $H_0$ and $H_1$ matter for the isotopy
relation. -/
structure TopAmbientIsotopy where
  /-- The forward family. -/
  H : ℝ → R3 → R3
  /-- The inverse family. -/
  Hinv : ℝ → R3 → R3
  /-- The forward family is jointly continuous in `(t, x)`. -/
  continuous : Continuous (Function.uncurry H)
  /-- The inverse family is jointly continuous in `(t, x)`. -/
  continuous_inv : Continuous (Function.uncurry Hinv)
  /-- `Hinv t` is a left inverse of `H t`. -/
  inv_left : ∀ t x, Hinv t (H t x) = x
  /-- `Hinv t` is a right inverse of `H t`. -/
  inv_right : ∀ t x, H t (Hinv t x) = x
  /-- The isotopy starts at the identity. -/
  start : H 0 = id

/-- **Topological ambient isotopy of subsets.** Two subsets $A$ and $B$ of $\mathbb{R}^3$ are
unoriented topologically ambient isotopic if there is a topological ambient isotopy $(H_t)$ of
$\mathbb{R}^3$ whose time-one map carries $A$ onto $B$, that is, $H_1(A) = B$.

"Unoriented" because this is a set-level relation that forgets any parametrization. -/
def Set.UnorientedTopAmbIsotopic (A B : Set R3) : Prop :=
  ∃ Φ : TopAmbientIsotopy, Φ.H 1 '' A = B

/-! ## The closed `2`-disk, unit circle, half-space, and model planes -/

/-- **Closed unit disk in the plane.** The closed unit Euclidean disk
$\{(x, y) \in \mathbb{R} \times \mathbb{R} \mid x^2 + y^2 \le 1\}$, the source of the
parametrization of a slicing disk.

The disk and its boundary circle are written out by the equations $x^2 + y^2 \le 1$ and
$x^2 + y^2 = 1$ rather than as the closed unit ball and unit sphere of $\mathbb{R} \times
\mathbb{R}$. The product carries the sup norm, so that ball would be the square $[-1, 1]^2$ and
that sphere its boundary, which has corners. At a corner, no smooth map with injective
derivative can match a corner-free smooth knot as its boundary, so slice disks parametrized by
the square cannot exist, and every knot would fail to be smoothly slice. -/
abbrev disk2 : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

/-- **Unit circle in the plane.** The unit Euclidean circle
$\{(x, y) \in \mathbb{R} \times \mathbb{R} \mid x^2 + y^2 = 1\}$, the source of the boundary of
a slicing disk. -/
abbrev circle1 : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- **Closed upper half-space.** The closed upper half-space in $\mathbb{R}^3 \times \mathbb{R}$
is the set $\mathbb{R}^3 \times [0, \infty)$ of points $(x, s)$ with $s \ge 0$.

We identify $\mathbb{R}^3 \times [0, \infty)$ with $B^4 \setminus \{\mathrm{pt}\}$, so slice
disks live here. -/
def upperHalf : Set (R3 × ℝ) := { q | 0 ≤ q.2 }

/-- **Model interior $2$-plane.** The model interior $2$-plane in $\mathbb{R}^3 \times \mathbb{R}$
is the set of points $((x_1, x_2, x_3), t)$ with $x_2 = x_3 = 0$, where $x_1$ and $t$ are
arbitrary. It is the local model for interior local flatness of an embedded $2$-disk. -/
def modelPlane2 : Set (R3 × ℝ) := { q | q.1 1 = 0 ∧ q.1 2 = 0 }

/-- **Model half-plane.** The model half-plane is the set of pairs $((p_1, p_2, p_3), s)$ in
$\mathbb{R}^3 \times \mathbb{R}$ with $p_2 = p_3 = 0$ and $s \ge 0$. It is a copy of the closed
half-plane $\mathbb{R} \times [0, \infty)$, with coordinates $p_1$ and $s$, lying in the upper
half-space $s \ge 0$.

It is the local model for boundary local flatness of a properly embedded disk. -/
def modelHalfPlane2 : Set (R3 × ℝ) := { q | q.1 1 = 0 ∧ q.1 2 = 0 ∧ 0 ≤ q.2 }

/-! ## Smooth slice-ness on a smooth `Knot`

A smooth knot `K` is smoothly slice if its image bounds a smooth properly
embedded `2`-disk in the upper half-space `ℝ³ × [0, ∞)`. Because `K`'s
image is a smooth `1`-submanifold, set-level boundary equality with the
disk's smooth boundary image works cleanly.
-/

/-- **Smoothly slice (smooth knot version).** Let
$\Delta = \{(x, y) \in \mathbb{R}^2 : x^2 + y^2 \le 1\}$ be the closed unit disk and
$C = \{(x, y) \in \mathbb{R}^2 : x^2 + y^2 = 1\}$ its boundary circle. A smooth knot $K$ is
smoothly slice if there is a smooth ($C^\infty$) map $f : \mathbb{R}^2 \to \mathbb{R}^3 \times
\mathbb{R}$ such that $f$ is injective on $\Delta$; for every $p \in \Delta$ the last coordinate
of $f(p)$ is nonnegative, and it is $0$ exactly when $p \in C$; the derivative of $f$ at every
point of $\Delta$ is injective; and the image of $C$ under the $\mathbb{R}^3$-component of $f$
is the image of $K$. -/
def Knot.SmoothlySlice (K : Knot) : Prop :=
  ∃ D : ℝ × ℝ → R3 × ℝ,
    ContDiff ℝ (⊤ : ℕ∞) D ∧
    Set.InjOn D disk2 ∧
    (∀ p ∈ disk2, 0 ≤ (D p).2) ∧
    (∀ p ∈ disk2, (D p).2 = 0 ↔ p ∈ circle1) ∧
    (∀ p ∈ disk2, Function.Injective (fderiv ℝ D p)) ∧
    (fun p => (D p).1) '' circle1 = Set.range K.curve

/-! ## Topological slice-ness on a smooth `Knot`

Topological sliceness requires a *locally flat* topological proper embedding
of the disk. Local flatness is encoded by `PartialHomeomorph` of `ℝ³ × ℝ`:
at every disk point, a partial homeomorphism whose source is an open
neighborhood of that point carries the disk image locally onto the model
`2`-plane (interior case) or model half-plane in the half-space (boundary
case). The boundary case is essential: a chart on all of `ℝ⁴` to a full
plane does not encode proper boundary behaviour at points where the disk
meets `ℝ³ × {0}`.
-/

/-- **Local flatness at an interior point.** Let $q \in \mathbb{R}^3 \times \mathbb{R}$ and
$D : \mathbb{R}^2 \to \mathbb{R}^3 \times \mathbb{R}$. Write $\Delta = \{(x, y) : x^2 + y^2 \le 1\}$
for the closed unit disk and $P = \{((p_1, p_2, p_3), s) : p_2 = p_3 = 0\}$ for the model plane.
The image $D(\Delta)$ is locally flat at $q$ in the interior sense if there is a homeomorphism
$h : U \to V$ between open subsets $U$, $V$ of $\mathbb{R}^3 \times \mathbb{R}$ such that $q \in U$
and $h(U \cap D(\Delta)) = V \cap P$. -/
def IsLocallyFlatInterior (D : ℝ × ℝ → R3 × ℝ) (q : R3 × ℝ) : Prop :=
  ∃ h : OpenPartialHomeomorph (R3 × ℝ) (R3 × ℝ),
    q ∈ h.source ∧
    h.toFun '' (h.source ∩ D '' disk2) = h.target ∩ modelPlane2

/-- **Local flatness at a boundary point.** Let $q \in \mathbb{R}^3 \times \mathbb{R}$ and
$D : \mathbb{R}^2 \to \mathbb{R}^3 \times \mathbb{R}$. Write $\Delta = \{(x, y) : x^2 + y^2 \le 1\}$
for the closed unit disk, $H = \{(p, s) : s \ge 0\}$ for the closed upper half-space, and
$P = \{((p_1, p_2, p_3), s) : p_2 = p_3 = 0,\ s \ge 0\}$ for the model half-plane. The image
$D(\Delta)$ is locally flat at $q$ in the boundary sense if there is a homeomorphism $h : U \to V$
between open subsets $U$, $V$ of $\mathbb{R}^3 \times \mathbb{R}$ such that $q \in U$,
$h(U \cap H) = V \cap H$ and $h(U \cap D(\Delta)) = V \cap P$.

The chart is open in $\mathbb{R}^3 \times \mathbb{R}$ rather than in $H$: when the last coordinate
of $q$ is $0$, every open neighbourhood of $q$ leaves $H$. -/
def IsLocallyFlatBoundary (D : ℝ × ℝ → R3 × ℝ) (q : R3 × ℝ) : Prop :=
  ∃ h : OpenPartialHomeomorph (R3 × ℝ) (R3 × ℝ),
    q ∈ h.source ∧
    h.toFun '' (h.source ∩ upperHalf) = h.target ∩ upperHalf ∧
    h.toFun '' (h.source ∩ D '' disk2) = h.target ∩ modelHalfPlane2

/-- **Topologically slice (smooth knot version).** Write points of $\mathbb{R}^3 \times \mathbb{R}$
as $(x, s)$ with $x = (x_1, x_2, x_3)$. Let $H = \{(x, s) : s \ge 0\}$ be the closed upper
half-space, $P = \{(x, s) : x_2 = x_3 = 0\}$ the model plane and $P_+ = P \cap H$ the model
half-plane, and let $D^2 = \{(a, b) \in \mathbb{R}^2 : a^2 + b^2 \le 1\}$ and
$S^1 = \{(a, b) \in \mathbb{R}^2 : a^2 + b^2 = 1\}$. A smooth knot $K$ is topologically slice if
there is a continuous map $D : \mathbb{R}^2 \to \mathbb{R}^3 \times \mathbb{R}$, injective on
$D^2$, such that: for every $p \in D^2$ the last coordinate of $D(p)$ is nonnegative, and it is
$0$ exactly when $p \in S^1$; for every $p \in D^2 \setminus S^1$ there is a homeomorphism
$h : U \to V$ between open subsets of $\mathbb{R}^3 \times \mathbb{R}$ with $D(p) \in U$ and
$h(U \cap D(D^2)) = V \cap P$; for every $p \in S^1$ there is such a homeomorphism with
$D(p) \in U$, $h(U \cap H) = V \cap H$ and $h(U \cap D(D^2)) = V \cap P_+$; and the image of
$S^1$ under the $\mathbb{R}^3$-component of $D$ is the image of $K$. -/
def Knot.TopologicallySlice (K : Knot) : Prop :=
  ∃ D : ℝ × ℝ → R3 × ℝ,
    Continuous D ∧
    Set.InjOn D disk2 ∧
    (∀ p ∈ disk2, 0 ≤ (D p).2) ∧
    (∀ p ∈ disk2, (D p).2 = 0 ↔ p ∈ circle1) ∧
    (∀ p ∈ disk2 \ circle1, IsLocallyFlatInterior D (D p)) ∧
    (∀ p ∈ circle1, IsLocallyFlatBoundary D (D p)) ∧
    (fun p => (D p).1) '' circle1 = Set.range K.curve

/-! ## Piecewise-linear knots -/

/-- **Parametrization of a closed polyline.** Let $v_0, \dots, v_{n-1}$ be a list of $n \ge 1$
points of $\mathbb{R}^3$. The polyline curve is the $n$-periodic map
$\gamma : \mathbb{R} \to \mathbb{R}^3$ with $\gamma(k + \alpha) = (1 - \alpha) v_k + \alpha v_{k+1}$
for integers $0 \le k < n$ and reals $0 \le \alpha < 1$, where indices are taken modulo $n$ (so
$v_n = v_0$). For the empty list the curve is constantly $0$. -/
noncomputable def plCurve (vertices : List R3) (t : ℝ) : R3 :=
  if h : vertices.length = 0 then 0
  else
    let n : ℕ := vertices.length
    let s : ℝ := t - (n : ℝ) * Int.floor (t / (n : ℝ))
    let k : ℕ := (Int.floor s).toNat
    let α : ℝ := s - k
    (1 - α) • vertices[k % n]'(Nat.mod_lt _ (Nat.pos_of_ne_zero h)) +
      α • vertices[(k + 1) % n]'(Nat.mod_lt _ (Nat.pos_of_ne_zero h))

/-- **PL knot (closed polyline).** A PL knot is a list $v_0, \dots, v_{n-1}$ of points of
$\mathbb{R}^3$ with $n \ge 3$, viewed as the vertices, in order, of the closed polyline with edges
from $v_i$ to $v_{i+1}$ for $i < n - 1$ and from $v_{n-1}$ back to $v_0$.

Simplicity of the polyline (that it is an embedded closed curve) is not part of the data; it is
imposed as a separate condition. -/
structure PLKnot where
  /-- The ordered list of polyline vertices. -/
  vertices : List R3
  /-- A closed polyline needs at least three vertices to be non-degenerate. -/
  three_le : 3 ≤ vertices.length

/-- **Image of a PL knot.** Let $K$ be a PL knot with vertices $v_0, \dots, v_{n-1}$. Its image is
the subset of $\mathbb{R}^3$ traced by the closed polyline through these vertices: the image of the
half-open interval $[0, n)$ under the parametrization that sends $k + \alpha$, for an integer
$0 \le k < n$ and a real $0 \le \alpha < 1$, to $(1 - \alpha) v_k + \alpha v_{k+1}$, with indices
taken modulo $n$. -/
def PLKnot.image (K : PLKnot) : Set R3 :=
  plCurve K.vertices '' Set.Ico (0 : ℝ) (K.vertices.length : ℝ)

/-- **Simple PL knot.** A PL knot $K$ with vertices $v_0, \dots, v_{n-1}$ is simple if its closed
polyline parametrization, which sends $k + \alpha$, for an integer $0 \le k < n$ and a real
$0 \le \alpha < 1$, to $(1 - \alpha) v_k + \alpha v_{k+1}$ (indices modulo $n$), is injective on
the half-open interval $[0, n)$.

Equivalently, the polyline is a simple closed curve: all vertices are distinct, non-adjacent
edges are disjoint, and adjacent edges meet only at their shared vertex. -/
def PLKnot.IsSimple (K : PLKnot) : Prop :=
  ∀ s t : ℝ,
    s ∈ Set.Ico (0 : ℝ) (K.vertices.length : ℝ) →
    t ∈ Set.Ico (0 : ℝ) (K.vertices.length : ℝ) →
    plCurve K.vertices s = plCurve K.vertices t →
    s = t

/-! ## Bridge to smooth slice-ness via a smooth knot representative

The standard fact (PL = smooth = tame in dimension 3) underlies these
definitions: every PL knot has a smooth knot ambient-isotopic to it, and
the converse holds for tame smooth knots. We do not formalize that fact,
but our `PLKnot.SmoothlySlice` and `PLKnot.TopologicallySlice` admit
honest witnesses precisely when the PL polyline represents a slice
knot type in the standard sense.
-/

/-- **Smooth representative of a PL knot.** A smooth knot $J$ is a smooth representative of
the piecewise-linear knot $K$ if the image of $J$ and the image of $K$ are unoriented
topologically ambient isotopic in $\mathbb{R}^3$: some topological ambient isotopy $(H_t)$ of
$\mathbb{R}^3$ satisfies $H_1(\operatorname{im} J) = \operatorname{im} K$.

When the polyline $K$ is simple, both curves are tame, and this agrees with the usual relation
of having the same smooth/PL knot type. -/
def PLKnot.HasSmoothRepresentative (K : PLKnot) (J : Knot) : Prop :=
  Set.UnorientedTopAmbIsotopic (Set.range J.curve) K.image

/-- **Smoothly slice (PL knot version).** A PL knot $K$ is smoothly slice if there is a smooth
knot $J$ that is smoothly slice and is a smooth representative of $K$: for some topological
ambient isotopy $(H_t)$ of $\mathbb{R}^3$, the map $H_1$ carries the image of $J$ onto the image
(trace) of the polyline $K$.

Piccirillo's theorem that the Conway knot is not smoothly slice is stated with this notion. -/
def PLKnot.SmoothlySlice (K : PLKnot) : Prop :=
  ∃ J : Knot, K.HasSmoothRepresentative J ∧ J.SmoothlySlice

/-- **Topologically slice (PL knot version).** A PL knot $K$ is topologically slice if there is a
smooth knot $J$ that is a smooth representative of $K$, meaning that the image of $J$ and the image
of $K$ are unoriented topologically ambient isotopic subsets of $\mathbb{R}^3$, and such that $J$
is topologically slice as a smooth knot. -/
def PLKnot.TopologicallySlice (K : PLKnot) : Prop :=
  ∃ J : Knot, K.HasSmoothRepresentative J ∧ J.TopologicallySlice

end KnotTheory

namespace KnotTheory

/-!
# PL closure of a braid word

For `n : ℕ` and `word : List ℤ` interpreted as a braid word on `n` strands
(`+i` is the generator `σ_i`, the crossing of strand `i` over strand
`i + 1`; `-i` is `σ_i⁻¹`), `braidClosure n word` produces the vertex list
of the *Markov closure* traced as a single polyline component starting at
strand position `1`. For braid words whose closure is a knot, this traces
the entire knot; for multi-component link closures it traces only the
component containing position `1`.

Coordinate layout. Strands sit at integer `x`-positions `1, …, n`. The
braid box spans `z ∈ [-word.length, 0]`, one unit of `z`-depth per
crossing. Over-strands lift to `y = 1`, under-strands stay at `y = 0`,
designed so that the two strands of any crossing are `y`-separated.
Closure arcs swing through `y = 100`, well outside the braid box.

The layout *intends* to produce a simple polyline, but simplicity is not
proved here; it is a separate obligation, expressed by `PLKnot.IsSimple`
and discharged where needed (e.g. the `conwayKnot_isSimple` benchmark
hole). The function is silent on invalid input — `|w| = 0` or `|w| ≥ n`
— and produces garbage in those cases.
-/

namespace BraidClosure

/-- **Point from three coordinates.** For real numbers $x$, $y$, $z$, this is the point
$(x, y, z)$ of the Euclidean space $\mathbb{R}^3$. -/
noncomputable def mkR3 (x y z : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then x else if i.val = 1 then y else z)

/-- **Braid closure traversal state.** A traversal state for tracing the closure of a braid
consists of the current strand position, a natural number, and the list of points of
$\mathbb{R}^3$ accumulated so far, in order, as vertices of the polyline. -/
structure State where
  /-- Current strand `x`-position. -/
  pos : ℕ
  /-- Polyline vertices accumulated so far, in order. -/
  vertices : List R3

/-- **Tracing a strand through one crossing.** Let a traversal state consist of a current
strand position $p \in \mathbb{N}$ and a list of vertices in $\mathbb{R}^3$, let
$w \in \mathbb{Z}$ be a braid generator with $i = |w|$, and let
$z_{\mathrm{top}}, z_{\mathrm{bot}} \in \mathbb{R}$. Put
$z_{\mathrm{hi}} = z_{\mathrm{top}} - (z_{\mathrm{top}} - z_{\mathrm{bot}})/4$ and
$z_{\mathrm{lo}} = z_{\mathrm{bot}} + (z_{\mathrm{top}} - z_{\mathrm{bot}})/4$. The new state is
obtained by changing the position and appending the listed points, in order, to the vertex
list. If $p = i$ and $w > 0$, the new position is $i + 1$ and the points are
$(i, 1, z_{\mathrm{hi}})$, $(i + 1, 1, z_{\mathrm{lo}})$, $(i + 1, 0, z_{\mathrm{bot}})$. If
$p = i$ and $w \le 0$, the new position is $i + 1$ and the only point is
$(i + 1, 0, z_{\mathrm{bot}})$. If $p = i + 1$ and $w > 0$, the new position is $i$ and the
only point is $(i, 0, z_{\mathrm{bot}})$. If $p = i + 1$ and $w \le 0$, the new position is
$i$ and the points are $(i + 1, 1, z_{\mathrm{hi}})$, $(i, 1, z_{\mathrm{lo}})$,
$(i, 0, z_{\mathrm{bot}})$. Otherwise the position stays $p$ and the only point is
$(p, 0, z_{\mathrm{bot}})$.

The step is meant for $z_{\mathrm{bot}} < z_{\mathrm{top}}$, with the crossing in the slab
between these heights: the strand passing over is lifted to $y = 1$, and the strand passing
under stays at $y = 0$. -/
noncomputable def applyCrossing (state : State) (w : ℤ) (zTop zBot : ℝ) : State :=
  let i : ℕ := w.natAbs
  let p : ℕ := state.pos
  let zMidHi : ℝ := zTop - (zTop - zBot) / 4
  let zMidLo : ℝ := zBot + (zTop - zBot) / 4
  if p = i then
    -- We are at the lower-index strand of the crossing; we swap to position `i + 1`.
    if 0 < w then
      -- σ_i: lower strand goes OVER. Lift to `y = 1`, swap, drop.
      { pos := i + 1
        vertices := state.vertices ++
          [ mkR3 (i : ℝ) 1 zMidHi,
            mkR3 ((i + 1 : ℕ) : ℝ) 1 zMidLo,
            mkR3 ((i + 1 : ℕ) : ℝ) 0 zBot ] }
    else
      -- σ_i⁻¹: lower strand goes UNDER. Stay at `y = 0`, swap.
      { pos := i + 1
        vertices := state.vertices ++ [ mkR3 ((i + 1 : ℕ) : ℝ) 0 zBot ] }
  else if p = i + 1 then
    -- We are at the upper-index strand of the crossing; we swap to position `i`.
    if 0 < w then
      -- σ_i: we are the UNDER strand.
      { pos := i
        vertices := state.vertices ++ [ mkR3 (i : ℝ) 0 zBot ] }
    else
      -- σ_i⁻¹: we are the OVER strand.
      { pos := i
        vertices := state.vertices ++
          [ mkR3 ((i + 1 : ℕ) : ℝ) 1 zMidHi,
            mkR3 (i : ℝ) 1 zMidLo,
            mkR3 (i : ℝ) 0 zBot ] }
  else
    -- Not participating in this crossing; descend straight.
    { state with vertices := state.vertices ++ [ mkR3 (p : ℝ) 0 zBot ] }

/-- **Tracing a strand through a braid word.** Given a traversal state $s$, a braid word
$w_0 w_1 \cdots w_{m-1}$ (a list of integers) and a starting index $k \in \mathbb{N}$, the
one-crossing step is applied to the state for each generator in turn, starting from $s$: the
generator $w_j$ is applied with top height $-(k + j)$ and bottom height $-(k + j + 1)$. The
result is the final state; for the empty word it is $s$. -/
noncomputable def applyWord : State → List ℤ → ℕ → State
  | state, [], _ => state
  | state, w :: ws, k =>
      let state' := applyCrossing state w (-(k : ℝ)) (-((k : ℝ) + 1))
      applyWord state' ws (k + 1)

/-- **One pass of the braid closure.** Let $w$ be a braid word (a list of integers) of length $m$.
Starting from a traversal state, one pass applies the letters of $w$ in order as crossings, the
$k$-th letter (counting from $0$) occupying the slab $-(k+1) \le z \le -k$; this moves the state
to a strand position $p$ and appends the crossing vertices. It then appends the closure arc: the
vertices $(p, 100, -m)$ and $(p, 100, 0)$, followed by $(p, 0, 0)$ unless $p = 1$. The resulting
state has position $p$ and the extended vertex list.

When $p = 1$ the vertex $(1, 0, 0)$ is left out because the polyline starts there, so the closure
arc already returns to its first vertex. -/
noncomputable def onePass (word : List ℤ) (state : State) : State :=
  let afterBraid := applyWord state word 0
  let m : ℝ := word.length
  let p : ℕ := afterBraid.pos
  let arc :=
    if p = 1 then
      [ mkR3 (p : ℝ) 100 (-m), mkR3 (p : ℝ) 100 0 ]
    else
      [ mkR3 (p : ℝ) 100 (-m), mkR3 (p : ℝ) 100 0, mkR3 (p : ℝ) 0 0 ]
  { pos := p, vertices := afterBraid.vertices ++ arc }

/-- **Iterated braid-closure passes.** For a braid word $w$, a number $f$ of remaining passes and
a traversal state $S$, the iteration returns $S$ when $f = 0$. When $f > 0$ it applies one pass
of $w$ to $S$, obtaining a state $S'$; it returns $S'$ if the strand position of $S'$ is $1$, and
otherwise iterates on $S'$ with $f - 1$ passes remaining.

The bound $f$ guarantees termination. The braid closure on $n$ strands uses $f = n$, since at
most $n$ distinct strand positions are visited. -/
noncomputable def iterate (word : List ℤ) : ℕ → State → State
  | 0, state => state
  | f + 1, state =>
      let s' := onePass word state
      if s'.pos = 1 then s' else iterate word f s'

end BraidClosure

/-- **Polyline closure of a braid word.** Let $n \in \mathbb{N}$, and let
$w = w_0 w_1 \cdots w_{m-1}$ be a braid word (a list of integers, where $i > 0$ stands for
$\sigma_i$ and $-i$ for $\sigma_i^{-1}$). If $m = 0$, the value is the junk list $(0, 0, 0)$,
$(1, 0, 0)$, $(0, 1, 0)$. Otherwise the value is a list of vertices in $\mathbb{R}^3$ tracing the
closure of $w$ as one polyline component. It starts at the vertex $(1, 0, 0)$ on strand position
$1$ and makes passes through the braid: in each pass the crossing $w_j$ occupies the slab between
heights $z = -(j + 1)$ and $z = -j$, with the strand passing over lifted to $y = 1$, and each
pass is followed by a closure arc through $y = 100$ back up to height $z = 0$. Tracing stops as
soon as a pass ends at position $1$, or after $n$ passes.

The layout is designed for words with $1 \le |w_j| \le n - 1$ for every $j$, where the strands
sit at the $x$-positions $1, \dots, n$; other words still yield a vertex list, but not a
meaningful one. -/
noncomputable def braidClosure (n : ℕ) (word : List ℤ) : List R3 :=
  if word.length = 0 then
    -- Junk fallback for the empty-word case (no PL data to derive).
    [BraidClosure.mkR3 0 0 0, BraidClosure.mkR3 1 0 0, BraidClosure.mkR3 0 1 0]
  else
    let init : BraidClosure.State :=
      { pos := 1, vertices := [BraidClosure.mkR3 1 0 0] }
    (BraidClosure.iterate word n init).vertices

end KnotTheory

namespace KnotTheory

/-!
# The Conway knot 11n34 as a PL knot

The Conway knot has braid index 4 and a standard 4-braid representation in
KnotInfo. We package the resulting polyline as a `PLKnot`.

`conwayKnot` is now a trusted, `sorry`-free term: its only proof field,
`three_le`, is discharged by kernel computation of the (78-vertex) list
length. Simplicity of the polyline — an embedded simple closed curve —
is a `PLKnot.IsSimple` fact rather than a structure field, and is posed
as the separate benchmark hole `conwayKnot_isSimple` in `Piccirillo`
rather than carried here as an unchecked proof field. The topological
problem `conway_knot_topologically_slice` reuses this same trusted
`conwayKnot`; a solver there must likewise establish simplicity in order
to exhibit a smooth representative.
-/

/-- **Braid word for the Conway knot.** The braid word
$\sigma_1^{-2} \sigma_2 \sigma_1^{-1} \sigma_2 \sigma_1^{-1} \sigma_3 \sigma_2^{-2} \sigma_3^{2}$
on $4$ strands, encoded as the list of integers $[-1, -1, 2, -1, 2, -1, 3, -2, -2, 3, 3]$, where
an entry $i > 0$ stands for the generator $\sigma_i$ and $-i$ for $\sigma_i^{-1}$. It has
length $11$ and writhe $-1$, and is a braid word for the Conway knot 11n34.

Source: KnotInfo's `11n_34` record, `braid_notation` field. The Knot Atlas
records a different but Markov-equivalent presentation for the same knot,
`[1, 1, 2, -3, 2, 1, -3, -2, -2, -3, -3]` (which it labels `K11n34`, the
mirror of the Conway knot); both representations agree on braid index 4,
braid length 11, and writhe `-1`. Sliceness is mirror-invariant, so either
braid word is a valid witness for `conway_knot_not_smoothly_slice`. -/
def conwayBraidWord : List ℤ := [-1, -1, 2, -1, 2, -1, 3, -2, -2, 3, 3]

set_option maxRecDepth 10000 in
/-- **The Conway knot.** The Conway knot 11n34 as a piecewise-linear closed polyline in
$\mathbb{R}^3$: its vertices are those of the polyline closure, on $4$ strands, of the braid word
$\sigma_1^{-2} \sigma_2 \sigma_1^{-1} \sigma_2 \sigma_1^{-1} \sigma_3 \sigma_2^{-2} \sigma_3^{2}$
for the Conway knot. -/
noncomputable def conwayKnot : PLKnot where
  vertices := braidClosure 4 conwayBraidWord
  three_le := by
    have h : (braidClosure 4 conwayBraidWord).length = 78 := by rfl
    omega

end KnotTheory

end MathlibExt.Topology.ConwayKnotShared
