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

/-- The ambient space `ℝ³`, as a Euclidean inner-product space. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- An oriented smooth knot in `ℝ³`: a 2π-periodic, smooth, injective immersion.
The orientation is the one induced by the parametrization. -/
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

/-- An oriented two-component smooth link in `ℝ³`: a pair of oriented knots
with disjoint images. -/
structure TwoLink where
  /-- The first component. -/
  K : Knot
  /-- The second component. -/
  L : Knot
  /-- The two components have disjoint images in `ℝ³`. -/
  disjoint : Disjoint (Set.range K.curve) (Set.range L.curve)

/-- A smooth ambient isotopy of `ℝ³`: a one-parameter family `H t : ℝ³ → ℝ³`
of diffeomorphisms, jointly smooth in `(t, x)`, starting at the identity.
The inverse family `Hinv` is also jointly smooth. -/
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

/-- Two oriented knots are ambient-isotopic if some ambient isotopy of `ℝ³`
carries the parametrized knot `K₁` to the parametrized knot `K₂`, up to an
orientation-preserving smooth reparametrization of the source circle. -/
def Knot.Isotopic (K₁ K₂ : Knot) : Prop :=
  ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam, ∀ t, Φ.H 1 (K₁.curve t) = K₂.curve (σ.f t)

/-- Two oriented two-component links are ambient-isotopic if a single ambient
isotopy carries each oriented component of the first link to the
corresponding oriented component of the second. -/
def TwoLink.Isotopic (L₁ L₂ : TwoLink) : Prop :=
  ∃ Φ : AmbientIsotopy, ∃ σ τ : CircleReparam,
    (∀ t, Φ.H 1 (L₁.K.curve t) = L₂.K.curve (σ.f t)) ∧
    (∀ t, Φ.H 1 (L₁.L.curve t) = L₂.L.curve (τ.f t))

/-- Reflection through the `xy`-plane in `ℝ³`: `(x, y, z) ↦ (x, y, -z)`. -/
def reflectZ (p : R3) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 => if i = 2 then -p.ofLp i else p.ofLp i)

/-- A knot is *chiral* if it is not ambient-isotopic, in the
orientation-sensitive sense used in this benchmark, to its mirror image (the
reflection of the image through the `xy`-plane). -/
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

/-- A topological ambient isotopy of `ℝ³`: a one-parameter family of self-
homeomorphisms of `ℝ³`, jointly continuous in `(t, x)`, with a jointly
continuous inverse family, starting at the identity. The time domain is
`ℝ` for consistency with `AmbientIsotopy` in `Prelude.lean`; only `H 0`
and `H 1` matter for the isotopy relation. -/
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

/-- Two subsets of `ℝ³` are *unoriented topologically ambient isotopic*
if some topological ambient isotopy of `ℝ³` carries one onto the other.
"Unoriented" because this is a set-level relation that forgets any
parametrization. -/
def Set.UnorientedTopAmbIsotopic (A B : Set R3) : Prop :=
  ∃ Φ : TopAmbientIsotopy, Φ.H 1 '' A = B

/-! ## The closed `2`-disk, unit circle, half-space, and model planes -/

/-- The closed unit Euclidean `2`-disk `{(x, y) | x² + y² ≤ 1}`, the source
of a slicing disk's parametrization.

We spell the disk and its boundary out explicitly via `x² + y² ≤ 1` / `= 1`
rather than as `Metric.closedBall`/`Metric.sphere` on `ℝ × ℝ`: the product
norm on `ℝ × ℝ` is the *sup* norm, so `Metric.closedBall 0 1` would be the
*square* `[-1, 1]²` and `Metric.sphere 0 1` its cornered boundary. Smooth
slice-ness over a cornered domain is vacuously unsatisfiable — at a corner
no smooth immersion can match a corner-free smooth knot boundary while
keeping an injective derivative — which would make `Knot.SmoothlySlice`
false for *every* knot. -/
abbrev disk2 : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

/-- The unit Euclidean circle `{(x, y) | x² + y² = 1}` in `ℝ²`, the source of
the slicing disk's boundary. -/
abbrev circle1 : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- The closed upper half-space `ℝ³ × [0, ∞)` in `ℝ³ × ℝ`. We identify
`ℝ³ × [0, ∞)` with `B⁴ ∖ {pt}`, so slice disks live here. -/
def upperHalf : Set (R3 × ℝ) := { q | 0 ≤ q.2 }

/-- Model interior `2`-plane in `ℝ³ × ℝ`: the locus where the last two
coordinates of `q.1` and `q.2` all vanish. Used to express interior local
flatness of an embedded `2`-disk. -/
def modelPlane2 : Set (R3 × ℝ) := { q | q.1 1 = 0 ∧ q.1 2 = 0 }

/-- Model boundary half-plane in the upper half-space. The disk sits in
the plane `q.1 1 = 0 ∧ q.1 2 = 0` (a copy of `ℝ × ℝ`, parametrized by
`q.1 0` and `q.2`) and is restricted to the half-space `q.2 ≥ 0`. Used
to express boundary local flatness of a proper embedded disk. -/
def modelHalfPlane2 : Set (R3 × ℝ) := { q | q.1 1 = 0 ∧ q.1 2 = 0 ∧ 0 ≤ q.2 }

/-! ## Smooth slice-ness on a smooth `Knot`

A smooth knot `K` is smoothly slice if its image bounds a smooth properly
embedded `2`-disk in the upper half-space `ℝ³ × [0, ∞)`. Because `K`'s
image is a smooth `1`-submanifold, set-level boundary equality with the
disk's smooth boundary image works cleanly.
-/

/-- **Smoothly slice (smooth knot version).** -/
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

/-- Local flatness of the disk image at an *interior* disk point `q`. -/
def IsLocallyFlatInterior (D : ℝ × ℝ → R3 × ℝ) (q : R3 × ℝ) : Prop :=
  ∃ h : OpenPartialHomeomorph (R3 × ℝ) (R3 × ℝ),
    q ∈ h.source ∧
    h.toFun '' (h.source ∩ D '' disk2) = h.target ∩ modelPlane2

/-- Local flatness of the disk image at a *boundary* disk point `q`. The
chart is ambient-open in `ℝ³ × ℝ` (it cannot be contained in the closed
half-space because `q.2 = 0` forces any open neighborhood of `q` to
escape the half-space), but it preserves the half-space and maps the
disk image onto the model half-plane in the half-space. -/
def IsLocallyFlatBoundary (D : ℝ × ℝ → R3 × ℝ) (q : R3 × ℝ) : Prop :=
  ∃ h : OpenPartialHomeomorph (R3 × ℝ) (R3 × ℝ),
    q ∈ h.source ∧
    h.toFun '' (h.source ∩ upperHalf) = h.target ∩ upperHalf ∧
    h.toFun '' (h.source ∩ D '' disk2) = h.target ∩ modelHalfPlane2

/-- **Topologically slice (smooth knot version).** A smooth knot is
topologically slice if its image bounds a *locally flat* topologically
embedded proper `2`-disk in the upper half-space, with interior and
boundary points using the matching local model. -/
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

/-- Linear interpolation across the closed polyline with `vertices.length`
edges, each parametrized over unit time, extended periodically. Junk
value `0` on the empty list. -/
noncomputable def plCurve (vertices : List R3) (t : ℝ) : R3 :=
  if h : vertices.length = 0 then 0
  else
    let n : ℕ := vertices.length
    let s : ℝ := t - (n : ℝ) * Int.floor (t / (n : ℝ))
    let k : ℕ := (Int.floor s).toNat
    let α : ℝ := s - k
    (1 - α) • vertices[k % n]'(Nat.mod_lt _ (Nat.pos_of_ne_zero h)) +
      α • vertices[(k + 1) % n]'(Nat.mod_lt _ (Nat.pos_of_ne_zero h))

/-- A piecewise-linear closed polyline in `ℝ³` with at least three vertices.

Simplicity (being an embedded simple closed curve) is *not* bundled into the
structure; it is expressed separately as `PLKnot.IsSimple`. Keeping it out of
the structure lets named polylines such as `conwayKnot` be written down as
trusted, `sorry`-free data, with the finite-but-laborious simplicity proof
posed as its own benchmark obligation rather than carried as an unchecked
proof field. -/
structure PLKnot where
  /-- The ordered list of polyline vertices. -/
  vertices : List R3
  /-- A closed polyline needs at least three vertices to be non-degenerate. -/
  three_le : 3 ≤ vertices.length

/-- The image of the PL knot in `ℝ³` (the trace of the polyline). -/
def PLKnot.image (K : PLKnot) : Set R3 :=
  plCurve K.vertices '' Set.Ico (0 : ℝ) (K.vertices.length : ℝ)

/-- The polyline is a *simple closed curve*: the periodic parametrization is
injective on a half-open fundamental domain `[0, vertices.length)`.
Equivalent to: all vertices distinct, non-adjacent edges disjoint, adjacent
edges meet only at their shared vertex. -/
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

/-- A smooth knot `J` is a *smooth representative* of the PL knot `K` if
their images are unoriented topologically ambient isotopic in `ℝ³`. For
tame curves (which both sides are by construction) this is equivalent to
the usual smooth/PL knot type relation. -/
def PLKnot.HasSmoothRepresentative (K : PLKnot) (J : Knot) : Prop :=
  Set.UnorientedTopAmbIsotopic (Set.range J.curve) K.image

/-- **Smoothly slice (PL knot version).** A PL knot is smoothly slice if
some smooth knot of the same knot type is smoothly slice. This is
Piccirillo's theorem about the Conway knot in the form most natural for
a polyline witness. -/
def PLKnot.SmoothlySlice (K : PLKnot) : Prop :=
  ∃ J : Knot, K.HasSmoothRepresentative J ∧ J.SmoothlySlice

/-- **Topologically slice (PL knot version).** A PL knot is topologically
slice if some smooth knot of the same knot type is topologically slice. -/
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

/-- Construct an `R3` element from three coordinates `(x, y, z)`. -/
noncomputable def mkR3 (x y z : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then x else if i.val = 1 then y else z)

/-- Traversal state: the current strand position and the accumulated
vertex list of the polyline so far. -/
structure State where
  /-- Current strand `x`-position. -/
  pos : ℕ
  /-- Polyline vertices accumulated so far, in order. -/
  vertices : List R3

/-- Apply one braid generator to the traversal state. The crossing
occupies the `z`-slab `[zBot, zTop]` (with `zBot < zTop`). The braid
generator is `w = ±i`; we cross strands at positions `i` and `i + 1`,
with `i = w.natAbs`. -/
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

/-- Apply all braid generators in `word` starting from crossing index `k`,
accumulating vertices in `state`. -/
noncomputable def applyWord : State → List ℤ → ℕ → State
  | state, [], _ => state
  | state, w :: ws, k =>
      let state' := applyCrossing state w (-(k : ℝ)) (-((k : ℝ) + 1))
      applyWord state' ws (k + 1)

/-- One pass through the braid box plus a closure arc. If the pass ends
at position `1`, the closure arc closes back to the polyline's starting
vertex `(1, 0, 0)` and we omit the redundant final vertex. Otherwise
we continue at the top of the new position. -/
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

/-- Iterate passes until back at position `1`, bounded by `fuel` to
guarantee termination (we visit at most `n` distinct strand positions). -/
noncomputable def iterate (word : List ℤ) : ℕ → State → State
  | 0, state => state
  | f + 1, state =>
      let s' := onePass word state
      if s'.pos = 1 then s' else iterate word f s'

end BraidClosure

/-- The PL closure of a braid word on `n` strands, traced as one polyline
component starting at strand position `1`. -/
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

/-- A braid word for the Conway knot 11n34, on 4 strands, of length 11
and writhe `-1`. Each `±i` represents the braid generator `σ_i` (or its
inverse, for negative sign).

Source: KnotInfo's `11n_34` record, `braid_notation` field. The Knot Atlas
records a different but Markov-equivalent presentation for the same knot,
`[1, 1, 2, -3, 2, 1, -3, -2, -2, -3, -3]` (which it labels `K11n34`, the
mirror of the Conway knot); both representations agree on braid index 4,
braid length 11, and writhe `-1`. Sliceness is mirror-invariant, so either
braid word is a valid witness for `conway_knot_not_smoothly_slice`. -/
def conwayBraidWord : List ℤ := [-1, -1, 2, -1, 2, -1, 3, -2, -2, 3, 3]

set_option maxRecDepth 10000 in
/-- The Conway knot 11n34 as a piecewise-linear closed polyline in `ℝ³`,
realized as the braid closure of `conwayBraidWord` on 4 strands. -/
noncomputable def conwayKnot : PLKnot where
  vertices := braidClosure 4 conwayBraidWord
  three_le := by
    have h : (braidClosure 4 conwayBraidWord).length = 78 := by rfl
    omega

end KnotTheory

end MathlibExt.Topology.ConwayKnotShared
