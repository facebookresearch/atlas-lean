/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mirrored polygonal rooms not lit from every point (Geometry Junkyard)

D. Eppstein, The Geometry Junkyard: Open Problems, mirrored room illumination: the old open problem
of, given a polygon in which all sides are perfect mirrors, and a point source of light, whether the
entire polygon will be lit up (the answer is no if smooth curves are allowed).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.MirroredRoomIlluminationAMR38Problem0009Wanted

/-!
Source: D. Eppstein, The Geometry Junkyard: Open Problems, item 'Mirrored room illumination'.
UnsolvedMath record UM-03900009 (`AMR-038-0009`), dataset ulamai/UnsolvedMath v1.8.0.

The item links C. Piatko's summary (comp.theory, 6 March 1990,
https://ics.uci.edu/~eppstein/junkyard/mirror.html) of the two precise problems as J. O'Rourke,
Art Gallery Theorems and Algorithms (1987), pp. 265-266, states them: for a polygon whose edges are
perfect mirrors, is there always at least one interior point from which it is completely
illuminable by a point light, and is it always illuminable from each of its points, assuming that
a light ray is absorbed if it hits a vertex? Only the second question is stated here (Tokarsky
answered it); the first is open and is the legacy entry
`OpenConjectures/Combinatorics/IsEveryPolygonalRoomInThePlaneIlluminableFromSomePoint`.

`WantedExt` cannot import `OpenConjectures` (`lakefile.toml` and `scripts/check_health.sh` allow
only `MathlibExt`, `CSLibExt` and `PhyslibExt`), and the repository's polygonal-room and light-path
definitions exist only in the legacy (non-`module`) entry
`OpenConjectures/Combinatorics/IsEveryPolygonalRoomInThePlaneIlluminableFromSomePoint` (Straus's
open 'from some point' question). The definitions below (`Plane`, `cyclicSucc`, `wallSegment`,
`PolygonalRoom`, `lineThrough`, `IsWallTangentAt`, `unitDirection`, `reflectInLine`, the path index
helpers, `LightPath`, `Illuminates`) are copies with the same names and bodies, as
`WantedExt.Analysis.SeveralComplexVariablesShared` repeats OpenConjectures definitions; the legacy
file's lemma `cyclicSucc_ne_self` is not copied (statements only). A room is a simple polygon's open
interior; a light path has straight legs in the open interior and reflects specularly at points
where the wall is locally straight, so light reaching a corner is absorbed, the usual convention.
Source and target range over the open floor, where Tokarsky's points lie; the room is lit up from
the source when every floor point is illuminated.
-/

noncomputable section


/-- The Euclidean plane in which the polygonal room lies. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The next index in a finite cyclic ordering. -/
def cyclicSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- The closed side beginning at vertex `i` of a cyclic vertex list. -/
def wallSegment {n : ℕ} (v : Fin n → Plane) (i : Fin n) : Set Plane :=
  segment ℝ (v i) (v (cyclicSucc i))

/-- A bounded, connected, regular open planar region whose frontier is one
simple finite polygonal cycle. The closure is the physical room, while
`inside` is the open floor area. Redundant collinear subdivision vertices are
allowed and do not affect the geometric definitions below. -/
structure PolygonalRoom where
  /-- The number of sides (equivalently, of listed vertices) of the boundary polygon. -/
  sideCount : ℕ
  atLeastThree : 3 ≤ sideCount
  /-- The vertices of the boundary polygon, in cyclic order. -/
  vertex : Fin sideCount → Plane
  vertex_injective : Function.Injective vertex
  /-- The open floor area of the room, whose frontier is the boundary polygon. -/
  inside : Set Plane
  inside_isOpen : IsOpen inside
  inside_nonempty : inside.Nonempty
  inside_preconnected : IsPreconnected inside
  inside_bounded : Bornology.IsBounded inside
  regular_inside : interior (closure inside) = inside
  frontier_eq_walls :
    frontier inside = {p | ∃ i : Fin sideCount, p ∈ wallSegment vertex i}
  walls_meet_only_at_shared_endpoints :
    ∀ i j : Fin sideCount, i ≠ j →
      wallSegment vertex i ∩ wallSegment vertex j ⊆
        ({vertex i, vertex (cyclicSucc i)} : Set Plane) ∩
          ({vertex j, vertex (cyclicSucc j)} : Set Plane)

/-- The physical room, including its mirrored walls. -/
def PolygonalRoom.closedRoom (R : PolygonalRoom) : Set Plane :=
  closure R.inside

/-- The affine line through `p` in the nonzero direction `direction`. -/
def lineThrough (p direction : Plane) : Set Plane :=
  {q | ∃ t : ℝ, q = p + t • direction}

/-- `direction` is a tangent to a geometrically smooth point of the mirrored
boundary. This is stated using the local frontier itself, rather than a chosen
side in a polygonal presentation, so subdividing a straight wall does not
change which reflections are admitted. -/
def IsWallTangentAt (R : PolygonalRoom) (p direction : Plane) : Prop :=
  direction ≠ 0 ∧ p ∈ frontier R.inside ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : Plane, dist q p < ε →
      (q ∈ frontier R.inside ↔ q ∈ lineThrough p direction)

/-- The unit direction from `a` to `b`; light paths only use this when
`a ≠ b`. -/
def unitDirection (a b : Plane) : Plane :=
  (‖b - a‖)⁻¹ • (b - a)

/-- Orthogonal reflection of `velocity` in the line spanned by the nonzero
vector `wallDirection`. -/
def reflectInLine (wallDirection velocity : Plane) : Plane :=
  (2 * (inner ℝ velocity wallDirection / inner ℝ wallDirection wallDirection)) •
      wallDirection - velocity

/-- The first point index in a path having `n` reflection points. -/
def pathFirst (n : ℕ) : Fin (n + 2) := ⟨0, by omega⟩

/-- The final point index in a path having `n` reflection points. -/
def pathLast (n : ℕ) : Fin (n + 2) := ⟨n + 1, by omega⟩

/-- The initial endpoint index of a leg of a finite light path. -/
def legStart {n : ℕ} (i : Fin (n + 1)) : Fin (n + 2) :=
  ⟨i.val, by omega⟩

/-- The terminal endpoint index of a leg of a finite light path. -/
def legFinish {n : ℕ} (i : Fin (n + 1)) : Fin (n + 2) :=
  ⟨i.val + 1, by omega⟩

/-- The point immediately before reflection number `i`. -/
def beforeReflection {n : ℕ} (i : Fin n) : Fin (n + 2) :=
  ⟨i.val, by omega⟩

/-- Reflection point number `i`. -/
def atReflection {n : ℕ} (i : Fin n) : Fin (n + 2) :=
  ⟨i.val + 1, by omega⟩

/-- The point immediately after reflection number `i`. -/
def afterReflection {n : ℕ} (i : Fin n) : Fin (n + 2) :=
  ⟨i.val + 2, by omega⟩

/-- A finite optical path from `source` to `target`. Its open straight legs
stay in the room's interior, every intermediate point is a locally straight
point of the mirrored frontier, and each change of direction is the specular
reflection in that local tangent line. -/
structure LightPath (R : PolygonalRoom) (source target : Plane) where
  /-- The number of reflection points of the path. -/
  reflectionCount : ℕ
  /-- The points of the path in order: the source, the reflection points, and the target. -/
  point : Fin (reflectionCount + 2) → Plane
  /-- For each reflection, a direction of the wall's tangent line at the reflection point. -/
  reflectionTangent : Fin reflectionCount → Plane
  starts_at_source : point (pathFirst reflectionCount) = source
  ends_at_target : point (pathLast reflectionCount) = target
  leg_nondegenerate :
    ∀ i : Fin (reflectionCount + 1),
      point (legStart i) ≠ point (legFinish i)
  open_legs_inside :
    ∀ i : Fin (reflectionCount + 1),
      openSegment ℝ (point (legStart i)) (point (legFinish i)) ⊆ R.inside
  reflections_on_smooth_walls :
    ∀ i : Fin reflectionCount,
      IsWallTangentAt R (point (atReflection i)) (reflectionTangent i)
  specular_law :
    ∀ i : Fin reflectionCount,
      unitDirection (point (atReflection i)) (point (afterReflection i)) =
        reflectInLine (reflectionTangent i)
          (unitDirection (point (beforeReflection i)) (point (atReflection i)))

/-- A target is illuminated when it is the source itself or is joined to the
source by a finite light path with any finite number of reflections. -/
def Illuminates (R : PolygonalRoom) (source target : Plane) : Prop :=
  source = target ∨ Nonempty (LightPath R source target)

/-- The illumination question as posed (Geometry Junkyard, mirrored room illumination): in every
polygonal room with perfectly mirrored walls, a point light source at any point of the open floor
lights up every point of the floor. -/
def everyPointIlluminatesEveryPoint : Prop :=
  ∀ R : PolygonalRoom, ∀ source ∈ R.inside, ∀ target ∈ R.inside, Illuminates R source target



end

/--
Resolved false: Tokarsky constructed a polygonal room with mirrored walls and two floor points such
that light from one never reaches the other. Source: D. Eppstein, The Geometry Junkyard: Open
Problems, item 'Mirrored room illumination'; resolution: G. W. Tokarsky, Polygonal rooms not
illuminable from every point, Amer. Math. Monthly 102 (1995), no. 10, 867-879, DOI
10.1080/00029890.1995.12004679; as recalled by S. Lelièvre, T. Monteil and B. Weiss, Everything is
illuminated, Geom. Topol. 20 (2016), arXiv:1407.2975, Tokarsky's title theorem: a polygonal room
with two points that do not illuminate each other; Lelièvre-Monteil-Weiss §1: 'The classical
illumination problem was first posed in the 1950s, when it was asked whether there exists a
polygonal room with a pair of points which do not illuminate each other. First examples were found
by Tokarsky [Tok95] and Boshernitzan', https://arxiv.org/abs/1407.2975.
-/
public theorem_wanted everyPointIlluminatesEveryPoint_refuted : ¬ everyPointIlluminatesEveryPoint

end MathlibExt.Geometry.MirroredRoomIlluminationAMR38Problem0009Wanted
