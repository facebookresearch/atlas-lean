/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HOTARU BEAM is NP-complete

Source:
T. Otsuji, P. Fulla and T. Fukunaga, "NP-completeness and physical zero-knowledge proof of
Hotaru Beam", arXiv:2603.01393 (2026) (Section 2: the rules; Theorem 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HotaruBeamDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HotaruBeam

/-!
# HOTARU BEAM is NP-complete

Otsuji, Fulla and Fukunaga, Section 2: "Hotaru Beam is played on a rectangular grid. Several
circles, called fireflies, are placed on the intersections of the grid. For each firefly, there is
a dot placed on one of the intersections of its boundary and grid lines, and there also may be a
number inside the circle." "The task is to draw a beam from each firefly. The beam starts from the
dot, follows the grid lines, and stops when it reaches a firefly's boundary (possibly the same one
as it started from)." The beams must satisfy:
- "Beams do not intersect nor do they branch; therefore a beam cannot end at a firefly's dot
  since another beam (or the same beam) starts at that point."
- "The number inside a firefly prescribes the number of bends of its beam." Without a number,
  the number of bends is not restricted.
- "All fireflies must end up connected into a single component by the beams."

INSTANCE: a rectangular grid with fireflies, their dots, and their optional numbers.
QUESTION: does the instance admit a solution? (Theorem 1: NP-complete.)

The grid has the intersections `(x, y)` with `x < W` and `y < H`. A firefly is given by its
intersection, the direction `d < 4` of its dot (`0`: `+x`, `1`: `+y`, `2`: `-x`, `3`: `-y`),
and `(numbered, number)`. A beam of firefly `f` is the list `B` of intersections it visits after
leaving `f`; `f :: B` is a lattice path of unit grid segments, its first step goes in the
direction of `f`'s dot, every intersection of `B` is in the grid, the intersections before the
last are not fireflies (a beam stops at the first firefly it reaches), and the last is the
firefly `g = tgt f` where the beam ends (possibly `f` itself). The beam enters `g` from the
intersection before the last one, which must not be the neighbor of `g` in the direction of
`g`'s dot (a beam cannot end at a dot). The bends of a beam are the interior points of the path
`f :: B` where it turns, i.e. where the two neighboring points are not symmetric about it. The
beams do not intersect: the intersections that beams pass through (all but the last point of
each beam) are pairwise distinct, within one beam and across beams; together with the dot rule
this also keeps the segments of different beams apart. Connectivity is
`SimpleGraph.Connected` of the graph on the fireflies joining `f` and `tgt f`, so an instance
has at least one firefly. An unnumbered firefly carries `(false, 0)`, so every instance has one
encoding.

Grid dimensions are given in unary (`W` and `H` are the lengths of lists of `true`s): a beam
can follow the grid lines through every intersection, so a solution has size proportional to
`W · H`, which a binary encoding would make exponential in the input.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HOTARU BEAM is NP-complete.** Source: Otsuji, Fulla and Fukunaga (2026), Theorem 1. -/
public theorem_wanted hotaruBeam_npComplete :
    hotaruBeamDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hotaruBeamDec

end MetaMathlibExt.Complexity.NPComplete.HotaruBeam
