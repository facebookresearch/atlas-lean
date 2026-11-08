/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Peak descents of a Dyck step list

`dyckPeakDescents l` lists, for each peak `UD` of the step list `l` from left to right, the length
of the maximal run of `D`s starting at that peak's `D`.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck Paths, and
Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article 24.5.2, Section 2.
-/

namespace MetaMathlibExt

@[expose] public section

open DyckStep

/-- The descent lengths of a step list, one per peak from left to right: for each
peak `UD`, the length `j` of the maximal run of `D`s that starts at its `D`, so
that the peak and its descent form the primitive block `U D^j`.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Dyck paths). -/
def dyckPeakDescents (l : List DyckStep) : List ℕ :=
  ((List.range l.length).filter fun i => decide (l[i]? = some U ∧ l[i + 1]? = some D)).map
    fun i => ((l.drop (i + 1)).takeWhile (· == D)).length

/-- The source's sample path `U U U (U D^3) (U D^2) U (U D) U (U D^3)` has four
peaks with descents `3, 2, 1, 3`.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
theorem dyckPeakDescents_sample :
    dyckPeakDescents [U, U, U, U, D, D, D, U, D, D, U, U, D, U, U, D, D, D] =
      [3, 2, 1, 3] := by
  decide

end

end MetaMathlibExt
