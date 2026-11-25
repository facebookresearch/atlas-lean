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

/-- **Peak descents.** Let $l$ be a finite sequence of up steps $U$ and down steps $D$. A peak
of $l$ is a position where a step $U$ is immediately followed by a step $D$. The peak descents
of $l$ form the list that has, for each peak from left to right, the length $j$ of the maximal
run of consecutive steps $D$ that starts at the $D$ of that peak, so that the peak and its
descent form the primitive block $U D^j$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2 (Dyck paths). -/
def dyckPeakDescents (l : List DyckStep) : List ℕ :=
  ((List.range l.length).filter fun i => decide (l[i]? = some U ∧ l[i + 1]? = some D)).map
    fun i => ((l.drop (i + 1)).takeWhile (· == D)).length

/-- **Peak descents of a sample Dyck path.** The Dyck path $UUUUDDDUDDUUDUUDDD$, which factors
as $U\,U\,U\,(UD^3)(UD^2)\,U\,(UD)\,U\,(UD^3)$, has four peaks $UD$, and the lengths of the
maximal runs of $D$ steps starting at the $D$ of each peak are, from left to right,
$3, 2, 1, 3$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Section 2. -/
theorem dyckPeakDescents_sample :
    dyckPeakDescents [U, U, U, U, D, D, D, U, D, D, U, U, D, U, U, D, D, D] =
      [3, 2, 1, 3] := by
  decide

end

end MetaMathlibExt
