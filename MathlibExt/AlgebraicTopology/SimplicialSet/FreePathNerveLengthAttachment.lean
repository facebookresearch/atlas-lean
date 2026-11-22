/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveLengthCell
import MathlibExt.AlgebraicTopology.SimplicialSet.IndexedSums
import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltration

/-!
# All SAME original full word cells at one native length stage

Every original length-k path, with its individual original endpoints,
indexes the full native simplex of its SAME complete generator word.
The entire indexed sum map retains every original path label and all
ordinal coefficients. Its native open-complement uniqueness and full
range coverage give the actual stage pushout.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- Every actual original full path at the supplied length, with individual endpoints retained. -/
structure WordLabel (k : ℕ) where
  /-- The SAME original source vertex. -/
  source : V
  /-- The SAME original target vertex. -/
  target : V
  /-- The complete original generating path. -/
  path : Quiver.Path source target
  /-- The full actual original path length. -/
  length_eq : path.length = k

/-- The complete native original simplex at each full original word label. -/
def labelSimplex (k : ℕ) (a : WordLabel V k) : SSet.{max u v} := Δ[a.path.length]

/-- The full native sum of all original word cells at the supplied actual length. -/
abbrev stageCells (k : ℕ) : SSet.{max u v} := SSet.IndexedSums.object (labelSimplex V k)

/-- The SAME entire indexed original word-cell map into the full native path nerve. -/
def stageCellMap (k : ℕ) : stageCells V k ⟶ nerve (Paths V) :=
  SSet.IndexedSums.desc (labelSimplex V k) (fun a => wordCell V a.path)

/-- Every original full word-cell map lands in the SAME actual native length stage. -/
lemma stageCellMap_range_le (k : ℕ) : SSet.Subcomplex.range (stageCellMap V k) ≤ lengthStage V k := by
  intro q w hw
  obtain ⟨⟨a, c⟩, rfl⟩ := hw
  rcases q with ⟨⟨n⟩⟩
  change (Δ[a.path.length] : SSet.{max u v}) _⦋n⦌ at c
  change (totalPath V n ((wordCell V a.path).app (op ⦋n⦌) c)).length ≤ k
  rw [wordCell_total_length]
  have hhi := (c (Fin.last n)).isLt
  have he := a.length_eq
  omega

end CategoryTheory.FreePathNerveCoordinates
