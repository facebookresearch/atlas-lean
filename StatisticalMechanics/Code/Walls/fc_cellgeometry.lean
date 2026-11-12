/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.FK.RandomCluster
import Code.FK.SuperMultiplicative
import Code.FK.FKInterfaceSubadd
import Code.FK.QuadrantPartition
import Code.FK.EdgeConfigZ

open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice








section IsoInvariance
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]



theorem fc_fkZEdge_iso (φ : G ≃g H) (p q : ℝ) :
    ecz_fkZEdge G p q = ecz_fkZEdge H p q :=
  ecz_fkZEdge_iso φ p q

end IsoInvariance







section VanHove
variable {d : ℕ}



abbrev fc_Tcg (m n : ℕ) : ℕ := ecz_T m n



abbrev fc_center (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n)) : Site d := ecz_center m n c




noncomputable abbrev fc_vanHoveTag (m n : ℕ) (x : boxVerts d n) :
    Option (Fin d → Fin (fc_Tcg m n)) := ecz_vanHoveTag m n x





theorem fc_vanHoveTag_eq_some_iff (m n : ℕ) (x : boxVerts d n)
    (c : Fin d → Fin (fc_Tcg m n)) :
    fc_vanHoveTag m n x = some c
      ↔ ∀ i, ((x : Site d) i - fc_center m n c i).natAbs ≤ m :=
  ecz_vanHoveTag_eq_some_iff m n x c






noncomputable def fc_cellBlockIso (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n)) :
    boxGraph d m ≃g qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c) :=
  ecz_cellBlockIso m n c




theorem fc_cellBlockIso_apply (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n)) (y : boxVerts d m) :
    (((fc_cellBlockIso m n c y : {x : boxVerts d n // fc_vanHoveTag m n x = some c}) :
        boxVerts d n) : Site d)
      = fun i => (y : Site d) i + fc_center m n c i :=
  rfl






theorem fc_cellBlock_fkZEdge (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n)) (p q : ℝ) :
    ecz_fkZEdge (qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)) p q
      = ecz_fkZEdge (boxGraph d m) p q :=
  ecz_cellBlock_fkZEdge m n c p q






theorem fc_cellBlock_fkZEdge_via_iso_load_bearing (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n))
    (p q : ℝ) :
    ecz_fkZEdge (qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)) p q
      = ecz_fkZEdge (boxGraph d m) p q :=
  (fc_fkZEdge_iso (fc_cellBlockIso m n c) p q).symm



theorem fc_cellBlock_edge_card (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n)) :
    (qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)).edgeFinset.card
      = (boxGraph d m).edgeFinset.card :=
  ecz_cellBlock_edge_card m n c




theorem fc_cell_card (m n : ℕ) :
    Fintype.card (Fin d → Fin (fc_Tcg m n)) = (fc_Tcg m n) ^ d :=
  ecz_cell_card m n




noncomputable def fc_restUnivIso (m n : ℕ) :
    qp_restG (boxGraph d n) (fc_vanHoveTag m n) Finset.univ ≃g boxGraph d n :=
  ecz_restUnivIso m n






theorem fc_cellBlockIso_nonvacuous (m n : ℕ) (hmn : m ≤ n) :
    ∃ c : Fin d → Fin (fc_Tcg m n),
      Nonempty (boxGraph d m ≃g qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)) := by
  have hT : 1 ≤ fc_Tcg m n := by
    change 1 ≤ ecz_T m n
    rw [ecz_T, Nat.le_div_iff_mul_le (by omega)]
    omega
  refine ⟨fun _ => ⟨0, by omega⟩, ⟨fc_cellBlockIso m n _⟩⟩

end VanHove

end StatMech.Walls
