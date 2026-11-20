/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.RevealmentTranslation

namespace StatMech
namespace OSSS
namespace CenteredFirstHit

open Lattice RevealmentConstruction RevealmentTranslation


def centeredClosedBox {d : Nat} (u : Site d) (m : Nat) : Set (Site d) :=
  {x | centeredRadius u x <= m}

theorem center_mem_centeredClosedBox {d : Nat} (u : Site d) (m : Nat) :
    u ∈ centeredClosedBox u m := by
  simp [centeredClosedBox, centeredRadius_self]



theorem connected_centeredBoundary_has_within
    {d m : Nat} {omega : ConfigSpace (Sym2 (Site d))} {u z : Site d}
    (hz : z ∈ centeredBoundary u m) (hconn : Connected d omega u z) :
    ∃ z' : centeredClosedBox u m,
      (z' : Site d) ∈ centeredBoundary u m ∧
      ConnectedWithin d omega (centeredClosedBox u m)
        ⟨u, center_mem_centeredClosedBox u m⟩ z' := by
  change (openSubgraph d omega).Reachable u z at hconn
  rw [SimpleGraph.reachable_iff_reflTransGen] at hconn
  let origin : centeredClosedBox u m :=
    ⟨u, center_mem_centeredClosedBox u m⟩
  suffices H : ∀ w : Site d,
      Relation.ReflTransGen (openSubgraph d omega).Adj u w ->
      (∃ b : centeredClosedBox u m,
          (b : Site d) ∈ centeredBoundary u m ∧
          (openSubgraphInduce d omega (centeredClosedBox u m)).Reachable origin b) ∨
        (centeredRadius u w < m ∧
          ∃ wi : centeredClosedBox u m, (wi : Site d) = w ∧
            (openSubgraphInduce d omega (centeredClosedBox u m)).Reachable origin wi) by
    rcases H z hconn with hdone | ⟨hlt, _⟩
    · exact hdone
    · change centeredRadius u z = m at hz
      omega
  intro w hw
  induction hw with
  | refl =>
      by_cases hm : m = 0
      · left
        refine ⟨origin, ?_, SimpleGraph.Reachable.refl origin⟩
        change centeredRadius u u = m
        simp [hm, centeredRadius_self]
      · right
        refine ⟨?_, origin, rfl, SimpleGraph.Reachable.refl origin⟩
        simpa [centeredRadius_self] using Nat.zero_lt_of_ne_zero hm
  | @tail a b hab hadj ih =>
      rcases ih with hdone | ⟨ha, ai, hai, hreach⟩
      · exact Or.inl hdone
      · have hb_le : centeredRadius u b <= m := by
          have hstep := centeredRadius_step_le u a b
            ((openSubgraph_le omega) hadj)
          omega
        let bi : centeredClosedBox u m := ⟨b, hb_le⟩
        have hadjInd :
            (openSubgraphInduce d omega (centeredClosedBox u m)).Adj ai bi := by
          rw [openSubgraphInduce_adj]
          simpa [hai] using hadj
        have hreach' := hreach.trans hadjInd.reachable
        by_cases hb : centeredRadius u b = m
        · left
          exact ⟨bi, hb, hreach'⟩
        · right
          exact ⟨lt_of_le_of_ne hb_le hb, bi, rfl, hreach'⟩


theorem connectedToSet_centered_has_within
    {d m : Nat} {omega : ConfigSpace (Sym2 (Site d))} {u : Site d}
    (hconn : ConnectedToSet d omega u (centeredBoundary u m)) :
    ∃ z : centeredClosedBox u m,
      (z : Site d) ∈ centeredBoundary u m ∧
      ConnectedWithin d omega (centeredClosedBox u m)
        ⟨u, center_mem_centeredClosedBox u m⟩ z := by
  obtain ⟨z, hz, huz⟩ := hconn
  exact connected_centeredBoundary_has_within hz huz

end CenteredFirstHit
end OSSS
end StatMech
