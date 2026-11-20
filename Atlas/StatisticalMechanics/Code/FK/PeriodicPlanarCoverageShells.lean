/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarCoverage











open Finset MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


noncomputable def PeriodicGraph.orbitVertexToBuffered
    (P : PeriodicGraph V) (n : Nat) :
    P.OrbitVertex n ↪ P.BufferedVertex n where
  toFun x := ⟨x.1, P.orbitBox_mono (P.id_le_bufferedRadius n) x.2⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : P.BufferedVertex n => z.1) hxy



noncomputable def PeriodicGraph.orbitShellCandidatePairs
    (P : PeriodicGraph V) (n : Nat) :
    Finset (P.BufferedVertex n × P.BufferedVertex n) :=
  ((Finset.univ : Finset (P.OrbitVertex n)) ×ˢ
      (Finset.univ : Finset (P.OrbitVertex n))).image
    (fun xy => (P.orbitVertexToBuffered n xy.1,
      P.orbitVertexToBuffered n xy.2))



noncomputable def PeriodicGraph.canonicalConnectionShellPairs
    (P : PeriodicGraph V) (n : Nat) :
    Finset (P.BufferedVertex n × P.BufferedVertex n) :=
  (P.orbitShellCandidatePairs n).filter
    (fun xy => n ≤ P.graph.dist xy.1.1 xy.2.1)

theorem PeriodicGraph.mem_canonicalConnectionShellPairs_dist
    (P : PeriodicGraph V) (n : Nat)
    (xy : P.BufferedVertex n × P.BufferedVertex n)
    (hxy : xy ∈ P.canonicalConnectionShellPairs n) :
    n ≤ P.graph.dist xy.1.1 xy.2.1 := by
  exact (Finset.mem_filter.1 hxy).2

theorem PeriodicGraph.orbitShellCandidatePairs_card_le
    (P : PeriodicGraph V) (n : Nat) :
    (P.orbitShellCandidatePairs n).card ≤ (P.orbitBox n).card ^ 2 := by
  unfold PeriodicGraph.orbitShellCandidatePairs
  calc
    _ ≤ ((Finset.univ : Finset (P.OrbitVertex n)) ×ˢ
        (Finset.univ : Finset (P.OrbitVertex n))).card :=
      Finset.card_image_le
    _ = Fintype.card (P.OrbitVertex n) ^ 2 := by
      simp [pow_two]
    _ = (P.orbitBox n).card ^ 2 := by
      rw [Fintype.card_coe]


theorem PeriodicGraph.canonicalConnectionShellPairs_card_le
    (P : PeriodicGraph V) (n : Nat) :
    (P.canonicalConnectionShellPairs n).card ≤
      (81 * P.fundamentalDomain.card ^ 2) * (n + 1) ^ 4 := by
  have horbit :=
    PeriodicPlanarDualPair.PeriodicGraph.orbitBox_card_le_quadratic P n
  have hlinear : 2 * n + 1 ≤ 3 * (n + 1) := by omega
  calc
    (P.canonicalConnectionShellPairs n).card ≤
        (P.orbitShellCandidatePairs n).card := Finset.card_filter_le _ _
    _ ≤ (P.orbitBox n).card ^ 2 :=
      P.orbitShellCandidatePairs_card_le n
    _ ≤ (((2 * n + 1) ^ 2 * P.fundamentalDomain.card) ^ 2) :=
      Nat.pow_le_pow_left horbit 2
    _ = (2 * n + 1) ^ 4 * P.fundamentalDomain.card ^ 2 := by ring
    _ ≤ (3 * (n + 1)) ^ 4 * P.fundamentalDomain.card ^ 2 := by
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlinear 4)
    _ = (81 * P.fundamentalDomain.card ^ 2) * (n + 1) ^ 4 := by ring

end StatMech.FK.PeriodicPlanar
