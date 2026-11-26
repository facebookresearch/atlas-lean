/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Coverage

/-!
# Canonical connection shells in orbit boxes

The canonical shell of radius `n`: all pairs of orbit-box vertices at graph distance at least `n`,
with a polynomial bound `81 |D|² (n + 1)⁴` on their number.

## i. Overview

Orbit-box vertices embed in the buffered box. The canonical shell keeps the pairs of orbit-box
vertices at graph distance at least `n`; since the orbit box has at most `(2n + 1)² |D|` vertices
(`D` the fundamental domain), the shell has at most `81 |D|² (n + 1)⁴` pairs. These are the
counting inputs for polynomial connection shells in `Coverage`.
Both results are unconditional.

## ii. Key results

- `PeriodicGraph.canonicalConnectionShellPairs` : pairs of orbit-box vertices at distance at
  least `n`.
- `PeriodicGraph.mem_canonicalConnectionShellPairs_dist` : every canonical pair is at distance at
  least `n`.
- `PeriodicGraph.canonicalConnectionShellPairs_card_le` : the canonical shell has at most
  `81 |D|² (n + 1)⁴` pairs.

## iii. Table of contents

- A. Canonical shells
- B. Counting bounds

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open Finset MeasureTheory Set SimpleGraph

set_option linter.unusedSectionVars false

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

/-! ## A. Canonical shells -/

/-- The embedding of orbit-box vertices into the buffered box of the same radius. -/
noncomputable def PeriodicGraph.orbitVertexToBuffered
    (P : PeriodicGraph V) (n : Nat) :
    P.OrbitVertex n ↪ P.BufferedVertex n where
  toFun x := ⟨x.1, P.orbitBox_mono (P.id_le_bufferedRadius n) x.2⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : P.BufferedVertex n => z.1) hxy

/-- All pairs of orbit-box vertices of radius `n`, as pairs of buffered-box vertices. -/
noncomputable def PeriodicGraph.orbitShellCandidatePairs
    (P : PeriodicGraph V) (n : Nat) :
    Finset (P.BufferedVertex n × P.BufferedVertex n) :=
  ((Finset.univ : Finset (P.OrbitVertex n)) ×ˢ
      (Finset.univ : Finset (P.OrbitVertex n))).image
    (fun xy => (P.orbitVertexToBuffered n xy.1,
      P.orbitVertexToBuffered n xy.2))

/-- The canonical shell of radius `n`: pairs of orbit-box vertices at graph distance at least `n`.
-/
noncomputable def PeriodicGraph.canonicalConnectionShellPairs
    (P : PeriodicGraph V) (n : Nat) :
    Finset (P.BufferedVertex n × P.BufferedVertex n) :=
  (P.orbitShellCandidatePairs n).filter
    (fun xy => n ≤ P.graph.dist xy.1.1 xy.2.1)

/-- Every pair in the canonical shell of radius `n` is at graph distance at least `n`. -/
lemma PeriodicGraph.mem_canonicalConnectionShellPairs_dist
    (P : PeriodicGraph V) (n : Nat)
    (xy : P.BufferedVertex n × P.BufferedVertex n)
    (hxy : xy ∈ P.canonicalConnectionShellPairs n) :
    n ≤ P.graph.dist xy.1.1 xy.2.1 := by
  exact (Finset.mem_filter.1 hxy).2

/-! ## B. Counting bounds -/

lemma PeriodicGraph.orbitShellCandidatePairs_card_le
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

/-- The canonical shell of radius `n` has at most `81 |D|² (n + 1)⁴` pairs, `D` the fundamental
domain. -/
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
