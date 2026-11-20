/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldRectangleLimit










open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}




theorem PeriodicPlaneEmbedding.exists_uniform_translatedTemplate_mergeError_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Nat -> Finset V) (R : Nat -> ι -> Finset V) :
    ∃ radius : Nat -> Nat,
      (∀ n, n ≤ radius n) ∧
      ∀ (z : Nat -> Site 2) (i : Nat -> ι)
        (a b c d : Nat -> Real),
        (∀ n, (P.shift (z n) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) ->
        Tendsto (fun n => mu.real
          (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
            ((L n).image (P.shift (z n)))
            ((R n (i n)).image (P.shift (z n)))))
          atTop (nhds 0) := by
  obtain ⟨radius, hradius⟩ :=
    P.exists_uniform_pairMergeRadius mu hunique L R
  refine ⟨radius, fun n => (hradius n).1,
    fun z i a b c d hbox => ?_⟩
  have hepsilon : Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hepsilon
  intro n
  exact (E.translated_rectanglePairMergeErrorUnion_measureReal_le
    mu hTI (z n) (a n) (b n) (c n) (d n)
    (L n) (R n (i n)) (radius n) (hbox n)).trans
      (((hradius n).2 (i n)).le)

end StatMech.FK.PeriodicPlanar
