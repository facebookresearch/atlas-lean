/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectangleLimit

/-!
# Uniform merge radius for translated templates

Under uniqueness of the infinite cluster, one radius sequence makes the rectangle merge errors of
all translated template pairs from a finite family tend to zero.

## i. Overview

`rectanglePairMergeErrorUnion a b c d L R` is the event that two finite sources `L` and `R` both
reach the infinite cluster but are not joined inside the rectangle `[a, b] × [c, d]`. When the
infinite cluster is unique almost surely, the merge error of a fixed pair within the ball of
radius `N` tends to zero as `N → ∞`. Choosing the radius uniformly over a finite index set `ι`
(via `PeriodicGraph.exists_uniform_pairMergeRadius`) and using translation invariance, the merge
error tends to zero for any translates of the templates and any rectangles that contain the
translated buffered ball.

Headline fidelity:
`PeriodicPlaneEmbedding.exists_uniform_translatedTemplate_mergeError_tendsto_zero`
is proved conditionally on translation invariance and almost sure uniqueness of the infinite
cluster. The instance arguments `[Fintype ι] [DecidableEq ι]` are used only in the proof (the
type does not mention them); removing them would change the statement, so they are kept.

## ii. Key results

- `PeriodicPlaneEmbedding.exists_uniform_translatedTemplate_mergeError_tendsto_zero`

## iii. Table of contents

- A. Uniform merge radius

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Uniform merge radius -/

-- The instance binder is kept so that existing callers and the statement are unchanged.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- For a translation-invariant measure with a unique infinite cluster and a finite family of
template pairs `(L n, R n i)`, there is a radius sequence `radius n ≥ n` such that, for all
translations `z n`, choices `i n` and rectangles containing the translated buffered ball of radius
`radius n`, the rectangle merge error of the translated pair tends to zero. See also
`PeriodicGraph.exists_uniform_pairMergeRadius` (untranslated, in the ball). -/
lemma PeriodicPlaneEmbedding.exists_uniform_translatedTemplate_mergeError_tendsto_zero
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
