/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.PushoutFlag
public import MathlibExt.KTheory.Exact.Quillen.Basic

/-!
# Explicit six-cell flag data for a raw Quillen span

For a raw admissible span `X ←↞ S.apex ↪ Y`, this file packages explicit
kernel, pushout, and quotient objects; the maps relating the six nonzero
cells; the pushout square; and all four admissible exact sequences needed by
a later genuine degree-three flag.

Every raw span admits such data. The existence theorem does not select a
global flag or introduce an instance. This file adds no span-isomorphism
transport, quotient descent, composition or exact-functor coherence,
Stage-3 object, edgewise construction, realization, equivalence, additivity,
K-space, `π₀`/`K₀`, spectrum, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Explicit exact six-cell flag data attached to a raw Quillen span.

The nonzero cells are `kernelObj`, `S.apex`, `Y`, `X`, `pushoutObj`, and
`quotientObj`. The four exact triples are kernel/apex/source,
kernel/target/pushout, apex/target/quotient, and source/pushout/quotient. -/
structure QuillenSpanFlagData {X Y : C} (S : QuillenSpan X Y) where
  /-- Kernel object for the admissible epi `S.l`. -/
  kernelObj : C
  /-- Pushout object of `S.r` along `S.l`. -/
  pushoutObj : C
  /-- Quotient object for the admissible mono `S.r`. -/
  quotientObj : C
  /-- Kernel inclusion. -/
  kernelι : kernelObj ⟶ S.apex
  /-- Quotient projection. -/
  quotientπ : Y ⟶ quotientObj
  /-- Pushout leg from the source. -/
  sourceToPushout : X ⟶ pushoutObj
  /-- Pushout leg from the target. -/
  targetToPushout : Y ⟶ pushoutObj
  /-- Induced map from the pushout to the quotient. -/
  pushoutToQuotient : pushoutObj ⟶ quotientObj
  /-- The kernel inclusion followed by the span left leg is zero. -/
  kernel_left_zero : kernelι ≫ S.l = 0
  /-- The span right leg followed by the quotient projection is zero. -/
  right_quotient_zero : S.r ≫ quotientπ = 0
  /-- Pushout square, oriented as
  `S.l ≫ sourceToPushout = S.r ≫ targetToPushout`. -/
  pushoutSquare :
    IsPushout S.l S.r sourceToPushout targetToPushout
  /-- The pushout-to-quotient map restricts to the quotient projection on
  the target leg. -/
  target_pushoutToQuotient :
    targetToPushout ≫ pushoutToQuotient = quotientπ
  /-- The pushout-to-quotient map kills the source leg. -/
  source_pushoutToQuotient_zero :
    sourceToPushout ≫ pushoutToQuotient = 0
  /-- The lower-left sequence has zero composite. -/
  kernel_targetToPushout_zero :
    (kernelι ≫ S.r) ≫ targetToPushout = 0
  /-- The original left-leg sequence `K ↪ S.apex ↠ X`. -/
  kernel_apex_source_exact :
    IsAdmissibleExact
      (ShortComplex.mk kernelι S.l kernel_left_zero)
  /-- The original right-leg sequence `S.apex ↪ Y ↠ Q`. -/
  apex_target_quotient_exact :
    IsAdmissibleExact
      (ShortComplex.mk S.r quotientπ right_quotient_zero)
  /-- The completed lower-left sequence `K ↪ Y ↠ P`. -/
  kernel_target_pushout_exact :
    IsAdmissibleExact
      (ShortComplex.mk (kernelι ≫ S.r) targetToPushout
        kernel_targetToPushout_zero)
  /-- The completed lower-right sequence `X ↪ P ↠ Q`. -/
  source_pushout_quotient_exact :
    IsAdmissibleExact
      (ShortComplex.mk sourceToPushout pushoutToQuotient
        source_pushoutToQuotient_zero)

/-- The stored pushout-to-quotient map is the canonical map induced by the
stored pushout square and quotient projection. -/
theorem QuillenSpanFlagData.pushoutToQuotient_eq
    {X Y : C} {S : QuillenSpan X Y} (D : QuillenSpanFlagData S) :
    D.pushoutToQuotient =
      pushoutQuotientMap S.l S.r D.quotientπ D.sourceToPushout
        D.targetToPushout D.right_quotient_zero D.pushoutSquare := by
  apply D.pushoutSquare.hom_ext
  · rw [D.source_pushoutToQuotient_zero, pushoutQuotientMap_x]
  · rw [D.target_pushoutToQuotient, pushoutQuotientMap_y]

/-- Every raw Quillen span admits explicit six-cell flag data. This is only
an existence theorem: it does not choose a public flag. -/
theorem QuillenSpanFlagData.nonempty {X Y : C} (S : QuillenSpan X Y) :
    Nonempty (QuillenSpanFlagData S) := by
  obtain ⟨K, k, wk, hk⟩ := S.wl
  obtain ⟨Q, q, wq, hq⟩ := S.wr
  have hr : IsAdmissibleMono S.r := ⟨Q, q, wq, hq⟩
  obtain ⟨P, x, y, sq, _hx⟩ :=
    ExactCategory.admissibleMono_pushout
      (X := S.apex) (Y := Y) (i := S.r) hr
      (X' := X) (f := S.l)
  let pq : P ⟶ Q := pushoutQuotientMap S.l S.r q x y wq sq
  have hxpq : x ≫ pq = 0 := by
    exact pushoutQuotientMap_x S.l S.r q x y wq sq
  have hypq : y ≫ pq = q := by
    exact pushoutQuotientMap_y S.l S.r q x y wq sq
  have hky : (k ≫ S.r) ≫ y = 0 := by
    rw [Category.assoc, ← sq.w, ← Category.assoc, wk, zero_comp]
  have hKYP :
      IsAdmissibleExact (ShortComplex.mk (k ≫ S.r) y hky) := by
    simpa only using
      isAdmissibleExact_comp_pushout k S.l S.r q x y wk wq hk hq sq
  have hXPQ : IsAdmissibleExact (ShortComplex.mk x pq hxpq) := by
    simpa only [pq] using
      isAdmissibleExact_pushoutQuotientMap S.l S.r q x y wq hq sq
  exact ⟨{
    kernelObj := K
    pushoutObj := P
    quotientObj := Q
    kernelι := k
    quotientπ := q
    sourceToPushout := x
    targetToPushout := y
    pushoutToQuotient := pq
    kernel_left_zero := wk
    right_quotient_zero := wq
    pushoutSquare := sq
    target_pushoutToQuotient := hypq
    source_pushoutToQuotient_zero := hxpq
    kernel_targetToPushout_zero := hky
    kernel_apex_source_exact := hk
    apex_target_quotient_exact := hq
    kernel_target_pushout_exact := hKYP
    source_pushout_quotient_exact := hXPQ }⟩

end AlgebraicKTheory
