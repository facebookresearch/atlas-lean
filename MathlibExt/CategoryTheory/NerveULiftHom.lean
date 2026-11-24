/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveULiftObject

/-!
# Original point-map weakness under the canonical Hom-lifted nerve

The existing `SSet.nerveULiftHomIso` retains every original arrow inside
the same source and target objects. Its inverse identifies the original
point maps, so their weakness is preserved and reflected.
-/

@[expose] public section


noncomputable section

universe u v w

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory

/-- The same full original nerve point-map property is preserved and reflected by canonical
source Hom universe lift. -/
theorem nerveULiftHom_point_weak_iff (C : Type u) [Category.{v} C] :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (nerve
      (ULiftHom.{w} C))) ↔
      SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (nerve C)) := by
  let e := (SSet.nerveULiftHomIso.{u,v,w} C).symm
  let p := SSet.stdSimplex.isTerminalObj₀.from (nerve C)
  let q := SSet.stdSimplex.isTerminalObj₀.from (nerve (ULiftHom.{w} C))
  let d := SSet.uliftStandardSimplexIso.{max u v,w} ⦋0⦌
  have he : e.hom ≫ q = SSet.uliftFunctor.map p ≫ d.hom :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  constructor
  · intro hq
    have hc := SSet.realizationWeakEquivalences.comp_mem e.hom q
      (SSet.realizationWeakEquivalences.of_isIso _) hq
    have hL :=
      (SSet.realizationWeakEquivalences.cancel_right_of_respectsIso (SSet.uliftFunctor.map
        p) d.hom).mp (he ▸ hc)
    exact (SSet.realizationWeak_ulift_map_iff p).mp hL
  · intro hp
    have hL := (SSet.realizationWeak_ulift_map_iff p).mpr hp
    have hc := SSet.realizationWeakEquivalences.comp_mem (SSet.uliftFunctor.map p) d.hom hL
      (SSet.realizationWeakEquivalences.of_isIso _)
    exact (SSet.realizationWeakEquivalences.cancel_left_of_respectsIso e.hom q).mp (he.symm ▸ hc)

end CategoryTheory
