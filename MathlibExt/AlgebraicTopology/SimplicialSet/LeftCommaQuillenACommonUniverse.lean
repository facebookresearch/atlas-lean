/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenACommonUniverse
import MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaOppositeComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ToTopReversal
import MathlibExt.CategoryTheory.NerveOppositeNaturality

/-!
# Genuine left-comma Quillen A in the actual native common universe

The SAME actual original StructuredArrow nerves are compared with the
right commas for the original opposite functor by canonical nerve
reversal. The full original realization isomorphisms and right-comma
Quillen A give weakness of the SAME original common-Hom nerve map.
-/

noncomputable section
universe u v w
open CategoryTheory Opposite
open scoped Simplicial
namespace SSet
variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- Genuine native common-universe Quillen A from weakness of EVERY actual original left comma nerve. -/
theorem nerveMapCommonHom_weak_of_leftComma (F : C ⥤ D)
    (hPoint : ∀ d : D, realizationWeakEquivalences
      (stdSimplex.isTerminalObj₀.from (nerve (StructuredArrow d F) : SSet.{max u v w}))) :
    realizationWeakEquivalences (nerveMapCommonHom.{u, w, v} F) := by
  have hOpp : realizationWeakEquivalences (nerveMapCommonHom.{u, w, v} F.op) := by
    apply nerveMapCommonHom_weak_of_rightComma.{u, v, w} F.op
    intro d
    let L : SSet.{max u v w} := nerve (StructuredArrow d.unop F)
    let R : SSet.{max u v w} := nerve (CostructuredArrow F.op d)
    let e := leftCommaOppositeNerveIso.{max u w, max v w, u} F d
    let e0 : SimplicialObject.opFunctor.obj (Δ[0] : SSet.{max u v w}) ≅ (Δ[0] : SSet.{max u v w}) :=
      stdSimplex.opIso.{max u v w} ⦋0⦌
    let _ : IsIso e0.hom := e0.isIso_hom
    have hs : realizationWeakEquivalences
        (SimplicialObject.opFunctor.map (stdSimplex.isTerminalObj₀.from L)) :=
      toTopReversal_mem_weakHomotopyEquivalences _ (hPoint d.unop)
    have hpost : realizationWeakEquivalences
        (SimplicialObject.opFunctor.map (stdSimplex.isTerminalObj₀.from L) ≫ e0.hom) :=
      realizationWeakEquivalences.comp_mem _ _ hs (realizationWeakEquivalences.of_isIso _)
    have heq : SimplicialObject.opFunctor.map (stdSimplex.isTerminalObj₀.from L) ≫ e0.hom =
        e.hom ≫ stdSimplex.isTerminalObj₀.from R :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [heq] at hpost
    exact realizationWeakEquivalences.of_precomp e.hom (stdSimplex.isTerminalObj₀.from R)
      (realizationWeakEquivalences.of_isIso _) hpost
  have hnat := nerveOppositeSimplicialIso_nerveMapCommonHom_naturality.{u, w, v} F
  have hrev := toTopReversalIso_naturality (nerveMapCommonHom.{u, w, v} F)
  let eC := SSet.toTop.mapIso (nerveOppositeSimplicialIso C) ≪≫ toTopReversalIso (nerve C)
  let eD := SSet.toTop.mapIso (nerveOppositeSimplicialIso D) ≪≫ toTopReversalIso (nerve D)
  have heq : SSet.toTop.map (nerveMapCommonHom.{u, w, v} F.op) ≫ eD.hom =
      eC.hom ≫ SSet.toTop.map (nerveMapCommonHom.{u, w, v} F) := by
    dsimp only [eC, eD, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← SSet.toTop.map_comp, ← hnat, SSet.toTop.map_comp,
      Category.assoc, hrev, ← Category.assoc]
  have hh := TopCat.weakHomotopyEquivalences.comp_mem _ _ hOpp
    (TopCat.weakHomotopyEquivalences.of_isIso eD.hom)
  rw [heq] at hh
  exact TopCat.weakHomotopyEquivalences.of_precomp _ _
    (TopCat.weakHomotopyEquivalences.of_isIso eC.hom) hh

end SSet
