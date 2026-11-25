/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanTerminalWeightRows

/-!
# Every original Bousfield--Kan simplex has a weighted source coefficient

The canonical terminal-weight row isomorphism retains a complete native
chain and its source coefficient in every degree. Its actual inverse
shows every simplex of the SAME Bousfield--Kan carrier lies in a weighted
inclusion. Full maps are consequently determined on these actual
inclusions, with independent indexing object and Hom universes.
-/

noncomputable section

universe uJ vJ

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

variable {J : Type uJ} [Category.{vJ} J]

/-- EVERY original Bousfield--Kan simplex comes from a full original weighted chain and
source coefficient. -/
theorem bkHocolim_simplex_has_weighted_preimage (D : J ⥤ SSet.{max uJ vJ}) (n : ℕ)
    (a : (bkHocolim D).obj (op ⦋n⦌)) :
    ∃ (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
      (x : (D.obj p.1.left).obj (op ⦋n⦌)),
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x = a := by
  let e := terminalWeightRowDegreeIso D (op ⦋n⦌) n
  let z := e.hom a
  let p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n := ⟨z.1, z.2.2⟩
  refine ⟨p, z.2.1, ?_⟩
  apply injective_of_mono e.hom
  have h := ConcreteCategory.congr_hom (terminalWeightRowDegreeIso_hom_rowIncl D (op ⦋n⦌) n p) z.2.1
  rw [wbarRowIncl_eq_wbarIncl_app] at h
  have he : (⟨z.1, z.2.1, z.2.2⟩ : CategoryBar.replObj J (wbarDegreeCoefficient D (op
  ⦋n⦌)) n) = z := by
    cases z
    rfl
  exact h.trans he

/-- Full maps from the SAME Bousfield--Kan carrier are determined on all their entire
original weighted inclusions. -/
theorem bkHocolim_hom_ext_weighted (D : J ⥤ SSet.{max uJ vJ}) {X : SSet.{max uJ vJ}}
    {f g : bkHocolim D ⟶ X}
    (h : ∀ n (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
      (a : (D.obj p.1.left).obj (op ⦋n⦌)),
      f.app (op ⦋n⦌) ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n
      p).app (op ⦋n⦌) a) =
      g.app (op ⦋n⦌) ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n
      p).app (op ⦋n⦌) a)) : f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  obtain ⟨p, x, rfl⟩ := bkHocolim_simplex_has_weighted_preimage D n a
  exact h n p x

end SSet
