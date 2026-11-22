/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Native Kan fibrancy of arbitrary full subcomplexes

A full subcomplex of a Kan complex is Kan for any selected vertex set.
Horns of dimension at least two retain all vertices, so the existing full
inclusion lifting theorem restricts the original filler. A one-dimensional
horn is filled by the constant edge on its prescribed vertex. This asserts
fibrancy of the full subcomplex, not fibrancy of its inclusion; the latter
has a separate component-invariance hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Subcomplex

/-- Any native full subcomplex of a Kan complex is Kan, with no component-closure requirement. -/
theorem kanComplex_full {X : SSet.{u}} [KanComplex X] (V : Set (X _⦋0⦌)) :
    KanComplex (full V : SSet.{u}) := by
  rw [KanComplex.iff]
  intro n i f hf
  cases n with
  | zero =>
    fin_cases i
    · let a := f (1 : Fin 2) (by decide)
      refine ⟨SSet.const (SSet.yonedaEquiv a), ?_⟩
      intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · change SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.const (SSet.yonedaEquiv a) = a
        conv_rhs => rw [← SSet.yonedaEquiv.symm_apply_apply a, SSet.yonedaEquiv_symm_zero]
        rfl
    · let a := f (0 : Fin 2) (by decide)
      refine ⟨SSet.const (SSet.yonedaEquiv a), ?_⟩
      intro j hj
      fin_cases j
      · change SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.const (SSet.yonedaEquiv a) = a
        conv_rhs => rw [← SSet.yonedaEquiv.symm_apply_apply a, SSet.yonedaEquiv_symm_zero]
        rfl
      · exact (hj rfl).elim
  | succ n =>
    obtain ⟨g, hg⟩ := KanComplex.hornFilling (hf.desc ≫ (full V).ι)
    let _ : HasLiftingProperty (horn.{u} (n + 2) i).ι (full V).ι :=
      hasLiftingProperty_horn_full_ι V i
    let sq : CommSq hf.desc (horn.{u} (n + 2) i).ι (full V).ι g := ⟨hg⟩
    refine ⟨sq.lift, ?_⟩
    intro j hj
    rw [← horn.ι_ι_assoc i j hj, sq.fac_left]
    exact hf.ι_desc j hj

end SSet.Subcomplex
