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

public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The module exactness of finitely generated projectives

The existing split exact structure on `FGProjectiveCat` has exactly the
short complexes that are short exact after the actual inclusion into
`ModuleCat`. The quotient is projective, so the module short exact
sequence splits. Fullness and faithfulness lift the splitting through
the inclusion.

The ring need not be Noetherian. The ring and module universes are
independent, and neither a smallness nor a cancellation hypothesis is
imposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace FGProjectiveCat

variable {R : Type u} [Ring R]

/-- A short complex of finite projectives that is short exact as an
actual module sequence has a splitting in the finite projective
category, over an arbitrary ring. -/
def splittingOfModuleShortExact (S : ShortComplex (FGProjectiveCat.{v} R))
    (hS : (S.map (toModuleCat (R := R))).ShortExact) : S.Splitting := by
  let i := toModuleCat (R := R)
  let _ : Module.Projective R S.X₃.obj := S.X₃.property.2
  let _ : Projective (S.map i).X₃ :=
    inferInstanceAs (Projective S.X₃.obj)
  let t : (S.map i).Splitting := hS.splittingOfProjective
  let r : S.X₂ ⟶ S.X₁ := i.preimage t.r
  let s : S.X₃ ⟶ S.X₂ := i.preimage t.s
  exact
    { r := r
      s := s
      f_r := i.map_injective (by simpa [i, r, ShortComplex.map] using t.f_r)
      s_g := i.map_injective (by simpa [i, s, ShortComplex.map] using t.s_g)
      id := i.map_injective (by simpa [i, r, s, ShortComplex.map] using t.id) }

/-- The actual module short exact sequences are precisely the admissible
exact sequences for the existing split exact structure on finite
projectives. No Noetherian assumption is needed. -/
theorem isAdmissibleExact_iff_moduleShortExact (S : ShortComplex (FGProjectiveCat.{v} R)) :
    ExactCategory.IsAdmissibleExact S ↔ (S.map (toModuleCat (R := R))).ShortExact := by
  constructor
  · intro hS
    change Nonempty S.Splitting at hS
    obtain ⟨s⟩ := hS
    exact (s.map (toModuleCat (R := R))).shortExact
  · intro hS
    exact ExactCategory.isAdmissibleExact_of_splitting (splittingOfModuleShortExact S hS)

end FGProjectiveCat

end
