/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/


-- Original unranked source notice follows verbatim.
/-
Author: @junekim623, Muse
-/
-- Original ranked gluing source notice follows verbatim.
/-
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license.
Authors: @junekim623, Muse
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Gluing locally free sheaves from free presentations

For a cover of the terminal object, suppose each restriction of a module
sheaf is isomorphic to a free sheaf on an index type `Ix i`. The transported
free generators give local freeness. The index types may vary over the cover
and may be infinite. If each `Ix i` is equivalent to `Fin n`, the same cover
and generating sections give local freeness of rank `n`.
-/

@[expose] public section

universe u v₁ u₁ w

open _root_.CategoryTheory CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

namespace SheafOfModules

section Gluing

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules presented by free sheaves over a cover is locally
free. Each chart contributes the tautological generators transported along
its iso via Mathlib's `GeneratingSections.equivOfIso`; the resulting
local generator data is shrunk into the site universe by
`LocalGeneratorsData.isLocallyFree`. -/
theorem IsLocallyFree.of_free_isos {M : SheafOfModules.{u} R} {I : Type w}
    (X : I → C) (hX : J.CoversTop X) (Ix : I → Type u)
    (e : ∀ i, _root_.SheafOfModules.free (R := R.over (X i)) (Ix i) ≅ M.over (X i)) :
    M.IsLocallyFree := by
  let q : M.LocalGeneratorsData :=
    { I := I, X := X, coversTop := hX,
      generators := fun i => (_root_.SheafOfModules.GeneratingSections.equivOfIso (e i))
        (_root_.SheafOfModules.free.generatingSections (R := R.over (X i)) (Ix i)) }
  have : q.IsLocallyFreeData := ⟨fun i => by
    change IsIso (((_root_.SheafOfModules.free.generatingSections
      (R := R.over (X i)) (Ix i)).ofEpi (e i).hom).π)
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π,
      _root_.SheafOfModules.free.generatingSections_π]
    exact IsIso.comp_isIso' (Iso.isIso_hom (Iso.refl _)) (e i).isIso_hom⟩
  exact q.isLocallyFree

end Gluing

end SheafOfModules

end

@[expose] public section

universe u

open _root_.CategoryTheory CategoryTheory Limits

namespace SheafOfModules

universe u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf presented by finite-rank free sheaves over a cover is locally
free of that rank: each chart contributes the tautological generators
transported along its iso, and the rank data is the given index
equivalences. Ranked analogue of `IsLocallyFree.of_free_isos`. -/
theorem IsLocallyFreeOfRank.of_free_isos {M : SheafOfModules.{u} R} {n : ℕ}
    {I : Type u₁} (X : I → C) (hX : J.CoversTop X) (Ix : I → Type u)
    (e : ∀ i, _root_.SheafOfModules.free (R := R.over (X i)) (Ix i) ≅ M.over (X i))
    (r : ∀ i, Nonempty (Ix i ≃ Fin n)) :
    SheafOfModules.IsLocallyFreeOfRank (R := R) M n := by
  let q : M.LocalGeneratorsData :=
    { I := I, X := X, coversTop := hX,
      generators := fun i =>
        (_root_.SheafOfModules.free.generatingSections (R := R.over (X i)) (Ix i)).ofEpi (e i).hom }
  have hfree : q.IsLocallyFreeData := ⟨fun i => by
    change IsIso (((_root_.SheafOfModules.free.generatingSections
      (R := R.over (X i)) (Ix i)).ofEpi (e i).hom).π)
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π, _root_.SheafOfModules.free.generatingSections_π]
    exact IsIso.comp_isIso' (Iso.isIso_hom (Iso.refl _)) (e i).isIso_hom⟩
  refine ⟨q, { isLocallyFreeData := hfree, rank_eq := fun i => r i }⟩


end SheafOfModules

end
