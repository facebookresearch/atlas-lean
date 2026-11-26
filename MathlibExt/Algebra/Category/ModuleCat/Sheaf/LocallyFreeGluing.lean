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
# Local freeness from free presentations on a cover

Let `(C,J)` be a site, `R : Sheaf J RingCat.{u}`, and `M` a module sheaf. Suppose a family `X
: I → C` covers the top and each restriction `M.over (X i)` is isomorphic to a free sheaf on
an index type `Ix i`. Under weak additive sheafification and the locally-bijective comparison
on all slice sites, `M` is locally free. The local basis sets may vary and may be infinite.

With additive sheafification on the slice sites and a fixed `n : ℕ`, if every `Ix i` is
equivalent to `Fin n`, the same local free presentations show that `M` is locally free of rank
`n`.
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

/-- Let `C : Type u₁` have morphism universe `v₁`, `J` a Grothendieck topology, and `R : Sheaf J
RingCat.{u}`. Assume weak additive sheafification and `WEqualsLocallyBijective` on every
`J.over X`. For `M : SheafOfModules.{u} R`, a covering family `X : I → C` with `I : Type w`,
sets `Ix i : Type u`, and isomorphisms `free_{R.over(X i)}(Ix i) ≅ M.over (X i)`, the sheaf
`M` is locally free. -/
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

/-- Let `C : Type u₁` have morphism universe `v₁`, `J` a Grothendieck topology, and `R : Sheaf J
RingCat.{u}`. Assume `HasSheafify` for additive presheaves and `WEqualsLocallyBijective` on
every `J.over X`. For `M : SheafOfModules.{u} R`, `n : ℕ`, a cover `X : I → C` with `I : Type
u₁`, sets `Ix i : Type u`, and isomorphisms `free_{R.over(X i)}(Ix i) ≅ M.over (X i)`, if
every `Ix i` admits an equivalence with `Fin n`, then `IsLocallyFreeOfRank M n`. -/
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
