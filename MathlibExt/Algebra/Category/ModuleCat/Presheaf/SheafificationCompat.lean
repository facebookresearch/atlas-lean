/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

-- Additional author credit: Junyan Xu.




public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Sheafification over a sheaf of commutative rings

Let R be a sheaf of commutative rings on a site (C,J). Forgetting commutativity gives a sheaf
of rings with the same section rings; the identity comparison of the underlying ring
presheaves is locally injective and locally surjective.

Under the stated weak sheafification, locally bijective characterization for additive
presheaves, and preservation of sheaves by the ring-forgetful functor, this comparison defines
sheafification from R-module presheaves to module sheaves over the underlying ring sheaf.
-/

@[expose] public section

universe v v' u u'

open _root_.CategoryTheory CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace CategoryTheory.Sheaf

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (R : Sheaf J CommRingCat.{u})

/-- The identity comparison of underlying ring presheaves.

For a commutative ring sheaf R, its underlying ring presheaf is identified with the presheaf
underlying its ring-valued sheaf composition. The comparison morphism is the identity. -/
def commRingCatForget₂Id :
    R.obj ⋙ forget₂ _ RingCat.{u} ⟶ ((sheafCompose J (forget₂ ..)).obj R).obj :=
  𝟙 _

instance : Presheaf.IsLocallyInjective J (commRingCatForget₂Id R) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (𝟙 _))

instance :  Presheaf.IsLocallySurjective J (commRingCatForget₂Id R) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (𝟙 _))

end CategoryTheory.Sheaf

namespace PresheafOfModules

-- Upstream scopes this in a `section`; here it precedes `sheafificationCommId` only.
variable [HasWeakSheafify J AddCommGrpCat.{v}]

/-- Module sheafification over a commutative ring sheaf.

Using the identity comparison of underlying ring presheaves, sheafify R-module presheaves to
module sheaves over the corresponding ring sheaf, under the stated site and weak-
sheafification assumptions. -/
noncomputable abbrev sheafificationCommId [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :
    PresheafOfModules.{v} (R.obj ⋙ forget₂ ..) ⥤
    SheafOfModules.{v} ((sheafCompose J (forget₂ ..)).obj R) :=
  PresheafOfModules.sheafification (Sheaf.commRingCatForget₂Id R)

end PresheafOfModules

end
