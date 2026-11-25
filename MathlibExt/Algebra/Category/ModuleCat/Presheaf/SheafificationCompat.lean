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

The canonical identity comparison on the underlying ring presheaves is
locally injective and locally surjective. It induces the sheafification
functor `PresheafOfModules.sheafificationCommId` for module presheaves over
a sheaf of commutative rings.
-/

@[expose] public section

universe v v' u u'

open _root_.CategoryTheory CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace CategoryTheory.Sheaf

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (R : Sheaf J CommRingCat.{u})

/-- The α argument for `PresheafOfModules.sheafification` when the presheaf of rings is
a sheaf of commutative rings. -/
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

/-- The sheafification functor for presheaves of modules over `R`. -/
noncomputable abbrev sheafificationCommId [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :
    PresheafOfModules.{v} (R.obj ⋙ forget₂ ..) ⥤
    SheafOfModules.{v} ((sheafCompose J (forget₂ ..)).obj R) :=
  PresheafOfModules.sheafification (Sheaf.commRingCatForget₂Id R)

end PresheafOfModules

end
