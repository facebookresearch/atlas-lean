/-
Historical source header, verbatim:
  /-
  Copyright (c) 2026 @junekim623, Muse. All rights reserved.
  Released under Apache 2.0 license.
  Authors: @junekim623, Muse
  -/

/-
Author: @toskua
-/


Original source:
FormalizedTextbooks.Hartshorne1977.Algebra.Category.ModuleCat.Presheaf.StalkRingCatIso
Retained source at current upstream base c965fb053ef253e5d24b9d6c42b9bf17bea115e4.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Ring/commutative-ring stalk bridge for module presheaves

For a presheaf of commutative rings `R`, the `RingCat` stalk of
`R ⋙ forget₂ CommRingCat RingCat` is identified with the image of the
`CommRingCat` stalk, since `forget₂` preserves filtered colimits. The
identification sends germs to germs, and the two resulting module structures
on a module-presheaf stalk agree: acting by `r` through the commutative stalk
is the same as acting by its image through the ring stalk.

## Main declarations

* `PresheafOfModules.stalkRingCatIso` — the `RingCat` stalk iso.
* `PresheafOfModules.stalkRingEquiv` — the iso as a `RingEquiv`.
* `PresheafOfModules.stalkRingEquiv_germ` — the equiv sends germs to germs.
* `PresheafOfModules.stalkModule_smul_stalkRingEquiv` — the two stalk module
  structures agree through the equiv.
-/

@[expose] public section

universe u

open _root_.CategoryTheory CategoryTheory _root_.TopCat TopCat _root_.TopologicalSpace TopologicalSpace Limits

namespace PresheafOfModules

variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u})

/-- The `RingCat` stalk of `R ⋙ forget₂` is the image of the `CommRingCat`
stalk, since `forget₂ CommRingCat RingCat` preserves filtered colimits. -/
noncomputable def stalkRingCatIso (x : X) :
    (forget₂ CommRingCat RingCat.{u}).obj (R.stalk x) ≅
      TopCat.Presheaf.stalk (R ⋙ forget₂ CommRingCat RingCat.{u}) x :=
  preservesColimitIso (forget₂ CommRingCat RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R)

/-- The stalk bridge as a `RingEquiv` on carriers. -/
noncomputable def stalkRingEquiv (x : X) :
    ↥(R.stalk x) ≃+*
      ↥(TopCat.Presheaf.stalk (R ⋙ forget₂ CommRingCat RingCat.{u}) x) :=
  (stalkRingCatIso R x).ringCatIsoToRingEquiv

/-- The stalk bridge sends commutative germs to ring germs. -/
theorem stalkRingEquiv_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (r : ↥(R.obj (Opposite.op U))) :
    stalkRingEquiv R x (R.germ U x hx r) =
      TopCat.Presheaf.germ (R ⋙ forget₂ CommRingCat RingCat.{u}) U x hx r := by
  have h := ι_preservesColimitIso_hom (forget₂ CommRingCat RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R) (Opposite.op ⟨U, hx⟩)
  exact ConcreteCategory.congr_hom h r

/-- The `CommRingCat`-stalk and `RingCat`-stalk module structures on a
module-presheaf stalk agree through the stalk bridge. -/
theorem stalkModule_smul_stalkRingEquiv (x : X)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u}))
    (r : ↥(R.stalk x)) (m : ↥(TopCat.Presheaf.stalk M.presheaf x)) :
    (stalkRingEquiv R x r) • m = r • m := by
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  obtain ⟨V, hVU, hxV, a, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq R r hxU
  have hsV : TopCat.Presheaf.germ M.presheaf U x hxU s =
        TopCat.Presheaf.germ M.presheaf V x hxV
          (M.presheaf.map (homOfLE hVU).op s) :=
    (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hVU) x hxV s).symm
  rw [hsV, stalkRingEquiv_germ]
  have hRing := PresheafOfModules.germ_ringCat_smul
    (R := R ⋙ forget₂ CommRingCat RingCat.{u}) (M := M) (x := x)
    V hxV a (M.presheaf.map (homOfLE hVU).op s)
  have hComm := PresheafOfModules.germ_smul (R := R) M x
    V hxV a (M.presheaf.map (homOfLE hVU).op s)
  exact hRing.symm.trans hComm

end PresheafOfModules

end
