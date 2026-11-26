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
# Stalk rings before and after forgetting commutativity

For a commutative ring presheaf R on a topological space X, forgetting commutativity preserves
the filtered colimit defining the stalk. Thus the underlying ring of R_x is canonically
isomorphic to the RingCat stalk of the underlying ring presheaf.

The resulting ring equivalence sends germs to germs. On the stalk of an R-module presheaf,
scalar action through this equivalence agrees with the action of the commutative stalk ring.
-/

@[expose] public section

universe u

open _root_.CategoryTheory CategoryTheory _root_.TopCat TopCat _root_.TopologicalSpace TopologicalSpace Limits

namespace PresheafOfModules

variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u})

/-- The stalk isomorphism for forgetting ring commutativity.

The ring underlying the CommRingCat stalk R_x is isomorphic to the RingCat stalk of R with
commutativity forgotten. -/
noncomputable def stalkRingCatIso (x : X) :
    (forget₂ CommRingCat RingCat.{u}).obj (R.stalk x) ≅
      TopCat.Presheaf.stalk (R ⋙ forget₂ CommRingCat RingCat.{u}) x :=
  preservesColimitIso (forget₂ CommRingCat RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R)

/-- The ring equivalence between the two stalk constructions.

The stalk comparison gives a ring equivalence R_x ≃ ((forget commutativity) R)_x. -/
noncomputable def stalkRingEquiv (x : X) :
    ↥(R.stalk x) ≃+*
      ↥(TopCat.Presheaf.stalk (R ⋙ forget₂ CommRingCat RingCat.{u}) x) :=
  (stalkRingCatIso R x).ringCatIsoToRingEquiv

/-- The stalk ring equivalence preserves germ coordinates.

For r ∈ R(U) and x ∈ U, the equivalence sends the CommRingCat germ of r to the RingCat germ of
the same section. -/
theorem stalkRingEquiv_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (r : ↥(R.obj (Opposite.op U))) :
    stalkRingEquiv R x (R.germ U x hx r) =
      TopCat.Presheaf.germ (R ⋙ forget₂ CommRingCat RingCat.{u}) U x hx r := by
  have h := ι_preservesColimitIso_hom (forget₂ CommRingCat RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R) (Opposite.op ⟨U, hx⟩)
  exact ConcreteCategory.congr_hom h r

/-- Compatibility of the two stalk scalar actions.

For r ∈ R_x and m in a module-presheaf stalk, acting by the image of r under the stalk ring
equivalence equals acting by r through the commutative stalk ring. -/
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
