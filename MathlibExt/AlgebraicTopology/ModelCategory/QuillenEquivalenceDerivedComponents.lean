/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedReplacementComparison
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# The canonical derived unit and counit of a genuine Quillen equivalence

The actual Hovey criterion and genuine replacement arrows make the
original canonical derived components invertible. Native model
factorizations supply the replacements; no weak unit, derived equivalence
or localization-equivalence outcome is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits MorphismProperty

namespace HomotopicalAlgebra
variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [adj.IsQuillenEquivalence]

local notation "WC" => weakEquivalences C
local notation "WD" => weakEquivalences D
local notation "data" => quillenDerivedAdjunctionData adj

/-- Any actual weak fibrant replacement proves invertibility of the SAME canonical derived unit
component. -/
theorem quillenEquivalenceDerived_unit_isIso_of_replacement
    (X : C) [IsCofibrant X] {Y : D} [IsFibrant Y]
    (f : L.obj X ⟶ Y) [WeakEquivalence f] :
    IsIso ((data).adjunction.unit.app ((WC).Q.obj X)) := by
  let _ : IsIso ((data).leftComparison.app X) :=
    quillenDerived_leftComparison_isIso_of_isCofibrant adj X
  let _ : IsIso ((data).rightComparison.app Y) :=
    quillenDerived_rightComparison_isIso_of_isFibrant adj Y
  let _ : IsIso ((WD).Q.map f) := Localization.inverts (WD).Q WD f (mem_weakEquivalences f)
  let _ : WeakEquivalence (adj.homEquiv X Y f) :=
    (Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff (adj := adj) f).mp inferInstance
  let _ : IsIso ((WC).Q.map (adj.homEquiv X Y f)) :=
    Localization.inverts (WC).Q WC _ (mem_weakEquivalences _)
  exact IsIso.of_isIso_fac_right (quillenDerived_unit_replacement_fac adj X f)

/-- Any actual weak cofibrant replacement proves invertibility of the SAME canonical derived counit
component. -/
theorem quillenEquivalenceDerived_counit_isIso_of_replacement
    {X : C} [IsCofibrant X] (Y : D) [IsFibrant Y]
    (g : X ⟶ R.obj Y) [WeakEquivalence g] :
    IsIso ((data).adjunction.counit.app ((WD).Q.obj Y)) := by
  let _ : IsIso ((data).leftComparison.app X) :=
    quillenDerived_leftComparison_isIso_of_isCofibrant adj X
  let _ : IsIso ((data).rightComparison.app Y) :=
    quillenDerived_rightComparison_isIso_of_isFibrant adj Y
  let _ : IsIso ((WC).Q.map g) := Localization.inverts (WC).Q WC g (mem_weakEquivalences g)
  have hf : WeakEquivalence ((adj.homEquiv X Y).symm g) := by
    apply (Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff (adj := adj) _).mpr
    simpa only [Equiv.apply_symm_apply] using (inferInstanceAs (WeakEquivalence g))
  let _ : WeakEquivalence ((adj.homEquiv X Y).symm g) := hf
  let _ : IsIso ((WD).Q.map ((adj.homEquiv X Y).symm g)) :=
    Localization.inverts (WD).Q WD _ (mem_weakEquivalences _)
  exact IsIso.of_isIso_fac_left (quillenDerived_counit_replacement_fac adj Y g)

/-- The original native model factorization supplies a replacement for every genuine cofibrant
source. -/
theorem quillenEquivalenceDerived_unit_isIso_of_isCofibrant
    (X : C) [IsCofibrant X] : IsIso ((data).adjunction.unit.app ((WC).Q.obj X)) := by
  let f := factorizationData (trivialCofibrations D) (fibrations D) (terminal.from (L.obj X))
  let _ : WeakEquivalence f.i := (weakEquivalence_iff _).mpr f.hi.2
  let _ : Fibration f.p := (fibration_iff _).mpr f.hp
  let _ : IsFibrant f.Z := (isFibrant_iff_of_isTerminal f.p terminalIsTerminal).mpr inferInstance
  exact quillenEquivalenceDerived_unit_isIso_of_replacement adj X f.i

/-- The original native model factorization supplies a replacement for every genuine fibrant target.
-/
theorem quillenEquivalenceDerived_counit_isIso_of_isFibrant
    (Y : D) [IsFibrant Y] : IsIso ((data).adjunction.counit.app ((WD).Q.obj Y)) := by
  let f := factorizationData (cofibrations C) (trivialFibrations C) (initial.to (R.obj Y))
  let _ : Cofibration f.i := (cofibration_iff _).mpr f.hi
  let _ : WeakEquivalence f.p := (weakEquivalence_iff _).mpr f.hp.2
  let _ : IsCofibrant f.Z := (isCofibrant_iff_of_isInitial f.i initialIsInitial).mpr inferInstance
  exact quillenEquivalenceDerived_counit_isIso_of_replacement adj Y f.p

end HomotopicalAlgebra
