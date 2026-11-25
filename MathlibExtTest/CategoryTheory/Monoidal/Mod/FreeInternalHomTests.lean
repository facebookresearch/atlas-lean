/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Mod.FreeInternalHom
import Lean.Util.CollectAxioms

/-!
# Public clients for original free-module internal Homs

Evaluation, module linearity and target naturality work with equalizers alone.
The source-precomposition clients add only the original coequalizer hypothesis.
The tests use the actual free unit, bundled natural isomorphism and arbitrary
source-module arrows, with independent object and morphism universes.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace FreeInternalHomPublicClients

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] (A : CommMon C)

example (P : C) (N : Mod C A.X) :
    ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N).X ≅ (ihom P).obj N.X :=
  Mod.FreeInternalHom.iso A P N

example (P T : C) (N : Mod C A.X) (q : P ⊗ T ⟶ N.X) :
    ((Mod.freeForgetAdjunction A.X).unit.app P ▷ T) ≫
      Mod.FreeInternalHom.parameterExtension A P T N q = q :=
  Mod.FreeInternalHom.parameterExtension_generator A P T N q

example (P : C) (N : Mod C A.X) :
    Mod.FreeInternalHom.forward A P N ≫ Mod.FreeInternalHom.inverse A P N = 𝟙 _ :=
  (Mod.FreeInternalHom.iso A P N).hom_inv_id

example (P : C) (N : Mod C A.X) :
    Mod.FreeInternalHom.inverse A P N ≫ Mod.FreeInternalHom.forward A P N = 𝟙 _ :=
  (Mod.FreeInternalHom.iso A P N).inv_hom_id

example (P : C) {N N' : Mod C A.X} (f : N ⟶ N') :
    ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).map f).hom ≫
        (Mod.FreeInternalHom.comparison A P).hom.app N' =
      (Mod.FreeInternalHom.comparison A P).hom.app N ≫ (ihom P).map f.hom :=
  (Mod.FreeInternalHom.comparison A P).hom.naturality f

example (P : C) {N N' : Mod C A.X} (f : N ⟶ N') :
    (ihom P).map f.hom ≫ (Mod.FreeInternalHom.comparison A P).inv.app N' =
      (Mod.FreeInternalHom.comparison A P).inv.app N ≫
        ((Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).map f).hom :=
  (Mod.FreeInternalHom.comparison A P).inv.naturality f

example (P : C) (N M : Mod C A.X)
    (f : M ⟶ (Mod.internalHomOfEqualizer A ((Mod.free A.X).obj P)).obj N) :
    M ⟶ Mod.internalHomAuxiliary A P N :=
  f ≫ (Mod.FreeInternalHom.moduleIso A P N).hom

section Source

variable [HasCoequalizers C]

local instance : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
local instance : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

example {M M' : Mod C A.X} (f : M ⟶ M') (N : Mod C A.X) :
    ((MonoidalClosed.pre f).app N).hom ≫ Mod.internalHomι A M N =
      Mod.internalHomι A M' N ≫ (MonoidalClosed.pre f.hom).app N.X :=
  Mod.FreeInternalHom.precompose_projection A f N

example {P P' : C} (f : (Mod.free A.X).obj P' ⟶ (Mod.free A.X).obj P)
    (N : Mod C A.X) :
    ((MonoidalClosed.pre f).app N).hom ≫ Mod.FreeInternalHom.forward A P' N =
      Mod.internalHomι A ((Mod.free A.X).obj P) N ≫
        (MonoidalClosed.pre ((Mod.freeForgetAdjunction A.X).unit.app P' ≫ f.hom)).app N.X :=
  Mod.FreeInternalHom.forward_precompose A f N

example {P P' : C} (f : P' ⟶ P) (N : Mod C A.X) :
    ((MonoidalClosed.pre ((Mod.free A.X).map f)).app N).hom ≫
        Mod.FreeInternalHom.forward A P' N =
      Mod.FreeInternalHom.forward A P N ≫ (MonoidalClosed.pre f).app N.X :=
  Mod.FreeInternalHom.forward_free_map A f N

end Source

end FreeInternalHomPublicClients

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let some moduleIdx := env.getModuleIdxFor? ``CategoryTheory.Mod.FreeInternalHom.iso
    | throwError "The free-module internal-Hom API is not imported"
  let names := env.constants.fold (init := #[]) fun names name _ =>
    if env.getModuleIdxFor? name == some moduleIdx then names.push name else names
  unless names.size > 0 do
    throwError "No free-module internal-Hom declarations were audited"
  for name in names do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun ax =>
      ax != ``propext && ax != ``Quot.sound && ax != ``Classical.choice
    unless forbidden.isEmpty do
      throwError "Nonstandard axioms in {name}: {forbidden}"
  logInfo m!"Free-module internal-Hom public clients: {names.size} declarations, standard axioms"
