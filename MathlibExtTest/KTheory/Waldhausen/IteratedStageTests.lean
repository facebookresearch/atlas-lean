/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStage

public section
set_option autoImplicit false
noncomputable section

universe u v uD vD uE vE

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.IteratedStage

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Zero iterations retain the actual original carrier. -/
theorem originalIterationBase : IteratedStage C [] = C := iteratedStage_nil C

/-- The actual iterated category has its earned original Waldhausen value. -/
@[instance_reducible]
def originalIterationStructure (ns : List ℕ) :
    WaldhausenCategoryWithoutGluing (IteratedStage C ns) := inferInstance

/-- Successive iteration retains the literal original stage category. -/
theorem originalIterationSuccessor (n : ℕ) (ns : List ℕ) :
    IteratedStage C (n :: ns) = Stage (IteratedStage C ns) n :=
  iteratedStage_cons C n ns

variable {C}
variable {D : Type (max uD vD)} [Category.{vD} D] [HasZeroObject D]
    [WaldhausenCategoryWithoutGluing D]
variable {E : Type (max uE vE)} [Category.{vE} E] [HasZeroObject E]
    [WaldhausenCategoryWithoutGluing E]
variable {F : C ⥤ D} {G : D ⥤ E}

/-- Arbitrary original exact functors earn exactness at every iteration. -/
theorem originalIteratedMapExact (hF : F.IsWaldhausenExact) (ns : List ℕ) :
    (mapIteratedStage hF ns).IsWaldhausenExact :=
  mapIteratedStage_isWaldhausenExact hF ns

/-- The same exact functor retains its original value at degree list zero. -/
theorem originalIteratedMapBase (hF : F.IsWaldhausenExact) :
    mapIteratedStage hF [] = baseIteratedStageFunctor (F := F) :=
  mapIteratedStage_nil hF

/-- Arbitrary iterations retain the original identity functor. -/
theorem originalIteratedMapIdentity (ns : List ℕ) :
    mapIteratedStage (Functor.IsWaldhausenExact.id (C := C)) ns =
      𝟭 (IteratedStage C ns) := mapIteratedStage_id ns

/-- Independent source, middle and target universes retain actual composition. -/
theorem originalIteratedMapComposition (hF : F.IsWaldhausenExact)
    (hG : G.IsWaldhausenExact) (ns : List ℕ) :
    mapIteratedStage (hF.comp hG) ns =
      mapIteratedStage hF ns ⋙ mapIteratedStage hG ns :=
  mapIteratedStage_comp hF hG ns

/-- Every actual iteration retains the earned base gluing axiom, without a stage gluing input. -/
theorem originalIterationGluing (hGlue : WaldhausenGluingAxiom (C := C)) (ns : List ℕ) :
    WaldhausenGluingAxiom (C := IteratedStage C ns) :=
  iteratedStageWaldhausenGluingAxiom C hGlue ns

end MathlibExtTest.IteratedStage
