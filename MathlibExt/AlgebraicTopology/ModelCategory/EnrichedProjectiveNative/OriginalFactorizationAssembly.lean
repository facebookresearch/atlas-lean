/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModelFromLevel
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Replacement
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK

/-!
# The actual native I/K records as inputs to generic model assembly

The existing native I record is classified for the original level dictionary.
The generic level adapter retypes that same entire record to the I lifting
classes. The K input is the original full-label K record at the original
realized cardinal and caller bottom. All original replacement and unit/counit
functions are retained. Generic assembly receives these complete records
and its class laws directly.

This supplies the given factor inputs for recognition. It neither assumes
nor proves the remaining all-target K-right weak-intersection law and does
not construct or claim completion of a native stable model.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OriginalFactorizationAssembly

open OperatorStabilizationK

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual existing level I value is reclassified without selecting another record. -/
def originalI :
    FunctorialFactorizationData (NativeK.levelI (I := A)).rlp.llp
      (NativeK.levelI (I := A)).rlp := by
  letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
    Native.modelCategory (B := B) (A := A)
  exact OriginalGeneratedModel.originalIFromLevel
    (Native.modelCategory (B := B) (A := A)) (NativeK.levelI (I := A))
    (Native.cofibrations_eq (B := B) (A := A))
    (Native.cofibrantFactorizationData (B := B) (A := A))

/-- The entire native I middle functor is the original existing level functor. -/
theorem originalI_Z :
    let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.modelCategory (B := B) (A := A)
    (originalI (B := B) (A := A)).Z =
      (Native.cofibrantFactorizationData (B := B) (A := A)).Z := rfl

/-- The entire native I inclusion remains the original level inclusion function. -/
theorem originalI_i :
    let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.modelCategory (B := B) (A := A)
    (originalI (B := B) (A := A)).i =
      (Native.cofibrantFactorizationData (B := B) (A := A)).i := rfl

/-- The entire native I projection remains the original level projection function. -/
theorem originalI_p :
    let : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      Native.modelCategory (B := B) (A := A)
    (originalI (B := B) (A := A)).p =
      (Native.cofibrantFactorizationData (B := B) (A := A)).p := rfl

/-- Keep the same actual original zero-arrow family in the complete I replacement. -/
def replacementFromI : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} A :=
  Diagrams.fromZeroArrow ⋙ (originalI (B := B) (A := A)).Z

/-- The whole reclassified I replacement is the actual original native Q functor. -/
theorem replacementFromI_eq_original : replacementFromI (B := B) (A := A) =
    Replacement.cofibrantReplacement (B := B) (A := A) := rfl

/-- Keep the entire original I projection natural transformation. -/
def replacementProjectionFromI :
    replacementFromI (B := B) (A := A) ⟶ 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Functor.whiskerLeft Diagrams.fromZeroArrow (originalI (B := B) (A := A)).p

/-- The entire projection is the original native Q counit, with all coefficients retained. -/
theorem replacementProjectionFromI_eq_original :
    replacementProjectionFromI (B := B) (A := A) =
      Replacement.cofibrantReplacementCounit (B := B) (A := A) := rfl

variable {L : Type} (s : NativeStabilizationFamily.{u, v} A L)

/-- The original full-label K record retains its entire original cardinal/bottom construction. -/
def originalK : FunctorialFactorizationData (NativeK.generators s).rlp.llp
    (NativeK.generators s).rlp := NativeK.factorizationData (B := B) s

/-- The whole returned K record is exactly the original supplied native K record. -/
theorem originalK_eq_original : originalK (B := B) s =
    NativeK.factorizationData (B := B) s := rfl

/-- The original terminal-arrow family supplies the complete K replacement. -/
def replacementFromK : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} A :=
  Diagrams.toZeroArrow ⋙ (originalK (B := B) s).Z

/-- The entire K replacement is the original full native Omega-replacement functor. -/
theorem replacementFromK_eq_original : replacementFromK (B := B) s =
    NativeK.omegaReplacement (B := B) s := rfl

/-- The K replacement unit is the original complete K inclusion natural transformation. -/
def replacementUnitFromK : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A) ⟶
    replacementFromK (B := B) s :=
  Functor.whiskerLeft Diagrams.toZeroArrow (originalK (B := B) s).i

/-- The entire unit is the actual original native K unit on every original coefficient. -/
theorem replacementUnitFromK_eq_original : replacementUnitFromK (B := B) s =
    NativeK.omegaReplacementUnit (B := B) s := rfl

end HomotopicalAlgebra.EnrichedProjective.Native.OriginalFactorizationAssembly
