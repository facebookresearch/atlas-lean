/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.OriginalFactorizationAssembly
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableClassAssembly

/-!
# Full native I and K factorizations in the stable candidate classes

The original I record factors every arrow as an I-left map followed by
a K-right Omega-test equivalence. The original K record factors every
arrow as an I-left Omega-test equivalence followed by a K-right map.
The only additional source condition for the second classification is
cofibrancy of the actual index Hom objects.

Both records retain the original realized-generator cardinal, ordinal
bottom, middle functor and its entire Arrow action, and both natural
factor maps. Their membership proofs are reclassified using the proved
native class inclusions. Constructing the stable model from these records
additionally uses the all-target right-class recognition theorem.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.StableFactorization

open OperatorStabilizationK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  Native.generatorsI_isCardinalForSmallObjectArgument
  NativeK.generators_isCardinalForSmallObjectArgument

/-- The complete original I record, classified by the actual stable candidate classes. -/
def cofibrantFactorizationData :
    FunctorialFactorizationData (NativeK.levelI (I := I)).rlp.llp
      ((NativeK.generators s).rlp ⊓ NativeK.omegaTests s) :=
  (OriginalFactorizationAssembly.originalI (B := B) (A := I)).ofLE
    le_rfl (NativeK.levelI_right_le_KRight_omegaTests s)

/-- The complete original K record, classified by actual Hom cofibrancy and native acyclicity. -/
def fibrantFactorizationData
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    FunctorialFactorizationData
      ((NativeK.levelI (I := I)).rlp.llp ⊓ NativeK.omegaTests s)
      (NativeK.generators s).rlp :=
  (NativeK.factorizationData s).ofLE
    (by
      rw [← Native.cofibrations_eq]
      exact NativeK.left_le_levelCofibrations_and_omegaTests s hHom)
    le_rfl

/-- The entire I middle functor is the original level I middle functor. -/
theorem cofibrantFactorizationData_Z :
    (cofibrantFactorizationData (B := B) s).Z =
      (OriginalFactorizationAssembly.originalI (B := B) (A := I)).Z := rfl

/-- The entire I inclusion is the original level I natural transformation. -/
theorem cofibrantFactorizationData_i :
    (cofibrantFactorizationData (B := B) s).i =
      (OriginalFactorizationAssembly.originalI (B := B) (A := I)).i := rfl

/-- The entire I projection is the original level I natural transformation. -/
theorem cofibrantFactorizationData_p :
    (cofibrantFactorizationData (B := B) s).p =
      (OriginalFactorizationAssembly.originalI (B := B) (A := I)).p := rfl

/-- Every original I Arrow map is the original realized-cardinal small-object map. -/
theorem cofibrantFactorizationData_Z_map
    {F G : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : F ⟶ G) :
    (cofibrantFactorizationData (B := B) s).Z.map φ =
      SmallObject.objMap (NativeK.levelI (I := I)) realizedGeneratorCardinal.{v} φ := rfl

/-- Every I inclusion component is the original same-cardinal injection. -/
theorem cofibrantFactorizationData_i_app
    (F : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (cofibrantFactorizationData (B := B) s).i.app F =
      SmallObject.ιObj (NativeK.levelI (I := I)) realizedGeneratorCardinal.{v} F.hom := rfl

/-- Every I projection component is the original same-cardinal projection. -/
theorem cofibrantFactorizationData_p_app
    (F : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (cofibrantFactorizationData (B := B) s).p.app F =
      SmallObject.πObj (NativeK.levelI (I := I)) realizedGeneratorCardinal.{v} F.hom := rfl

variable (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))

/-- The entire K middle functor is the original full-family K middle functor. -/
theorem fibrantFactorizationData_Z :
    (fibrantFactorizationData (B := B) s hHom).Z = (NativeK.factorizationData s).Z := rfl

/-- The entire K inclusion is the original full-family K natural transformation. -/
theorem fibrantFactorizationData_i :
    (fibrantFactorizationData (B := B) s hHom).i = (NativeK.factorizationData s).i := rfl

/-- The entire K projection is the original full-family K natural transformation. -/
theorem fibrantFactorizationData_p :
    (fibrantFactorizationData (B := B) s hHom).p = (NativeK.factorizationData s).p := rfl

/-- Every original K Arrow map is the full original realized-cardinal small-object map. -/
theorem fibrantFactorizationData_Z_map
    {F G : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : F ⟶ G) :
    (fibrantFactorizationData (B := B) s hHom).Z.map φ =
      SmallObject.objMap (NativeK.generators s) realizedGeneratorCardinal.{v} φ := rfl

/-- Every K inclusion component is the original correlated-family injection. -/
theorem fibrantFactorizationData_i_app
    (F : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (fibrantFactorizationData (B := B) s hHom).i.app F =
      SmallObject.ιObj (NativeK.generators s) realizedGeneratorCardinal.{v} F.hom := rfl

/-- Every K projection component is the original correlated-family projection. -/
theorem fibrantFactorizationData_p_app
    (F : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (fibrantFactorizationData (B := B) s hHom).p.app F =
      SmallObject.πObj (NativeK.generators s) realizedGeneratorCardinal.{v} F.hom := rfl

/-- The complete original I and K factorizations retain both original Arrow equations. -/
theorem factorizationData_fac
    (F : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (cofibrantFactorizationData (B := B) s).i.app F ≫
        (cofibrantFactorizationData (B := B) s).p.app F = F.hom ∧
      (fibrantFactorizationData (B := B) s hHom).i.app F ≫
        (fibrantFactorizationData (B := B) s hHom).p.app F = F.hom :=
  ⟨(cofibrantFactorizationData s).fac_app,
    (fibrantFactorizationData s hHom).fac_app⟩

/-- Both original natural transformations retain both sides of every original Arrow input. -/
theorem factorizationData_naturality
    {F G : CategoryTheory.Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (φ : F ⟶ G) :
    (cofibrantFactorizationData (B := B) s).i.app F ≫
        (cofibrantFactorizationData (B := B) s).Z.map φ =
      φ.left ≫ (cofibrantFactorizationData (B := B) s).i.app G ∧
    (cofibrantFactorizationData (B := B) s).Z.map φ ≫
        (cofibrantFactorizationData (B := B) s).p.app G =
      (cofibrantFactorizationData (B := B) s).p.app F ≫ φ.right ∧
    (fibrantFactorizationData (B := B) s hHom).i.app F ≫
        (fibrantFactorizationData (B := B) s hHom).Z.map φ =
      φ.left ≫ (fibrantFactorizationData (B := B) s hHom).i.app G ∧
    (fibrantFactorizationData (B := B) s hHom).Z.map φ ≫
        (fibrantFactorizationData (B := B) s hHom).p.app G =
      (fibrantFactorizationData (B := B) s hHom).p.app F ≫ φ.right :=
  ⟨((cofibrantFactorizationData s).i.naturality φ).symm,
    (cofibrantFactorizationData s).p.naturality φ,
    ((fibrantFactorizationData s hHom).i.naturality φ).symm,
    (fibrantFactorizationData s hHom).p.naturality φ⟩

end HomotopicalAlgebra.EnrichedProjective.Native.StableFactorization
