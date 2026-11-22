/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationKAdapter
import MathlibExt.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# The actual original κ small-object construction for native K

The literal correlated K family is small. Its actual native closed cell
diagrams and the proved finite source matrix supply all six original κ
eligibility fields. The resulting complete functorial factorization retains
the actual original small-object Z/i/p and every full Arrow map.
The right class is levelF with the original mapping TF corners. Stable
acyclicity and native Ω recognition are separate required joins.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MorphismProperty CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableK

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- Smallness is the original shared native family's same literal K result. -/
theorem generators_isSmall : generators.{u, v}.IsSmall.{v} := by
  rw [← StabilizationKAdapter.generators_eq]
  exact NativeK.generators_isSmall
    StabilizationKAdapter.family

/-- All six eligibility fields are those proved for the same original family and cardinal. -/
theorem generators_isCardinalForSmallObjectArgument :
    generators.{u, v}.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  StabilizationKAdapter.original_generators_eligible

/-- The genuine native K small-object argument is supplied by that same original κ. -/
theorem generators_hasSmallObjectArgument : generators.{u, v}.HasSmallObjectArgument.{v} :=
  ⟨⟨realizedGeneratorCardinal.{v}, inferInstance, B,
    generators_isCardinalForSmallObjectArgument⟩⟩

attribute [local instance] generators_isCardinalForSmallObjectArgument

/-- The actual original small-object functorial factorization of the literal K family. -/
abbrev factorizationData : FunctorialFactorizationData generators.{u, v}.rlp.llp generators.rlp :=
  StabilizationKAdapter.originalFactorizationData (B := B)

/-- Every complete chosen functor and natural map is the original κ small-object value. -/
theorem factorizationData_fields :
    let original :=
      SmallObject.functorialFactorizationData generators.{u, v} realizedGeneratorCardinal.{v}
    factorizationData.{u, v}.Z = original.Z ∧ factorizationData.{u, v}.i = original.i ∧
      factorizationData.{u, v}.p = original.p :=
  ⟨rfl, rfl, rfl⟩

/-- The middle object is the original chosen κ iteration on the same caller arrow. -/
theorem factorizationData_Z_obj (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    factorizationData.Z.obj f = SmallObject.obj generators realizedGeneratorCardinal.{v} f.hom :=
  rfl

/-- Every whole Arrow map is the literal original κ iteration map. -/
theorem factorizationData_Z_map {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (φ : f ⟶ g) :
    factorizationData.Z.map φ = SmallObject.objMap generators realizedGeneratorCardinal.{v} φ :=
  rfl

/-- The left factor is the literal original chosen κ small-object injection. -/
theorem factorizationData_i_app (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    factorizationData.i.app f = SmallObject.ιObj generators realizedGeneratorCardinal.{v} f.hom :=
  rfl

/-- The right factor is the literal original chosen κ small-object projection. -/
theorem factorizationData_p_app (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    factorizationData.p.app f = SmallObject.πObj generators realizedGeneratorCardinal.{v} f.hom :=
  rfl

/-- The same original factors compose to the same original caller arrow. -/
theorem factorizationData_fac (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    factorizationData.i.app f ≫ factorizationData.p.app f = f.hom :=
  factorizationData.fac_app

/-- Complete left naturality retains every original Arrow square. -/
theorem factorizationData_i_naturality {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}}
    (φ : f ⟶ g) :
    factorizationData.i.app f ≫ factorizationData.Z.map φ = φ.left ≫ factorizationData.i.app g :=
  (factorizationData.i.naturality φ).symm

/-- Complete right naturality retains every original Arrow square. -/
theorem factorizationData_p_naturality {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}}
    (φ : f ⟶ g) :
    factorizationData.Z.map φ ≫ factorizationData.p.app g = factorizationData.p.app f ≫ φ.right :=
  factorizationData.p.naturality φ

/-- The original shared K-left class consists of native projective cofibrations. -/
theorem left_le_cofibrations : generators.{u, v}.rlp.llp ≤
    cofibrations PointedCGWH.SequentialSpectrum.{u, v} := by
  rw [← StabilizationKAdapter.generators_eq]
  exact NativeK.left_le_cofibrations
    StabilizationKAdapter.family

/-- The full original right class retains its native level fibration condition. -/
theorem right_le_fibrations : generators.{u, v}.rlp ≤
    fibrations PointedCGWH.SequentialSpectrum.{u, v} := fun _ _ _ hf => (lifting_iff _).mp hf |>.1

/-- Every actual chosen original left factor is a native projective cofibration. -/
theorem factorizationData_i_cofibration (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    cofibrations PointedCGWH.SequentialSpectrum.{u, v} (factorizationData.i.app f) :=
  left_le_cofibrations _ (factorizationData.hi f)

/-- Every actual chosen original right factor is a native level fibration. -/
theorem factorizationData_p_fibration (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    fibrations PointedCGWH.SequentialSpectrum.{u, v} (factorizationData.p.app f) :=
  right_le_fibrations _ (factorizationData.hp f)

/-- The same actual chosen right factor satisfies every original mapping TF corner. -/
theorem factorizationData_p_corners (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    trivialFibrations PointedCGWH.{u, v}
      (PointedCGWH.NativeMappingCorner.square
        (stabilizationCylinderSource n) (factorizationData.p.app f)).π :=
  (lifting_iff _).mp (factorizationData.hp f) |>.2 n

/-- The proved original data gives both full lifting classes and their genuine factorization. -/
theorem weakFactorizationSystem :
    IsWeakFactorizationSystem generators.{u, v}.rlp.llp generators.rlp := by
  rw [← StabilizationKAdapter.generators_eq]
  exact NativeK.weakFactorizationSystem.{u, v} StabilizationKAdapter.family

/-- The shared native middle functor is the same original sequential K computation. -/
theorem factorizationData_Z_eq_native :
    factorizationData.{u, v}.Z =
      (NativeK.factorizationData.{u, v}
        (B := B) StabilizationKAdapter.family).Z :=
  rfl

/-- The entire original sequential K left transformation is preserved by native reuse. -/
theorem factorizationData_i_eq_native :
    HEq factorizationData.{u, v}.i
      (NativeK.factorizationData.{u, v}
        (B := B) StabilizationKAdapter.family).i :=
  HEq.rfl

/-- The entire original sequential K right transformation keeps its native projection. -/
theorem factorizationData_p_eq_native :
    HEq factorizationData.{u, v}.p
      (NativeK.factorizationData.{u, v}
        (B := B) StabilizationKAdapter.family).p :=
  HEq.rfl

end PointedCGWH.SequentialSpectrum.StableK
