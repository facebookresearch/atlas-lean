/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.Algebra.Category.ModuleCat.Monoidal.Universe
import MathlibExt.Algebra.Category.ModuleCat.CompatibleScalarRestriction
import MathlibExt.Algebra.DirectSum.InternalGrade
import MathlibExt.AlgebraicTopology.SemiSimplicialObject.Homotopy
import MathlibExt.AlgebraicTopology.SemiSimplicialObject.TruncatedAlternatingFaceMapComplex
import MathlibExt.AlgebraicTopology.AlternatingFaceMapComplex.HomologyZero
import MathlibExt.AlgebraicTopology.SimplicialObject.HomOfComponents
import MathlibExt.CategoryTheory.Comma.Over.Diagram
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Integer and torsion clients for simplicial and tensor coordinates

Constant nonzero integer modules distinguish the full alternating boundary from
the boundary omitting its last face. Their identity prisms and front insertions
detect the negative prism sign and positive contraction sign. Lifted integer
modules test the tensor unit in a carrier universe above the ground ring.

Copies of the integer ring in each natural degree give a nonzero graded action
in degrees one, two and three. A doubling map on ZMod 6 tests scalar restriction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped Simplicial TensorProduct DirectSum

namespace SemiSimplicialExportsTests

private abbrev Z0 : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
private abbrev Z1 : ModuleCat.{1} ℤ := ModuleCat.of ℤ (ULift.{1} ℤ)

-- The ordinary native unit outside the lifted scope.
example : (𝟙_ (ModuleCat.{0} ℤ)) = ModuleCat.of ℤ ℤ := rfl

section LiftedTensor

open scoped ModuleCat.UniverseTensor

-- The scoped unit has a carrier in Type 1 while the ring lies in Type 0.
example : (𝟙_ (ModuleCat.{1} ℤ)) = ModuleCat.of ℤ (ULift.{1} ℤ) := rfl

example :
    (λ_ Z1).hom ((ULift.up (3 : ℤ)) ⊗ₜ[ℤ] (ULift.up (2 : ℤ))) =
      ULift.up (6 : ℤ) := by
  rw [ModuleCat.UniverseTensor.leftUnitor_tmul]
  rfl

example :
    (ρ_ Z1).hom ((ULift.up (2 : ℤ)) ⊗ₜ[ℤ] (ULift.up (3 : ℤ))) =
        ULift.up (6 : ℤ) ∧
      (β_ Z1 Z1).hom ((ULift.up (2 : ℤ)) ⊗ₜ[ℤ] (ULift.up (3 : ℤ))) =
        (ULift.up (3 : ℤ)) ⊗ₜ[ℤ] (ULift.up (2 : ℤ)) := by
  letI : MonoidalPreadditive (ModuleCat.{1} ℤ) := inferInstance
  letI : MonoidalLinear ℤ (ModuleCat.{1} ℤ) := inferInstance
  constructor
  · rw [ModuleCat.UniverseTensor.rightUnitor_tmul]
    rfl
  · rfl

end LiftedTensor

private abbrev R6 := ZMod 6
private def doubleMod : R6 →ₗ[R6] R6 := (2 : R6) • LinearMap.id

example :
    ModuleCat.compatibleRestrictScalarsEquiv ℤ R6 R6
        (((ModuleCat.restrictScalars (algebraMap ℤ R6)).map
          (ModuleCat.ofHom doubleMod)) (1 : R6)) = (2 : R6) ∧
      (2 : R6) ≠ 0 := by
  constructor
  · have h := LinearMap.congr_fun
      (ModuleCat.compatibleRestrictScalarsEquiv_naturality ℤ R6 R6 doubleMod)
      (1 : (ModuleCat.restrictScalars (algebraMap ℤ R6)).obj (ModuleCat.of R6 R6))
    change ModuleCat.compatibleRestrictScalarsEquiv ℤ R6 R6
        (((ModuleCat.restrictScalars (algebraMap ℤ R6)).map
          (ModuleCat.ofHom doubleMod)) (1 : R6)) = doubleMod (1 : R6) at h
    exact h.trans (by rfl)
  · decide

private abbrev GF (_ : ℕ) := ℤ
private abbrev a3 : GF 1 := 3
private abbrev a2 : GF 2 := 2
private abbrev a6 : GF 3 := 6

example :
    ((DirectSum.decompose (DirectSum.internalGrade ℤ ℕ GF)
          (DirectSum.of GF 1 a3) 1 :
        DirectSum.internalGrade ℤ ℕ GF 1) : DirectSum ℕ GF) =
        DirectSum.of GF 1 a3 ∧
      DirectSum.of GF 1 a3 • DirectSum.of GF 2 a2 ∈
        DirectSum.internalGrade ℤ ℕ GF 3 ∧
      DirectSum.of GF 1 a3 • DirectSum.of GF 2 a2 = DirectSum.of GF 3 a6 ∧
      Module.Finite ℤ (DirectSum.internalGrade ℤ ℕ GF 1) := by
  constructor
  · simpa using DirectSum.coe_decompose_internalGrade ℤ ℕ GF
      (DirectSum.of GF 1 a3) 1
  · constructor
    · have h3 : DirectSum.of GF 1 a3 ∈ DirectSum.internalGrade ℤ ℕ GF 1 :=
        (DirectSum.mem_internalGrade_iff ℤ ℕ GF _ _).mpr ⟨a3, rfl⟩
      have h2 : DirectSum.of GF 2 a2 ∈ DirectSum.internalGrade ℤ ℕ GF 2 :=
        (DirectSum.mem_internalGrade_iff ℤ ℕ GF _ _).mpr ⟨a2, rfl⟩
      exact SetLike.GradedSMul.smul_mem h3 h2
    · constructor
      · rw [DirectSum.Gmodule.of_smul_of]
        rfl
      · exact Module.Finite.range (DirectSum.lof ℤ ℕ GF 1)

private abbrev semiZ : SemiSimplicialObject (ModuleCat.{0} ℤ) :=
  (Functor.const SemiSimplexCategoryᵒᵖ).obj Z0
private abbrev simpZ : SimplicialObject (ModuleCat.{0} ℤ) :=
  (Functor.const SimplexCategoryᵒᵖ).obj Z0

example :
    ((AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex
      (ModuleCat.{0} ℤ)).obj semiZ).d 1 0 = 0 := by
  letI : (AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex
    (ModuleCat.{0} ℤ)).Additive := inferInstance
  rw [AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex_obj_d]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val • (𝟙 Z0)) = 0
  rw [Fin.sum_univ_two]
  simp

example :
    ((AlgebraicTopology.lastFaceOmittedAlternatingFaceMapComplex
      (ModuleCat.{0} ℤ)).obj semiZ).d 1 0 = 𝟙 Z0 ∧
      (𝟙 Z0 : Z0 ⟶ Z0) ≠ 0 := by
  letI : (AlgebraicTopology.lastFaceOmittedAlternatingFaceMapComplex
    (ModuleCat.{0} ℤ)).Additive := inferInstance
  constructor
  · rw [AlgebraicTopology.lastFaceOmittedAlternatingFaceMapComplex_obj_d]
    change (∑ i : Fin 1, (-1 : ℤ) ^ i.val • (𝟙 Z0)) = 𝟙 Z0
    simp
  · intro h
    have h1 := congrArg (fun f : Z0 ⟶ Z0 => f (1 : ℤ)) h
    norm_num at h1

private def identityPrism :
    SemiSimplicialObject.Homotopy (𝟙 semiZ) (𝟙 semiZ) where
  h _ := 𝟙 Z0
  h_zero_comp_δ_zero _ := by simp [semiZ, SemiSimplicialObject.δ_def]
  h_last_comp_δ_last _ := by simp [semiZ, SemiSimplicialObject.δ_def]
  h_succ_comp_δ_castSucc_of_lt _ _ _ := by
    simp [semiZ, SemiSimplicialObject.δ_def]
  h_succ_comp_δ_castSucc_succ _ := by simp [semiZ, SemiSimplicialObject.δ_def]
  h_castSucc_comp_δ_succ_of_lt _ _ _ := by
    simp [semiZ, SemiSimplicialObject.δ_def]

example :
    identityPrism.toChainHomotopy.hom 0 1 (1 : ℤ) = (-1 : ℤ) := by
  rw [SemiSimplicialObject.Homotopy.toChainHomotopy_hom]
  change (-(∑ i : Fin 1, (-1 : ℤ) ^ i.val • (𝟙 Z0))) (1 : ℤ) = (-1 : ℤ)
  simp

private abbrev frontIdentity (n : ℕ) : semiZ _⦋n⦌ₛ ⟶ semiZ _⦋n + 1⦌ₛ := 𝟙 Z0
private theorem frontFirst (n : ℕ) :
    frontIdentity n ≫ semiZ.δ (0 : Fin (n + 2)) = 𝟙 (semiZ _⦋n⦌ₛ) := by
  simp [frontIdentity, semiZ, SemiSimplicialObject.δ_def]
private theorem frontShift (n : ℕ) (i : Fin (n + 1)) :
    frontIdentity (n + 1) ≫ semiZ.δ i.succ.castSucc =
      semiZ.δ i.castSucc ≫ frontIdentity n := by
  simp [frontIdentity, semiZ, SemiSimplicialObject.δ_def]

example :
    (AlgebraicTopology.LastFaceOmittedAlternatingFaceMapComplex.contractingHomotopy
      semiZ frontIdentity frontFirst frontShift).hom 0 1 (1 : ℤ) = (1 : ℤ) := by
  rw [AlgebraicTopology.LastFaceOmittedAlternatingFaceMapComplex.contractingHomotopy_hom]
  rfl

private def coequalizerToZ :
    coequalizer (simpZ.δ (0 : Fin 2)) (simpZ.δ (1 : Fin 2)) ⟶ Z0 :=
  coequalizer.desc (𝟙 Z0) (by simp [simpZ, SimplicialObject.δ_def])

private abbrev classTriangle : Z0 ⟶ Z0 :=
  AlgebraicTopology.AlternatingFaceMapComplex.homologyZeroClass simpZ ≫
    (AlgebraicTopology.AlternatingFaceMapComplex.homologyZeroIsoCoequalizer simpZ).hom ≫
      coequalizerToZ

example : classTriangle (7 : ℤ) = (7 : ℤ) := by
  have h : classTriangle = 𝟙 Z0 := by
    rw [show classTriangle =
      (AlgebraicTopology.AlternatingFaceMapComplex.homologyZeroClass simpZ ≫
        (AlgebraicTopology.AlternatingFaceMapComplex.homologyZeroIsoCoequalizer simpZ).hom) ≫
          coequalizerToZ from (Category.assoc _ _ _).symm]
    rw [AlgebraicTopology.AlternatingFaceMapComplex.homologyZeroIsoCoequalizer_class]
    exact coequalizer.π_desc _ _ _ _
  exact congrArg (fun f : Z0 ⟶ Z0 => f (7 : ℤ)) h

private def zDouble : Z0 ⟶ Z0 := ModuleCat.ofHom ((2 : ℤ) • LinearMap.id)
private def simplicialDouble : simpZ ⟶ simpZ :=
  SimplicialObject.homOfComponents (fun _ => zDouble)
    (by intro n i; simp [simpZ, SimplicialObject.δ_def])
    (by intro n i; simp [simpZ, SimplicialObject.σ_def])

example : simplicialDouble.app (op (SimplexCategory.mk 2)) (3 : ℤ) = (6 : ℤ) := by
  rw [show simplicialDouble.app (op (SimplexCategory.mk 2)) = zDouble from rfl]
  rfl

private abbrev J := Discrete (Fin 2)
private abbrev diagram : J ⥤ ModuleCat.{0} ℤ := (Functor.const J).obj Z0
private def diagramDouble : diagram ⟶ diagram where
  app _ := zDouble
  naturality _ := by simp [diagram]
private abbrev augmentedP : Over ((Functor.const J).obj Z0) := Over.mk diagramDouble
private abbrev augmentedQ : Over ((Functor.const J).obj Z0) := Over.mk (𝟙 diagram)
private def augmentedMap : augmentedP ⟶ augmentedQ :=
  Over.homMk diagramDouble (by simp)

example :
    (((Over.liftDiagramFunctor Z0).map augmentedMap).app (Discrete.mk (0 : Fin 2))).left
      (3 : ℤ) = (6 : ℤ) := rfl

end SemiSimplicialExportsTests
