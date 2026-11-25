/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.AssociatedGraded
public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.SymmetricComparison

/-!
# Basis coordinates and the intrinsic PBW comparison

A chosen ordered basis identifies the basis-indexed PBW graded model with the intrinsic
associated graded enveloping algebra, preserving symbols, scalars, and multiplication.

The resulting symmetric-algebra equivalence has the canonical symmetric comparison as its
underlying algebra map. Thus the forward map is independent of the basis choice.
-/

@[expose] public section

noncomputable section

universe u v w w'

namespace UniversalEnvelopingAlgebra

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

namespace PBW

/-- The constructed basis wrapper has the linear quotient direct-sum structure, by its addition
and scalar characteristic laws. -/
def associatedGradedRawLinearEquiv (b : Module.Basis I R L) :
    PBW.AssociatedGraded b ≃ₗ[R] GradedModule R L where
  __ := associatedGradedRawEquiv b
  map_add' := associatedGraded_toGradedModule_add b
  map_smul' := associatedGraded_toGradedModule_smul b

end PBW

/-- The intrinsic graded algebra and the old PBW wrapper have literally the same quotient
direct-sum carrier. -/
def associatedGradedBasisLinearEquiv (b : Module.Basis I R L) :
    AssociatedGraded R L ≃ₗ[R] PBW.AssociatedGraded b :=
  (PBW.associatedGradedRawLinearEquiv b).symm

@[simp]
theorem associatedGradedBasisLinearEquiv_symbol (b : Module.Basis I R L) (n : ℕ)
    (u : degreeFiltration R L n) :
    associatedGradedBasisLinearEquiv b (associatedGradedSymbol R L n u) = PBW.symbol b n u := by
  apply (PBW.associatedGradedRawLinearEquiv b).injective
  change DirectSum.lof R ℕ (PBW.GradedLayer R L) n
      ((PBW.gradedLowerStage R L n).mkQ u) = (PBW.symbol b n u).toGradedModule
  exact (PBW.ofGradedLayer_toGradedModule b n _).symm

theorem associatedGradedBasisLinearEquiv_one (b : Module.Basis I R L) :
    associatedGradedBasisLinearEquiv b 1 = 1 := by
  rw [← associatedGradedSymbol_one R L, associatedGradedBasisLinearEquiv_symbol, PBW.symbol_one]

theorem associatedGradedBasisLinearEquiv_mul (b : Module.Basis I R L)
    (x y : AssociatedGraded R L) :
    associatedGradedBasisLinearEquiv b (x * y) =
      associatedGradedBasisLinearEquiv b x * associatedGradedBasisLinearEquiv b y := by
  have h : ∀ x : AssociatedGraded R L, ∀ y : AssociatedGraded R L,
      associatedGradedBasisLinearEquiv b (x * y) =
        associatedGradedBasisLinearEquiv b x * associatedGradedBasisLinearEquiv b y := by
    intro x
    refine FilteredAlgebra.symbol_induction (degreeFiltration R L) ?_ ?_ ?_ x
    · intro y
      rw [zero_mul, map_zero, zero_mul]
    · intro n u y
      refine FilteredAlgebra.symbol_induction (degreeFiltration R L) ?_ ?_ ?_ y
      · rw [mul_zero, map_zero, mul_zero]
      · intro m v
        change associatedGradedBasisLinearEquiv b
            (associatedGradedSymbol R L n u * associatedGradedSymbol R L m v) =
          associatedGradedBasisLinearEquiv b (associatedGradedSymbol R L n u) *
            associatedGradedBasisLinearEquiv b (associatedGradedSymbol R L m v)
        rw [associatedGradedSymbol_mul, associatedGradedBasisLinearEquiv_symbol,
          associatedGradedBasisLinearEquiv_symbol, associatedGradedBasisLinearEquiv_symbol,
          PBW.symbol_mul]
      · intro y z hy hz
        rw [mul_add, map_add, hy, hz, map_add, mul_add]
    · intro x y hx hy z
      rw [add_mul, map_add, hx z, hy z, map_add, add_mul]
  exact h x y

/-- Equality of the two associated graded products, from their symbol multiplication laws. -/
def associatedGradedBasisEquiv (b : Module.Basis I R L) :
    AssociatedGraded R L ≃ₐ[R] PBW.AssociatedGraded b :=
  AlgEquiv.ofLinearEquiv (associatedGradedBasisLinearEquiv b)
    (associatedGradedBasisLinearEquiv_one b) (associatedGradedBasisLinearEquiv_mul b)

@[simp]
theorem associatedGradedBasisEquiv_symbol (b : Module.Basis I R L) (n : ℕ)
    (u : degreeFiltration R L n) :
    associatedGradedBasisEquiv b (associatedGradedSymbol R L n u) = PBW.symbol b n u :=
  associatedGradedBasisLinearEquiv_symbol b n u

/-- The free PBW isomorphism on the intrinsic quotient algebra. -/
def symmetricPBWEquivOfBasis (b : Module.Basis I R L) :
    SymmetricAlgebra R L ≃ₐ[R] AssociatedGraded R L :=
  (PBW.symmetricPBWEquiv b).trans (associatedGradedBasisEquiv b).symm

@[simp]
theorem symmetricPBWEquivOfBasis_ι (b : Module.Basis I R L) (x : L) :
    symmetricPBWEquivOfBasis b (SymmetricAlgebra.ι R L x) =
      associatedGradedGeneratorSymbol R L x := by
  apply (associatedGradedBasisEquiv b).injective
  change associatedGradedBasisEquiv b
      ((associatedGradedBasisEquiv b).symm
        (PBW.symmetricPBWEquiv b (SymmetricAlgebra.ι R L x))) =
    associatedGradedBasisEquiv b (associatedGradedGeneratorSymbol R L x)
  rw [AlgEquiv.apply_symm_apply, PBW.symmetricPBWEquiv_ι_apply,
    PBW.generatorSymbol_apply, associatedGradedGeneratorSymbol_apply,
    associatedGradedBasisEquiv_symbol]

/-- The free PBW isomorphism is exactly the canonical symmetric lift. -/
theorem symmetricPBWEquivOfBasis_toAlgHom (b : Module.Basis I R L) :
    (symmetricPBWEquivOfBasis b).toAlgHom = symmetricComparison R L := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  exact (symmetricPBWEquivOfBasis_ι b x).trans (symmetricComparison_ι R L x).symm

/-- The isomorphism on the intrinsic graded carrier is independent of the chosen basis and of its
ordered index type. -/
theorem symmetricPBWEquivOfBasis_eq {J : Type w'} [LinearOrder J]
    (b : Module.Basis I R L) (c : Module.Basis J R L) :
    symmetricPBWEquivOfBasis b = symmetricPBWEquivOfBasis c := by
  apply AlgEquiv.ext
  intro x
  change (symmetricPBWEquivOfBasis b).toAlgHom x = (symmetricPBWEquivOfBasis c).toAlgHom x
  rw [symmetricPBWEquivOfBasis_toAlgHom, symmetricPBWEquivOfBasis_toAlgHom]

variable (R L)

/-- PBW for a free underlying module now concerns the intrinsic associated graded algebra and its
canonical comparison. -/
theorem symmetricComparison_bijective_of_free [Module.Free R L] :
    Function.Bijective (symmetricComparison R L) := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex R L) := linearOrderOfSTO WellOrderingRel
  rw [← symmetricPBWEquivOfBasis_toAlgHom (Module.Free.chooseBasis R L)]
  exact (symmetricPBWEquivOfBasis (Module.Free.chooseBasis R L)).bijective

end UniversalEnvelopingAlgebra
