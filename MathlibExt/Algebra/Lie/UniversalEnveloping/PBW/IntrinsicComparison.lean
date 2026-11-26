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
# PBW coordinates for the intrinsic associated graded algebra

Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L an ordered basis. The PBW
coordinate model and the intrinsic associated graded algebra share the quotient-layer direct
sum and are R-algebra equivalent, preserving the symbols and their product.

This gives Sym_R(L) ≃ₐ[R] gr(U_R(L)). Its forward algebra map is the canonical
generator-symbol comparison, so the entire equivalence is independent of the ordered basis and
its index universe. In particular, that canonical comparison is bijective whenever L is free
over R.
-/

@[expose] public section

noncomputable section

universe u v w w'

namespace UniversalEnvelopingAlgebra

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

namespace PBW

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I. The
equivalence from PBW.AssociatedGraded(b) to GradedModule R L is R-linear: it preserves both
addition and scalar multiplication. Its forward map takes the finite-support quotient-layer
coordinates, and its inverse returns the associated graded element with those coordinates. -/
def associatedGradedRawLinearEquiv (b : Module.Basis I R L) :
    PBW.AssociatedGraded b ≃ₗ[R] GradedModule R L where
  __ := associatedGradedRawEquiv b
  map_add' := associatedGraded_toGradedModule_add b
  map_smul' := associatedGraded_toGradedModule_smul b

end PBW

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I. There
is an R-linear equivalence gr(U_R(L)) ≃ₗ[R] PBW.AssociatedGraded(b). Both carriers consist of
the same finite-support sum of degree quotient layers; the equivalence sends an intrinsic
quotient-coordinate family to the PBW associated graded element with that family. -/
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

/-- For an ordered basis b : Basis I R L of an R-Lie algebra over a commutative ring R, the
quotient-coordinate linear equivalence gr(U_R(L)) ≃ₗ[R] PBW.AssociatedGraded(b) preserves the
unit and multiplication and hence is an R-algebra equivalence. The products agree because both
send degree-n and degree-m symbols to the degree-(n+m) symbol of the enveloping product. -/
def associatedGradedBasisEquiv (b : Module.Basis I R L) :
    AssociatedGraded R L ≃ₐ[R] PBW.AssociatedGraded b :=
  AlgEquiv.ofLinearEquiv (associatedGradedBasisLinearEquiv b)
    (associatedGradedBasisLinearEquiv_one b) (associatedGradedBasisLinearEquiv_mul b)

@[simp]
theorem associatedGradedBasisEquiv_symbol (b : Module.Basis I R L) (n : ℕ)
    (u : degreeFiltration R L n) :
    associatedGradedBasisEquiv b (associatedGradedSymbol R L n u) = PBW.symbol b n u :=
  associatedGradedBasisLinearEquiv_symbol b n u

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I. The
symmetric PBW coordinate equivalence followed by the inverse intrinsic-to-PBW graded
comparison gives Sym_R(L) ≃ₐ[R] gr(U_R(L)). Its forward map sends the symmetric generator x to
the degree-one symbol of ι(x). -/
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

/-- For an ordered basis b : Basis I R L over a commutative ring R, the underlying R-algebra
homomorphism of symmetricPBWEquivOfBasis(b) equals symmetricComparison R L. Both maps have
domain Sym_R(L) and codomain the intrinsic gr(U_R(L)), and send each symmetric generator x to
symbol_1(ι(x)). -/
theorem symmetricPBWEquivOfBasis_toAlgHom (b : Module.Basis I R L) :
    (symmetricPBWEquivOfBasis b).toAlgHom = symmetricComparison R L := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  exact (symmetricPBWEquivOfBasis_ι b x).trans (symmetricComparison_ι R L x).symm

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L and c : Basis J R L two
bases, with LinearOrder I and LinearOrder J. Then the R-algebra equivalences Sym_R(L) ≃ₐ[R]
gr(U_R(L)) constructed from b and c are equal. The basis index types may lie in independent
universes. Equality holds for the entire equivalences because their forward maps are the same
canonical generator-symbol comparison. -/
theorem symmetricPBWEquivOfBasis_eq {J : Type w'} [LinearOrder J]
    (b : Module.Basis I R L) (c : Module.Basis J R L) :
    symmetricPBWEquivOfBasis b = symmetricPBWEquivOfBasis c := by
  apply AlgEquiv.ext
  intro x
  change (symmetricPBWEquivOfBasis b).toAlgHom x = (symmetricPBWEquivOfBasis c).toAlgHom x
  rw [symmetricPBWEquivOfBasis_toAlgHom, symmetricPBWEquivOfBasis_toAlgHom]

variable (R L)

/-- Let R be a commutative ring and L an R-Lie algebra whose underlying R-module is free. The
canonical R-algebra map Sym_R(L) → gr(U_R(L)), taking a symmetric generator x to the
degree-one symbol of ι(x), is bijective. The assertion concerns the intrinsic
degree-filtration associated graded algebra and requires neither a specified ordered basis nor
a finite-rank or characteristic hypothesis. -/
theorem symmetricComparison_bijective_of_free [Module.Free R L] :
    Function.Bijective (symmetricComparison R L) := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex R L) := linearOrderOfSTO WellOrderingRel
  rw [← symmetricPBWEquivOfBasis_toAlgHom (Module.Free.chooseBasis R L)]
  exact (symmetricPBWEquivOfBasis (Module.Free.chooseBasis R L)).bijective

end UniversalEnvelopingAlgebra
