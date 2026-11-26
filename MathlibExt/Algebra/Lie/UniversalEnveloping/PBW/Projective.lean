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

public import MathlibExt.Algebra.Lie.ProjectiveFreeCover
public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.IntrinsicComparison

/-!
# PBW for projective underlying Lie modules

Let R be a commutative ring and L an R-Lie algebra whose underlying R-module is projective. A
free R-module Lie algebra W with Lie maps i : L → W and π : W → L satisfying πi=id gives a
split cover. The free PBW equivalence on W transfers through this retract to the intrinsic
associated graded of U_R(L).

The canonical map Sym_R(L) → gr(U_R(L)) is an R-algebra equivalence. Its inverse is gr(U_R(i))
followed by the inverse free-cover PBW equivalence and then Sym_R(π). This also proves
injectivity of ι : L → U_R(L). No finite-rank or characteristic hypothesis is imposed.
-/

@[expose] public section

noncomputable section

universe u v

namespace UniversalEnvelopingAlgebra

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L] [Module.Projective R L]

/-- For an arbitrary type X, choose a linear order on X. This order can be used on the basis index
of the free Lie cover in the projective PBW construction; no finiteness or pre-existing order
on X is required. -/
def coverIndexOrder (X : Type*) : LinearOrder X := by
  classical
  exact linearOrderOfSTO WellOrderingRel
attribute [local instance] coverIndexOrder

/-- Let R be a commutative ring and L an R-Lie algebra with projective underlying R-module. Let W
be its projective free Lie cover with inclusion i : L →ₗ⁅R⁆ W. Define Sym_R(L) →ₐ[R] Sym_R(W)
by the symmetric universal property, sending the generator x to the symmetric generator i(x).
This is Sym_R(i) for the chosen split cover. -/
abbrev coverSymmetricInclusion :
    SymmetricAlgebra R L →ₐ[R] SymmetricAlgebra R (LieAlgebra.ProjectiveFreeCover R L) :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι R (LieAlgebra.ProjectiveFreeCover R L)).comp
      (LieAlgebra.projectiveCoverInclusion R L).toLinearMap)

/-- Let R be a commutative ring and L an R-Lie algebra with projective underlying R-module. Let π
: W →ₗ⁅R⁆ L be the projection from its free Lie cover. The R-algebra map Sym_R(W) → Sym_R(L)
sends the symmetric generator w to the generator π(w). It is the symmetric lift of the
R-linear map obtained by composing π with the symmetric generator inclusion. -/
abbrev coverSymmetricProjection :
    SymmetricAlgebra R (LieAlgebra.ProjectiveFreeCover R L) →ₐ[R] SymmetricAlgebra R L :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι R L).comp (LieAlgebra.projectiveCoverProjection R L).toLinearMap)

/-- Let R be a commutative ring and L an R-Lie algebra with projective underlying R-module. Its
projective free cover W has a chosen basis, equipped with a linear order on its index type.
Applying free PBW to this basis gives Sym_R(W) ≃ₐ[R] gr(U_R(W)). The forward map is the
canonical degree-one generator-symbol comparison on W. -/
abbrev coverPBWEquiv :
    SymmetricAlgebra R (LieAlgebra.ProjectiveFreeCover R L) ≃ₐ[R]
      AssociatedGraded R (LieAlgebra.ProjectiveFreeCover R L) :=
  symmetricPBWEquivOfBasis (LieAlgebra.projectiveFreeCoverBasis R L)

theorem coverPBWEquiv_toAlgHom :
    (coverPBWEquiv R L).toAlgHom =
      symmetricComparison R (LieAlgebra.ProjectiveFreeCover R L) :=
  symmetricPBWEquivOfBasis_toAlgHom (LieAlgebra.projectiveFreeCoverBasis R L)

theorem coverSymmetricProjection_inclusion_apply (x : SymmetricAlgebra R L) :
    coverSymmetricProjection R L (coverSymmetricInclusion R L x) = x := by
  have h : (coverSymmetricProjection R L).comp (coverSymmetricInclusion R L) =
      AlgHom.id R (SymmetricAlgebra R L) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro a
    change SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι R L).comp (LieAlgebra.projectiveCoverProjection R L).toLinearMap)
        (SymmetricAlgebra.lift
          ((SymmetricAlgebra.ι R (LieAlgebra.ProjectiveFreeCover R L)).comp
            (LieAlgebra.projectiveCoverInclusion R L).toLinearMap)
          (SymmetricAlgebra.ι R L a)) = SymmetricAlgebra.ι R L a
    rw [SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
      SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
    exact congrArg (SymmetricAlgebra.ι R L)
      (LieAlgebra.projectiveCoverLinearProjection_inclusion_apply R L a)
  exact congrArg (fun f : SymmetricAlgebra R L →ₐ[R] SymmetricAlgebra R L => f x) h

/-- Let R be a commutative ring and L an R-Lie algebra with projective underlying R-module. For
its split free Lie cover i : L → W and π : W → L with π∘i=id_L, the canonical enveloping
algebra maps satisfy U_R(π) ∘ U_R(i) = id_{U_R(L)}. This is an equality of R-algebra maps on
the full enveloping algebra. -/
theorem map_projectiveCoverProjection_comp_inclusion :
    (map R (LieAlgebra.projectiveCoverProjection R L)).comp
        (map R (LieAlgebra.projectiveCoverInclusion R L)) =
      AlgHom.id R (UniversalEnvelopingAlgebra R L) := by
  rw [← map_comp, LieAlgebra.projectiveCoverProjection_comp_inclusion, map_id]

/-- Let R be a commutative ring and L an R-Lie algebra with projective underlying R-module. If i :
L → W and π : W → L are the inclusion and projection of its split free Lie cover, then
gr(U_R(π)) ∘ gr(U_R(i)) = id_{gr(U_R(L))}. These R-algebra maps are induced by the
filtration-preserving enveloping maps on the intrinsic degree quotient direct sums. -/
theorem associatedGradedMap_projectiveCoverProjection_comp_inclusion :
    (associatedGradedMap R (LieAlgebra.projectiveCoverProjection R L)).comp
        (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L)) =
      AlgHom.id R (AssociatedGraded R L) := by
  rw [← associatedGradedMap_comp, LieAlgebra.projectiveCoverProjection_comp_inclusion,
    associatedGradedMap_id]

/-- Let R be a commutative ring and L an R-Lie algebra with projective underlying R-module. For
its free cover i : L → W and π : W → L, and the free PBW equivalence e_W : Sym_R(W) ≃ₐ[R]
gr(U_R(W)), define gr(U_R(L)) →ₐ[R] Sym_R(L) as Sym_R(π) ∘ e_W⁻¹ ∘ gr(U_R(i)). This is the
inverse of the canonical symmetric comparison for L. -/
def projectivePBWInverse : AssociatedGraded R L →ₐ[R] SymmetricAlgebra R L :=
  (coverSymmetricProjection R L).comp
    ((coverPBWEquiv R L).symm.toAlgHom.comp
      (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L)))

/-- Let R be a commutative ring and L an R-Lie algebra with projective underlying R-module, with
free cover i : L → W, π : W → L, and basis PBW equivalence e_W. For x ∈ gr(U_R(L)), the
projective PBW inverse has value Sym_R(π)(e_W⁻¹(gr(U_R(i))(x))). Thus the formula first
includes the graded class into the cover, then uses the inverse free PBW coordinates and
projects in the symmetric algebra. -/
theorem projectivePBWInverse_apply (x : AssociatedGraded R L) :
    projectivePBWInverse R L x =
      SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι R L).comp (LieAlgebra.projectiveCoverProjection R L).toLinearMap)
        ((symmetricPBWEquivOfBasis (LieAlgebra.projectiveFreeCoverBasis R L)).symm
          (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L) x)) := rfl

theorem projectivePBWInverse_leftInverse (x : SymmetricAlgebra R L) :
    projectivePBWInverse R L (symmetricComparison R L x) = x := by
  have hi := congrArg
    (fun f : SymmetricAlgebra R L →ₐ[R]
        AssociatedGraded R (LieAlgebra.ProjectiveFreeCover R L) => f x)
    (symmetricComparison_naturality R (LieAlgebra.projectiveCoverInclusion R L))
  change associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L)
      (symmetricComparison R L x) =
    symmetricComparison R (LieAlgebra.ProjectiveFreeCover R L) (coverSymmetricInclusion R L x)
    at hi
  change coverSymmetricProjection R L
      ((coverPBWEquiv R L).symm
        (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L)
          (symmetricComparison R L x))) = x
  rw [hi, ← coverPBWEquiv_toAlgHom]
  change coverSymmetricProjection R L
      ((coverPBWEquiv R L).symm ((coverPBWEquiv R L) (coverSymmetricInclusion R L x))) = x
  rw [AlgEquiv.symm_apply_apply]
  exact coverSymmetricProjection_inclusion_apply R L x

theorem projectivePBWInverse_rightInverse (x : AssociatedGraded R L) :
    symmetricComparison R L (projectivePBWInverse R L x) = x := by
  let y := (coverPBWEquiv R L).symm
    (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L) x)
  have hp := congrArg
    (fun f : SymmetricAlgebra R (LieAlgebra.ProjectiveFreeCover R L) →ₐ[R]
        AssociatedGraded R L => f y)
    (symmetricComparison_naturality R (LieAlgebra.projectiveCoverProjection R L))
  change associatedGradedMap R (LieAlgebra.projectiveCoverProjection R L)
      (symmetricComparison R (LieAlgebra.ProjectiveFreeCover R L) y) =
    symmetricComparison R L (coverSymmetricProjection R L y) at hp
  change symmetricComparison R L (coverSymmetricProjection R L y) = x
  rw [← hp, ← coverPBWEquiv_toAlgHom]
  change associatedGradedMap R (LieAlgebra.projectiveCoverProjection R L)
      ((coverPBWEquiv R L) ((coverPBWEquiv R L).symm
        (associatedGradedMap R (LieAlgebra.projectiveCoverInclusion R L) x))) = x
  rw [AlgEquiv.apply_symm_apply]
  exact congrArg (fun f : AssociatedGraded R L →ₐ[R] AssociatedGraded R L => f x)
    (associatedGradedMap_projectiveCoverProjection_comp_inclusion R L)

/-- For an R-Lie algebra L over a commutative ring R with Module.Projective R L, the canonical
generator-symbol map defines Sym_R(L) ≃ₐ[R] gr(U_R(L)). Its inverse is Sym_R(π) ∘ e_W⁻¹ ∘
gr(U_R(i)) for the split free Lie cover W. The forward map remains the canonical
symmetricComparison, and no free basis of L is required. -/
def symmetricPBWEquivOfProjective : SymmetricAlgebra R L ≃ₐ[R] AssociatedGraded R L where
  __ := symmetricComparison R L
  invFun := projectivePBWInverse R L
  left_inv := projectivePBWInverse_leftInverse R L
  right_inv := projectivePBWInverse_rightInverse R L

@[simp]
theorem symmetricPBWEquivOfProjective_toAlgHom :
    (symmetricPBWEquivOfProjective R L).toAlgHom = symmetricComparison R L := rfl

@[simp]
theorem symmetricPBWEquivOfProjective_symm_apply (x : AssociatedGraded R L) :
    (symmetricPBWEquivOfProjective R L).symm x = projectivePBWInverse R L x := rfl

@[simp]
theorem symmetricPBWEquivOfProjective_ι (x : L) :
    symmetricPBWEquivOfProjective R L (SymmetricAlgebra.ι R L x) =
      associatedGradedGeneratorSymbol R L x := symmetricComparison_ι R L x

/-- Let R be a commutative ring and L an R-Lie algebra with projective underlying R-module. The
canonical map Sym_R(L) → gr(U_R(L)), sending x to the degree-one symbol of ι(x), is bijective.
Its domain and codomain are the symmetric algebra and intrinsic associated graded algebra; no
finite-generation, freeness, or characteristic condition is imposed. -/
theorem symmetricComparison_bijective_of_projective :
    Function.Bijective (symmetricComparison R L) :=
  (symmetricPBWEquivOfProjective R L).bijective

/-- Let R be a commutative ring, L an R-Lie algebra with projective underlying R-module, and b :
Basis I R L with LinearOrder I. The projective-cover PBW equivalence Sym_R(L) ≃ₐ[R] gr(U_R(L))
equals symmetricPBWEquivOfBasis(b). Both forward maps are the canonical generator-symbol
comparison, so the equality is of the entire R-algebra equivalences, including their inverses. -/
theorem symmetricPBWEquivOfProjective_eq_of_basis {I : Type*} [LinearOrder I]
    (b : Module.Basis I R L) :
    symmetricPBWEquivOfProjective R L = symmetricPBWEquivOfBasis b := by
  apply AlgEquiv.ext
  intro x
  change symmetricComparison R L x = (symmetricPBWEquivOfBasis b).toAlgHom x
  rw [symmetricPBWEquivOfBasis_toAlgHom]

/-- Let R be a commutative ring and L an R-Lie algebra whose underlying R-module is projective.
The canonical Lie map ι : L → U_R(L) is injective. The split free Lie cover transfers
injectivity from its free enveloping generator map; the hypothesis concerns the underlying
R-module, with no finite-rank or characteristic restriction. -/
theorem ι_injective_of_projective : Function.Injective (ι R (L := L)) := by
  intro x y hxy
  have hi : ι R (LieAlgebra.projectiveCoverInclusion R L x) =
      ι R (LieAlgebra.projectiveCoverInclusion R L y) := by
    simpa only [map_ι] using
      congrArg (map R (LieAlgebra.projectiveCoverInclusion R L)) hxy
  have hixy := (PBW.ι_injective_of_free
    (R := R) (L := LieAlgebra.ProjectiveFreeCover R L)) hi
  simpa only [LieAlgebra.projectiveCoverProjection_inclusion_apply] using
    congrArg (LieAlgebra.projectiveCoverProjection R L) hixy

end UniversalEnvelopingAlgebra
