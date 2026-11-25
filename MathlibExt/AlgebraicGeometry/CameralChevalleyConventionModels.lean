/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralAdmissibleTorusBundles

/-!
# The pinned Chevalley convention comparison

The adapter is an actual G group automorphism and its actual restriction
to N. It inverts the embedded torus, fixes the Weyl quotient, and uses
conjugation by the actual SL2 Weyl matrix on every simple-root SL2 map.
Its Lie and coefficient comparisons are fixed by every native jet and
adjoint matrix. The image of the Borel Lie module is the Cartan plus
the negative root spaces. Thus the normalizer scalar is inverted before
transporting beta; no function on arbitrary normalizer images is used.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 6--8 and 15--16;
the pinned Chevalley involution of a complex reductive group.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralChevalleyConventionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralReductiveSources
open CameralRamificationTensorModels CameralNormalizerShifts SchemeLieJetFamilies
open RegularCentralizerAffineModels ExpansionParameterModels RankTwoMatrixGroupModels
open scoped TensorProduct

theorem weyl_conjugation_normalizer {A : Type} [CommRing A] (c : Aˣ) :
    weylMatrix A * normalizerMatrix c * (weylMatrix A)⁻¹ = normalizerMatrix c⁻¹ := by
  calc
    weylMatrix A * normalizerMatrix c * (weylMatrix A)⁻¹ = weylMatrix A * diagonalMatrix c := by
      simp only [normalizerMatrix, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
    _ = normalizerMatrix c⁻¹ := by
      rw [normalizerMatrix]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [weylMatrix, diagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two]

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)

attribute [local instance] CameralRamificationTensorModels.torusGroup

def thetaSL2 : sl2Scheme ⟶ sl2Scheme :=
  SchemeLieJetFamilies.conjugate sl2Scheme
    (toUnit sl2Scheme ≫ RankTwoMatrixGroupModels.weylPoint) (𝟙 sl2Scheme)

def oppositeBorelModule : Submodule ℂ F.lie.carrier :=
  LinearMap.range F.source.cartan ⊔
    ⨆ (i : Fin F.roots.count) (_hi : PositiveRoot G tori F i),
      weightSpace G F.lie.carrier F.lie.model F.jets F.adjoint (tori F.rank)
        F.source.torus (-F.roots.exponent i)

structure ChevalleyComparison where
  group : G ≅ G
  group_hom : IsMonHom group.hom
  group_involution : group.hom ≫ group.hom = 𝟙 G
  torus : F.source.torus ≫ group.hom = ι[Torus F] ≫ F.source.torus
  normalizer : F.normalizer.scheme ≅ F.normalizer.scheme
  normalizer_hom : letI := F.normalizer.group; IsMonHom normalizer.hom
  normalizer_involution : normalizer.hom ≫ normalizer.hom = 𝟙 F.normalizer.scheme
  normalizer_inclusion : normalizer.hom ≫ F.normalizer.inclusion =
    F.normalizer.inclusion ≫ group.hom
  normalizer_torus : F.normalizer.torus ≫ normalizer.hom = ι[Torus F] ≫ F.normalizer.torus
  weyl : normalizer.hom ≫ F.normalizer.quotient = F.normalizer.quotient
  simpleSL2 : ∀ (i : Fin F.roots.count) (_hi : SimpleRoot G tori F i),
    (K.sl2 i).map ≫ group.hom = thetaSL2 ≫ (K.sl2 i).map
  lie : F.lie.carrier ≃ₗ[ℂ] F.lie.carrier
  lie_bracket : ∀ v w : F.lie.carrier, lie ⁅v, w⁆ = ⁅lie v, lie w⁆
  scalar : ∀ A : CommAlgCat.{0} ℂ, LieAt F.lie.carrier A ≃ₗ[A] LieAt F.lie.carrier A
  pure : ∀ (A : CommAlgCat.{0} ℂ) (a : A) (v : F.lie.carrier),
    scalar A (a ⊗ₜ[ℂ] v) = a ⊗ₜ[ℂ] lie v
  jets : ∀ (A : CommAlgCat.{0} ℂ) (v : LieAt F.lie.carrier A),
    jetPoint G F.lie.carrier F.lie.model F.jets A v ≫ group.hom =
      jetPoint G F.lie.carrier F.lie.model F.jets A (scalar A v)
  coefficients : ∀ {A A' : CommAlgCat.{0} ℂ} (f : A ⟶ A') (v : LieAt F.lie.carrier A),
    scalar A' (changeLie F.lie.carrier f v) = changeLie F.lie.carrier f (scalar A v)
  adjoint : ∀ (A : CommAlgCat.{0} ℂ) (g : affine A ⟶ G) (v : LieAt F.lie.carrier A),
    scalar A (F.adjoint.adjoint A g v) = F.adjoint.adjoint A (g ≫ group.hom) (scalar A v)
  cartan : ∀ v : Fin F.rank → ℂ, lie (F.source.cartan v) = -F.source.cartan v
  positive : ∀ (i : Fin F.roots.count) (_hi : SimpleRoot G tori F i),
    lie (K.sl2 i).positiveVector = -(K.sl2 i).negativeVector
  negative : ∀ (i : Fin F.roots.count) (_hi : SimpleRoot G tori F i),
    lie (K.sl2 i).negativeVector = -(K.sl2 i).positiveVector
  opposite_borel : F.borel.subalgebra.toSubmodule.map lie.toLinearMap = oppositeBorelModule F
  normalizer_parameter : letI := (tori 1).group
    ∀ (i : Fin F.roots.count) (_hi : SimpleRoot G tori F i)
      (U : Over (Spec (.of ℂ))) (c : U ⟶ torusScheme ℂ 1),
    c ≫ (K.sl2 i).normalizer ≫ normalizer.hom =
      c ≫ ι[torusScheme ℂ 1] ≫ (K.sl2 i).normalizer
  transport_adjoint : letI := (tori 1).group
    ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl)
      (hn : Label F n w) (i j : Fin F.roots.count) (_hi : SimpleRoot G tori F i)
      (_hj : SimpleRoot G tori F j) (hij : K.permutations.index w i = j)
      (A : CommAlgCat.{0} ℂ) (f : affine A ⟶ U),
    F.adjoint.adjoint A (f ≫ n ≫ normalizer.hom ≫ F.normalizer.inclusion)
      (1 ⊗ₜ[ℂ] (K.sl2 i).positiveVector) =
    coefficientUnit tori A
      (f ≫ (K.transporters U n w hn i j hij).scalar ≫ ι[torusScheme ℂ 1]) ⊗ₜ[ℂ]
      (K.sl2 j).positiveVector

theorem thetaLabel (Q : ChevalleyComparison F K) {U : Over (Spec (.of ℂ))}
    (n : U ⟶ F.normalizer.scheme) (w : F.Weyl) (hn : Label F n w) :
    Label F (n ≫ Q.normalizer.hom) w := by
  intro x
  rw [Category.assoc, Q.weyl]
  exact hn x

end MathlibExt.AlgebraicGeometry.CameralChevalleyConventionModels
