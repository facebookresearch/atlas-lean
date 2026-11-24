/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralFoundationPackages
public import MathlibExt.AlgebraicGeometry.RankTwoMatrixGroupModels
public import Mathlib.Tactic.FinCases

/-!
# Actual root SL2 maps, normalizer lifts and conjugation parameters

Root maps are scheme group homomorphisms from the actual SL2 coordinate
scheme. Their diagonal is the actual coroot, and their two infinitesimal
unipotents are nonzero vectors in the actual positive and negative Lie
weight spaces. No injectivity is imposed: a nonprimitive coroot may kill
the central minus identity in G.

The normalizer lift keeps the actual SL2 parameter n(c)=(0,-c;c inverse,0).
Conjugation is normalized by the actual GL2 matrix diag(alpha(t),1), or
by the corresponding coefficient read from the native adjoint action.
Thus conjugation may change the lift even when its image in G is unchanged.

Source: Donagi--Gaitsgory, arXiv:math/0005132v3, Sections 5--6 and 8;
the rank-one derived Levi and root homomorphisms of a complex reductive group.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralRootSL2Sources

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralTorusBands CameralReductiveSources
open ExpansionParameterModels SchemeLieJetFamilies TorusInfinitesimalPoints
open RankTwoMatrixGroupModels GeneralLinearFrameSchemes
open scoped Matrix TensorProduct

def conjugatingMatrix {R : Type} [CommRing R] (u : Rˣ) :
    Matrix.GeneralLinearGroup (Fin 2) R where
  val := !![↑u, 0; 0, 1]
  inv := !![↑u⁻¹, 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def normalizerMatrix {R : Type} [CommRing R] (u : Rˣ) :
    Matrix.SpecialLinearGroup (Fin 2) R := diagonalMatrix u * weylMatrix R

variable [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory]

def normalizerLift (Gm : TorusTheory ℂ 1) : torusScheme ℂ 1 ⟶ sl2Scheme :=
  (SL2MatrixTheory.points (torusScheme ℂ 1)).symm
    (normalizerMatrix (Gm.units (torusScheme ℂ 1) (𝟙 (torusScheme ℂ 1)) 0))

def upperJet (A : CommAlgCat.{0} ℂ) (a : A) : TorusInfinitesimalPoints.doubled A ⟶ sl2Scheme :=
  (SL2MatrixTheory.points (TorusInfinitesimalPoints.doubled A)).symm
    (upperMatrix ((Scheme.ΓSpecIso (.of (TrivSqZeroExt A A))).inv.hom (TrivSqZeroExt.inr a)))

def lowerJet (A : CommAlgCat.{0} ℂ) (a : A) : TorusInfinitesimalPoints.doubled A ⟶ sl2Scheme :=
  (SL2MatrixTheory.points (TorusInfinitesimalPoints.doubled A)).symm
    (lowerMatrix ((Scheme.ΓSpecIso (.of (TrivSqZeroExt A A))).inv.hom (TrivSqZeroExt.inr a)))

variable (G : Over (Spec (.of ℂ))) [GrpObj G] (tori : ∀ n : ℕ, TorusTheory ℂ n)
  (F : Foundation G tori)

def PositiveRoot (i : Fin F.roots.count) : Prop :=
  weightSpace G F.lie.carrier F.lie.model F.jets F.adjoint (tori F.rank)
    F.source.torus (F.roots.exponent i) ≤ F.borel.subalgebra.toSubmodule

def SimpleRoot (i : Fin F.roots.count) : Prop :=
  PositiveRoot G tori F i ∧ ∀ j k : Fin F.roots.count,
    PositiveRoot G tori F j → PositiveRoot G tori F k →
      F.roots.exponent j + F.roots.exponent k ≠ F.roots.exponent i

structure RootPermutations where
  index : F.Weyl →* Equiv.Perm (Fin F.roots.count)
  character : ∀ w i, (F.roots.action w).asIso.hom ≫ F.roots.character i =
    F.roots.character (index w⁻¹ i)
  coroot : ∀ w i, F.roots.coroot i ≫ (F.roots.action w).asIso.hom =
    F.roots.coroot (index w i)
  reflection : ∀ w i,
    F.roots.reflection (index w i) = w * F.roots.reflection i * w⁻¹
  negative : Equiv.Perm (Fin F.roots.count)
  negative_exponent : ∀ i, F.roots.exponent (negative i) = -F.roots.exponent i
  negative_involution : ∀ i, negative (negative i) = i
  negative_reflection : ∀ i, F.roots.reflection (negative i) = F.roots.reflection i
  negative_index : ∀ w i, index w (negative i) = negative (index w i)
  negative_coroot : letI := (tori 1).group
    ∀ i, F.roots.coroot (negative i) = ι[torusScheme ℂ 1] ≫ F.roots.coroot i

structure RootSL2Map (i : Fin F.roots.count) where
  map : sl2Scheme ⟶ G
  hom : IsMonHom map
  diagonal : RankTwoMatrixGroupModels.diagonal (tori 1) ≫ map =
    F.roots.coroot i ≫ F.source.torus
  positiveVector : F.lie.carrier
  positive_nonzero : positiveVector ≠ 0
  positive_weight : positiveVector ∈
    weightSpace G F.lie.carrier F.lie.model F.jets F.adjoint (tori F.rank)
      F.source.torus (F.roots.exponent i)
  negativeVector : F.lie.carrier
  negative_nonzero : negativeVector ≠ 0
  negative_weight : negativeVector ∈
    weightSpace G F.lie.carrier F.lie.model F.jets F.adjoint (tori F.rank)
      F.source.torus (-F.roots.exponent i)
  upper : ∀ (A : CommAlgCat.{0} ℂ) (a : A), upperJet A a ≫ map =
    jetPoint G F.lie.carrier F.lie.model F.jets A (a ⊗ₜ[ℂ] positiveVector)
  lower : ∀ (A : CommAlgCat.{0} ℂ) (a : A), lowerJet A a ≫ map =
    jetPoint G F.lie.carrier F.lie.model F.jets A (a ⊗ₜ[ℂ] negativeVector)
  normalizer : torusScheme ℂ 1 ⟶ F.normalizer.scheme
  normalizer_inclusion : normalizer ≫ F.normalizer.inclusion = normalizerLift (tori 1) ≫ map
  normalizer_weyl : ∀ (U : Over (Spec (.of ℂ))) (c : U ⟶ torusScheme ℂ 1) (x : U.left),
    F.weyl.points U (c ≫ normalizer ≫ F.normalizer.quotient) x = F.roots.reflection i
  torusConjugation : torusScheme ℂ F.rank ⊗ sl2Scheme ⟶ sl2Scheme
  torus_matrix : ∀ (U : Over (Spec (.of ℂ))) (t : U ⟶ torusScheme ℂ F.rank) (s : U ⟶ sl2Scheme),
    GL2MatrixTheory.points U
      (CartesianMonoidalCategory.lift t s ≫ torusConjugation ≫ SL2MatrixTheory.inclusion) =
    conjugatingMatrix ((tori 1).units U (t ≫ F.roots.character i) 0) *
      (SL2MatrixTheory.points U s).toGL *
        (conjugatingMatrix ((tori 1).units U (t ≫ F.roots.character i) 0))⁻¹
  torus_in_group : torusConjugation ≫ map =
    SchemeLieJetFamilies.conjugate G
      (fst (torusScheme ℂ F.rank) sl2Scheme ≫ F.source.torus)
      (snd (torusScheme ℂ F.rank) sl2Scheme ≫ map)

def coefficientUnit (A : CommAlgCat.{0} ℂ) (c : affine A ⟶ torusScheme ℂ 1) : A :=
  (Scheme.ΓSpecIso (.of A)).hom.hom ((tori 1).units (affine A) c 0 : Γ((affine A).left, ⊤))

/-- The SL2 conjugation lift is fixed by the native adjoint coefficient on actual root vectors. -/
structure NormalizerTransporter (P : RootPermutations G tori F)
    (S : ∀ i, RootSL2Map G tori F i) (U : Over (Spec (.of ℂ)))
    (n : U ⟶ F.normalizer.scheme) (w : F.Weyl)
    (_hw : ∀ x : U.left, F.weyl.points U (n ≫ F.normalizer.quotient) x = w)
    (i j : Fin F.roots.count) (_hij : P.index w i = j) where
  scalar : U ⟶ torusScheme ℂ 1
  adjoint : ∀ (A : CommAlgCat.{0} ℂ) (f : affine A ⟶ U),
    F.adjoint.adjoint A (f ≫ n ≫ F.normalizer.inclusion) (1 ⊗ₜ[ℂ] (S i).positiveVector) =
      coefficientUnit tori A (f ≫ scalar) ⊗ₜ[ℂ] (S j).positiveVector
  lift : U ⊗ sl2Scheme ⟶ sl2Scheme
  matrix : ∀ (U' : Over (Spec (.of ℂ))) (f : U' ⟶ U) (s : U' ⟶ sl2Scheme),
    GL2MatrixTheory.points U'
      (CartesianMonoidalCategory.lift f s ≫ lift ≫ SL2MatrixTheory.inclusion) =
    conjugatingMatrix (((tori 1).units U' (f ≫ scalar) 0)⁻¹) *
      (SL2MatrixTheory.points U' s).toGL *
        (conjugatingMatrix (((tori 1).units U' (f ≫ scalar) 0)⁻¹))⁻¹
  in_group : lift ≫ (S i).map = SchemeLieJetFamilies.conjugate G
    (fst U sl2Scheme ≫ n ≫ F.normalizer.inclusion ≫ ι[G]) (snd U sl2Scheme ≫ (S j).map)

structure RootNormalizerGeometry where
  permutations : RootPermutations G tori F
  sl2 : ∀ i, RootSL2Map G tori F i
  transporters : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl)
      (hw : ∀ x : U.left, F.weyl.points U (n ≫ F.normalizer.quotient) x = w)
      (i j : Fin F.roots.count) (hij : permutations.index w i = j),
    NormalizerTransporter G tori F permutations sl2 U n w hw i j hij
  corootHom : letI := (tori 1).group; letI := (tori F.rank).group
    ∀ i, IsMonHom (F.roots.coroot i)
  characterHom : letI := (tori 1).group; letI := (tori F.rank).group
    ∀ i, IsMonHom (F.roots.character i)
  actionHom : letI := (tori F.rank).group
    ∀ w, IsMonHom (F.roots.action w).asIso.hom

end MathlibExt.AlgebraicGeometry.CameralRootSL2Sources
