/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPositiveNaturality
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricShuffleCoordinates
public import MathlibExt.Algebra.Homology.Hochschild.CoefficientMapFunctoriality
public import MathlibExt.Algebra.Homology.ChainGradedPairingPositivePostcomp
public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveCochains

/-!
# Normalized positive shuffle indecomposables

Relations are images of signed shuffle pairings with both
input degrees positive, followed by Hochschild normalization.
The target has coefficient M and ground quotient tails A/(k·1).
The raw-to-normalized map exists over every commutative ground
ring; it need not be a quasi-isomorphism integrally. Rational
homotopy comparison uses the Eulerian kernel and projector.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct MonoidalCategory BigOperators

universe u v w v' z

namespace ModuleCat.Algebra.Hochschild.Symmetric

section IndependentCoefficients

variable (k : Type u) (A : Type v) (M : Type w) [CommRing k] [CommRing A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M]


/-- The original both-positive shuffle quotient, retaining the original coefficient world. -/
def positiveQuotient : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    HomologicalComplex.ChainGradedPairing.positiveImageQuotient (pairing.{u, v, w} k A M)
      (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M)

/-- The relations in the original normalized tensor coordinates are target images. -/
def normalizedPositiveRelations (n : ℕ) :
    Submodule k ((normalizedChainComplex k A M).X n) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    HomologicalComplex.ChainGradedPairing.positiveImages
      ((pairing.{u, v, w} k A M).postcomp (normalizationProjection k A M)) n

/-- The true normalized positive relation module is the image of the true raw one. -/
theorem normalizedPositiveRelations_eq_map (n : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  normalizedPositiveRelations k A M n =
      (HomologicalComplex.ChainGradedPairing.positiveImages (pairing.{u, v, w} k A M) n).map
        ((normalizationProjection k A M).f n).hom := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    HomologicalComplex.ChainGradedPairing.positiveImages_postcomp
      (pairing.{u, v, w} k A M) (normalizationProjection k A M) n

/-- Restriction of the original complete differential gives the normalized quotient complex. -/
def normalizedPositiveQuotient : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    HomologicalComplex.ChainGradedPairing.positiveImageQuotient
      ((pairing.{u, v, w} k A M).postcomp (normalizationProjection k A M))
      (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M)

/-- The original normalized chains map by the native quotient-class projection. -/
def normalizedPositiveProjection :
    normalizedChainComplex k A M ⟶ normalizedPositiveQuotient k A M := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    HomologicalComplex.ChainGradedPairing.positiveImageProjection
      ((pairing.{u, v, w} k A M).postcomp (normalizationProjection k A M))
      (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M)

/-- The raw positive quotient maps by its factorwise normalization. -/
def positiveQuotientNormalization :
    positiveQuotient k A M ⟶ normalizedPositiveQuotient k A M := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    HomologicalComplex.ChainGradedPairing.positiveImageQuotientPostcompMap
      (pairing.{u, v, w} k A M) (normalizationProjection k A M)
      (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M)

/-- The descended map retains the original full normalization square. -/
@[reassoc]
theorem positiveQuotientNormalization_projection :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  HomologicalComplex.ChainGradedPairing.positiveImageProjection (pairing.{u, v, w} k A M)
        (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M) ≫
        positiveQuotientNormalization k A M =
      normalizationProjection k A M ≫ normalizedPositiveProjection k A M := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    HomologicalComplex.ChainGradedPairing.positiveImageQuotientPostcompMap_projection
      (pairing.{u, v, w} k A M) (normalizationProjection k A M)
      (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M)

/-- The complete original unit-degeneracy relation module is the normalization kernel. -/
theorem ker_symmetricNormalizationProjection_f (n : ℕ) :
    LinearMap.ker ((normalizationProjection k A M).f n).hom =
      TensorPower.coefficientQuotientRelations (unitSubmodule k A) M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  change LinearMap.ker ((ModuleCat.Algebra.Hochschild.normalizationProjection k A M).f n).hom = _
  rw [ModuleCat.Algebra.Hochschild.normalizationProjection_f]
  exact normalizationLevelMap_ker k A M n

/-- The normalized relation preimage adds exactly the original unit-degeneracy relations. -/
theorem comap_normalizedPositiveRelations (n : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  (normalizedPositiveRelations k A M n).comap
        ((normalizationProjection k A M).f n).hom =
      HomologicalComplex.ChainGradedPairing.positiveImages (pairing.{u, v, w} k A M) n ⊔
        TensorPower.coefficientQuotientRelations (unitSubmodule k A) M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  rw [normalizedPositiveRelations_eq_map, Submodule.comap_map_eq,
    ker_symmetricNormalizationProjection_f]

/-- Its kernel is the unit-degeneracy image inside the raw positive quotient. -/
theorem ker_positiveQuotientNormalization_f (n : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  LinearMap.ker ((positiveQuotientNormalization k A M).f n).hom =
      (TensorPower.coefficientQuotientRelations (unitSubmodule k A) M n).map
        (HomologicalComplex.ChainGradedPairing.positiveImages (pairing.{u, v, w} k A M) n).mkQ := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  change LinearMap.ker ((HomologicalComplex.ChainGradedPairing.positiveImageQuotientPostcompMap
      (pairing.{u, v, w} k A M) (normalizationProjection k A M)
      (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M)).f n).hom = _
  rw [HomologicalComplex.ChainGradedPairing.ker_positiveImageQuotientPostcompMap,
    ker_symmetricNormalizationProjection_f]

/-- The all-degree normalization map is surjective on quotient coordinates. -/
theorem positiveQuotientNormalization_f_surjective (n : ℕ) :
    Function.Surjective ((positiveQuotientNormalization k A M).f n).hom := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  apply HomologicalComplex.ChainGradedPairing.positiveImageQuotientPostcompMap_surjective
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  change Function.Surjective
    ((ModuleCat.Algebra.Hochschild.normalizationProjection k A M).f n).hom
  rw [ModuleCat.Algebra.Hochschild.normalizationProjection_f]
  exact TensorPower.coefficientQuotientMap_surjective (unitSubmodule k A) M n

/-- Raw positive shuffle homology in every nonnegative degree. -/
def positiveHomology (n : ℕ) : ModuleCat.{max u v w} k := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    (positiveQuotient k A M).homology n

/-- Normalized positive shuffle homology in every nonnegative degree. -/
def normalizedPositiveHomology (n : ℕ) : ModuleCat.{max u v w} k := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    (normalizedPositiveQuotient k A M).homology n

/-- The all-degree homology comparison; no isomorphism premise is built into its type. -/
def positiveNormalizationHomologyMap (n : ℕ) :
    positiveHomology k A M n ⟶ normalizedPositiveHomology k A M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    HomologicalComplex.homologyMap (positiveQuotientNormalization k A M) n

/-- Cochains on normalized indecomposables use an explicit ground-linear target. -/
def normalizedPositiveCochainComplex (G : ModuleCat.{max u v w} k) :
    CochainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    HomologicalComplex.ChainGradedPairing.positiveImageCochainComplex
      ((pairing.{u, v, w} k A M).postcomp (normalizationProjection k A M))
      (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M) G

/-- Their all-degree cohomology uses the constructed coboundary. -/
def normalizedPositiveCohomology (G : ModuleCat.{max u v w} k) (n : ℕ) :
    ModuleCat.{max u v w} k := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    (normalizedPositiveCochainComplex k A M G).homology n

/-- The explicit ground-linear target module varies through the cohomology functor. -/
def normalizedPositiveCohomologyFunctor (n : ℕ) :
    ModuleCat.{max u v w} k ⥤ ModuleCat.{max u v w} k := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact
    HomologicalComplex.linearHomCochainComplexHomologyFunctor k (ModuleCat.{max u v w} k)
      (normalizedPositiveQuotient k A M) n

/-- The original signed shuffle word in the normalized tensor level. -/
def normalizedShuffleWord (p q : ℕ) (a0 : A) (m : M)
    (a : Fin p → A) (b : Fin q → A) :
    M ⊗[k] TensorPower k (p + q) (quotientCarrier k A) :=
  ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
    AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
      ((a0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
        (fun j => (unitSubmodule k A).mkQ (Fin.append a b (s.perm.symm j))))

/-- Each quotient-chain projection component is the native original class map. -/
theorem normalizedPositiveProjection_f_mkQ (n : ℕ) :
    let π : normalizedChainLevel k A M n →ₗ[k]
        (normalizedChainLevel k A M n) ⧸ normalizedPositiveRelations k A M n :=
      ((normalizedPositiveProjection.{u, v, w} k A M).f n).hom
    π = (normalizedPositiveRelations k A M n).mkQ := rfl

omit [IsScalarTower k A M] in
/-- The computational coordinates retain every original coefficient, sign and word position. -/
theorem normalizedShuffleWord_eq_sum (p q : ℕ) (a0 : A) (m : M)
    (a : Fin p → A) (b : Fin q → A) :
    normalizedShuffleWord k A M p q a0 m a b =
      ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
          ((a0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
            (fun j => (unitSubmodule k A).mkQ (Fin.append a b (s.perm.symm j)))) := rfl

/-- The postcomposed pairing has these normalized word coordinates. -/
theorem pairing_pair_normalizedShuffleWord (p q : ℕ) (a0 : A) (m : M)
    (a : Fin p → A) (b : Fin q → A) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
      ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
    letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
    letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
    letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
    let y : normalizedChainLevel k A M (p + q) :=
      (((pairing.{u, v, w} k A M).postcomp (normalizationProjection.{u, v, w} k A M)).pair p q).hom
        ((ULift.up a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b))
    y = normalizedShuffleWord k A M p q a0 m a b := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  change ((normalizationProjection.{u, v, w} k A M).f (p + q)).hom
    (((pairing.{u, v, w} k A M).pair p q).hom
      ((ULift.up a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
        (m ⊗ₜ[k] PiTensorProduct.tprod k b))) = _
  rw [pairing_pair_tprod]
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  change ((ModuleCat.Algebra.Hochschild.normalizationProjection k A M).f (p + q)).hom
    (∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
      AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
        ((a0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
          (fun j => Fin.append a b (s.perm.symm j)))) = _
  rw [ModuleCat.Algebra.Hochschild.normalizationProjection_f]
  let N : (M ⊗[k] TensorPower k (p + q) A) →ₗ[k]
      M ⊗[k] TensorPower k (p + q) (quotientCarrier k A) :=
    TensorPower.coefficientQuotientMap (unitSubmodule k A) M (p + q)
  change N
    (∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
      AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
        ((a0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
          (fun j => Fin.append a b (s.perm.symm j)))) = _
  calc
    _ = ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        N (AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
          ((a0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
            (fun j => Fin.append a b (s.perm.symm j)))) := map_sum N _ _
    _ = normalizedShuffleWord k A M p q a0 m a b := by
      unfold normalizedShuffleWord
      apply Finset.sum_congr rfl
      intro s _
      rw [map_zsmul]
      exact congrArg (fun z => AlgebraicTopology.EilenbergZilber.shuffleSignZ s • z)
        (TensorPower.coefficientQuotientMap_tmul_tprod (unitSubmodule k A) M (p + q)
          (a0 • m) (fun j => Fin.append a b (s.perm.symm j)))

/-- The relation membership is before applying the quotient map. -/
theorem normalizedShuffleWord_mem_relations (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (a0 : A) (m : M) (a : Fin p → A) (b : Fin q → A) :
    normalizedShuffleWord k A M p q a0 m a b ∈ normalizedPositiveRelations k A M (p + q) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  let x : (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k]
      (M ⊗[k] TensorPower k q A) :=
    (ULift.up a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
      (m ⊗ₜ[k] PiTensorProduct.tprod k b)
  have hx := HomologicalComplex.ChainGradedPairing.pairAt_mem_positiveImages
    ((pairing.{u, v, w} k A M).postcomp (normalizationProjection.{u, v, w} k A M))
    p q (p + q) rfl hp hq x
  have hv :
      ((((pairing.{u, v, w} k A M).postcomp (normalizationProjection.{u, v, w} k A M)).pair p q).hom x) =
        normalizedShuffleWord k A M p q a0 m a b :=
    pairing_pair_normalizedShuffleWord k A M p q a0 m a b
  change (((pairing.{u, v, w} k A M).postcomp (normalizationProjection.{u, v, w} k A M)).pair p q).hom x ∈
    normalizedPositiveRelations k A M (p + q) at hx
  exact hv ▸ hx

/-- Every normalized proper shuffle word is killed, with its original coefficient and signs. -/
theorem normalizedPositiveProjection_shuffle_word (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (a0 : A) (m : M) (a : Fin p → A) (b : Fin q → A) :
    let π : normalizedChainLevel k A M (p + q) →ₗ[k]
        (normalizedChainLevel k A M (p + q)) ⧸ normalizedPositiveRelations k A M (p + q) :=
      (normalizedPositiveRelations k A M (p + q)).mkQ
    π
        (∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
          AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
            ((a0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
              (fun j => (unitSubmodule k A).mkQ (Fin.append a b (s.perm.symm j))))) = 0 := by
  change (normalizedPositiveRelations k A M (p + q)).mkQ
      (normalizedShuffleWord k A M p q a0 m a b) = 0
  exact (Submodule.Quotient.mk_eq_zero (normalizedPositiveRelations k A M (p + q))).2
    (normalizedShuffleWord_mem_relations k A M p q hp hq a0 m a b)

end IndependentCoefficients

section ParameterMaps

variable {k : Type u} [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A]
  {B : Type v'} [CommRing B] [Algebra k B]
  {M N : Type (max u v v' z)} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [IsScalarTower k A M] [IsScalarTower k B N]


/-- Actual algebra/coefficient maps descend to the normalized positive quotient. -/
def normalizedPositiveQuotientMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    normalizedPositiveQuotient k A M ⟶ normalizedPositiveQuotient k B N := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  exact
    HomologicalComplex.ChainGradedPairing.positiveImageQuotientMap
      ((pairing.{u, v, max u v v' z} k A M).postcomp (normalizationProjection k A M))
      (boundary_one_zero k A (ULift.{max u v v' z} A)) (boundary_one_zero k A M)
      ((pairing.{u, v', max u v v' z} k B N).postcomp (normalizationProjection k B N))
      (boundary_one_zero k B (ULift.{max u v v' z} B)) (boundary_one_zero k B N)
      (coefficientChainMap.{u, v, v', z} g
        (regularCoefficientMap g.toNonUnitalAlgHom :
          ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
        (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom))
      (coefficientChainMap.{u, v, v', z} g f hf)
      (normalizedCoefficientMap.{u, v, v', z} g f hf)
      (pairing_normalizationProjection_naturality.{u, v, v', z} g f hf)

/-- The new quotient map retains the original normalized coefficient-map square. -/
@[reassoc]
theorem normalizedPositiveQuotientMap_projection (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    normalizedPositiveProjection k A M ≫ normalizedPositiveQuotientMap.{u, v, v', z} g f hf =
      normalizedCoefficientMap.{u, v, v', z} g f hf ≫ normalizedPositiveProjection k B N := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  exact
    HomologicalComplex.ChainGradedPairing.positiveImageProjection_map _ _ _ _ _ _
      _ _ _ (pairing_normalizationProjection_naturality.{u, v, v', z} g f hf)

/-- Normalizing indecomposables commutes with algebra/coefficient changes. -/
@[reassoc]
theorem positiveQuotientNormalization_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  positiveQuotientMap.{u, v, v', z} g f hf ≫ positiveQuotientNormalization k B N =
      positiveQuotientNormalization k A M ≫ normalizedPositiveQuotientMap.{u, v, v', z} g f hf := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext q
  refine Quotient.inductionOn' q ?_
  intro x
  change (normalizedPositiveRelations k B N n).mkQ
      (((normalizationProjection k B N).f n).hom
        (((coefficientChainMap.{u, v, v', z} g f hf).f n).hom x)) =
    (normalizedPositiveRelations k B N n).mkQ
      (((normalizedCoefficientMap.{u, v, v', z} g f hf).f n).hom
        (((normalizationProjection k A M).f n).hom x))
  apply congrArg (normalizedPositiveRelations k B N n).mkQ
  exact (ConcreteCategory.congr_hom
    (congrArg (fun τ => τ.f n)
      (normalizationProjection_coefficientMap.{u, v, v', z} g f hf)) x).symm

/-- The already constructed raw parameter map induces homology maps in every degree. -/
def positiveHomologyMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    positiveHomology k A M n ⟶ positiveHomology k B N n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  exact
    HomologicalComplex.homologyMap (positiveQuotientMap.{u, v, v', z} g f hf) n

/-- Actual parameter maps induce homology maps in every nonnegative degree. -/
def normalizedPositiveHomologyMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    normalizedPositiveHomology k A M n ⟶ normalizedPositiveHomology k B N n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  exact
    HomologicalComplex.homologyMap (normalizedPositiveQuotientMap.{u, v, v', z} g f hf) n

/-- The normalization comparison commutes with parameter maps on all homology degrees. -/
@[reassoc]
theorem positiveNormalizationHomologyMap_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    positiveHomologyMap.{u, v, v', z} g f hf n ≫ positiveNormalizationHomologyMap k B N n =
      positiveNormalizationHomologyMap k A M n ≫ normalizedPositiveHomologyMap.{u, v, v', z} g f hf n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{max u v v' z} k) (ComplexShape.down ℕ) n
  let r : positiveQuotient k A M ⟶ positiveQuotient k B N :=
    positiveQuotientMap.{u, v, v', z} g f hf
  let s : normalizedPositiveQuotient k A M ⟶ normalizedPositiveQuotient k B N :=
    normalizedPositiveQuotientMap.{u, v, v', z} g f hf
  let p : positiveQuotient k A M ⟶ normalizedPositiveQuotient k A M :=
    positiveQuotientNormalization k A M
  let q : positiveQuotient k B N ⟶ normalizedPositiveQuotient k B N :=
    positiveQuotientNormalization k B N
  have h : r ≫ q = p ≫ s :=
    positiveQuotientNormalization_naturality.{u, v, v', z} g f hf
  change F.map r ≫ F.map q = F.map p ≫ F.map s
  calc
    F.map r ≫ F.map q = F.map (r ≫ q) := (F.map_comp r q).symm
    _ = F.map (p ≫ s) := congrArg F.map h
    _ = F.map p ≫ F.map s := F.map_comp p s

/-- Actual algebra/coefficient changes pull normalized quotient cochains back contravariantly. -/
def normalizedPositiveCochainMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (G : ModuleCat.{max u v v' z} k) :
    normalizedPositiveCochainComplex k B N G ⟶ normalizedPositiveCochainComplex k A M G := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  exact
    (HomologicalComplex.linearHomCochainComplexFunctor k (ModuleCat.{max u v v' z} k) G).map
      (normalizedPositiveQuotientMap.{u, v, v', z} g f hf).op

/-- The induced cohomology maps retain every nonnegative cohomological degree. -/
def normalizedPositiveCohomologyMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (G : ModuleCat.{max u v v' z} k) (n : ℕ) :
    normalizedPositiveCohomology k B N G n ⟶ normalizedPositiveCohomology k A M G n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  exact
    HomologicalComplex.homologyMap (normalizedPositiveCochainMap.{u, v, v', z} g f hf G) n

end ParameterMaps

end ModuleCat.Algebra.Hochschild.Symmetric
