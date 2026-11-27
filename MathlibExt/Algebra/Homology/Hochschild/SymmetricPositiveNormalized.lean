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
# Normalized both-positive shuffle quotients and their maps

Let k be a commutative ring, A a commutative k-algebra and M a compatible symmetric coefficient
module. In degree n, let Sₙ be the sum of the raw shuffle pairing images with p,q > 0 and p+q=n.
Normalization Nₙ replaces each algebra tail by its class in V = A/(k·1). The normalized relation
module is Nₙ(Sₙ), and the raw and normalized proper quotient complexes are P = C/S and P̄ =
C̄/N(S).

Normalization descends to a degreewise surjective chain map P → P̄. If Dₙ is the unit-degeneracy
submodule ker Nₙ, the preimage of normalized relations is Sₙ+Dₙ, and the descended map has
kernel equal to the image of Dₙ in Cₙ/Sₙ. Explicit signed shuffle-word formulas describe the
normalized pairing images and show that every both-positive word is killed by the normalized
quotient projection.

A unital k-algebra map g : A → B and a k-linear coefficient map f satisfying f(a·m) = g(a)·f(m)
induce natural raw and normalized quotient chain and homology maps. For a fixed ground-module
target G, normalized quotient Hom_k(-,G) cochains and cohomology vary contravariantly in these
parameters; they vary covariantly in G. All degrees are indexed by ℕ, and separate
algebra/coefficient universes are accommodated by a common coefficient category.

For proper Harrison shuffle relations, see J.-L. Loday, Cyclic Homology, second edition, §4.2.
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


/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. The quotients Pₙ = Cₙ/Sₙ, with the induced Hochschild
boundary, form the ℕ-indexed k-module chain complex positiveQuotient k A M. The ground ring,
algebra and coefficient universes may differ. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. normalizedPositiveRelations in degree n is the sum of
the images of the raw pairing components followed by Nₙ, restricted to p,q > 0 and p+q=n. It is
a k-submodule of C̄ₙ. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. For every n : ℕ, normalizedPositiveRelations k A M n
equals the submodule image Nₙ(Sₙ) in C̄ₙ. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. The normalized quotients P̄ₙ = C̄ₙ/Nₙ(Sₙ), with their
descended normalized Hochschild differentials, form normalizedPositiveQuotient, an ℕ-indexed
chain complex of k-modules. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. The degreewise class maps C̄ₙ → C̄ₙ/Nₙ(Sₙ) form the
chain map normalizedPositiveProjection : C̄(A,M) → normalizedPositiveQuotient k A M. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. Since Nₙ sends Sₙ into normalizedPositiveRelations,
normalization descends to a chain map P = C/S → P̄ = C̄/N(S). This is
positiveQuotientNormalization k A M, acting on each quotient class by [x] ↦ [Nₙx]. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. If π : C → P and π̄ : C̄ → P̄ are the proper quotient
projections and N̄ : P → P̄ the induced normalization map, then π ≫ N̄ = N ≫ π̄. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. For every n : ℕ, ker Nₙ is
TensorPower.coefficientQuotientRelations(k·1,M,n), the submodule generated by coefficient
tensors with at least one tail factor in k·1. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. Let Dₙ = ker Nₙ be the coefficient unit-degeneracy
relation submodule. The inverse image of normalizedPositiveRelations under Nₙ is Sₙ + Dₙ,
expressed as the supremum of these two submodules of Cₙ. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. For n : ℕ, the kernel of the component N̄ₙ : Cₙ/Sₙ →
C̄ₙ/Nₙ(Sₙ) is the image of the unit-degeneracy submodule Dₙ under the raw proper quotient class
map Cₙ → Cₙ/Sₙ. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. For every n : ℕ, the underlying linear map
(positiveQuotientNormalization k A M).f n is surjective from the raw proper quotient term to the
normalized proper quotient term. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. For n : ℕ, positiveHomology k A M n is the homology
k-module Hₙ(P) of the raw both-positive quotient chain complex P = C/S. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. For n : ℕ, normalizedPositiveHomology k A M n is the
homology k-module Hₙ(P̄) of the normalized both-positive quotient P̄ = C̄/N(S). -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. In every n : ℕ, the chain map
positiveQuotientNormalization induces positiveNormalizationHomologyMap : Hₙ(P) → Hₙ(P̄). -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. For a k-module G in the common coefficient universe,
normalizedPositiveCochainComplex is the cochain complex Hom_k(P̄,G), with degree-n term
Hom_k(P̄ₙ,G) and coboundary given by precomposition with the normalized quotient boundary. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. For a k-module G in the common coefficient universe and
n : ℕ, normalizedPositiveCohomology k A M G n is Hⁿ(Hom_k(P̄,G)). -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. For each n : ℕ, G ↦ Hⁿ(Hom_k(P̄,G)) is a functor on
k-modules in the common coefficient universe. A target map G → G′ acts by postcomposition of
normalized proper quotient cochains. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. For p,q : ℕ, a₀ ∈ A, m ∈ M and words a,b
of lengths p,q, normalizedShuffleWord is ∑s sign(s)·((a₀·m) ⊗ ⊗ⱼρ(append(a,b)(s⁻¹j))) in C̄ₚ₊q,
where s ranges over (p,q)-shuffles and ρ : A → V. -/
def normalizedShuffleWord (p q : ℕ) (a0 : A) (m : M)
    (a : Fin p → A) (b : Fin q → A) :
    M ⊗[k] TensorPower k (p + q) (quotientCarrier k A) :=
  ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
    AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
      ((a0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
        (fun j => (unitSubmodule k A).mkQ (Fin.append a b (s.perm.symm j))))

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. Let Sₙ be the sum of all shuffle pairing
component images with p,q > 0 and p+q=n. In degree n : ℕ, the underlying linear map of
normalizedPositiveProjection equals the quotient map C̄ₙ → C̄ₙ/normalizedPositiveRelations k A M
n. -/
theorem normalizedPositiveProjection_f_mkQ (n : ℕ) :
    let π : normalizedChainLevel k A M n →ₗ[k]
        (normalizedChainLevel k A M n) ⧸ normalizedPositiveRelations k A M n :=
      ((normalizedPositiveProjection.{u, v, w} k A M).f n).hom
    π = (normalizedPositiveRelations k A M n).mkQ := rfl

omit [IsScalarTower k A M] in
/-- Let k be a commutative ring, A a commutative k-algebra and M a k- and A-module. For p,q : ℕ, a₀
∈ A, m ∈ M and words a,b, normalizedShuffleWord is exactly ∑s shuffleSignZ(s)·((a₀·m) ⊗
⊗ⱼ[(append(a,b))(s.perm⁻¹j)]), with each tail class taken in A/(k·1). -/
theorem normalizedShuffleWord_eq_sum (p q : ℕ) (a0 : A) (m : M)
    (a : Fin p → A) (b : Fin q → A) :
    normalizedShuffleWord k A M p q a0 m a b =
      ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
          ((a0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
            (fun j => (unitSubmodule k A).mkQ (Fin.append a b (s.perm.symm j)))) := rfl

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. For p,q : ℕ, the raw shuffle pairing on
(a₀ ⊗ ⊗a) ⊗ (m ⊗ ⊗b), postcomposed with degree-p+q normalization, equals normalizedShuffleWord k
A M p q a₀ m a b. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. For p,q > 0, a₀ ∈ A, m ∈ M and words a,b
of lengths p,q, normalizedShuffleWord k A M p q a₀ m a b lies in normalizedPositiveRelations k A
M (p+q). -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action and symmetric right action. Put Cₙ = M ⊗_k A^{⊗n}, V = A/(k·1), C̄ₙ = M ⊗_k V^{⊗n}, and
let Nₙ : Cₙ → C̄ₙ apply the quotient map to every tail. For p,q > 0 and coefficient words
a₀,m,a,b, the quotient class of the full signed normalizedShuffleWord is zero in
normalizedPositiveQuotient k A M at degree p+q. -/
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


/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible symmetric coefficient
modules in a common universe containing k,A,B. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy
f(a·m) = g(a)·f(m). The normalized coefficient chain map descends through the both-positive
shuffle relation images to normalizedPositiveQuotientMap : P̄(A,M) → P̄(B,N), a k-module chain
map. -/
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

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible symmetric coefficient
modules in a common universe containing k,A,B. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy
f(a·m) = g(a)·f(m). If π̄_A,π̄_B are normalizedPositiveProjection, F̄ is
normalizedCoefficientMap and Q̄ is normalizedPositiveQuotientMap, then π̄_A ≫ Q̄ = F̄ ≫ π̄_B. -/
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

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible symmetric coefficient
modules in a common universe containing k,A,B. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy
f(a·m) = g(a)·f(m). Let Q and Q̄ be the raw and normalized proper quotient maps and N̄_A,N̄_B
the proper normalization maps. Then Q ≫ N̄_B = N̄_A ≫ Q̄ as chain maps from P(A,M) to P̄(B,N). -/
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

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible symmetric coefficient
modules in a common universe containing k,A,B. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy
f(a·m) = g(a)·f(m). For every n : ℕ, the raw chain map positiveQuotientMap induces
positiveHomologyMap : Hₙ(P(A,M)) → Hₙ(P(B,N)). -/
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

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible symmetric coefficient
modules in a common universe containing k,A,B. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy
f(a·m) = g(a)·f(m). For every n : ℕ, normalizedPositiveQuotientMap induces
normalizedPositiveHomologyMap : Hₙ(P̄(A,M)) → Hₙ(P̄(B,N)). -/
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

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible symmetric coefficient
modules in a common universe containing k,A,B. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy
f(a·m) = g(a)·f(m). For n : ℕ, write H(Q),H(Q̄) for the raw and normalized proper quotient
homology maps. Then H(Q) ≫ positiveNormalizationHomologyMap(B,N) =
positiveNormalizationHomologyMap(A,M) ≫ H(Q̄), in degree n. -/
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

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible symmetric coefficient
modules in a common universe containing k,A,B. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy
f(a·m) = g(a)·f(m). For a fixed k-module G in the common coefficient universe, precomposition
with normalizedPositiveQuotientMap gives a cochain map Hom_k(P̄(B,N),G) → Hom_k(P̄(A,M),G). Its
degree-n action is φ ↦ φ ∘ Q̄ₙ. -/
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

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible symmetric coefficient
modules in a common universe containing k,A,B. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy
f(a·m) = g(a)·f(m). For a fixed k-module G in the common coefficient universe and n : ℕ,
normalizedPositiveCochainMap induces Hⁿ(Hom_k(P̄(B,N),G)) → Hⁿ(Hom_k(P̄(A,M),G)). -/
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
