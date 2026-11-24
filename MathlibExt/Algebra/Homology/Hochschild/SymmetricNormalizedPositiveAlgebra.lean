/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricNormalizationAlgebra

/-!
# Normalized proper shuffle quotient complexes over A

The normalized relation module is the image of the A-linear
proper relation module under factorwise normalization. The
normalized boundary preserves it, giving an A-module quotient
complex, its projection and the raw-to-normalized map. Both
input shuffle degrees are positive; quotient tails remain
the ground modules A/(k·1).
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The original normalized proper relation module is its A-linear image. -/
def algebraNormalizedPositiveRelations (n : ℕ) :
    Submodule A (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :=
  (algebraPositiveRelations k A M n).map (algebraNormalizationLevelMap k A M n)

/-- The normalized A-module relation set is exactly the original ground-linear proper relation set. -/
theorem algebraNormalizedPositiveRelations_restrictScalars (n : ℕ) :
    (algebraNormalizedPositiveRelations k A M n).restrictScalars k =
      normalizedPositiveRelations k A M n := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  rw [normalizedPositiveRelations_eq_map]
  ext x
  change (∃ y, y ∈ algebraPositiveRelations k A M n ∧ algebraNormalizationLevelMap k A M n y = x) ↔
    ∃ y, y ∈ rawPositiveRelations k A M n ∧ ((normalizationProjection k A M).f n).hom y = x
  rw [nativeNormalizationProjection_f]
  rfl

/-- The original normalized proper relations vanish in the original two low degrees. -/
theorem algebraNormalizedPositiveRelations_low (n : ℕ) (hn : n ≤ 1) :
    algebraNormalizedPositiveRelations k A M n = ⊥ := by
  rw [algebraNormalizedPositiveRelations, algebraPositiveRelations_low k A M n hn, Submodule.map_bot]

/-- The original normalized differential preserves the image relation module. -/
theorem algebraNormalizedPositiveRelations_boundary (n : ℕ)
    {x : M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)}
    (hx : x ∈ algebraNormalizedPositiveRelations k A M (n + 1)) :
    algebraNormalizedBoundary k A M n x ∈ algebraNormalizedPositiveRelations k A M n := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  apply Submodule.mem_map.mpr
  refine ⟨algebraBoundary k A M n y, algebraPositiveRelations_boundary k A M n hy, ?_⟩
  exact (nativeNormalizationBoundary_apply k A M n y).symm

/-- The native quotient differential of the normalized proper A-modules. -/
def algebraNormalizedPositiveQuotientDifferential (n : ℕ) :
    ModuleCat.of A ((M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
      algebraNormalizedPositiveRelations k A M (n + 1)) ⟶
    ModuleCat.of A ((M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
      algebraNormalizedPositiveRelations k A M n) :=
  ModuleCat.ofHom ((algebraNormalizedPositiveRelations k A M (n + 1)).mapQ
    (algebraNormalizedPositiveRelations k A M n) (algebraNormalizedBoundary k A M n)
      (fun _ hx => algebraNormalizedPositiveRelations_boundary k A M n hx))

/-- The normalized quotient differential squares to zero by its original normalized boundary. -/
theorem algebraNormalizedPositiveQuotientDifferential_comp (n : ℕ) :
    algebraNormalizedPositiveQuotientDifferential k A M (n + 1) ≫
      algebraNormalizedPositiveQuotientDifferential k A M n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  change (algebraNormalizedPositiveRelations k A M n).mkQ
    (algebraNormalizedBoundary k A M n (algebraNormalizedBoundary k A M (n + 1) y)) = 0
  rw [show algebraNormalizedBoundary k A M n (algebraNormalizedBoundary k A M (n + 1) y) = 0 from
    DFunLike.congr_fun (algebraNormalizedBoundary_comp k A M n) y, map_zero]

/-- The normalized proper-shuffle quotient in the original A-module chain category. -/
def algebraNormalizedPositiveQuotientComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A
    ((M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
      algebraNormalizedPositiveRelations k A M n))
    (algebraNormalizedPositiveQuotientDifferential k A M)
    (algebraNormalizedPositiveQuotientDifferential_comp k A M)

/-- The original full normalized chain projects by its A-module quotient classes. -/
def algebraNormalizedPositiveProjection :
    algebraNormalizedChainComplex k A M ⟶ algebraNormalizedPositiveQuotientComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraNormalizedPositiveRelations k A M n).mkQ) (by
    intro n
    apply ModuleCat.hom_ext
    dsimp only [algebraNormalizedChainComplex, algebraNormalizedPositiveQuotientComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    dsimp only [algebraNormalizedPositiveQuotientDifferential]
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    exact Submodule.mapQ_mkQ (algebraNormalizedPositiveRelations k A M (n + 1))
      (algebraNormalizedPositiveRelations k A M n) (algebraNormalizedBoundary k A M n)
      (h := fun _ hx => algebraNormalizedPositiveRelations_boundary k A M n hx))

/-- The original raw proper quotient normalizes through the A-linear image relations. -/
def algebraPositiveNormalization :
    algebraPositiveQuotientComplex k A M ⟶ algebraNormalizedPositiveQuotientComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((algebraPositiveRelations k A M n).mapQ (algebraNormalizedPositiveRelations k A M n)
      (algebraNormalizationLevelMap k A M n) (fun _ hx => Submodule.mem_map.mpr ⟨_, hx, rfl⟩))) (by
        intro n
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        dsimp only [algebraPositiveQuotientComplex, algebraNormalizedPositiveQuotientComplex]
        rw [ChainComplex.of_d, ChainComplex.of_d]
        refine Quotient.inductionOn' x ?_
        intro y
        change (algebraNormalizedPositiveRelations k A M n).mkQ
            (algebraNormalizedBoundary k A M n (algebraNormalizationLevelMap k A M (n + 1) y)) =
          (algebraNormalizedPositiveRelations k A M n).mkQ
            (algebraNormalizationLevelMap k A M n (algebraBoundary k A M n y))
        exact congrArg (algebraNormalizedPositiveRelations k A M n).mkQ
          (nativeNormalizationBoundary_apply k A M n y))

/-- The original proper normalization map retains every original coefficient tensor representative. -/
theorem algebraPositiveNormalization_f_mkQ (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    ((algebraPositiveNormalization k A M).f n).hom ((algebraPositiveRelations k A M n).mkQ x) =
      (algebraNormalizedPositiveRelations k A M n).mkQ (algebraNormalizationLevelMap k A M n x) := rfl

end ModuleCat.Algebra.Hochschild.Symmetric
