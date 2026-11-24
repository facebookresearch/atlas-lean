/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- UNEXECUTED source proposal. Actual proper quotient normalization over A. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianComplex
public import MathlibExt.Algebra.Homology.HomotopyEquivOnSplitImages
public import MathlibExt.Algebra.Homology.SplitHomotopyKernel

/-!
# Proper-shuffle normalization and projected homotopies

Over a ground ring containing ℚ, proper relation modules
are kernels of the zero-plus-first Eulerian projectors.
Projecting the full normalization section and homotopy
gives a homotopy equivalence of the proper quotient
complexes. The full section and homotopy are not required
to commute with the projectors. The quotients use
both-positive shuffle relations.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

private theorem mkQ_idempotent {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (P : Submodule R V) (E : V →ₗ[R] V) (hP : P = LinearMap.ker E)
    (hE : E.comp E = E) (x : V) : P.mkQ (E x) = P.mkQ x := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  change E x - x ∈ LinearMap.ker P.mkQ
  rw [Submodule.ker_mkQ, hP]
  change E (E x - x) = 0
  rw [map_sub]
  have h := DFunLike.congr_fun hE x
  change E (E x) = E x at h
  rw [h, sub_self]

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The first-projector kernel constructs an A-linear section of
the original raw proper quotient. -/
def algebraPositiveEulerianSectionLevel (n : ℕ) :
    ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n) →ₗ[A]
      M ⊗[k] TensorPower k n A :=
  (algebraPositiveRelations k A M n).liftQ (algebraFirstEulerianOperator k A M n)
    (algebraPositiveRelations_eq_firstEulerianKernel k A M n).le

/-- The normalized proper quotient has the corresponding original A-linear section. -/
def algebraNormalizedPositiveEulerianSectionLevel (n : ℕ) :
    ((M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
      algebraNormalizedPositiveRelations k A M n) →ₗ[A]
        M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
  (algebraNormalizedPositiveRelations k A M n).liftQ
    (algebraNormalizedFirstEulerianOperator k A M n)
    (algebraNormalizedPositiveRelations_eq_firstEulerianKernel k A M n).le

/-- The raw quotient section applies exactly the original full first projector to a representative. -/
theorem algebraPositiveEulerianSectionLevel_mkQ (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    algebraPositiveEulerianSectionLevel k A M n ((algebraPositiveRelations k A M n).mkQ x) =
      algebraFirstEulerianOperator k A M n x := rfl

/-- The normalized quotient section applies the original normalized full first projector. -/
theorem algebraNormalizedPositiveEulerianSectionLevel_mkQ (n : ℕ)
    (x : M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :
    algebraNormalizedPositiveEulerianSectionLevel k A M n
        ((algebraNormalizedPositiveRelations k A M n).mkQ x) =
      algebraNormalizedFirstEulerianOperator k A M n x := rfl

/-- The raw quotient section is a chain map by the first Eulerian boundary square. -/
def algebraPositiveEulerianSection :
    algebraPositiveQuotientComplex k A M ⟶ algebraRawComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraPositiveEulerianSectionLevel k A M n)) (by
    intro n
    apply ModuleCat.hom_ext
    ext y
    refine Quotient.inductionOn' y ?_
    intro x
    dsimp only [algebraRawComplex, algebraPositiveQuotientComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    change algebraBoundary k A M n (algebraFirstEulerianOperator k A M (n + 1) x) =
      algebraFirstEulerianOperator k A M n (algebraBoundary k A M n x)
    have h := congrArg ModuleCat.Hom.hom
      ((algebraFirstEulerianChainMap k A M).comm (n + 1) n)
    simp only [ModuleCat.hom_comp, algebraFirstEulerianChainMap_f] at h
    dsimp only [algebraRawComplex] at h
    rw [ChainComplex.of_d] at h
    exact congrArg (fun l : (M ⊗[k] TensorPower k (n + 1) A) →ₗ[A]
      (M ⊗[k] TensorPower k n A) => l x) h)

/-- The normalized quotient section is a chain map for the original normalized boundary. -/
def algebraNormalizedPositiveEulerianSection :
    algebraNormalizedPositiveQuotientComplex k A M ⟶ algebraNormalizedChainComplex k A M :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (algebraNormalizedPositiveEulerianSectionLevel k A M n)) (by
      intro n
      apply ModuleCat.hom_ext
      ext y
      refine Quotient.inductionOn' y ?_
      intro x
      dsimp only [algebraNormalizedChainComplex, algebraNormalizedPositiveQuotientComplex]
      rw [ChainComplex.of_d, ChainComplex.of_d]
      change algebraNormalizedBoundary k A M n (algebraNormalizedFirstEulerianOperator k A M (n + 1) x) =
        algebraNormalizedFirstEulerianOperator k A M n (algebraNormalizedBoundary k A M n x)
      have h := congrArg ModuleCat.Hom.hom
        ((algebraNormalizedFirstEulerianChainMap k A M).comm (n + 1) n)
      simp only [ModuleCat.hom_comp, algebraNormalizedFirstEulerianChainMap_f] at h
      dsimp only [algebraNormalizedChainComplex] at h
      rw [ChainComplex.of_d] at h
      exact congrArg (fun l :
        (M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) →ₗ[A]
        (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) => l x) h)

/-- Projection followed by the raw quotient section is the original first chain projector. -/
@[reassoc]
theorem algebraRawPositiveProjection_eulerianSection :
    algebraRawPositiveProjection k A M ≫ algebraPositiveEulerianSection k A M =
      algebraFirstEulerianChainMap k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Projection followed by the normalized quotient section is its original first chain projector. -/
@[reassoc]
theorem algebraNormalizedPositiveProjection_eulerianSection :
    algebraNormalizedPositiveProjection k A M ≫ algebraNormalizedPositiveEulerianSection k A M =
      algebraNormalizedFirstEulerianChainMap k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- The original raw proper quotient is an split image of its original first projector. -/
@[reassoc]
theorem algebraPositiveEulerianSection_projection :
    algebraPositiveEulerianSection k A M ≫ algebraRawPositiveProjection k A M =
      𝟙 (algebraPositiveQuotientComplex k A M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext y
  refine Quotient.inductionOn' y ?_
  intro x
  exact mkQ_idempotent (algebraPositiveRelations k A M n) (algebraFirstEulerianOperator k A M n)
    (algebraPositiveRelations_eq_firstEulerianKernel k A M n)
    (algebraFirstEulerianOperator_idempotent k A M n) x

/-- The original normalized proper quotient is an split image of its first projector. -/
@[reassoc]
theorem algebraNormalizedPositiveEulerianSection_projection :
    algebraNormalizedPositiveEulerianSection k A M ≫ algebraNormalizedPositiveProjection k A M =
      𝟙 (algebraNormalizedPositiveQuotientComplex k A M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext y
  refine Quotient.inductionOn' y ?_
  intro x
  exact mkQ_idempotent (algebraNormalizedPositiveRelations k A M n)
    (algebraNormalizedFirstEulerianOperator k A M n)
    (algebraNormalizedPositiveRelations_eq_firstEulerianKernel k A M n)
    (algebraNormalizedFirstEulerianOperator_idempotent k A M n) x

/-- The original raw and normalized proper projectors commute with the same normalization. -/
theorem properProjectors_normalization :
    (algebraRawPositiveProjection k A M ≫ algebraPositiveEulerianSection k A M) ≫
        algebraNormalizationProjection k A M =
      algebraNormalizationProjection k A M ≫
        (algebraNormalizedPositiveProjection k A M ≫ algebraNormalizedPositiveEulerianSection k A M) := by
  rw [algebraRawPositiveProjection_eulerianSection, algebraNormalizedPositiveProjection_eulerianSection]
  exact (algebraNormalizationProjection_firstEulerian k A M).symm

/-- Original full normalization restricts and projects to the proper quotient homotopy equivalence. -/
def algebraPositiveNormalizationHomotopyEquiv :
    HomotopyEquiv (algebraPositiveQuotientComplex k A M)
      (algebraNormalizedPositiveQuotientComplex k A M) :=
  HomologicalComplex.homotopyEquivOnSplitImages
    (algebraNormalizationProjection k A M) (algebraNormalizationInverse k A M)
    (algebraNormalizationInverse_projection k A M)
    (algebraNormalizationHomotopyEquiv k A M).homotopyHomInvId
    (algebraPositiveEulerianSection k A M) (algebraRawPositiveProjection k A M)
    (algebraPositiveEulerianSection_projection k A M)
    (algebraNormalizedPositiveEulerianSection k A M) (algebraNormalizedPositiveProjection k A M)
    (algebraNormalizedPositiveEulerianSection_projection k A M)
    (properProjectors_normalization k A M)

/-- The forward map is the original A-linear proper normalization on every
original quotient representative, not an abstract replacement comparison. -/
theorem algebraPositiveNormalizationHomotopyEquiv_hom :
    (algebraPositiveNormalizationHomotopyEquiv k A M).hom = algebraPositiveNormalization k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext y
  refine Quotient.inductionOn' y ?_
  intro x
  change (algebraNormalizedPositiveRelations k A M n).mkQ
      (algebraNormalizationLevelMap k A M n (algebraFirstEulerianOperator k A M n x)) =
    (algebraNormalizedPositiveRelations k A M n).mkQ (algebraNormalizationLevelMap k A M n x)
  have hp : algebraNormalizationLevelMap k A M n (algebraFirstEulerianOperator k A M n x) =
      algebraNormalizedFirstEulerianOperator k A M n (algebraNormalizationLevelMap k A M n x) := by
    have h := DFunLike.congr_fun (algebraNormalizationLevelMap_firstEulerian k A M n) x
    simp only [LinearMap.comp_apply] at h
    exact h
  rw [hp]
  exact mkQ_idempotent (algebraNormalizedPositiveRelations k A M n)
    (algebraNormalizedFirstEulerianOperator k A M n)
    (algebraNormalizedPositiveRelations_eq_firstEulerianKernel k A M n)
    (algebraNormalizedFirstEulerianOperator_idempotent k A M n)
    (algebraNormalizationLevelMap k A M n x)

/-- The inverse is the normalized first-projector section followed by
the original normalization section and the original raw quotient. -/
theorem algebraPositiveNormalizationHomotopyEquiv_inv :
    (algebraPositiveNormalizationHomotopyEquiv k A M).inv =
      algebraNormalizedPositiveEulerianSection k A M ≫ algebraNormalizationInverse k A M ≫
        algebraRawPositiveProjection k A M := rfl

/-- The projected original inverse is an exact right inverse on the original normalized proper quotient. -/
@[reassoc]
theorem algebraPositiveNormalizationHomotopyEquiv_inv_hom :
    (algebraPositiveNormalizationHomotopyEquiv k A M).inv ≫ algebraPositiveNormalization k A M =
      𝟙 (algebraNormalizedPositiveQuotientComplex k A M) := by
  have h := HomologicalComplex.splitImageInverse_forward
    (algebraNormalizationProjection k A M) (algebraNormalizationInverse k A M)
    (algebraNormalizationInverse_projection k A M)
    (algebraPositiveEulerianSection k A M) (algebraRawPositiveProjection k A M)
    (algebraNormalizedPositiveEulerianSection k A M) (algebraNormalizedPositiveProjection k A M)
    (algebraNormalizedPositiveEulerianSection_projection k A M)
    (properProjectors_normalization k A M)
  change (algebraPositiveNormalizationHomotopyEquiv k A M).inv ≫
    (algebraPositiveNormalizationHomotopyEquiv k A M).hom = _ at h
  rw [algebraPositiveNormalizationHomotopyEquiv_hom] at h
  exact h

/-- The original A-linear proper normalization is a quasi-isomorphism by its projected homotopy equivalence. -/
instance algebraPositiveNormalization_quasiIso : _root_.QuasiIso (algebraPositiveNormalization k A M) := by
  rw [← algebraPositiveNormalizationHomotopyEquiv_hom]
  exact (algebraPositiveNormalizationHomotopyEquiv k A M).quasiIso_hom

/-- The A-linear proper normalization kernel is contracted by the original projected native homotopy. -/
def algebraPositiveNormalizationKernelContraction :
    Homotopy (𝟙 (kernel (algebraPositiveNormalization k A M))) 0 :=
  HomologicalComplex.splitHomotopyKernelContraction
    (algebraPositiveNormalization k A M) (algebraPositiveNormalizationHomotopyEquiv k A M).inv
    (algebraPositiveNormalizationHomotopyEquiv_inv_hom k A M)
    (by
      simpa only [algebraPositiveNormalizationHomotopyEquiv_hom] using
        (algebraPositiveNormalizationHomotopyEquiv k A M).homotopyHomInvId)

/-- The proper normalization kernel is contractible in the original A-module category. -/
theorem algebraPositiveNormalizationKernel_contractible :
    (kernel (algebraPositiveNormalization k A M)).Contractible :=
  HomologicalComplex.splitHomotopyKernel_contractible
    (algebraPositiveNormalization k A M) (algebraPositiveNormalizationHomotopyEquiv k A M).inv
    (algebraPositiveNormalizationHomotopyEquiv_inv_hom k A M)
    (by
      simpa only [algebraPositiveNormalizationHomotopyEquiv_hom] using
        (algebraPositiveNormalizationHomotopyEquiv k A M).homotopyHomInvId)

/-- Original all-degree proper normalization homology is induced by the original quotient normalization map. -/
def algebraPositiveNormalizationHomologyIso (n : ℕ) :
    (algebraPositiveQuotientComplex k A M).homology n ≅
      (algebraNormalizedPositiveQuotientComplex k A M).homology n :=
  (algebraPositiveNormalizationHomotopyEquiv k A M).toHomologyIso n

/-- The homology comparison retains the original proper normalization as its forward homology map. -/
theorem algebraPositiveNormalizationHomologyIso_hom (n : ℕ) :
    (algebraPositiveNormalizationHomologyIso k A M n).hom =
      HomologicalComplex.homologyMap (algebraPositiveNormalization k A M) n := by
  change HomologicalComplex.homologyMap (algebraPositiveNormalizationHomotopyEquiv k A M).hom n = _
  rw [algebraPositiveNormalizationHomotopyEquiv_hom]

end ModuleCat.Algebra.Hochschild.Symmetric
