/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianPositiveKernel
public import MathlibExt.Algebra.Homology.Hochschild.EulerianChainMaps
public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleCotangentMap

/-!
# Eulerian section of the proper-shuffle quotient

Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible symmetric
coefficient module. The sum of the weight-zero and weight-one Eulerian chain projectors has
kernel equal, degree by degree, to the both-positive coefficient shuffle relation submodule. The
quotient-to-image isomorphism therefore defines a section [x] ↦ Eₙx of each proper quotient
term.

The Eulerian boundary identities make these sections a chain map. Projection followed by the
section is the weight-zero-plus-one projector; the section followed by projection is the
identity on the proper quotient. Consequently the proper quotient is a retract of Hochschild
chains. Both weights are retained before restricting to positive indices.

For the Eulerian decomposition and its relation to proper Harrison shuffles, see J.-L. Loday,
Cyclic Homology, second edition, §§4.2 and 4.5.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. firstEulerianChainMap is eulerianChainMap k A M 0 + eulerianChainMap k A
M 1, an endomorphism of the Hochschild chain complex. It retains both Eulerian weights zero and
one, including the degree-zero coefficient term. -/
def firstEulerianChainMap : chainComplex k A M ⟶ chainComplex k A M :=
  eulerianChainMap k A M 0 + eulerianChainMap k A M 1

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. In degree n : ℕ, the underlying linear map of firstEulerianChainMap is
firstEulerianOperator k A M n, the sum of the coefficient Eulerian operators of weights zero and
one. -/
theorem firstEulerianChainMap_f (n : ℕ) :
    ((firstEulerianChainMap k A M).f n).hom = firstEulerianOperator k A M n := rfl

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. The both-positive shuffle relation submodule Sₙ equals the kernel of the
retained Eulerian operator Eₙ. The quotient-to-range isomorphism followed by range inclusion
gives a k-linear map Pₙ = Cₙ(A,M)/Sₙ → Cₙ(A,M), sending [x] to Eₙx. -/
def properEulerianSectionLevel (n : ℕ) :
    (positiveQuotient k A M).X n →ₗ[k] M ⊗[k] TensorPower k n A :=
  (LinearMap.range (firstEulerianOperator k A M n)).subtype.comp
    (firstEulerianQuotientLevelEquiv k A M n).toLinearMap

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. For n : ℕ and x ∈ M ⊗[k] A^{⊗n}, properEulerianSectionLevel k A M n
sends the class of x modulo rawPositiveRelations to firstEulerianOperator k A M n x. -/
theorem properEulerianSectionLevel_mkQ (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    properEulerianSectionLevel k A M n ((rawPositiveRelations k A M n).mkQ x) =
      firstEulerianOperator k A M n x := by
  change ((firstEulerianOperator k A M n).quotKerEquivRange
    (Submodule.quotEquivOfEq _ _ (rawPositiveRelations_eq_firstEulerianKernel k A M n)
      (Submodule.Quotient.mk x)) : M ⊗[k] TensorPower k n A) = _
  rw [Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivRange_apply_mk _ x

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. The degreewise maps [x] ↦ Eₙx form a chain map properEulerianSection :
positiveQuotient k A M → chainComplex k A M, because the retained Eulerian operators commute
with the Hochschild boundary. -/
def properEulerianSection : positiveQuotient k A M ⟶ chainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (properEulerianSectionLevel k A M n)) (by
    intro n
    let f₁ : ((M ⊗[k] TensorPower k (n + 1) A) ⧸ rawPositiveRelations k A M (n + 1)) →ₗ[k]
        M ⊗[k] TensorPower k (n + 1) A := properEulerianSectionLevel k A M (n + 1)
    let f₀ : ((M ⊗[k] TensorPower k n A) ⧸ rawPositiveRelations k A M n) →ₗ[k]
        M ⊗[k] TensorPower k n A := properEulerianSectionLevel k A M n
    let d : (M ⊗[k] TensorPower k (n + 1) A) →ₗ[k] M ⊗[k] TensorPower k n A :=
      ((chainComplex k A M).d (n + 1) n).hom
    let δ : ((M ⊗[k] TensorPower k (n + 1) A) ⧸ rawPositiveRelations k A M (n + 1)) →ₗ[k]
        ((M ⊗[k] TensorPower k n A) ⧸ rawPositiveRelations k A M n) :=
      ((positiveQuotient k A M).d (n + 1) n).hom
    apply ModuleCat.hom_ext
    change d.comp f₁ = f₀.comp δ
    apply LinearMap.ext
    intro y
    refine Quotient.inductionOn' y ?_
    intro x
    have hf₁ : f₁ ((rawPositiveRelations k A M (n + 1)).mkQ x) =
        firstEulerianOperator k A M (n + 1) x := properEulerianSectionLevel_mkQ k A M (n + 1) x
    have hδ : δ ((rawPositiveRelations k A M (n + 1)).mkQ x) =
        (rawPositiveRelations k A M n).mkQ (algebraBoundary k A M n x) :=
      positiveQuotient_d_mk k A M n x
    have hf₀ : f₀ ((rawPositiveRelations k A M n).mkQ (algebraBoundary k A M n x)) =
        firstEulerianOperator k A M n (algebraBoundary k A M n x) :=
      properEulerianSectionLevel_mkQ k A M n (algebraBoundary k A M n x)
    have hE : d (firstEulerianOperator k A M (n + 1) x) =
        firstEulerianOperator k A M n (algebraBoundary k A M n x) := by
      have h := ConcreteCategory.congr_hom ((firstEulerianChainMap k A M).comm (n + 1) n) x
      exact h
    exact (congrArg d hf₁).trans
      (hE.trans (hf₀.symm.trans (congrArg f₀ hδ.symm))))

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. For every n : ℕ, the nth component of properEulerianSection has
underlying linear map properEulerianSectionLevel k A M n, the
quotient-to-retained-Eulerian-image section. -/
theorem properEulerianSection_f (n : ℕ) :
    ((properEulerianSection k A M).f n).hom = properEulerianSectionLevel k A M n := rfl

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. The composite chainComplex k A M → positiveQuotient k A M → chainComplex
k A M, with maps properShuffleProjection and properEulerianSection, equals firstEulerianChainMap
k A M. -/
@[reassoc]
theorem properShuffleProjection_eulerianSection :
    properShuffleProjection k A M ≫ properEulerianSection k A M = firstEulerianChainMap k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (properEulerianSectionLevel k A M n).comp (rawPositiveRelations k A M n).mkQ =
    firstEulerianOperator k A M n
  apply LinearMap.ext
  exact properEulerianSectionLevel_mkQ k A M n

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. firstEulerianChainMap composed with itself equals firstEulerianChainMap.
The weight-zero and weight-one Eulerian projectors are idempotent and mutually orthogonal. -/
theorem firstEulerianChainMap_idempotent :
    firstEulerianChainMap k A M ≫ firstEulerianChainMap k A M = firstEulerianChainMap k A M := by
  simp only [firstEulerianChainMap, Preadditive.comp_add, Preadditive.add_comp,
    eulerianChainMap_comp, ite_true, ite_eq_right (by omega : (0 : ℕ) ≠ 1),
    ite_eq_right (by omega : (1 : ℕ) ≠ 0), add_zero, zero_add]

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module with its
symmetric right action. properEulerianSection k A M followed by properShuffleProjection k A M is
the identity of positiveQuotient k A M. Thus the both-positive proper-shuffle quotient is a
retract of the Hochschild chain complex. -/
@[reassoc]
theorem properEulerianSection_projection :
    properEulerianSection k A M ≫ properShuffleProjection k A M = 𝟙 (positiveQuotient k A M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (rawPositiveRelations k A M n).mkQ.comp (properEulerianSectionLevel k A M n) = LinearMap.id
  refine LinearMap.ext (fun y : (M ⊗[k] TensorPower k n A) ⧸ rawPositiveRelations k A M n => ?_)
  refine Quotient.inductionOn' y (fun x : M ⊗[k] TensorPower k n A => ?_)
  change (rawPositiveRelations k A M n).mkQ
      (properEulerianSectionLevel k A M n ((rawPositiveRelations k A M n).mkQ x)) =
    (rawPositiveRelations k A M n).mkQ x
  rw [properEulerianSectionLevel_mkQ]
  apply sub_eq_zero.mp
  rw [← map_sub]
  change firstEulerianOperator k A M n x - x ∈
    LinearMap.ker (rawPositiveRelations k A M n).mkQ
  rw [Submodule.ker_mkQ, rawPositiveRelations_eq_firstEulerianKernel]
  change firstEulerianOperator k A M n (firstEulerianOperator k A M n x - x) = 0
  rw [map_sub]
  have h := congrArg (fun f => (f.f n).hom) (firstEulerianChainMap_idempotent k A M)
  change (firstEulerianOperator k A M n).comp (firstEulerianOperator k A M n) =
    firstEulerianOperator k A M n at h
  exact sub_eq_zero.mpr (LinearMap.congr_fun h x)

end ModuleCat.Algebra.Hochschild.Symmetric
