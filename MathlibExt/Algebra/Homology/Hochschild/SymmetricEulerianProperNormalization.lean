/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianComplex
public import MathlibExt.Algebra.Homology.HomotopyEquivOnSplitImages
public import MathlibExt.Algebra.Homology.SplitHomotopyKernel

/-!
# Proper-shuffle normalization and Eulerian split images

Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. In degree n, quotient the raw Hochschild term M ⊗[k] A^{⊗n} by both-positive
coefficient shuffle relations. The corresponding normalized term uses V = A/(k·1) as a k-module;
its A-action is on M alone. These relation modules are kernels of the zero-plus-first Eulerian
projectors, so the projectors provide chain sections of both proper quotient projections.

Hochschild normalization intertwines the raw and normalized projectors. Projecting its section
and homotopy through these split images gives an A-linear proper normalization homotopy
equivalence, a strict right inverse of its forward map, and a contraction of its kernel. No
commutation of the full normalization homotopy with the projectors is required. Restricting this
equivalence to k and transporting the endpoints through the scalar-restriction comparisons gives
the ground-linear equivalence and the homology comparisons in every natural-number degree. The
quotient normalization maps themselves are defined integrally.
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

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. In degree n, the A-linear section from (M ⊗[k] A^{⊗n})/Sₙ to M ⊗[k] A^{⊗n} sends [x]
to Eₙx, where Sₙ consists of both-positive coefficient shuffles and Eₙ is the zero-plus-first
Eulerian projector. The equality Sₙ = ker Eₙ makes this map well-defined. -/
def algebraPositiveEulerianSectionLevel (n : ℕ) :
    ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n) →ₗ[A]
      M ⊗[k] TensorPower k n A :=
  (algebraPositiveRelations k A M n).liftQ (algebraFirstEulerianOperator k A M n)
    (algebraPositiveRelations_eq_firstEulerianKernel k A M n).le

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. Put V = A/(k·1), regarded as a k-module. The A-linear section from (M ⊗[k] V^{⊗n})/S̄ₙ
to M ⊗[k] V^{⊗n} sends [x] to the normalized zero-plus-first Eulerian projector Ēₙx. The
A-action is on M, and S̄ₙ consists of both-positive coefficient shuffles. -/
def algebraNormalizedPositiveEulerianSectionLevel (n : ℕ) :
    ((M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
      algebraNormalizedPositiveRelations k A M n) →ₗ[A]
        M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
  (algebraNormalizedPositiveRelations k A M n).liftQ
    (algebraNormalizedFirstEulerianOperator k A M n)
    (algebraNormalizedPositiveRelations_eq_firstEulerianKernel k A M n).le

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. For n : ℕ and x ∈ M ⊗[k] A^{⊗n}, the section of the raw proper quotient sends the
class of x modulo algebraPositiveRelations to algebraFirstEulerianOperator k A M n x. -/
theorem algebraPositiveEulerianSectionLevel_mkQ (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    algebraPositiveEulerianSectionLevel k A M n ((algebraPositiveRelations k A M n).mkQ x) =
      algebraFirstEulerianOperator k A M n x := rfl

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. For n : ℕ and x ∈ M ⊗[k] (A/(k·1))^{⊗n}, the section of the normalized proper quotient
sends [x] to algebraNormalizedFirstEulerianOperator k A M n x. -/
theorem algebraNormalizedPositiveEulerianSectionLevel_mkQ (n : ℕ)
    (x : M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :
    algebraNormalizedPositiveEulerianSectionLevel k A M n
        ((algebraNormalizedPositiveRelations k A M n).mkQ x) =
      algebraNormalizedFirstEulerianOperator k A M n x := rfl

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The degreewise maps [x] ↦ Eₙx form an A-linear chain map from the raw proper-shuffle
quotient to the Hochschild chain complex. Its chain-map equation follows from Eₙ b = b Eₙ₊₁. -/
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

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The degreewise normalized Eulerian sections [x] ↦ Ēₙx form an A-linear chain map from
the normalized proper-shuffle quotient to the normalized Hochschild complex with terms M ⊗[k]
(A/(k·1))^{⊗n}. -/
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

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. Projection from the raw Hochschild complex to its proper-shuffle quotient, followed by
the Eulerian section back to the raw complex, equals algebraFirstEulerianChainMap k A M. -/
@[reassoc]
theorem algebraRawPositiveProjection_eulerianSection :
    algebraRawPositiveProjection k A M ≫ algebraPositiveEulerianSection k A M =
      algebraFirstEulerianChainMap k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. Projection from the normalized Hochschild complex to its proper-shuffle quotient,
followed by its Eulerian section, equals algebraNormalizedFirstEulerianChainMap k A M. -/
@[reassoc]
theorem algebraNormalizedPositiveProjection_eulerianSection :
    algebraNormalizedPositiveProjection k A M ≫ algebraNormalizedPositiveEulerianSection k A M =
      algebraNormalizedFirstEulerianChainMap k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The Eulerian section from the raw proper-shuffle quotient, followed by the quotient
projection, is the identity on algebraPositiveQuotientComplex k A M. Thus the quotient is a
split image of the first Eulerian chain projector. -/
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

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The normalized Eulerian section, followed by the proper-shuffle quotient projection,
is the identity on algebraNormalizedPositiveQuotientComplex k A M. -/
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

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. Let π and s be the raw proper quotient projection and Eulerian section, and let π̄ and
s̄ be their normalized counterparts. For the Hochschild normalization map N, the equality (π ≫
s) ≫ N = N ≫ (π̄ ≫ s̄) holds. -/
theorem properProjectors_normalization :
    (algebraRawPositiveProjection k A M ≫ algebraPositiveEulerianSection k A M) ≫
        algebraNormalizationProjection k A M =
      algebraNormalizationProjection k A M ≫
        (algebraNormalizedPositiveProjection k A M ≫ algebraNormalizedPositiveEulerianSection k A M) := by
  rw [algebraRawPositiveProjection_eulerianSection, algebraNormalizedPositiveProjection_eulerianSection]
  exact (algebraNormalizationProjection_firstEulerian k A M).symm

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The raw and normalized proper-shuffle quotient complexes are homotopy equivalent in
the category of A-modules. Projecting the Hochschild normalization inverse and homotopy through
their Eulerian split images constructs the equivalence. Its forward map is the quotient
normalization N, and its inverse is s̄ ≫ N⁻¹ ≫ π; no commutation of the full normalization
homotopy with the projectors is assumed. -/
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

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The forward chain map of algebraPositiveNormalizationHomotopyEquiv k A M is exactly
algebraPositiveNormalization k A M, the map induced on proper-shuffle quotients by Hochschild
normalization. -/
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

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The inverse chain map of the proper normalization equivalence is the normalized
Eulerian section, followed by the Hochschild normalization inverse and the raw proper quotient
projection: s̄ ≫ N⁻¹ ≫ π. -/
theorem algebraPositiveNormalizationHomotopyEquiv_inv :
    (algebraPositiveNormalizationHomotopyEquiv k A M).inv =
      algebraNormalizedPositiveEulerianSection k A M ≫ algebraNormalizationInverse k A M ≫
        algebraRawPositiveProjection k A M := rfl

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The inverse map of algebraPositiveNormalizationHomotopyEquiv k A M, followed by
algebraPositiveNormalization k A M, is the identity on the normalized proper-shuffle quotient
complex. -/
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

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. Normalization from the raw to the normalized proper-shuffle quotient is a
quasi-isomorphism in the category of A-modules because it is the forward map of
algebraPositiveNormalizationHomotopyEquiv. -/
instance algebraPositiveNormalization_quasiIso : _root_.QuasiIso (algebraPositiveNormalization k A M) := by
  rw [← algebraPositiveNormalizationHomotopyEquiv_hom]
  exact (algebraPositiveNormalizationHomotopyEquiv k A M).quasiIso_hom

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The kernel complex of algebraPositiveNormalization k A M admits a chain homotopy from
its identity to zero. The contraction is induced by the projected normalization homotopy and the
strict right inverse of the quotient normalization map. -/
def algebraPositiveNormalizationKernelContraction :
    Homotopy (𝟙 (kernel (algebraPositiveNormalization k A M))) 0 :=
  HomologicalComplex.splitHomotopyKernelContraction
    (algebraPositiveNormalization k A M) (algebraPositiveNormalizationHomotopyEquiv k A M).inv
    (algebraPositiveNormalizationHomotopyEquiv_inv_hom k A M)
    (by
      simpa only [algebraPositiveNormalizationHomotopyEquiv_hom] using
        (algebraPositiveNormalizationHomotopyEquiv k A M).homotopyHomInvId)

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. There exists a chain homotopy from the identity of kernel
(algebraPositiveNormalization k A M) to its zero endomorphism, so this kernel complex is
contractible in the category of A-modules. -/
theorem algebraPositiveNormalizationKernel_contractible :
    Nonempty (Homotopy (𝟙 (kernel (algebraPositiveNormalization k A M))) 0) :=
  HomologicalComplex.splitHomotopyKernel_contractible
    (algebraPositiveNormalization k A M) (algebraPositiveNormalizationHomotopyEquiv k A M).inv
    (algebraPositiveNormalizationHomotopyEquiv_inv_hom k A M)
    (by
      simpa only [algebraPositiveNormalizationHomotopyEquiv_hom] using
        (algebraPositiveNormalizationHomotopyEquiv k A M).homotopyHomInvId)

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. For every n : ℕ, the raw and normalized proper-shuffle quotient complexes have
isomorphic nth homology in the category of A-modules. The isomorphism is induced by their proper
normalization homotopy equivalence. -/
def algebraPositiveNormalizationHomologyIso (n : ℕ) :
    (algebraPositiveQuotientComplex k A M).homology n ≅
      (algebraNormalizedPositiveQuotientComplex k A M).homology n :=
  (algebraPositiveNormalizationHomotopyEquiv k A M).toHomologyIso n

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. In degree n : ℕ, the forward map of algebraPositiveNormalizationHomologyIso k A M n
equals the homology map induced by algebraPositiveNormalization k A M. -/
theorem algebraPositiveNormalizationHomologyIso_hom (n : ℕ) :
    (algebraPositiveNormalizationHomologyIso k A M n).hom =
      HomologicalComplex.homologyMap (algebraPositiveNormalization k A M) n := by
  change HomologicalComplex.homologyMap (algebraPositiveNormalizationHomotopyEquiv k A M).hom n = _
  rw [algebraPositiveNormalizationHomotopyEquiv_hom]

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The ground-linear proper quotient and its normalized proper quotient are homotopy
equivalent. Restricting the A-linear normalization equivalence to k and transporting its
endpoints through the raw and normalized scalar-restriction isomorphisms gives this equivalence. -/
def positiveNormalizationHomotopyEquiv :
    HomotopyEquiv (positiveQuotient k A M) (normalizedPositiveQuotient k A M) :=
  ((HomotopyEquiv.ofIso (algebraPositiveQuotientRestrictionIso k A M).symm).trans
    ((ModuleCat.restrictScalars (algebraMap k A)).mapHomotopyEquiv
      (algebraPositiveNormalizationHomotopyEquiv k A M))).trans
    (HomotopyEquiv.ofIso (algebraNormalizedPositiveQuotientRestrictionIso k A M))

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The forward map of positiveNormalizationHomotopyEquiv k A M is exactly
positiveQuotientNormalization k A M, the ground-linear raw-to-normalized proper quotient map. -/
theorem positiveNormalizationHomotopyEquiv_hom :
    (positiveNormalizationHomotopyEquiv k A M).hom = positiveQuotientNormalization k A M := by
  change ((algebraPositiveQuotientRestrictionIso k A M).inv ≫
      ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (algebraPositiveNormalizationHomotopyEquiv k A M).hom) ≫
      (algebraNormalizedPositiveQuotientRestrictionIso k A M).hom =
    positiveQuotientNormalization k A M
  rw [algebraPositiveNormalizationHomotopyEquiv_hom, Category.assoc,
    algebraPositiveNormalization_restrictScalars, Iso.inv_hom_id_assoc]

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The inverse proper normalization map is the A-linear inverse restricted to k, preceded
by the inverse normalized quotient comparison and followed by the raw quotient comparison. All
three maps act on the corresponding ground-linear chain complexes. -/
theorem positiveNormalizationHomotopyEquiv_inv :
    (positiveNormalizationHomotopyEquiv k A M).inv =
      (algebraNormalizedPositiveQuotientRestrictionIso k A M).inv ≫
        ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (algebraPositiveNormalizationHomotopyEquiv k A M).inv ≫
            (algebraPositiveQuotientRestrictionIso k A M).hom := rfl

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. The ground-linear normalization map on proper-shuffle quotients is a
quasi-isomorphism, as the forward map of the transported normalization homotopy equivalence. -/
instance positiveQuotientNormalization_quasiIso :
    _root_.QuasiIso (positiveQuotientNormalization k A M) := by
  rw [← positiveNormalizationHomotopyEquiv_hom]
  exact (positiveNormalizationHomotopyEquiv k A M).quasiIso_hom

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. For each n : ℕ, normalization induces an isomorphism from positiveHomology k A M n to
normalizedPositiveHomology k A M n in the category of k-modules. -/
def positiveNormalizationHomologyIso (n : ℕ) :
    positiveHomology k A M n ≅ normalizedPositiveHomology k A M n :=
  (positiveNormalizationHomotopyEquiv k A M).toHomologyIso n

/-- Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an A-module with compatible
k-action. In degree n : ℕ, the forward map of positiveNormalizationHomologyIso k A M n equals
positiveNormalizationHomologyMap k A M n, induced by the integral quotient normalization map. -/
theorem positiveNormalizationHomologyIso_hom (n : ℕ) :
    (positiveNormalizationHomologyIso k A M n).hom =
      positiveNormalizationHomologyMap k A M n := by
  change HomologicalComplex.homologyMap (positiveNormalizationHomotopyEquiv k A M).hom n =
    HomologicalComplex.homologyMap (positiveQuotientNormalization k A M) n
  rw [positiveNormalizationHomotopyEquiv_hom]

end ModuleCat.Algebra.Hochschild.Symmetric
