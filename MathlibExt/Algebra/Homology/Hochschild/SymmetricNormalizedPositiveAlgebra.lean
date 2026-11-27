/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricNormalizationAlgebra

/-!
# Normalized proper shuffle quotients and scalar restriction

Let k be a commutative ring, A a commutative k-algebra and M an A-module with induced k-action.
The normalized relations are the A-linear images of the raw proper shuffle relations under
factorwise normalization. Their quotient complex has terms (M⊗_k(A/(k·1))^{⊗n})/S̄_n and
boundary induced by the normalized Hochschild differential; A acts on the coefficient, while the
quotient tails remain k-modules.

After restricting scalars to k, this complex is canonically isomorphic to the ground-linear
normalized proper quotient. The comparison preserves each quotient representative and commutes
with the raw-to-normalized map and the existing raw scalar-restriction comparison.
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. The normalized
A-submodule S̄_n is the image of the raw proper-shuffle submodule S_n under the A-linear
normalization map M⊗_kA^{⊗n} → C_n. The A-action affects the coefficient M. -/
def algebraNormalizedPositiveRelations (n : ℕ) :
    Submodule A (M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :=
  (algebraPositiveRelations k A M n).map (algebraNormalizationLevelMap k A M n)

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. Restricting the
A-submodule S̄_n to k gives exactly normalizedPositiveRelations(A,M,n), the ground-linear image
of the proper shuffle relations. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. For n ∈ ℕ with n≤1,
algebraNormalizedPositiveRelations(A,M,n)=0. Every proper shuffle relation requires both input
degrees positive, hence total degree at least two. -/
theorem algebraNormalizedPositiveRelations_low (n : ℕ) (hn : n ≤ 1) :
    algebraNormalizedPositiveRelations k A M n = ⊥ := by
  rw [algebraNormalizedPositiveRelations, algebraPositiveRelations_low k A M n hn, Submodule.map_bot]

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. The normalized boundary
b̄_n : C_{n+1} → C_n sends S̄_{n+1} into S̄_n. Equivalently, if x lies in
algebraNormalizedPositiveRelations in degree n+1, then algebraNormalizedBoundary_n(x) lies in
that submodule in degree n. -/
theorem algebraNormalizedPositiveRelations_boundary (n : ℕ)
    {x : M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)}
    (hx : x ∈ algebraNormalizedPositiveRelations k A M (n + 1)) :
    algebraNormalizedBoundary k A M n x ∈ algebraNormalizedPositiveRelations k A M n := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  apply Submodule.mem_map.mpr
  refine ⟨algebraBoundary k A M n y, algebraPositiveRelations_boundary k A M n hy, ?_⟩
  exact (nativeNormalizationBoundary_apply k A M n y).symm

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. The quotient differential
C_{n+1}/S̄_{n+1} → C_n/S̄_n is the A-linear map [x] ↦ [algebraNormalizedBoundary_n(x)], induced
by preservation of the relation submodules. -/
def algebraNormalizedPositiveQuotientDifferential (n : ℕ) :
    ModuleCat.of A ((M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
      algebraNormalizedPositiveRelations k A M (n + 1)) ⟶
    ModuleCat.of A ((M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
      algebraNormalizedPositiveRelations k A M n) :=
  ModuleCat.ofHom ((algebraNormalizedPositiveRelations k A M (n + 1)).mapQ
    (algebraNormalizedPositiveRelations k A M n) (algebraNormalizedBoundary k A M n)
      (fun _ hx => algebraNormalizedPositiveRelations_boundary k A M n hx))

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. For every n ∈ ℕ, the
induced differential from degree n+2 to n+1 followed by that from n+1 to n is zero, since the
normalized Hochschild boundary squares to zero. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. The normalized A-linear
proper quotient is the nonnegative chain complex with degree-n term C_n/S̄_n and differential
induced by algebraNormalizedBoundary. Its tensor tails V remain ground-ring modules. -/
def algebraNormalizedPositiveQuotientComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A
    ((M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
      algebraNormalizedPositiveRelations k A M n))
    (algebraNormalizedPositiveQuotientDifferential k A M)
    (algebraNormalizedPositiveQuotientDifferential_comp k A M)

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. The A-linear chain map
from algebraNormalizedChainComplex(A,M) to algebraNormalizedPositiveQuotientComplex(A,M) has
degree-n component the quotient projection C_n → C_n/S̄_n. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. Factorwise normalization
descends to an A-linear chain map from the raw proper quotient to the normalized proper
quotient. In degree n it sends the raw class [x] to [algebraNormalizationLevelMap_n(x)]. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. For n ∈ ℕ and x ∈
M⊗_kA^{⊗n}, the degree-n normalization map sends the class of x modulo raw A-linear proper
relations to the class of algebraNormalizationLevelMap_n(x) modulo S̄_n. -/
theorem algebraPositiveNormalization_f_mkQ (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    ((algebraPositiveNormalization k A M).f n).hom ((algebraPositiveRelations k A M n).mkQ x) =
      (algebraNormalizedPositiveRelations k A M n).mkQ (algebraNormalizationLevelMap k A M n x) := rfl

private def normalizedPositiveRestrictionLevelIso (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k A)).obj
        ((algebraNormalizedPositiveQuotientComplex k A M).X n) ≅
      (normalizedPositiveQuotient k A M).X n := by
  let e :
      ((M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
        algebraNormalizedPositiveRelations k A M n) ≃ₗ[k]
      (normalizedPositiveQuotient k A M).X n :=
    (Submodule.Quotient.restrictScalarsEquiv k
      (algebraNormalizedPositiveRelations k A M n)).symm.trans
        (Submodule.quotEquivOfEq _ _
          (algebraNormalizedPositiveRelations_restrictScalars k A M n))
  let f :
      (ModuleCat.restrictScalars (algebraMap k A)).obj
          ((algebraNormalizedPositiveQuotientComplex k A M).X n) ≃ₗ[k]
        ModuleCat.of k
          ((M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) ⧸
            algebraNormalizedPositiveRelations k A M n) :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        refine Quotient.inductionOn' x ?_
        intro y
        change (algebraNormalizedPositiveRelations k A M n).mkQ
            ((algebraMap k A r) • y) =
          (algebraNormalizedPositiveRelations k A M n).mkQ (r • y)
        have h : (algebraMap k A r) • y = r • y := by
          simpa only [Algebra.smul_def, mul_one, one_smul] using smul_assoc r (1 : A) y
        exact congrArg (algebraNormalizedPositiveRelations k A M n).mkQ h }
  exact (f.trans e).toModuleIso

private theorem normalizedPositiveRestrictionLevelIso_mk (n : ℕ)
    (x : M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :
    (normalizedPositiveRestrictionLevelIso k A M n).hom.hom
        ((algebraNormalizedPositiveRelations k A M n).mkQ x) =
      (normalizedPositiveRelations k A M n).mkQ x := by
  change Submodule.quotEquivOfEq _ _
      (algebraNormalizedPositiveRelations_restrictScalars k A M n)
      ((Submodule.Quotient.restrictScalarsEquiv k
        (algebraNormalizedPositiveRelations k A M n)).symm (Submodule.Quotient.mk x)) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  exact Submodule.quotEquivOfEq_mk _ _
    (algebraNormalizedPositiveRelations_restrictScalars k A M n) x

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. The ground-linear
normalized proper quotient differential sends [x] in degree n+1 to
[algebraNormalizedBoundary_n(x)] in degree n. -/
theorem normalizedPositiveQuotient_d_mk (n : ℕ)
    (x : M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :
    ((normalizedPositiveQuotient k A M).d (n + 1) n).hom
        ((normalizedPositiveRelations k A M (n + 1)).mkQ x) =
      (normalizedPositiveRelations k A M n).mkQ (algebraNormalizedBoundary k A M n x) := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  change ((HomologicalComplex.ChainGradedPairing.positiveImageQuotient
    ((pairing k A M).postcomp (normalizationProjection k A M))
    (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M)).d (n + 1) n).hom _ = _
  dsimp only [HomologicalComplex.ChainGradedPairing.positiveImageQuotient]
  rw [ChainComplex.of_d]
  rfl

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. For x ∈ M⊗_kA^{⊗n},
positiveQuotientNormalization_n sends its raw ground-linear proper class to the normalized
ground-linear class of algebraNormalizationLevelMap_n(x). -/
theorem positiveQuotientNormalization_f_mkQ (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    ((positiveQuotientNormalization k A M).f n).hom
        ((rawPositiveRelations k A M n).mkQ x) =
      (normalizedPositiveRelations k A M n).mkQ (algebraNormalizationLevelMap k A M n x) := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  have h := congrArg
    (fun f : chainComplex k A M ⟶ normalizedPositiveQuotient k A M => f.f n)
    (positiveQuotientNormalization_projection k A M)
  have hx := ConcreteCategory.congr_hom h x
  change ((positiveQuotientNormalization k A M).f n).hom
      ((rawPositiveRelations k A M n).mkQ x) =
    (normalizedPositiveRelations k A M n).mkQ (((normalizationProjection k A M).f n).hom x) at hx
  rw [nativeNormalizationProjection_f] at hx
  exact hx

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. Restricting the
normalized A-linear proper quotient complex to k is canonically isomorphic to
normalizedPositiveQuotient(A,M). The forward and inverse comparisons preserve the underlying
quotient representative in every degree. -/
def algebraNormalizedPositiveQuotientRestrictionIso :
    ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (algebraNormalizedPositiveQuotientComplex k A M) ≅ normalizedPositiveQuotient k A M :=
  HomologicalComplex.Hom.isoOfComponents (normalizedPositiveRestrictionLevelIso k A M) (by
    intro i j h
    change j + 1 = i at h
    subst i
    let S := ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (algebraNormalizedPositiveQuotientComplex k A M)
    let T := normalizedPositiveQuotient k A M
    let f₁ : S.X (j + 1) →ₗ[k] T.X (j + 1) :=
      (normalizedPositiveRestrictionLevelIso k A M (j + 1)).hom.hom
    let f₀ : S.X j →ₗ[k] T.X j :=
      (normalizedPositiveRestrictionLevelIso k A M j).hom.hom
    let d : T.X (j + 1) →ₗ[k] T.X j := (T.d (j + 1) j).hom
    let e : S.X (j + 1) →ₗ[k] S.X j := (S.d (j + 1) j).hom
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change d (f₁ z) = f₀ (e z)
    refine Quotient.inductionOn' z ?_
    intro x
    have hd : e ((algebraNormalizedPositiveRelations k A M (j + 1)).mkQ x) =
        (algebraNormalizedPositiveRelations k A M j).mkQ (algebraNormalizedBoundary k A M j x) := by
      change ((algebraNormalizedPositiveQuotientComplex k A M).d (j + 1) j).hom _ = _
      dsimp only [algebraNormalizedPositiveQuotientComplex]
      rw [ChainComplex.of_d]
      rfl
    have hf₁ : f₁ ((algebraNormalizedPositiveRelations k A M (j + 1)).mkQ x) =
        (normalizedPositiveRelations k A M (j + 1)).mkQ x :=
      normalizedPositiveRestrictionLevelIso_mk k A M (j + 1) x
    have hf₀ : f₀ ((algebraNormalizedPositiveRelations k A M j).mkQ
        (algebraNormalizedBoundary k A M j x)) =
        (normalizedPositiveRelations k A M j).mkQ (algebraNormalizedBoundary k A M j x) :=
      normalizedPositiveRestrictionLevelIso_mk k A M j (algebraNormalizedBoundary k A M j x)
    have hd' : d ((normalizedPositiveRelations k A M (j + 1)).mkQ x) =
        (normalizedPositiveRelations k A M j).mkQ (algebraNormalizedBoundary k A M j x) :=
      normalizedPositiveQuotient_d_mk k A M j x
    exact (congrArg d hf₁).trans
      (hd'.trans (hf₀.symm.trans (congrArg f₀ hd.symm))))

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. For x ∈ C_n, the degree-n
forward component of algebraNormalizedPositiveQuotientRestrictionIso sends the class of x modulo
S̄_n to the same class modulo normalizedPositiveRelations(A,M,n). -/
theorem algebraNormalizedPositiveQuotientRestrictionIso_hom_f_mk (n : ℕ)
    (x : M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :
    ((algebraNormalizedPositiveQuotientRestrictionIso k A M).hom.f n).hom
        ((algebraNormalizedPositiveRelations k A M n).mkQ x) =
      (normalizedPositiveRelations k A M n).mkQ x :=
  normalizedPositiveRestrictionLevelIso_mk k A M n x

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with its induced
k-action. Put V=A/(k·1), considered as a k-module, and C_n=M⊗_kV^{⊗n}. Let U restrict scalars
from A to k, Φ_raw be the raw proper quotient comparison and Φ_norm the normalized comparison.
Then U(algebraPositiveNormalization) ≫ Φ_norm.hom = Φ_raw.hom ≫ positiveQuotientNormalization as
maps from the restricted raw A-linear proper quotient to the ground-linear normalized proper
quotient. -/
@[reassoc]
theorem algebraPositiveNormalization_restrictScalars :
    ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (algebraPositiveNormalization k A M) ≫
      (algebraNormalizedPositiveQuotientRestrictionIso k A M).hom =
    (algebraPositiveQuotientRestrictionIso k A M).hom ≫ positiveQuotientNormalization k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change ((algebraNormalizedPositiveQuotientRestrictionIso k A M).hom.f n).hom
      (((algebraPositiveNormalization k A M).f n).hom z) =
    ((positiveQuotientNormalization k A M).f n).hom
      (((algebraPositiveQuotientRestrictionIso k A M).hom.f n).hom z)
  refine Quotient.inductionOn' z ?_
  intro x
  rw [algebraPositiveNormalization_f_mkQ,
    algebraNormalizedPositiveQuotientRestrictionIso_hom_f_mk]
  have hRaw : ((algebraPositiveQuotientRestrictionIso k A M).hom.f n).hom
      ((algebraPositiveRelations k A M n).mkQ x) =
    (rawPositiveRelations k A M n).mkQ x :=
    algebraPositiveQuotientRestrictionLevelIso_mk k A M n x
  rw [hRaw, positiveQuotientNormalization_f_mkQ]

end ModuleCat.Algebra.Hochschild.Symmetric
