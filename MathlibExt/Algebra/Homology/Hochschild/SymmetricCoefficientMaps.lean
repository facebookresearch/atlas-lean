/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricAlgebraComplex
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricNormalizedPositiveAlgebra
public import MathlibExt.Algebra.Homology.Hochschild.Maps

/-!
# Coefficient maps on algebra-linear Hochschild and proper-shuffle complexes

Let k be a commutative ring, A a commutative k-algebra and f : M → N an A-linear map between
modules with compatible k-actions. In every degree it acts as f ⊗ id on the coefficient tensor
and keeps all k-tensor tails. It commutes with the Hochschild boundary and the normalization
quotient A/(k·1). The same map preserves both-positive shuffle images, hence induces raw and
normalized proper-shuffle quotient chain maps with their original representatives.

See J.-L. Loday, Cyclic Homology, 2nd ed., Chapter 1 and §4.5, for coefficient functoriality
and shuffle quotients.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  {M N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module A N]
  [SMulCommClass k A M] [SMulCommClass k A N]
  [IsScalarTower k A M] [IsScalarTower k A N]

/-- The A-linear coefficient map in one Hochschild degree.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear map f : M → N,
this map is f ⊗ id on M ⊗[k] A⊗n → N ⊗[k] A⊗n. -/
def algebraCoefficientLevelMap (f : M →ₗ[A] N) (n : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[A] N ⊗[k] TensorPower k n A :=
  TensorProduct.AlgebraTensorModule.map f LinearMap.id

/-- The pure-word value of an A-linear coefficient map.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, m ⊗ x
maps to f(m) ⊗ x in degree n. -/
theorem algebraCoefficientLevelMap_tmul (f : M →ₗ[A] N) (n : ℕ) (m : M) (x : TensorPower k n A) :
    algebraCoefficientLevelMap k A f n (m ⊗ₜ[k] x) = f m ⊗ₜ[k] x := rfl

/-- The identity coefficient map acts identically on every A-linear Hochschild level.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
algebraCoefficientLevelMap(id_M,n)=id on M ⊗[k] A⊗n. -/
theorem algebraCoefficientLevelMap_id (n : ℕ) :
    algebraCoefficientLevelMap k A (LinearMap.id : M →ₗ[A] M) n = LinearMap.id :=
  TensorProduct.AlgebraTensorModule.map_id

/-- Ground restriction of the algebra-linear coefficient map.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N,
restriction from A to k agrees with the ground coefficient map having algebra arrow id_A and
coefficient arrow f. -/
theorem algebraCoefficientLevelMap_restrictScalars (f : M →ₗ[A] N) (n : ℕ) :
    (algebraCoefficientLevelMap k A f n).restrictScalars k =
      ModuleCat.Algebra.Hochschild.linearMap (NonUnitalAlgHom.id k A) (f.restrictScalars k) n := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  rw [LinearMap.restrictScalars_apply, algebraCoefficientLevelMap_tmul,
    ModuleCat.Algebra.Hochschild.linearMap_tprod]
  rfl

/-- The algebra-linear coefficient arrow commutes with the raw boundary.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, bₙ,N
∘ fₙ₊₁ = fₙ ∘ bₙ,M on the raw coefficient tensor levels. -/
theorem algebraCoefficientLevelMap_boundary (f : M →ₗ[A] N) (n : ℕ) :
    (algebraBoundary k A N n).comp (algebraCoefficientLevelMap k A f (n + 1)) =
      (algebraCoefficientLevelMap k A f n).comp (algebraBoundary k A M n) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  letI := opModule A N
  letI := actionsComm A N
  letI := kOpComm k A N
  letI := kOpTower k A N
  apply LinearMap.restrictScalars_injective k
  rw [LinearMap.restrictScalars_comp, LinearMap.restrictScalars_comp,
    algebraCoefficientLevelMap_restrictScalars, algebraCoefficientLevelMap_restrictScalars]
  apply LinearMap.ext
  intro x
  change ((ModuleCat.Algebra.Hochschild.chainComplex k A N).d (n + 1) n).hom
      (ModuleCat.Algebra.Hochschild.linearMap (NonUnitalAlgHom.id k A) (f.restrictScalars k) (n + 1) x) =
    ModuleCat.Algebra.Hochschild.linearMap (NonUnitalAlgHom.id k A) (f.restrictScalars k) n
      (((ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n).hom x)
  rw [ModuleCat.Algebra.Hochschild.chainComplex_d, ModuleCat.Algebra.Hochschild.chainComplex_d]
  have h := ModuleCat.Algebra.Hochschild.linearMap_boundary_comm
    (NonUnitalAlgHom.id k A) (f.restrictScalars k)
    (fun a m => f.map_smul a m)
    (fun a m => by
      change f (a • m) = a • f m
      exact f.map_smul a m) n
  exact DFunLike.congr_fun h x

/-- The raw A-linear Hochschild chain map induced by a coefficient arrow.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N,
assemble its maps f ⊗ id in all degrees of algebraRawComplex. -/
def algebraRawCoefficientMap (f : M →ₗ[A] N) : algebraRawComplex k A M ⟶ algebraRawComplex k A N :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraCoefficientLevelMap k A f n)) (by
    intro n
    apply ModuleCat.hom_ext
    dsimp only [algebraRawComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    exact algebraCoefficientLevelMap_boundary k A f n)

/-- The component formula of the raw algebra-linear coefficient chain map.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, its
nth component is algebraCoefficientLevelMap(f,n). -/
theorem algebraRawCoefficientMap_f (f : M →ₗ[A] N) (n : ℕ) :
    ((algebraRawCoefficientMap k A f).f n).hom = algebraCoefficientLevelMap k A f n := rfl

/-- The coefficient arrow on normalized A-linear Hochschild levels.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, apply
f to M and keep the tensor factors of the ground quotient A/(k·1). -/
def algebraNormalizedCoefficientLevelMap (f : M →ₗ[A] N) (n : ℕ) :
    M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[A]
      N ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
  TensorProduct.AlgebraTensorModule.map f LinearMap.id

/-- Coefficient maps commute with the A-linear normalization projection.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N,
projecting fₙ to normalized tensors equals applying its normalized coefficient map after the
projection of the source. -/
theorem algebraNormalizationLevelMap_coefficient (f : M →ₗ[A] N) (n : ℕ) :
    (algebraNormalizationLevelMap k A N n).comp (algebraCoefficientLevelMap k A f n) =
      (algebraNormalizedCoefficientLevelMap k A f n).comp (algebraNormalizationLevelMap k A M n) := by
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  simp only [TensorProduct.curry_apply, LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    algebraCoefficientLevelMap, algebraNormalizedCoefficientLevelMap, algebraNormalizationLevelMap,
    TensorProduct.AlgebraTensorModule.map_tmul, TensorProduct.AlgebraTensorModule.lTensor_tmul,
    LinearMap.id_apply]

/-- The normalized coefficient arrow commutes with the normalized boundary.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, the f
⊗ id maps on normalized tensor tails form a chain map. -/
theorem algebraNormalizedCoefficientLevelMap_boundary (f : M →ₗ[A] N) (n : ℕ) :
    (algebraNormalizedBoundary k A N n).comp (algebraNormalizedCoefficientLevelMap k A f (n + 1)) =
      (algebraNormalizedCoefficientLevelMap k A f n).comp (algebraNormalizedBoundary k A M n) := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := algebraNormalizationLevelMap_surjective k A M (n + 1) y
  have hM (z : M ⊗[k] TensorPower k (n + 1) A) :
      algebraNormalizedBoundary k A M n (algebraNormalizationLevelMap k A M (n + 1) z) =
        algebraNormalizationLevelMap k A M n (algebraBoundary k A M n z) :=
    nativeNormalizationBoundary_apply k A M n z
  have hN (z : N ⊗[k] TensorPower k (n + 1) A) :
      algebraNormalizedBoundary k A N n (algebraNormalizationLevelMap k A N (n + 1) z) =
        algebraNormalizationLevelMap k A N n (algebraBoundary k A N n z) :=
    nativeNormalizationBoundary_apply k A N n z
  change algebraNormalizedBoundary k A N n
      (algebraNormalizedCoefficientLevelMap k A f (n + 1) (algebraNormalizationLevelMap k A M (n + 1) x)) =
    algebraNormalizedCoefficientLevelMap k A f n
      (algebraNormalizedBoundary k A M n (algebraNormalizationLevelMap k A M (n + 1) x))
  have hc₁ : algebraNormalizationLevelMap k A N (n + 1) (algebraCoefficientLevelMap k A f (n + 1) x) =
      algebraNormalizedCoefficientLevelMap k A f (n + 1) (algebraNormalizationLevelMap k A M (n + 1) x) :=
    (LinearMap.comp_apply (algebraNormalizationLevelMap k A N (n + 1))
      (algebraCoefficientLevelMap k A f (n + 1)) x).symm.trans
      ((DFunLike.congr_fun (algebraNormalizationLevelMap_coefficient k A f (n + 1)) x).trans
        (LinearMap.comp_apply (algebraNormalizedCoefficientLevelMap k A f (n + 1))
          (algebraNormalizationLevelMap k A M (n + 1)) x))
  have hb : algebraBoundary k A N n (algebraCoefficientLevelMap k A f (n + 1) x) =
      algebraCoefficientLevelMap k A f n (algebraBoundary k A M n x) :=
    (LinearMap.comp_apply (algebraBoundary k A N n) (algebraCoefficientLevelMap k A f (n + 1)) x).symm.trans
      ((DFunLike.congr_fun (algebraCoefficientLevelMap_boundary k A f n) x).trans
        (LinearMap.comp_apply (algebraCoefficientLevelMap k A f n) (algebraBoundary k A M n) x))
  have hc₀ : algebraNormalizationLevelMap k A N n
        (algebraCoefficientLevelMap k A f n (algebraBoundary k A M n x)) =
      algebraNormalizedCoefficientLevelMap k A f n
        (algebraNormalizationLevelMap k A M n (algebraBoundary k A M n x)) :=
    (LinearMap.comp_apply (algebraNormalizationLevelMap k A N n) (algebraCoefficientLevelMap k A f n)
      (algebraBoundary k A M n x)).symm.trans
      ((DFunLike.congr_fun (algebraNormalizationLevelMap_coefficient k A f n)
          (algebraBoundary k A M n x)).trans
        (LinearMap.comp_apply (algebraNormalizedCoefficientLevelMap k A f n)
          (algebraNormalizationLevelMap k A M n) (algebraBoundary k A M n x)))
  calc
    _ = algebraNormalizedBoundary k A N n
        (algebraNormalizationLevelMap k A N (n + 1) (algebraCoefficientLevelMap k A f (n + 1) x)) :=
      congrArg (algebraNormalizedBoundary k A N n) hc₁.symm
    _ = algebraNormalizationLevelMap k A N n
        (algebraBoundary k A N n (algebraCoefficientLevelMap k A f (n + 1) x)) :=
      hN (algebraCoefficientLevelMap k A f (n + 1) x)
    _ = algebraNormalizationLevelMap k A N n
        (algebraCoefficientLevelMap k A f n (algebraBoundary k A M n x)) :=
      congrArg (algebraNormalizationLevelMap k A N n) hb
    _ = algebraNormalizedCoefficientLevelMap k A f n
        (algebraNormalizationLevelMap k A M n (algebraBoundary k A M n x)) := hc₀
    _ = _ := congrArg (algebraNormalizedCoefficientLevelMap k A f n) (hM x).symm

/-- The A-linear chain map of normalized Hochschild coefficients.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, this
chain map acts through f on M and fixes each normalized tail factor. -/
def algebraNormalizedCoefficientMap (f : M →ₗ[A] N) :
    algebraNormalizedChainComplex k A M ⟶ algebraNormalizedChainComplex k A N :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraNormalizedCoefficientLevelMap k A f n)) (by
    intro n
    apply ModuleCat.hom_ext
    dsimp only [algebraNormalizedChainComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    exact algebraNormalizedCoefficientLevelMap_boundary k A f n)

/-- The component of the normalized algebra-linear coefficient chain map.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, its
nth component is algebraNormalizedCoefficientLevelMap(f,n). -/
theorem algebraNormalizedCoefficientMap_f (f : M →ₗ[A] N) (n : ℕ) :
    ((algebraNormalizedCoefficientMap k A f).f n).hom =
      algebraNormalizedCoefficientLevelMap k A f n := rfl

/-- The raw-to-normalized coefficient chain square.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, raw f
followed by normalization equals source normalization followed by normalized f. -/
@[reassoc]
theorem algebraNormalizationProjection_coefficient (f : M →ₗ[A] N) :
    algebraRawCoefficientMap k A f ≫ algebraNormalizationProjection k A N =
      algebraNormalizationProjection k A M ≫ algebraNormalizedCoefficientMap k A f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
    algebraRawCoefficientMap_f, algebraNormalizedCoefficientMap_f]
  change (algebraNormalizationLevelMap k A N n).comp (algebraCoefficientLevelMap k A f n) =
    (algebraNormalizedCoefficientLevelMap k A f n).comp (algebraNormalizationLevelMap k A M n)
  exact algebraNormalizationLevelMap_coefficient k A f n

private theorem coefficientLevelMap_pairing (f : M →ₗ[A] N) (p q : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  ((algebraCoefficientLevelMap k A f (p + q)).restrictScalars k).comp
      ((pairing.{u, v, w} k A M).pair p q).hom =
    ((pairing.{u, v, w} k A N).pair p q).hom.comp
      (TensorProduct.map LinearMap.id ((algebraCoefficientLevelMap k A f q).restrictScalars k)) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  let pM : ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (M ⊗[k] TensorPower k q A)) →ₗ[k]
      M ⊗[k] TensorPower k (p + q) A := ((pairing.{u, v, w} k A M).pair p q).hom
  let pN : ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (N ⊗[k] TensorPower k q A)) →ₗ[k]
      N ⊗[k] TensorPower k (p + q) A := ((pairing.{u, v, w} k A N).pair p q).hom
  let c := (algebraCoefficientLevelMap k A f (p + q)).restrictScalars k
  let t : ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (M ⊗[k] TensorPower k q A)) →ₗ[k]
      ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (N ⊗[k] TensorPower k q A)) :=
    TensorProduct.map LinearMap.id ((algebraCoefficientLevelMap k A f q).restrictScalars k)
  change c.comp pM = pN.comp t
  apply TensorProduct.curry_injective
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro a0 a
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m b
  change c
      (pM
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k b))) =
    pN (t ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k b)))
  dsimp only [c, pM, pN, t]
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  change algebraCoefficientLevelMap k A f (p + q)
      (((pairing.{u, v, w} k A M).pair p q).hom
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k b))) =
    ((pairing.{u, v, w} k A N).pair p q).hom
      ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (f m ⊗ₜ[k] PiTensorProduct.tprod k b))
  rw [pairing_pair_tprod_as_tmul, algebraCoefficientLevelMap_tmul,
    pairing_pair_tprod_as_tmul, f.map_smul]

/-- The A-linear raw coefficient map preserves proper-shuffle images.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, the
degree-n both-positive relation module for M maps into that for N. -/
theorem algebraCoefficientLevelMap_positiveRelations (f : M →ₗ[A] N) (n : ℕ) :
    algebraPositiveRelations k A M n ≤
      (algebraPositiveRelations k A N n).comap (algebraCoefficientLevelMap k A f n) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  have hle : rawPositiveRelations k A M n ≤
      (rawPositiveRelations k A N n).comap ((algebraCoefficientLevelMap k A f n).restrictScalars k) := by
    change HomologicalComplex.ChainGradedPairing.positiveImages (pairing.{u, v, w} k A M) n ≤ _
    apply iSup_le
    rintro ⟨⟨p, q⟩, hp, hq, hpn⟩
    subst n
    intro z hz
    obtain ⟨y, rfl⟩ := hz
    have hy := HomologicalComplex.ChainGradedPairing.pairAt_mem_positiveImages
      (pairing.{u, v, w} k A N) p q (p + q) rfl hp hq
      (TensorProduct.map LinearMap.id ((algebraCoefficientLevelMap k A f q).restrictScalars k) y)
    let pM : ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (M ⊗[k] TensorPower k q A)) →ₗ[k]
        M ⊗[k] TensorPower k (p + q) A := ((pairing.{u, v, w} k A M).pair p q).hom
    let pN : ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (N ⊗[k] TensorPower k q A)) →ₗ[k]
        N ⊗[k] TensorPower k (p + q) A := ((pairing.{u, v, w} k A N).pair p q).hom
    let c := (algebraCoefficientLevelMap k A f (p + q)).restrictScalars k
    let t : ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (M ⊗[k] TensorPower k q A)) →ₗ[k]
        ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (N ⊗[k] TensorPower k q A)) :=
      TensorProduct.map LinearMap.id ((algebraCoefficientLevelMap k A f q).restrictScalars k)
    have hmap : c.comp pM = pN.comp t := coefficientLevelMap_pairing k A f p q
    have he' : algebraCoefficientLevelMap k A f (p + q)
        (((pairing.{u, v, w} k A M).pair p q).hom y) =
        ((pairing.{u, v, w} k A N).pair p q).hom
          (TensorProduct.map LinearMap.id ((algebraCoefficientLevelMap k A f q).restrictScalars k) y) := by
      change c (pM y) = pN (t y)
      exact congrArg (fun g : ((ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k]
        (M ⊗[k] TensorPower k q A)) →ₗ[k] N ⊗[k] TensorPower k (p + q) A => g y) hmap
    change algebraCoefficientLevelMap k A f (p + q)
      (((pairing.{u, v, w} k A M).pair p q).hom y) ∈ rawPositiveRelations k A N (p + q)
    rw [he']
    exact hy
  exact fun x hx => hle hx

/-- The normalized coefficient map preserves both-positive shuffle relations.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N,
normalized proper-shuffle images for M map into those for N in every degree. -/
theorem algebraNormalizedCoefficientLevelMap_positiveRelations (f : M →ₗ[A] N) (n : ℕ) :
    algebraNormalizedPositiveRelations k A M n ≤
      (algebraNormalizedPositiveRelations k A N n).comap (algebraNormalizedCoefficientLevelMap k A f n) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  apply Submodule.mem_map.mpr
  refine ⟨algebraCoefficientLevelMap k A f n x,
    algebraCoefficientLevelMap_positiveRelations k A f n hx, ?_⟩
  exact DFunLike.congr_fun (algebraNormalizationLevelMap_coefficient k A f n) x

/-- The coefficient chain map of the raw proper-shuffle quotient.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N,
descend the raw coefficient map through the both-positive relation modules. -/
def algebraPositiveCoefficientMap (f : M →ₗ[A] N) :
    algebraPositiveQuotientComplex k A M ⟶ algebraPositiveQuotientComplex k A N :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((algebraPositiveRelations k A M n).mapQ (algebraPositiveRelations k A N n)
      (algebraCoefficientLevelMap k A f n) (algebraCoefficientLevelMap_positiveRelations k A f n))) (by
        intro n
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        dsimp only [algebraPositiveQuotientComplex]
        rw [ChainComplex.of_d, ChainComplex.of_d]
        refine Quotient.inductionOn' y ?_
        intro x
        change (algebraPositiveRelations k A N n).mkQ
            (algebraBoundary k A N n (algebraCoefficientLevelMap k A f (n + 1) x)) =
          (algebraPositiveRelations k A N n).mkQ
            (algebraCoefficientLevelMap k A f n (algebraBoundary k A M n x))
        apply congrArg (algebraPositiveRelations k A N n).mkQ
        exact DFunLike.congr_fun (algebraCoefficientLevelMap_boundary k A f n) x)

/-- The raw proper-shuffle quotient coefficient map on a representative.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, the
class [x] in degree n maps to [algebraCoefficientLevelMap(f,n)(x)]. -/
theorem algebraPositiveCoefficientMap_f_mkQ (f : M →ₗ[A] N) (n : ℕ)
    (x : M ⊗[k] TensorPower k n A) :
    ((algebraPositiveCoefficientMap k A f).f n).hom ((algebraPositiveRelations k A M n).mkQ x) =
      (algebraPositiveRelations k A N n).mkQ (algebraCoefficientLevelMap k A f n x) := rfl

/-- Identity coefficients give the identity raw proper quotient chain map.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
algebraPositiveCoefficientMap(id_M) is the identity on its raw proper-shuffle quotient
complex. -/
theorem algebraPositiveCoefficientMap_id :
    algebraPositiveCoefficientMap k A (LinearMap.id : M →ₗ[A] M) =
      𝟙 (algebraPositiveQuotientComplex k A M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  refine Quotient.inductionOn' y ?_
  intro x
  change (algebraPositiveRelations k A M n).mkQ
      (algebraCoefficientLevelMap k A (LinearMap.id : M →ₗ[A] M) n x) =
    (algebraPositiveRelations k A M n).mkQ x
  rw [algebraCoefficientLevelMap_id]
  rfl

variable {L : Type w} [AddCommGroup L] [Module k L] [Module A L]
  [SMulCommClass k A L] [IsScalarTower k A L]

/-- Composition of coefficient arrows on raw proper-shuffle quotients.

For a commutative ring k, a commutative k-algebra A and compatible A-linear maps f : M → N and
g : N → L, the quotient chain maps compose to the map of g ∘ f. -/
@[reassoc]
theorem algebraPositiveCoefficientMap_comp (f : M →ₗ[A] N) (g : N →ₗ[A] L) :
    algebraPositiveCoefficientMap k A f ≫ algebraPositiveCoefficientMap k A g =
      algebraPositiveCoefficientMap k A (g.comp f) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  refine Quotient.inductionOn' y ?_
  intro x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  change (algebraPositiveRelations k A L n).mkQ
      (algebraCoefficientLevelMap k A g n (algebraCoefficientLevelMap k A f n x)) =
    (algebraPositiveRelations k A L n).mkQ (algebraCoefficientLevelMap k A (g.comp f) n x)
  apply congrArg (algebraPositiveRelations k A L n).mkQ
  have h := (TensorProduct.AlgebraTensorModule.map_comp g f
    (LinearMap.id : TensorPower k n A →ₗ[k] TensorPower k n A) LinearMap.id).symm
  simpa only [LinearMap.id_comp, LinearMap.comp_apply, algebraCoefficientLevelMap] using
    DFunLike.congr_fun h x

/-- The coefficient map of the normalized proper-shuffle quotient complex.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, its
normalized tensor maps descend through the normalized both-positive shuffle relations. -/
def algebraNormalizedPositiveCoefficientMap (f : M →ₗ[A] N) :
    algebraNormalizedPositiveQuotientComplex k A M ⟶ algebraNormalizedPositiveQuotientComplex k A N :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((algebraNormalizedPositiveRelations k A M n).mapQ (algebraNormalizedPositiveRelations k A N n)
      (algebraNormalizedCoefficientLevelMap k A f n)
      (algebraNormalizedCoefficientLevelMap_positiveRelations k A f n))) (by
        intro n
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        dsimp only [algebraNormalizedPositiveQuotientComplex]
        rw [ChainComplex.of_d, ChainComplex.of_d]
        refine Quotient.inductionOn' y ?_
        intro x
        change (algebraNormalizedPositiveRelations k A N n).mkQ
            (algebraNormalizedBoundary k A N n (algebraNormalizedCoefficientLevelMap k A f (n + 1) x)) =
          (algebraNormalizedPositiveRelations k A N n).mkQ
            (algebraNormalizedCoefficientLevelMap k A f n (algebraNormalizedBoundary k A M n x))
        apply congrArg (algebraNormalizedPositiveRelations k A N n).mkQ
        exact DFunLike.congr_fun (algebraNormalizedCoefficientLevelMap_boundary k A f n) x)

/-- The normalized proper-shuffle coefficient map on a quotient representative.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, [x]
maps to [algebraNormalizedCoefficientLevelMap(f,n)(x)] in degree n. -/
theorem algebraNormalizedPositiveCoefficientMap_f_mkQ (f : M →ₗ[A] N) (n : ℕ)
    (x : M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) :
    ((algebraNormalizedPositiveCoefficientMap k A f).f n).hom
        ((algebraNormalizedPositiveRelations k A M n).mkQ x) =
      (algebraNormalizedPositiveRelations k A N n).mkQ (algebraNormalizedCoefficientLevelMap k A f n x) := rfl

/-- Normalization intertwines the raw and normalized proper coefficient maps.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, its
raw proper quotient map followed by proper normalization equals proper normalization followed
by its normalized quotient map. -/
@[reassoc]
theorem algebraPositiveNormalization_coefficient (f : M →ₗ[A] N) :
    algebraPositiveCoefficientMap k A f ≫ algebraPositiveNormalization k A N =
      algebraPositiveNormalization k A M ≫ algebraNormalizedPositiveCoefficientMap k A f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  refine Quotient.inductionOn' y ?_
  intro x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  change (algebraNormalizedPositiveRelations k A N n).mkQ
      (algebraNormalizationLevelMap k A N n (algebraCoefficientLevelMap k A f n x)) =
    (algebraNormalizedPositiveRelations k A N n).mkQ
      (algebraNormalizedCoefficientLevelMap k A f n (algebraNormalizationLevelMap k A M n x))
  apply congrArg (algebraNormalizedPositiveRelations k A N n).mkQ
  exact DFunLike.congr_fun (algebraNormalizationLevelMap_coefficient k A f n) x

end ModuleCat.Algebra.Hochschild.Symmetric
