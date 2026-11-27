/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleCotangentQuasiIsoDegreeZero
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianPositiveKernel
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricShuffleCutOperator
public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormAlgebraNaturality
public import MathlibExt.LinearAlgebra.TensorPower.PermutationActionNaturality

/-!
# Naturality of the proper-shuffle cotangent augmentation

Let k be a commutative ring. Compatible algebra and coefficient maps preserve both-positive
shuffle relations and induce maps of the positive quotient and its degree-shifted cotangent
complex. These maps commute with the augmentation to coefficient Kähler differentials. The
relation inclusion itself is natural even for arbitrary ground-linear maps of the algebra and
coefficient modules.

The quotient maps are induced by the integral positive-image construction. Naturality of the
zero-plus-first Eulerian projector is proved separately over a ℚ-algebra.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct BigOperators

universe u v v' v'' w w' w''

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle

open ModuleCat.Algebra.Hochschild
open ModuleCat.Algebra.Hochschild.Symmetric

section IndependentWorlds

variable (k : Type u) [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A]
  {B : Type v'} [CommRing B] [Algebra k B]
  {C : Type v''} [CommRing C] [Algebra k C]
  {M : Type w} [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]
  {N : Type w'} [AddCommGroup N] [Module k N] [Module B N]
  [SMulCommClass k B N] [IsScalarTower k B N]
  {P : Type w''} [AddCommGroup P] [Module k P] [Module C P]
  [SMulCommClass k C P] [IsScalarTower k C P]

omit [Module A M] [SMulCommClass k A M] [IsScalarTower k A M]
  [Module B N] [SMulCommClass k B N] [IsScalarTower k B N] in
/-- Let k be a commutative ℚ-algebra, A and B commutative k-algebras, M,N k-modules, g : A → B a
k-algebra map and f : M → N k-linear. For n ∈ ℕ, put T_n=f⊗g^{⊗n} and E_n=e_n^(0)+e_n^(1),
acting on coefficient tensors. Then T_n ∘ E_A,M,n = E_B,N,n ∘ T_n. No compatibility with
coefficient algebra actions is needed for this projector equation. -/
theorem firstOperator_naturality [Algebra ℚ k] (g : A →ₐ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    (linearMap g.toNonUnitalAlgHom f n).comp (firstEulerianOperator k A M n) =
      (firstEulerianOperator k B N n).comp (linearMap g.toNonUnitalAlgHom f n) := by
  have h (i : ℕ) : (linearMap g.toNonUnitalAlgHom f n).comp (coefficientEulerianOperator k A M n i) =
      (coefficientEulerianOperator k B N n i).comp (linearMap g.toNonUnitalAlgHom f n) :=
    TensorPower.coefficientRationalPermutationAction_naturality n
      (Equiv.Perm.eulerianElement n i) g.toLinearMap f
  simp only [firstEulerianOperator, LinearMap.comp_add, LinearMap.add_comp, h]


private theorem shuffleCutEnd_linear_naturality (g : A →ₗ[k] B) {n : ℕ}
    (z : TensorPower.ShuffleDegreeCut n) :
    (PiTensorProduct.map (fun _ : Fin n => g)).comp
        (TensorPower.shuffleCutEnd (k := k) (V := A) z) =
      (TensorPower.shuffleCutEnd (k := k) (V := B) z).comp
        (PiTensorProduct.map (fun _ : Fin n => g)) := by
  rcases z with ⟨⟨p, q⟩, h⟩
  subst n
  rw [TensorPower.shuffleCutEnd_eq_cast, TensorPower.shuffleCutEnd_eq_cast]
  change (PiTensorProduct.map (fun _ : Fin (p + q) => g)).comp
      (TensorPower.signedShuffleEnd (k := k) (V := A) p q) =
    (TensorPower.signedShuffleEnd (k := k) (V := B) p q).comp
      (PiTensorProduct.map (fun _ : Fin (p + q) => g))
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, TensorPower.signedShuffleEnd, LinearMap.sum_apply,
    ← Int.cast_smul_eq_zsmul k, LinearMap.smul_apply, map_sum, map_smul,
    LinearEquiv.coe_toLinearMap, PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod]

private theorem coefficientShuffleCutEnd_linear_naturality (g : A →ₗ[k] B)
    (f : M →ₗ[k] N) {n : ℕ} (z : TensorPower.ShuffleDegreeCut n) :
    (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))).comp
        (coefficientShuffleCutEnd k A M z) =
      (coefficientShuffleCutEnd k B N z).comp
        (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))) := by
  rw [coefficientShuffleCutEnd_eq_map, coefficientShuffleCutEnd_eq_map]
  apply TensorProduct.ext
  intro m t
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  exact congrArg (fun y => f m ⊗ₜ[k] y)
    (DFunLike.congr_fun (shuffleCutEnd_linear_naturality k g z) t)

private theorem coefficientShuffleCutEnd_mem_relations {n : ℕ}
    (z : TensorPower.ProperShuffleDegreeCut n) (x : M ⊗[k] TensorPower k n A) :
    coefficientShuffleCutEnd k A M z.val x ∈ rawPositiveRelations k A M n := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  change (HomologicalComplex.ChainGradedPairing.pairAt
    (pairing k A M) z.val.val.1 z.val.val.2 n z.val.property).hom
      (coefficientShuffleCutInput k A M z.val x) ∈
        HomologicalComplex.ChainGradedPairing.positiveImages (pairing k A M) n
  exact HomologicalComplex.ChainGradedPairing.pairAt_mem_positiveImages
    (pairing k A M) z.val.val.1 z.val.val.2 n z.val.property
    z.property.1 z.property.2 _

private theorem signedShuffle_map_relation_zero (g : A →ₗ[k] B)
    (f : M →ₗ[k] N) (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    ((rawPositiveRelations k B N (p + q)).mkQ.comp
      (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin (p + q) => g)))).comp
        (signedRawShuffle k A M p q) = 0 := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  rw [← pairing_pair_signedRawShuffle k A M p q]
  apply TensorProduct.curry_injective
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro a₀
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro m
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro b
  let x := (a₀.down • m) ⊗ₜ[k]
    TensorPower.mulEquiv (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)
  let η := TensorProduct.map f (PiTensorProduct.map (fun _ : Fin (p + q) => g))
  change (rawPositiveRelations k B N (p + q)).mkQ
      (η (((pairing k A M).pair p q).hom
        ((a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b)))) = 0
  have hP := pairing_pair_tprod_as_tmul k A M p q a₀ m a b
  have hProduct := TensorPower.signedShuffleProduct_tprod (k := k) (V := A) p q a b
  have hCut := coefficientShuffleCutEnd_concat_tprod k A M p q (a₀.down • m) a b
  have hValue :
      ((pairing k A M).pair p q).hom
        ((a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
        coefficientShuffleCutEnd k A M ⟨(p, q), rfl⟩ x :=
    hP.trans ((congrArg (fun y => (a₀.down • m) ⊗ₜ[k] y) hProduct).symm.trans hCut.symm)
  rw [hValue]
  have hNatural := DFunLike.congr_fun
    (coefficientShuffleCutEnd_linear_naturality k g f ⟨(p, q), rfl⟩) x
  change η (coefficientShuffleCutEnd k A M ⟨(p, q), rfl⟩ x) =
    coefficientShuffleCutEnd k B N ⟨(p, q), rfl⟩ (η x) at hNatural
  rw [hNatural]
  exact (Submodule.Quotient.mk_eq_zero (p := rawPositiveRelations k B N (p + q))).mpr
    (coefficientShuffleCutEnd_mem_relations k (A := B) (M := N)
      ⟨⟨(p, q), rfl⟩, hp, hq⟩ (η x))


private theorem signedRawShuffle_tprod_eq_cut (p q : ℕ) (a₀ : ULift.{w} A) (m : M)
    (a : Fin p → A) (b : Fin q → A) :
    signedRawShuffle k A M p q
        ((a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
      coefficientShuffleCutEnd k A M ⟨(p, q), rfl⟩
        ((a₀.down • m) ⊗ₜ[k]
          TensorPower.mulEquiv (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  rw [← pairing_pair_signedRawShuffle k A M p q]
  have hP := pairing_pair_tprod_as_tmul k A M p q a₀ m a b
  have hProduct := TensorPower.signedShuffleProduct_tprod (k := k) (V := A) p q a b
  have hCut := coefficientShuffleCutEnd_concat_tprod k A M p q (a₀.down • m) a b
  exact hP.trans
    ((congrArg (fun y => (a₀.down • m) ⊗ₜ[k] y) hProduct).symm.trans hCut.symm)

private theorem signedRawShuffle_compatible_naturality (g : A →ₐ[k] B)
    (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) (p q : ℕ) :
    (linearMap g.toNonUnitalAlgHom f (p + q)).comp (signedRawShuffle k A M p q) =
      (signedRawShuffle k B N p q).comp
        (TensorProduct.map
          (linearMap g.toNonUnitalAlgHom
            (regularCoefficientMap g.toNonUnitalAlgHom :
              ULift.{w} A →ₗ[k] ULift.{w'} B) p)
          (linearMap g.toNonUnitalAlgHom f q)) := by
  apply TensorProduct.curry_injective
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro a₀
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro m
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, linearMap_tprod]
  rw [signedRawShuffle_tprod_eq_cut, signedRawShuffle_tprod_eq_cut]
  let x := (a₀.down • m) ⊗ₜ[k]
    TensorPower.mulEquiv (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)
  have hNatural := DFunLike.congr_fun
    (coefficientShuffleCutEnd_linear_naturality k g.toLinearMap f ⟨(p, q), rfl⟩) x
  change linearMap g.toNonUnitalAlgHom f (p + q)
      (coefficientShuffleCutEnd k A M ⟨(p, q), rfl⟩ x) =
    coefficientShuffleCutEnd k B N ⟨(p, q), rfl⟩
      (linearMap g.toNonUnitalAlgHom f (p + q) x) at hNatural
  rw [hNatural]
  apply congrArg (coefficientShuffleCutEnd k B N ⟨(p, q), rfl⟩)
  have hTail :
      PiTensorProduct.map (fun _ : Fin (p + q) => g.toLinearMap)
          (TensorPower.mulEquiv (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) =
        TensorPower.mulEquiv
          (PiTensorProduct.tprod k (fun i => g (a i)) ⊗ₜ[k]
            PiTensorProduct.tprod k (fun i => g (b i))) := by
    simp only [TensorPower.tprod_mul_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext i
    exact Fin.addCases (fun j => by simp) (fun j => by simp) i
  change f (a₀.down • m) ⊗ₜ[k]
      PiTensorProduct.map (fun _ : Fin (p + q) => g.toLinearMap)
        (TensorPower.mulEquiv (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) =
    (g a₀.down • f m) ⊗ₜ[k]
      TensorPower.mulEquiv
        (PiTensorProduct.tprod k (fun i => g (a i)) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun i => g (b i)))
  rw [hf]
  exact congrArg (fun y => (g a₀.down • f m) ⊗ₜ[k] y) hTail


/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. For arbitrary k-linear g : A → B and
f : M → N and n ∈ ℕ, the map T_n=f⊗g^{⊗n} sends the proper shuffle submodule S_A,M,n into
S_B,N,n. Equivalently S_A,M,n ≤ T_n⁻¹(S_B,N,n). These submodules are generated by the signed
pairing components with both input degrees positive; f need not intertwine the A/B-actions. -/
theorem relations_map_linear (g : A →ₗ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    rawPositiveRelations k A M n ≤
      (rawPositiveRelations k B N n).comap
        (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g))) := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  change HomologicalComplex.ChainGradedPairing.positiveImages (pairing k A M) n ≤
    (rawPositiveRelations k B N n).comap
      (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g)))
  rw [HomologicalComplex.ChainGradedPairing.positiveImages]
  apply iSup_le
  rintro ⟨⟨p, q⟩, hp, hq, h⟩
  subst n
  rintro y ⟨x, rfl⟩
  change (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin (p + q) => g)))
    ((HomologicalComplex.ChainGradedPairing.pairAt (pairing k A M) p q (p + q) rfl).hom x) ∈
      rawPositiveRelations k B N (p + q)
  have hPair :
      (HomologicalComplex.ChainGradedPairing.pairAt (pairing k A M) p q (p + q) rfl).hom =
        signedRawShuffle k A M p q := by
    rw [HomologicalComplex.ChainGradedPairing.pairAt_rfl]
    exact pairing_pair_signedRawShuffle k A M p q
  rw [hPair]
  have hx := DFunLike.congr_fun (signedShuffle_map_relation_zero k g f p q hp hq) x
  exact (Submodule.Quotient.mk_eq_zero (p := rawPositiveRelations k B N (p + q))).mp hx

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. For a k-algebra map g : A → B and
any k-linear f : M → N, the degree-n map T_n=f⊗g^{⊗n} preserves the both-positive shuffle
relation submodules: S_A,M,n ≤ T_n⁻¹(S_B,N,n), for every n ∈ ℕ. -/
theorem relations_map (g : A →ₐ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    rawPositiveRelations k A M n ≤
      (rawPositiveRelations k B N n).comap (linearMap g.toNonUnitalAlgHom f n) := by
  change rawPositiveRelations k A M n ≤
    (rawPositiveRelations k B N n).comap
      (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => g.toLinearMap)))
  exact relations_map_linear k g.toLinearMap f n

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. For g : A → B a k-algebra map and f
: M → N k-linear, quotientLinearMap in degree n is the induced map (M⊗_kA^{⊗n})/S_A,M,n →
(N⊗_kB^{⊗n})/S_B,N,n. It sends [x] to [(f⊗g^{⊗n})(x)]. -/
def quotientLinearMap (g : A →ₐ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    ((M ⊗[k] TensorPower k n A) ⧸ rawPositiveRelations k A M n) →ₗ[k]
      ((N ⊗[k] TensorPower k n B) ⧸ rawPositiveRelations k B N n) :=
  (rawPositiveRelations k A M n).mapQ (rawPositiveRelations k B N n)
    (linearMap g.toNonUnitalAlgHom f n) (relations_map k g f n)

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map, f
: M → N k-linear, n ∈ ℕ and x ∈ M⊗_kA^{⊗n}. If q_n is quotientLinearMap, then q_n(π_A,M,n(x)) =
π_B,N,n((f⊗g^{⊗n})(x)), where π denotes the quotient projections. -/
theorem quotientLinearMap_mkQ (g : A →ₐ[k] B) (f : M →ₗ[k] N) (n : ℕ)
    (x : M ⊗[k] TensorPower k n A) :
    quotientLinearMap k g f n ((rawPositiveRelations k A M n).mkQ x) =
      (rawPositiveRelations k B N n).mkQ (linearMap g.toNonUnitalAlgHom f n x) := rfl

/-- Let k be a commutative ring, A a commutative k-algebra and M a left A-module with induced
k-action. In every degree n ∈ ℕ, quotientLinearMap for id_A and id_M is the identity of
(M⊗_kA^{⊗n})/S_A,M,n. -/
theorem quotientLinearMap_id (n : ℕ) :
    quotientLinearMap k (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n = LinearMap.id := by
  refine LinearMap.ext (fun z : (M ⊗[k] TensorPower k n A) ⧸ rawPositiveRelations k A M n => ?_)
  refine Quotient.inductionOn' z (fun x : M ⊗[k] TensorPower k n A => ?_)
  change quotientLinearMap k (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n
      ((rawPositiveRelations k A M n).mkQ x) = (rawPositiveRelations k A M n).mkQ x
  have h := LinearMap.congr_fun (linearMap_id (k := k) (A := A) (M := M) n) x
  exact (quotientLinearMap_mkQ k (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n x).trans
    (congrArg (rawPositiveRelations k A M n).mkQ h)

/-- Let k be commutative, A,B,C commutative k-algebras and M,N,P modules over the respective
algebras with induced k-actions. For algebra maps g : A → B, h : B → C and k-linear f : M → N,
f′ : N → P, the degree-n quotient maps satisfy q_n(h,f′) ∘ q_n(g,f) = q_n(hg,f′f). No
coefficient-action compatibility is required for this quotient-level formula. -/
theorem quotientLinearMap_comp (g : A →ₐ[k] B) (h : B →ₐ[k] C)
    (f : M →ₗ[k] N) (f' : N →ₗ[k] P) (n : ℕ) :
    (quotientLinearMap k h f' n).comp (quotientLinearMap k g f n) =
      quotientLinearMap k (h.comp g) (f'.comp f) n := by
  refine LinearMap.ext (fun z : (M ⊗[k] TensorPower k n A) ⧸ rawPositiveRelations k A M n => ?_)
  refine Quotient.inductionOn' z (fun x : M ⊗[k] TensorPower k n A => ?_)
  change quotientLinearMap k h f' n
      (quotientLinearMap k g f n ((rawPositiveRelations k A M n).mkQ x)) =
    quotientLinearMap k (h.comp g) (f'.comp f) n ((rawPositiveRelations k A M n).mkQ x)
  have h₁ := quotientLinearMap_mkQ k g f n x
  have h₂ := quotientLinearMap_mkQ k h f' n (linearMap g.toNonUnitalAlgHom f n x)
  have h₃ := quotientLinearMap_mkQ k (h.comp g) (f'.comp f) n x
  have hc := LinearMap.congr_fun (linearMap_comp g.toNonUnitalAlgHom h.toNonUnitalAlgHom f f' n) x
  exact (congrArg (quotientLinearMap k h f' n) h₁).trans
    (h₂.trans ((congrArg (rawPositiveRelations k C P n).mkQ hc).trans h₃.symm))

/-- Let k be commutative, A a commutative k-algebra and M a left A-module with induced k-action,
given the symmetric right action ma=am. For n ∈ ℕ and x ∈ M⊗_kA^{⊗(n+1)}, the ground-linear
Hochschild boundary has value b_k,n(x)=algebraBoundary_n(x), the value of the A-linear boundary
on the same tensor. -/
theorem originalBoundary_value (n : ℕ) (x : M ⊗[k] TensorPower k (n + 1) A) :
    letI := opModule A M
    letI := actionsComm A M
    letI := kOpComm k A M
    letI := kOpTower k A M
    (ModuleCat.Algebra.Hochschild.boundary k A M n).hom x = algebraBoundary k A M n x := by
  let _ := opModule A M
  let _ := actionsComm A M
  let _ := kOpComm k A M
  let _ := kOpTower k A M
  have h := congrArg ModuleCat.Hom.hom (ModuleCat.Algebra.Hochschild.chainComplex_d k A M n)
  exact (LinearMap.congr_fun h x).symm

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map and
f : M → N a k-linear map satisfying f(a·m)=g(a)·f(m). For n ∈ ℕ and x ∈ M⊗_kA^{⊗(n+1)},
b_B,N,n(T_{n+1}(x)) = T_n(b_A,M,n(x)), where T_j=f⊗g^{⊗j} and b is the algebra-linear Hochschild
boundary. -/
theorem originalBoundary_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) (x : M ⊗[k] TensorPower k (n + 1) A) :
    algebraBoundary k B N n (linearMap g.toNonUnitalAlgHom f (n + 1) x) =
      linearMap g.toNonUnitalAlgHom f n (algebraBoundary k A M n x) := by
  let _ := opModule A M
  let _ := actionsComm A M
  let _ := kOpComm k A M
  let _ := kOpTower k A M
  let _ := opModule B N
  let _ := actionsComm B N
  let _ := kOpComm k B N
  let _ := kOpTower k B N
  have h := LinearMap.congr_fun (linearMap_boundary_comm g.toNonUnitalAlgHom f hf
    (by intro a m; exact hf a m) n) x
  change (ModuleCat.Algebra.Hochschild.boundary k B N n).hom (linearMap g.toNonUnitalAlgHom f (n + 1) x) =
    linearMap g.toNonUnitalAlgHom f n ((ModuleCat.Algebra.Hochschild.boundary k A M n).hom x) at h
  exact ((originalBoundary_value k n (linearMap g.toNonUnitalAlgHom f (n + 1) x)).symm.trans h).trans
    (congrArg (linearMap g.toNonUnitalAlgHom f n) (originalBoundary_value k n x))

end IndependentWorlds

section Complexes

variable (k : Type u) [CommRing k]
  {A B : Type v} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {M N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [SMulCommClass k A M] [SMulCommClass k B N]
  [IsScalarTower k A M] [IsScalarTower k B N]

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map and
f : M → N a k-linear map satisfying f(a·m)=g(a)·f(m). The induced chain map Q(g,f) :
positiveQuotient(A,M) → positiveQuotient(B,N) has degree-n component the proper-shuffle quotient
map induced by T_n=f⊗g^{⊗n}. It is obtained from the integral positive-image quotient map of the
signed chain pairings. -/
def chainMap (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) :
    positiveQuotient k A M ⟶ positiveQuotient k B N :=
by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  let r : ULift.{w} A →ₗ[k] ULift.{w} B := regularCoefficientMap g.toNonUnitalAlgHom
  have hr : ∀ a m, r (a • m) = g a • r m := by
    intro a m
    apply ULift.ext
    change g (a * m.down) = g a * g m.down
    exact g.map_mul a m.down
  let F₁ := originalAlgebraCoefficientChainMap k g r hr
  let F₂ := originalAlgebraCoefficientChainMap k g f hf
  have hPair : HomologicalComplex.tensorHom F₁ F₂ ≫ pairing k B N = pairing k A M ≫ F₂ := by
    apply HomologicalComplex.hom_ext
    intro n
    change (HomologicalComplex.tensorHom F₁ F₂).f n ≫ (pairing k B N).f n =
      (pairing k A M).f n ≫ F₂.f n
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := chainComplex k A (ULift.{w} A)) (K₂ := chainComplex k A M)
      (F := curriedTensor (ModuleCat.{max u v w} k)) (c := ComplexShape.down ℕ)
    intro p q h
    rw [← Category.assoc, HomologicalComplex.ιTensorObj_tensorHom, Category.assoc]
    change (F₁.f p ⊗ₘ F₂.f q) ≫
        HomologicalComplex.ChainGradedPairing.pairAt (pairing k B N) p q n h =
      HomologicalComplex.ChainGradedPairing.pairAt (pairing k A M) p q n h ≫ F₂.f n
    subst n
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, HomologicalComplex.ChainGradedPairing.pairAt_rfl]
    change ((pairing k B N).pair p q).hom.comp
        (TensorProduct.map (F₁.f p).hom (F₂.f q).hom) =
      (F₂.f (p + q)).hom.comp ((pairing k A M).pair p q).hom
    rw [show (F₁.f p).hom = linearMap g.toNonUnitalAlgHom r p from
      originalAlgebraCoefficientChainMap_f k g r hr p,
      show (F₂.f q).hom = linearMap g.toNonUnitalAlgHom f q from
        originalAlgebraCoefficientChainMap_f k g f hf q,
      show (F₂.f (p + q)).hom = linearMap g.toNonUnitalAlgHom f (p + q) from
        originalAlgebraCoefficientChainMap_f k g f hf (p + q),
      pairing_pair_signedRawShuffle, pairing_pair_signedRawShuffle]
    exact (signedRawShuffle_compatible_naturality k g f hf p q).symm
  exact HomologicalComplex.ChainGradedPairing.positiveImageQuotientMap
    (pairing k A M) (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M)
    (pairing k B N) (boundary_one_zero k B (ULift.{w} B)) (boundary_one_zero k B N)
    F₁ F₂ F₂ hPair


private theorem chainMap_projectionProof (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    properShuffleProjection k A M ≫ chainMap k g f hf =
      originalAlgebraCoefficientChainMap k g f hf ≫ properShuffleProjection k B N := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map and
f : M → N a k-linear map satisfying f(a·m)=g(a)·f(m). For n ∈ ℕ, the degree-n component of
chainMap(g,f) is quotientLinearMap(g,f,n), the map [x] ↦ [(f⊗g^{⊗n})(x)] on proper-shuffle
tensor quotients. -/
theorem chainMap_f (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    ((chainMap k g f hf).f n).hom = quotientLinearMap k g f n := by
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z (fun x => ?_)
  change ((chainMap k g f hf).f n).hom ((rawPositiveRelations k A M n).mkQ x) =
    (rawPositiveRelations k B N n).mkQ (linearMap g.toNonUnitalAlgHom f n x)
  have h := congrArg
    (fun t : chainComplex k A M ⟶ positiveQuotient k B N => t.f n)
    (chainMap_projectionProof k g f hf)
  have hx := ConcreteCategory.congr_hom h x
  change ((chainMap k g f hf).f n).hom ((rawPositiveRelations k A M n).mkQ x) =
    (rawPositiveRelations k B N n).mkQ
      (((originalAlgebraCoefficientChainMap k g f hf).f n).hom x) at hx
  rw [originalAlgebraCoefficientChainMap_f] at hx
  exact hx

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map and
f : M → N a k-linear map satisfying f(a·m)=g(a)·f(m). Let π_A,M and π_B,N be the projections
from the symmetric Hochschild complexes to their proper-shuffle quotients, and T(g,f) the raw
coefficient chain map. Then π_A,M ≫ chainMap(g,f) = T(g,f) ≫ π_B,N. -/
@[reassoc]
theorem chainMap_projection (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) :
    properShuffleProjection k A M ≫ chainMap k g f hf =
      originalAlgebraCoefficientChainMap k g f hf ≫ properShuffleProjection k B N := by
  exact chainMap_projectionProof k g f hf

/-- Let k be commutative, A a commutative k-algebra and M an A-module with induced k-action. The
chain map on positiveQuotient(A,M) induced by id_A and id_M is the identity. -/
theorem chainMap_id :
    chainMap k (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) (by intro a m; rfl) =
      𝟙 (positiveQuotient k A M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change quotientLinearMap k (AlgHom.id k A) (LinearMap.id : M →ₗ[k] M) n = LinearMap.id
  exact quotientLinearMap_id k n

/-- Let k be commutative, A,B,C commutative k-algebras and M,N,P modules over them with induced
k-actions. Given algebra maps g,h and compatible k-linear coefficient maps f,f′, the quotient
chain maps satisfy chainMap(g,f) ≫ chainMap(h,f′) = chainMap(hg,f′f). Compatibility means
f(a·m)=g(a)·f(m) and f′(b·n)=h(b)·f′(n). -/
@[reassoc]
theorem chainMap_comp {C : Type v} [CommRing C] [Algebra k C]
    {P : Type w} [AddCommGroup P] [Module k P] [Module C P]
    [SMulCommClass k C P] [IsScalarTower k C P]
    (g : A →ₐ[k] B) (h : B →ₐ[k] C) (f : M →ₗ[k] N) (f' : N →ₗ[k] P)
    (hf : ∀ a m, f (a • m) = g a • f m) (hf' : ∀ b n, f' (b • n) = h b • f' n) :
    chainMap k g f hf ≫ chainMap k h f' hf' =
      chainMap k (h.comp g) (f'.comp f) (by
        intro a m
        change f' (f (a • m)) = h (g a) • f' (f m)
        rw [hf, hf']) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (quotientLinearMap k h f' n).comp (quotientLinearMap k g f n) =
    quotientLinearMap k (h.comp g) (f'.comp f) n
  exact quotientLinearMap_comp k g h f f' n

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map and
f : M → N a k-linear map satisfying f(a·m)=g(a)·f(m). The map cotangentChainMap(g,f) is the
restriction of chainMap(g,f) along n ↦ n+1. It maps properCotangentComplex(A,M) to
properCotangentComplex(B,N), whose degree-n terms are the proper quotient terms in degree n+1. -/
def cotangentChainMap (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) :
    properCotangentComplex k A M ⟶ properCotangentComplex k B N :=
  HomologicalComplex.restrictionMap (chainMap k g f hf) ComplexShape.positiveNatEmbedding

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map and
f : M → N a k-linear map satisfying f(a·m)=g(a)·f(m). For n ∈ ℕ, the degree-n component of
cotangentChainMap(g,f) is quotientLinearMap(g,f,n+1). Thus its tensor representatives are mapped
by f⊗g^{⊗(n+1)}. -/
theorem cotangentChainMap_f (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    ((cotangentChainMap k g f hf).f n).hom = quotientLinearMap k g f (n + 1) := rfl

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map and
f : M → N a k-linear map satisfying f(a·m)=g(a)·f(m). The cotangentModuleMap is the
ground-linear map M⊗_AΩ_{A/k} → N⊗_BΩ_{B/k}, through the canonical one-form identifications. It
sends m⊗da to f(m)⊗d(g(a)). -/
def cotangentModuleMap (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) :
    coefficientCotangentModule k A M ⟶ coefficientCotangentModule k B N :=
  (cotangentFormOneIso k A M).inv ≫ (coefficientFormAlgebraComplexMap k g f hf).f 1 ≫
    (cotangentFormOneIso k B N).hom

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map and
f : M → N a k-linear map satisfying f(a·m)=g(a)·f(m). Let D_A and D_B map the degree-one proper
quotients to their coefficient one-form modules, and F¹(g,f) the one-form map. Then
chainMap(g,f)₁ ≫ D_B = D_A ≫ F¹(g,f). -/
@[reassoc]
theorem degreeMap_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N) (hf : ∀ a m, f (a • m) = g a • f m) :
    (chainMap k g f hf).f 1 ≫ properCotangentDegreeMap k B N =
      properCotangentDegreeMap k A M ≫
        (coefficientFormAlgebraComplexMap k g f hf).f 1 := by
  apply ModuleCat.hom_ext
  let D₁ := (properCotangentDegreeMap k B N).hom
  let D₀ := (properCotangentDegreeMap k A M).hom
  let F₁ := ((coefficientFormAlgebraComplexMap k g f hf).f 1).hom
  change D₁.comp (quotientLinearMap k g f 1) = F₁.comp D₀
  refine LinearMap.ext (fun z : (M ⊗[k] TensorPower k 1 A) ⧸ rawPositiveRelations k A M 1 => ?_)
  refine Quotient.inductionOn' z (fun x : M ⊗[k] TensorPower k 1 A => ?_)
  have hq := quotientLinearMap_mkQ k g f 1 x
  have h := congrArg
    (fun t : chainComplex k A M ⟶ coefficientDifferentialFormComplex k B N => (t.f 1).hom)
    (coefficientDifferentialFormChainMap_algebra k g f hf)
  let T₁ := ((coefficientDifferentialFormChainMap k B N).f 1).hom
  have hΓ := LinearMap.congr_fun (originalAlgebraCoefficientChainMap_f k g f hf 1) x
  have hv : T₁ (linearMap g.toNonUnitalAlgHom f 1 x) =
      F₁ (((coefficientDifferentialFormChainMap k A M).f 1).hom x) :=
    (congrArg T₁ hΓ.symm).trans (LinearMap.congr_fun h x)
  exact (congrArg D₁ hq).trans hv

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map and
f : M → N a k-linear map satisfying f(a·m)=g(a)·f(m). Let a_A and a_B be the scalar
augmentations from the degree-one proper quotients to M⊗_AΩ_{A/k} and N⊗_BΩ_{B/k}. Then
chainMap(g,f)₁ ≫ a_B = a_A ≫ cotangentModuleMap(g,f). -/
@[reassoc]
theorem scalarAugmentation_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    (chainMap k g f hf).f 1 ≫ properCotangentScalarAugmentation k B N =
      properCotangentScalarAugmentation k A M ≫ cotangentModuleMap k g f hf := by
  change (chainMap k g f hf).f 1 ≫ (properCotangentDegreeMap k B N ≫ (cotangentFormOneIso k B N).hom) =
    (properCotangentDegreeMap k A M ≫ (cotangentFormOneIso k A M).hom) ≫
      ((cotangentFormOneIso k A M).inv ≫ (coefficientFormAlgebraComplexMap k g f hf).f 1 ≫
        (cotangentFormOneIso k B N).hom)
  calc
    _ = ((chainMap k g f hf).f 1 ≫ properCotangentDegreeMap k B N) ≫ (cotangentFormOneIso k B N).hom :=
      (Category.assoc _ _ _).symm
    _ = (properCotangentDegreeMap k A M ≫ (coefficientFormAlgebraComplexMap k g f hf).f 1) ≫
        (cotangentFormOneIso k B N).hom :=
      congrArg (fun t => t ≫ (cotangentFormOneIso k B N).hom) (degreeMap_naturality k g f hf)
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Let k be a commutative ring, A and B commutative k-algebras, M a left A-module and N a left
B-module, with their k-actions induced by the algebra maps. Let g : A → B be a k-algebra map and
f : M → N a k-linear map satisfying f(a·m)=g(a)·f(m). Let ρ_A and ρ_B be the chain augmentations
from the shifted proper quotients to the degree-zero complexes on the coefficient cotangent
modules. Then cotangentChainMap(g,f) ≫ ρ_B = ρ_A ≫ cotangentModuleMap(g,f)[0]. -/
@[reassoc]
theorem augmentation_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    cotangentChainMap k g f hf ≫ properShuffleCotangentMap k B N =
      properShuffleCotangentMap k A M ≫
        (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (cotangentModuleMap k g f hf) := by
  apply (ChainComplex.toSingle₀Equiv (properCotangentComplex k A M) (coefficientCotangentModule k B N)).injective
  apply Subtype.ext
  change ((cotangentChainMap k g f hf ≫ properShuffleCotangentMap k B N).f 0) =
    ((properShuffleCotangentMap k A M ≫
      (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (cotangentModuleMap k g f hf)).f 0)
  simp only [HomologicalComplex.comp_f, properShuffleCotangentMap_f_zero, ChainComplex.single₀_map_f_zero]
  exact scalarAugmentation_naturality k g f hf

end Complexes

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle
