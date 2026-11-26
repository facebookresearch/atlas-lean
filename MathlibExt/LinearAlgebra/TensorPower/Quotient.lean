/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.TensorPower.Cons
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Factorwise quotients of tensor powers

Let k be a commutative ring, A a k-module and S ≤ A a submodule. The factorwise projection qₙ :
A⊗n → (A/S)⊗n is surjective. Its kernel Rₙ(S) is the span of pure tensors having at least one
entry in S, giving A⊗n/Rₙ(S) ≃ (A/S)⊗n.

For any k-module M, the map id_M ⊗ qₙ has kernel spanned by m ⊗ tprod(a) with an entry of a in
S. This yields the corresponding coefficient quotient equivalence and descent of linear maps
annihilating those generators. These constructions are natural in coefficient maps and module
maps preserving the chosen submodules.

For tensor products, quotients and right exactness, see N. Bourbaki, Algebra I, Chapter III.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct
open LinearMap

universe u v w z t

namespace TensorPower

variable {k : Type u} [CommRing k] {A : Type v} [AddCommGroup A] [Module k A]

/-- The factorwise projection to a tensor power of a quotient.

For a commutative ring k, a k-module A and S ≤ A, qₙ : A⊗n → (A/S)⊗n applies the quotient
projection A → A/S to each tensor factor. -/
def quotientMap (S : Submodule k A) (n : ℕ) :
    TensorPower k n A →ₗ[k] TensorPower k n (A ⧸ S) :=
  PiTensorProduct.map (fun _ : Fin n => S.mkQ)

/-- The quotient classes of the entries of a tensor word.

For a commutative ring k, a k-module A, S ≤ A and a : Fin n → A, qₙ(tprod(a)) = tprod(i ↦ [a
i]) in (A/S)⊗n. -/
@[simp]
theorem quotientMap_tprod (S : Submodule k A) (n : ℕ) (a : Fin n → A) :
    quotientMap S n (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (fun i => S.mkQ (a i)) :=
  PiTensorProduct.map_tprod _ _

/-- The relation submodule for factorwise quotienting.

For a commutative ring k, a k-module A and S ≤ A, Rₙ(S) is the k-span in A⊗n of tprod(a)
such that a i ∈ S for at least one i ∈ Fin n. -/
def quotientRelations (S : Submodule k A) (n : ℕ) : Submodule k (TensorPower k n A) :=
  Submodule.span k {x | ∃ a : Fin n → A, (∃ i, a i ∈ S) ∧
    PiTensorProduct.tprod k a = x}

/-- The degree-zero relation submodule is zero.

For a commutative ring k, a k-module A and S ≤ A, R₀(S) = 0 in A⊗0: an empty tensor word has
no entry belonging to S. -/
@[simp]
theorem quotientRelations_zero (S : Submodule k A) : quotientRelations S 0 = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨a, ⟨i, hi⟩, rfl⟩
  exact Fin.elim0 i

/-- Surjectivity of the factorwise tensor quotient.

For a commutative ring k, a k-module A, S ≤ A and n ≥ 0, qₙ : A⊗n → (A/S)⊗n is surjective. -/
theorem quotientMap_surjective (S : Submodule k A) (n : ℕ) :
    Function.Surjective (quotientMap S n) := by
  intro y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c a =>
      choose b hb using fun i => Submodule.mkQ_surjective S (a i)
      refine ⟨c • PiTensorProduct.tprod k b, ?_⟩
      rw [map_smul, quotientMap_tprod]
      exact congrArg (fun x => c • PiTensorProduct.tprod k x) (funext hb)
  | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add _ _ _⟩

/-- Factor relations vanish under the quotient projection.

For a commutative ring k, a k-module A and S ≤ A, Rₙ(S) ≤ ker(qₙ), since a pure tensor with
an entry in S has a zero quotient entry. -/
theorem quotientRelations_le_ker (S : Submodule k A) (n : ℕ) :
    quotientRelations S n ≤ LinearMap.ker (quotientMap S n) := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, ⟨i, hi⟩, rfl⟩
  change quotientMap S n (PiTensorProduct.tprod k a) = 0
  rw [quotientMap_tprod]
  exact (PiTensorProduct.tprod k).map_coord_zero i
    ((Submodule.Quotient.mk_eq_zero S).2 hi)

private theorem cons_tmul_mem_quotientRelations (S : Submodule k A) (n : ℕ) (a : A)
    {y : TensorPower k n A} (hy : y ∈ quotientRelations S n) :
    consEquiv k A n (a ⊗ₜ[k] y) ∈ quotientRelations S (n + 1) := by
  let f : TensorPower k n A →ₗ[k] TensorPower k (n + 1) A :=
    (consEquiv k A n).toLinearMap.comp (TensorProduct.mk k A (TensorPower k n A) a)
  have h : quotientRelations S n ≤ (quotientRelations S (n + 1)).comap f := by
    apply Submodule.span_le.mpr
    rintro x ⟨b, ⟨i, hi⟩, rfl⟩
    change consEquiv k A n (a ⊗ₜ[k] PiTensorProduct.tprod k b) ∈ quotientRelations S (n + 1)
    rw [consEquiv_tmul]
    exact Submodule.subset_span ⟨Fin.cons a b, ⟨i.succ, by simpa using hi⟩, rfl⟩
  exact h hy

private theorem cons_tmul_mem_quotientRelations_of_first (S : Submodule k A) (n : ℕ)
    {a : A} (ha : a ∈ S) (y : TensorPower k n A) :
    consEquiv k A n (a ⊗ₜ[k] y) ∈ quotientRelations S (n + 1) := by
  let f : TensorPower k n A →ₗ[k] TensorPower k (n + 1) A :=
    (consEquiv k A n).toLinearMap.comp (TensorProduct.mk k A (TensorPower k n A) a)
  have h : (⊤ : Submodule k (TensorPower k n A)) ≤
      (quotientRelations S (n + 1)).comap f := by
    rw [← PiTensorProduct.span_tprod_eq_top]
    apply Submodule.span_le.mpr
    rintro x ⟨b, rfl⟩
    change consEquiv k A n (a ⊗ₜ[k] PiTensorProduct.tprod k b) ∈ quotientRelations S (n + 1)
    rw [consEquiv_tmul]
    exact Submodule.subset_span ⟨Fin.cons a b, ⟨0, by simpa using ha⟩, rfl⟩
  exact h (show y ∈ (⊤ : Submodule k (TensorPower k n A)) from Submodule.mem_top)

/-- The kernel of a factorwise tensor quotient.

For a commutative ring k, a k-module A and S ≤ A, ker(qₙ) = Rₙ(S), the span of pure tensors
with at least one entry in S. -/
theorem quotientMap_ker (S : Submodule k A) (n : ℕ) :
    LinearMap.ker (quotientMap S n) = quotientRelations S n := by
  induction n with
  | zero =>
      rw [quotientRelations_zero]
      apply LinearMap.ker_eq_bot.mpr
      have h : (zeroEquiv k (A ⧸ S)).toLinearMap.comp (quotientMap S 0) =
          (zeroEquiv k A).toLinearMap := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro a
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, quotientMap_tprod, zeroEquiv,
          PiTensorProduct.isEmptyEquiv_apply_tprod]
      intro x y hxy
      apply (zeroEquiv k A).injective
      exact (DFunLike.congr_fun h x).symm.trans
        ((congrArg (zeroEquiv k (A ⧸ S)) hxy).trans (DFunLike.congr_fun h y))
  | succ n ih =>
      apply le_antisymm ?_ (quotientRelations_le_ker S (n + 1))
      have hker : LinearMap.ker (TensorProduct.map S.mkQ (quotientMap S n)) =
          LinearMap.range ((LinearMap.ker (quotientMap S n)).subtype.lTensor A) ⊔
            LinearMap.range (S.subtype.rTensor (TensorPower k n A)) :=
        TensorProduct.map_ker (hfg := LinearMap.exact_subtype_mkQ S)
          (hg := Submodule.mkQ_surjective S)
          (hfg' := (quotientMap S n).exact_subtype_ker_map)
          (hg' := quotientMap_surjective S n)
      have hleft : LinearMap.range ((LinearMap.ker (quotientMap S n)).subtype.lTensor A) ≤
          (quotientRelations S (n + 1)).comap (consEquiv k A n).toLinearMap := by
        rw [LinearMap.lTensor_def, TensorProduct.range_map_eq_span_tmul]
        apply Submodule.span_le.mpr
        rintro x ⟨a, b, rfl⟩
        exact cons_tmul_mem_quotientRelations S n a (by rw [← ih]; exact b.property)
      have hright : LinearMap.range (S.subtype.rTensor (TensorPower k n A)) ≤
          (quotientRelations S (n + 1)).comap (consEquiv k A n).toLinearMap := by
        rw [LinearMap.rTensor_def, TensorProduct.range_map_eq_span_tmul]
        apply Submodule.span_le.mpr
        rintro x ⟨a, b, rfl⟩
        exact cons_tmul_mem_quotientRelations_of_first S n a.property b
      intro x hx
      change quotientMap S (n + 1) x = 0 at hx
      have hmem : (consEquiv k A n).symm x ∈
          LinearMap.ker (TensorProduct.map S.mkQ (quotientMap S n)) := by
        change TensorProduct.map S.mkQ (quotientMap S n) ((consEquiv k A n).symm x) = 0
        apply (consEquiv k (A ⧸ S) n).injective
        have h := DFunLike.congr_fun (consEquiv_naturality S.mkQ n)
          ((consEquiv k A n).symm x)
        change consEquiv k (A ⧸ S) n
            (TensorProduct.map S.mkQ (quotientMap S n) ((consEquiv k A n).symm x)) =
          quotientMap S (n + 1) (consEquiv k A n ((consEquiv k A n).symm x)) at h
        simpa only [LinearEquiv.apply_symm_apply, hx, map_zero] using h
      rw [hker] at hmem
      have h := (sup_le hleft hright) hmem
      simpa only [Submodule.mem_comap, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using h

/-- The quotient tensor-power equivalence.

For a commutative ring k, a k-module A and S ≤ A, qₙ induces a k-linear equivalence
A⊗n/Rₙ(S) ≃ (A/S)⊗n. -/
def quotientEquiv (S : Submodule k A) (n : ℕ) :
    (TensorPower k n A ⧸ quotientRelations S n) ≃ₗ[k] TensorPower k n (A ⧸ S) :=
  (Submodule.quotEquivOfEq _ _ (quotientMap_ker S n).symm).trans
    ((quotientMap S n).quotKerEquivOfSurjective (quotientMap_surjective S n))

/-- The pure-tensor coordinates of the quotient equivalence.

For a commutative ring k, a k-module A, S ≤ A and a : Fin n → A, the class of tprod(a)
modulo Rₙ(S) maps to tprod(i ↦ [a i]) in (A/S)⊗n. -/
@[simp]
theorem quotientEquiv_mk_tprod (S : Submodule k A) (n : ℕ) (a : Fin n → A) :
    quotientEquiv S n (Submodule.Quotient.mk (PiTensorProduct.tprod k a)) =
      PiTensorProduct.tprod k (fun i => S.mkQ (a i)) := by
  change (quotientMap S n).quotKerEquivOfSurjective (quotientMap_surjective S n)
      (Submodule.Quotient.mk (PiTensorProduct.tprod k a)) = _
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk, quotientMap_tprod]

variable (S : Submodule k A) (M : Type w) [AddCommGroup M] [Module k M]

/-- The factorwise quotient with a fixed coefficient module.

For a commutative ring k, k-modules A,M and S ≤ A, Qₙ = id_M ⊗ qₙ maps M ⊗ A⊗n to M ⊗
(A/S)⊗n and retains the coefficient in M. -/
def coefficientQuotientMap (n : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[k] M ⊗[k] TensorPower k n (A ⧸ S) :=
  TensorProduct.map LinearMap.id (quotientMap S n)

/-- The quotient coordinates of a coefficient tensor word.

For a commutative ring k, k-modules A,M, S ≤ A, m ∈ M and a : Fin n → A, Qₙ(m ⊗ tprod(a)) =
m ⊗ tprod(i ↦ [a i]). -/
@[simp]
theorem coefficientQuotientMap_tmul_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    coefficientQuotientMap S M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => S.mkQ (a i)) := by
  rw [coefficientQuotientMap, TensorProduct.map_tmul, LinearMap.id_apply, quotientMap_tprod]

/-- The factor relations with an arbitrary coefficient.

For a commutative ring k, k-modules A,M and S ≤ A, Dₙ(S,M) is the span in M ⊗ A⊗n of m ⊗
tprod(a) with a i ∈ S for some i ∈ Fin n. -/
def coefficientQuotientRelations (n : ℕ) : Submodule k (M ⊗[k] TensorPower k n A) :=
  Submodule.span k {x | ∃ (m : M) (a : Fin n → A), (∃ i, a i ∈ S) ∧
    m ⊗ₜ[k] PiTensorProduct.tprod k a = x}

/-- Surjectivity of the coefficient tensor quotient.

For a commutative ring k, k-modules A,M and S ≤ A, Qₙ : M ⊗ A⊗n → M ⊗ (A/S)⊗n is surjective
for every n ≥ 0 and every coefficient module M. -/
theorem coefficientQuotientMap_surjective (n : ℕ) :
    Function.Surjective (coefficientQuotientMap S M n) :=
  TensorProduct.map_surjective (g := LinearMap.id) Function.surjective_id
    (quotientMap_surjective S n)

private theorem tmul_mem_coefficientQuotientRelations (n : ℕ) (m : M)
    {y : TensorPower k n A} (hy : y ∈ quotientRelations S n) :
    m ⊗ₜ[k] y ∈ coefficientQuotientRelations S M n := by
  have h : quotientRelations S n ≤
      (coefficientQuotientRelations S M n).comap (TensorProduct.mk k M _ m) := by
    apply Submodule.span_le.mpr
    rintro x ⟨a, ⟨i, hi⟩, rfl⟩
    exact Submodule.subset_span ⟨m, a, ⟨i, hi⟩, rfl⟩
  exact h hy

/-- The kernel of the coefficient tensor quotient.

For a commutative ring k, k-modules A,M and S ≤ A, ker(Qₙ) = Dₙ(S,M), the span of
coefficient tensor words with an entry in S. -/
theorem coefficientQuotientMap_ker (n : ℕ) :
    LinearMap.ker (coefficientQuotientMap S M n) =
      coefficientQuotientRelations S M n := by
  have hker : LinearMap.ker (coefficientQuotientMap S M n) =
      LinearMap.range ((LinearMap.ker (quotientMap S n)).subtype.lTensor M) := by
    exact (_root_.lTensor_exact M (quotientMap S n).exact_subtype_ker_map
      (quotientMap_surjective S n)).linearMap_ker_eq
  apply le_antisymm
  · rw [hker, LinearMap.lTensor_def, TensorProduct.range_map_eq_span_tmul]
    apply Submodule.span_le.mpr
    rintro x ⟨m, y, rfl⟩
    exact tmul_mem_coefficientQuotientRelations S M n m
      (by rw [← quotientMap_ker S n]; exact y.property)
  · apply Submodule.span_le.mpr
    rintro x ⟨m, a, ⟨i, hi⟩, rfl⟩
    change coefficientQuotientMap S M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) = 0
    rw [coefficientQuotientMap_tmul_tprod,
      (PiTensorProduct.tprod k).map_coord_zero i
        ((Submodule.Quotient.mk_eq_zero S).2 hi), TensorProduct.tmul_zero]

/-- The coefficient tensor quotient equivalence.

For a commutative ring k, k-modules A,M and S ≤ A, Qₙ induces (M ⊗ A⊗n)/Dₙ(S,M) ≃ M ⊗
(A/S)⊗n as k-modules. The coefficient and tensor-factor modules may lie in different
universes. -/
def coefficientQuotientEquiv (n : ℕ) :
    (M ⊗[k] TensorPower k n A ⧸ coefficientQuotientRelations S M n) ≃ₗ[k]
      M ⊗[k] TensorPower k n (A ⧸ S) :=
  (Submodule.quotEquivOfEq _ _ (coefficientQuotientMap_ker S M n).symm).trans
    ((coefficientQuotientMap S M n).quotKerEquivOfSurjective
      (coefficientQuotientMap_surjective S M n))

/-- The coefficient word coordinates of the quotient equivalence.

For a commutative ring k, k-modules A,M, S ≤ A, m ∈ M and a : Fin n → A, the class of m ⊗
tprod(a) modulo Dₙ(S,M) maps to m ⊗ tprod(i ↦ [a i]). -/
@[simp]
theorem coefficientQuotientEquiv_mk_tmul_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    coefficientQuotientEquiv S M n
        (Submodule.Quotient.mk (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => S.mkQ (a i)) := by
  change (coefficientQuotientMap S M n).quotKerEquivOfSurjective
      (coefficientQuotientMap_surjective S M n)
      (Submodule.Quotient.mk (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk, coefficientQuotientMap_tmul_tprod]

/-- The inverse equivalence on a projected coefficient tensor.

For a commutative ring k, k-modules A,M, S ≤ A and x ∈ M ⊗ A⊗n, the inverse coefficient
quotient equivalence sends Qₙ(x) to the class of x modulo Dₙ(S,M). -/
theorem coefficientQuotientEquiv_symm_apply_map (n : ℕ)
    (x : M ⊗[k] TensorPower k n A) :
    (coefficientQuotientEquiv S M n).symm (coefficientQuotientMap S M n x) =
      Submodule.Quotient.mk x := by
  apply (coefficientQuotientEquiv S M n).injective
  change _ = (coefficientQuotientMap S M n).quotKerEquivOfSurjective
    (coefficientQuotientMap_surjective S M n) (Submodule.Quotient.mk x)
  rw [LinearEquiv.apply_symm_apply, LinearMap.quotKerEquivOfSurjective_apply_mk]

variable {N : Type z} [AddCommGroup N] [Module k N]

/-- The generator criterion for annihilating coefficient relations.

For a commutative ring k, k-modules A,M,N, S ≤ A and a k-linear map f : M ⊗ A⊗n → N, Dₙ(S,M)
≤ ker(f) exactly when f(m ⊗ tprod(a)) = 0 whenever a i ∈ S for some i. -/
theorem coefficientQuotientRelations_le_ker_iff (n : ℕ)
    (f : M ⊗[k] TensorPower k n A →ₗ[k] N) :
    coefficientQuotientRelations S M n ≤ LinearMap.ker f ↔
      ∀ (m : M) (a : Fin n → A) (i : Fin n), a i ∈ S →
        f (m ⊗ₜ[k] PiTensorProduct.tprod k a) = 0 := by
  constructor
  · intro h m a i hi
    exact h (Submodule.subset_span ⟨m, a, ⟨i, hi⟩, rfl⟩)
  · intro h
    apply Submodule.span_le.mpr
    rintro x ⟨m, a, ⟨i, hi⟩, rfl⟩
    exact h m a i hi

/-- Descent of a linear map through the factorwise quotient.

For a commutative ring k, k-modules A,M,N, S ≤ A and f : M ⊗ A⊗n → N with Dₙ(S,M) ≤ ker(f),
this is the induced k-linear map M ⊗ (A/S)⊗n → N. -/
def liftCoefficientQuotient (n : ℕ) (f : M ⊗[k] TensorPower k n A →ₗ[k] N)
    (h : coefficientQuotientRelations S M n ≤ LinearMap.ker f) :
    M ⊗[k] TensorPower k n (A ⧸ S) →ₗ[k] N :=
  ((coefficientQuotientRelations S M n).liftQ f h).comp
    (coefficientQuotientEquiv S M n).symm.toLinearMap

/-- The defining identity for a descended coefficient map.

For a commutative ring k, k-modules A,M,N, S ≤ A and a k-linear map f annihilating Dₙ(S,M),
its descent f̄ satisfies f̄ ∘ Qₙ = f. -/
theorem liftCoefficientQuotient_comp (n : ℕ)
    (f : M ⊗[k] TensorPower k n A →ₗ[k] N)
    (h : coefficientQuotientRelations S M n ≤ LinearMap.ker f) :
    (liftCoefficientQuotient S M n f h).comp (coefficientQuotientMap S M n) = f := by
  apply LinearMap.ext
  intro x
  change (coefficientQuotientRelations S M n).liftQ f h
    ((coefficientQuotientEquiv S M n).symm (coefficientQuotientMap S M n x)) = f x
  rw [coefficientQuotientEquiv_symm_apply_map, Submodule.liftQ_apply]

/-- Cancellation after the coefficient quotient projection.

For a commutative ring k, k-modules A,M,N and S ≤ A, two k-linear maps f,g : M ⊗ (A/S)⊗n → N
are equal if f ∘ Qₙ = g ∘ Qₙ. -/
theorem coefficientQuotientMap_cancel (n : ℕ)
    {f g : M ⊗[k] TensorPower k n (A ⧸ S) →ₗ[k] N}
    (h : f.comp (coefficientQuotientMap S M n) =
      g.comp (coefficientQuotientMap S M n)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := coefficientQuotientMap_surjective S M n x
  exact DFunLike.congr_fun h x

variable {S M} {B : Type z} [AddCommGroup B] [Module k B]
  {T : Submodule k B} {M' : Type t} [AddCommGroup M'] [Module k M']

/-- Naturality of coefficient tensor quotients.

For a commutative ring k, k-linear maps g : M → M′ and f : A → B, and submodules S ≤ A, T ≤
B with f(S) ⊆ T, let f̄ : A/S → B/T be the induced map. Then (g ⊗ f̄⊗n) ∘ Qₙ,S = Qₙ,T ∘ (g ⊗
f⊗n). -/
theorem coefficientQuotientMap_naturality (g : M →ₗ[k] M') (f : A →ₗ[k] B)
    (h : S ≤ T.comap f) (n : ℕ) :
    (TensorProduct.map g (PiTensorProduct.map (fun _ : Fin n => S.mapQ T f h))).comp
        (coefficientQuotientMap S M n) =
      (coefficientQuotientMap T M' n).comp
        (TensorProduct.map g (PiTensorProduct.map (fun _ : Fin n => f))) := by
  have hmap (a : A) : S.mapQ T f h (S.mkQ a) = T.mkQ (f a) :=
    DFunLike.congr_fun (Submodule.mapQ_mkQ S T f (h := h)) a
  apply TensorProduct.ext'
  intro m y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c a =>
      simp only [TensorProduct.tmul_smul, map_smul,
        coefficientQuotientMap_tmul_tprod, TensorProduct.map_tmul,
        PiTensorProduct.map_tprod, LinearMap.comp_apply, hmap]
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy, LinearMap.comp_apply]

end TensorPower
