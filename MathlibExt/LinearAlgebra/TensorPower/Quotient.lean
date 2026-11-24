/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.TensorPower.Cons
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Quotients of tensor powers and coefficient tensors

Quotienting every tensor factor by a ground submodule quotients the tensor
power by the span of pure tensors with a factor in that submodule. The same
statement retains an arbitrary coefficient module. All maps use the original
modules and linear maps; no algebra, unit or flatness hypothesis is needed.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct
open LinearMap

universe u v w z t

namespace TensorPower

variable {k : Type u} [CommRing k] {A : Type v} [AddCommGroup A] [Module k A]

/-- The original quotient map applied to every factor. -/
def quotientMap (S : Submodule k A) (n : ℕ) :
    TensorPower k n A →ₗ[k] TensorPower k n (A ⧸ S) :=
  PiTensorProduct.map (fun _ : Fin n => S.mkQ)

/-- Every pure tuple is sent to the tuple of its actual quotient classes. -/
@[simp]
theorem quotientMap_tprod (S : Submodule k A) (n : ℕ) (a : Fin n → A) :
    quotientMap S n (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (fun i => S.mkQ (a i)) :=
  PiTensorProduct.map_tprod _ _

/-- The ground span of the pure tensors with a factor in the given submodule. -/
def quotientRelations (S : Submodule k A) (n : ℕ) : Submodule k (TensorPower k n A) :=
  Submodule.span k {x | ∃ a : Fin n → A, (∃ i, a i ∈ S) ∧
    PiTensorProduct.tprod k a = x}

/-- There is no factor to quotient in degree zero. -/
@[simp]
theorem quotientRelations_zero (S : Submodule k A) : quotientRelations S 0 = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨a, ⟨i, hi⟩, rfl⟩
  exact Fin.elim0 i

/-- Quotient classes of pure tuples still span the target tensor power. -/
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

/-- The stated tensor relations are killed by the actual quotient map. -/
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

/-- Right exactness gives precisely the advertised kernel, in every degree. -/
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

/-- The actual quotient of the tensor power by its factor relations. -/
def quotientEquiv (S : Submodule k A) (n : ℕ) :
    (TensorPower k n A ⧸ quotientRelations S n) ≃ₗ[k] TensorPower k n (A ⧸ S) :=
  (Submodule.quotEquivOfEq _ _ (quotientMap_ker S n).symm).trans
    ((quotientMap S n).quotKerEquivOfSurjective (quotientMap_surjective S n))

/-- The quotient equivalence retains the classes of the actual factors. -/
@[simp]
theorem quotientEquiv_mk_tprod (S : Submodule k A) (n : ℕ) (a : Fin n → A) :
    quotientEquiv S n (Submodule.Quotient.mk (PiTensorProduct.tprod k a)) =
      PiTensorProduct.tprod k (fun i => S.mkQ (a i)) := by
  change (quotientMap S n).quotKerEquivOfSurjective (quotientMap_surjective S n)
      (Submodule.Quotient.mk (PiTensorProduct.tprod k a)) = _
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk, quotientMap_tprod]

variable (S : Submodule k A) (M : Type w) [AddCommGroup M] [Module k M]

/-- The coefficient is retained, and only the tensor-power factors are quotiented. -/
def coefficientQuotientMap (n : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[k] M ⊗[k] TensorPower k n (A ⧸ S) :=
  TensorProduct.map LinearMap.id (quotientMap S n)

/-- Actual pure coefficient tensors map to their factorwise quotient classes. -/
@[simp]
theorem coefficientQuotientMap_tmul_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    coefficientQuotientMap S M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => S.mkQ (a i)) := by
  rw [coefficientQuotientMap, TensorProduct.map_tmul, LinearMap.id_apply, quotientMap_tprod]

/-- The coefficient version of the same ground tensor relations. -/
def coefficientQuotientRelations (n : ℕ) : Submodule k (M ⊗[k] TensorPower k n A) :=
  Submodule.span k {x | ∃ (m : M) (a : Fin n → A), (∃ i, a i ∈ S) ∧
    m ⊗ₜ[k] PiTensorProduct.tprod k a = x}

/-- The original quotient map remains surjective with arbitrary coefficients. -/
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

/-- The kernel consists exactly of the stated degenerate coefficient tensors. -/
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

/-- The quotient equivalence retains every original coefficient, in independent universes. -/
def coefficientQuotientEquiv (n : ℕ) :
    (M ⊗[k] TensorPower k n A ⧸ coefficientQuotientRelations S M n) ≃ₗ[k]
      M ⊗[k] TensorPower k n (A ⧸ S) :=
  (Submodule.quotEquivOfEq _ _ (coefficientQuotientMap_ker S M n).symm).trans
    ((coefficientQuotientMap S M n).quotKerEquivOfSurjective
      (coefficientQuotientMap_surjective S M n))

/-- The actual pure coefficient representative of the quotient equivalence. -/
@[simp]
theorem coefficientQuotientEquiv_mk_tmul_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    coefficientQuotientEquiv S M n
        (Submodule.Quotient.mk (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => S.mkQ (a i)) := by
  change (coefficientQuotientMap S M n).quotKerEquivOfSurjective
      (coefficientQuotientMap_surjective S M n)
      (Submodule.Quotient.mk (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk, coefficientQuotientMap_tmul_tprod]

/-- The inverse takes an actual quotient-map value back to its original quotient class. -/
theorem coefficientQuotientEquiv_symm_apply_map (n : ℕ)
    (x : M ⊗[k] TensorPower k n A) :
    (coefficientQuotientEquiv S M n).symm (coefficientQuotientMap S M n x) =
      Submodule.Quotient.mk x := by
  apply (coefficientQuotientEquiv S M n).injective
  change _ = (coefficientQuotientMap S M n).quotKerEquivOfSurjective
    (coefficientQuotientMap_surjective S M n) (Submodule.Quotient.mk x)
  rw [LinearEquiv.apply_symm_apply, LinearMap.quotKerEquivOfSurjective_apply_mk]

variable {N : Type z} [AddCommGroup N] [Module k N]

/-- Killing the ground relation submodule is exactly killing its pure generators. -/
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

/-- Universal descent through the actual factorwise quotient, for arbitrary ground maps. -/
def liftCoefficientQuotient (n : ℕ) (f : M ⊗[k] TensorPower k n A →ₗ[k] N)
    (h : coefficientQuotientRelations S M n ≤ LinearMap.ker f) :
    M ⊗[k] TensorPower k n (A ⧸ S) →ₗ[k] N :=
  ((coefficientQuotientRelations S M n).liftQ f h).comp
    (coefficientQuotientEquiv S M n).symm.toLinearMap

/-- The universal map retains the original values before quotienting. -/
theorem liftCoefficientQuotient_comp (n : ℕ)
    (f : M ⊗[k] TensorPower k n A →ₗ[k] N)
    (h : coefficientQuotientRelations S M n ≤ LinearMap.ker f) :
    (liftCoefficientQuotient S M n f h).comp (coefficientQuotientMap S M n) = f := by
  apply LinearMap.ext
  intro x
  change (coefficientQuotientRelations S M n).liftQ f h
    ((coefficientQuotientEquiv S M n).symm (coefficientQuotientMap S M n x)) = f x
  rw [coefficientQuotientEquiv_symm_apply_map, Submodule.liftQ_apply]

/-- The factorwise quotient is epic for actual linear maps. -/
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

/-- Every ground-linear coefficient/factor map preserving the submodule gives the actual square. -/
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
