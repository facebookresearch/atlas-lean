/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import MathlibExt.RingTheory.GradedAlgebra.Projection

/-!
# General tensor-algebra grading API

This file provides a reusable grading API for `TensorAlgebra R M`:

* `tprod` lies in the natural degree `n` piece `(range ι) ^ n`;
* `TensorPower.toTensorAlgebra` corestricts to that degree;
* linear equivalence `TensorPower R n M ≃ₗ degree n`;
* `TensorAlgebra.lift R f` is a `GradedAlgHom` when `f` lands in degree one.

It provides fully general statements over a
commutative semiring `R` and an `R`-module `M`, using `TensorAlgebra.equivDirectSum` and
`TensorAlgebra.toDirectSum`, for reuse in general graded-algebra settings.

## Main definitions

* `TensorAlgebra.degree R M n` – the degree-`n` submodule `(range ι) ^ n`.
* `TensorAlgebra.list_prod_mem_degree` – list product of degree-one elements lies in
  degree indexed by length.
* `TensorAlgebra.tprod_mem_degree` – `tprod` lies in `degree`.
* `TensorAlgebra.toTensorAlgebra_mem_degree` – `toTensorAlgebra` lands in `degree`.
* `TensorAlgebra.toDegree` – corestriction of `toTensorAlgebra` to `degree`.
* `TensorAlgebra.degreeToTensorPower` – projection from `degree` to `TensorPower`.
* `TensorAlgebra.tensorPowerEquivDegree` – the linear equivalence.
* `TensorAlgebra.range_toTensorAlgebra_eq_degree` – range of `toTensorAlgebra` is `degree`.
* `TensorAlgebra.degree_eq_span_range_tprod` – `degree n` is spanned by pure `tprod`s.
* `TensorAlgebra.lift_mem_degree` and `TensorAlgebra.liftGradedAlgHom` – graded lift.
-/

@[expose] public section

open scoped DirectSum TensorProduct
open TensorAlgebra DirectSum

namespace TensorAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Degree-`n` submodule of `TensorAlgebra R M`, defined as the `n`-th power of the
range of `ι`. This is the family used by `TensorAlgebra.gradedAlgebra`. -/
abbrev degree (R : Type*) (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]
    (n : ℕ) : Submodule R (TensorAlgebra R M) :=
  (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M)) ^ n

/-- Degree zero is the `1` submodule. -/
theorem degree_zero : degree R M 0 = 1 := by
  simp [degree, pow_zero]

/-- Degree one is the range of `ι`. -/
theorem degree_one : degree R M 1 = LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) := by
  simp [degree, pow_one]

/-- A list whose entries all lie in degree one has product in the degree indexed by
its length. This is the reusable list version of the graded multiplication for the
tensor algebra. -/
theorem list_prod_mem_degree {l : List (TensorAlgebra R M)}
    (hl : ∀ x ∈ l, x ∈ degree R M 1) : l.prod ∈ degree R M l.length := by
  induction l with
  | nil =>
    simp only [List.length_nil, List.prod_nil]
    exact SetLike.one_mem_graded _
  | cons hd tl ih =>
    have hd_mem : hd ∈ degree R M 1 := hl hd (by simp)
    have tl_mem : ∀ x ∈ tl, x ∈ degree R M 1 := fun x hx =>
      hl x (by simp [hx])
    have ih_mem : tl.prod ∈ degree R M tl.length := ih tl_mem
    have hmul : hd * tl.prod ∈ degree R M (1 + tl.length) :=
      SetLike.mul_mem_graded hd_mem ih_mem
    have h_eq : 1 + tl.length = (hd :: tl).length := by simp [Nat.add_comm]
    rw [h_eq] at hmul
    exact hmul

/-- `TensorAlgebra.tprod` lies in the natural degree `n` piece. -/
theorem tprod_mem_degree (n : ℕ) (x : Fin n → M) :
    tprod R M n x ∈ degree R M n := by
  rw [tprod_apply]
  have hmem : ∀ y ∈ List.ofFn (fun i => ι R (x i)), y ∈ degree R M 1 := by
    intro y hy
    rcases List.mem_ofFn.mp hy with ⟨i, rfl⟩
    rw [degree_one]
    exact LinearMap.mem_range_self _ _
  have hlen : (List.ofFn fun i => ι R (x i)).length = n := by simp
  have hprod : (List.ofFn fun i => ι R (x i)).prod ∈
      degree R M (List.ofFn fun i => ι R (x i)).length :=
    list_prod_mem_degree hmem
  rwa [hlen] at hprod

/-- `TensorPower.toTensorAlgebra` lands in the degree-`n` piece. -/
theorem toTensorAlgebra_mem_degree (n : ℕ) (x : TensorPower R n M) :
    TensorPower.toTensorAlgebra (R := R) (M := M) (n := n) x ∈ degree R M n := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, TensorPower.toTensorAlgebra_tprod]
    exact Submodule.smul_mem _ r (tprod_mem_degree n f)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Corestriction of `TensorPower.toTensorAlgebra` to its natural degree. -/
def toDegree (n : ℕ) : TensorPower R n M →ₗ[R] ↥(degree R M n) :=
  (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n)).codRestrict _
    (toTensorAlgebra_mem_degree n)

/-- The underlying element of `toDegree` is `toTensorAlgebra`. -/
@[simp]
theorem toDegree_apply_coe (n : ℕ) (x : TensorPower R n M) :
    (toDegree (R := R) (M := M) n x : TensorAlgebra R M) =
      TensorPower.toTensorAlgebra x :=
  rfl

/-- Pure tensors map to the product of `ι`'s in the degree submodule. -/
theorem toDegree_tprod (n : ℕ) (x : Fin n → M) :
    toDegree (R := R) (M := M) n (PiTensorProduct.tprod R x) =
      ⟨tprod R M n x, tprod_mem_degree n x⟩ := by
  apply Subtype.ext
  simp [toDegree, TensorPower.toTensorAlgebra_tprod]

/-! ### Lemmas for the equivalence with the direct sum -/

private lemma ofDirectSum_lof_eq_toTensorAlgebra (n : ℕ) (x : TensorPower R n M) :
    (ofDirectSum (R := R) (M := M)).toLinearMap
        (DirectSum.lof R ℕ (fun i => TensorPower R i M) n x) =
      TensorPower.toTensorAlgebra x := by
  have h_eq : (ofDirectSum (R := R) (M := M)).toLinearMap =
      DirectSum.toModule R ℕ (TensorAlgebra R M)
        (fun i => TensorPower.toTensorAlgebra (R := R) (M := M) (n := i)) := rfl
  rw [h_eq]
  exact DirectSum.toModule_lof R
    (M := fun i => TensorPower R i M)
    (φ := fun i => TensorPower.toTensorAlgebra (n := i)) n x

/-- `toDirectSum` sends `toTensorAlgebra` to the `n`-th direct-sum component. -/
theorem toDirectSum_toTensorAlgebra_eq_of (n : ℕ) (x : TensorPower R n M) :
    toDirectSum (R := R) (M := M) (TensorPower.toTensorAlgebra x) =
      DirectSum.of (fun i => TensorPower R i M) n x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h1 : TensorPower.toTensorAlgebra (PiTensorProduct.tprod (R := R) f) =
        tprod R M n f := TensorPower.toTensorAlgebra_tprod f
    calc toDirectSum (TensorPower.toTensorAlgebra (R := R) (r • (PiTensorProduct.tprod (R := R) f)))
        = toDirectSum (R := R) (r • tprod R M n f) := by
          rw [map_smul, h1]
      _ = r • toDirectSum (R := R) (tprod R M n f) := by rw [map_smul]
      _ = r • DirectSum.of (fun i => TensorPower R i M) n (PiTensorProduct.tprod (R := R) f) := by
          rw [toDirectSum_tensorPower_tprod]
      _ = DirectSum.of (fun i => TensorPower R i M) n (r • (PiTensorProduct.tprod (R := R) f)) := by
          rw [← DirectSum.of_smul]
  | add x y hx hy =>
    calc toDirectSum (TensorPower.toTensorAlgebra (R := R) (x + y))
        = toDirectSum (R := R) (TensorPower.toTensorAlgebra x + TensorPower.toTensorAlgebra y) := by
          rw [map_add]
      _ = toDirectSum (R := R) (TensorPower.toTensorAlgebra x) +
          toDirectSum (R := R) (TensorPower.toTensorAlgebra y) := by rw [map_add]
      _ = DirectSum.of (fun i => TensorPower R i M) n x +
          DirectSum.of (fun i => TensorPower R i M) n y := by rw [hx, hy]
      _ = DirectSum.of (fun i => TensorPower R i M) n (x + y) := by
          rw [← map_add]

private lemma proj_ofDirectSum_eq_lapply (n : ℕ) :
    (GradedAlgebra.proj (degree R M) n).comp
        (ofDirectSum (R := R) (M := M)).toLinearMap =
      (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n)).comp
        (DirectSum.component R ℕ (fun i => TensorPower R i M) n) := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [ofDirectSum_lof_eq_toTensorAlgebra]
  have hmem : TensorPower.toTensorAlgebra (R := R) (M := M) x ∈ degree R M i :=
    toTensorAlgebra_mem_degree i x
  by_cases hi : i = n
  · cases hi
    have h_comp : (DirectSum.component R ℕ (fun j => TensorPower R j M) n)
        (DirectSum.lof R ℕ (fun j => TensorPower R j M) n x) = x := by simp
    simp only [h_comp]
    exact GradedAlgebra.proj_eq_self hmem
  · have h_comp_zero : (DirectSum.component R ℕ (fun j => TensorPower R j M) n)
        (DirectSum.lof R ℕ (fun j => TensorPower R j M) i x) = 0 := by
      simp [DirectSum.component.of, hi]
    rw [h_comp_zero, map_zero]
    exact GradedAlgebra.proj_eq_zero_of_ne hmem hi

/-- Projection from the degree-`n` submodule to `TensorPower R n M`, using
`toDirectSum` and direct-sum projection. -/
def degreeToTensorPower (n : ℕ) : ↥(degree R M n) →ₗ[R] TensorPower R n M :=
  (DirectSum.component R ℕ (fun i => TensorPower R i M) n).comp
    ((toDirectSum (R := R) (M := M)).toLinearMap.comp (degree R M n).subtype)

/-- Left inverse: `degreeToTensorPower` after `toDegree` is identity. -/
private theorem degreeToTensorPower_toDegree (n : ℕ) (x : TensorPower R n M) :
    degreeToTensorPower (R := R) (M := M) n (toDegree (R := R) (M := M) n x) = x := by
  simp only [degreeToTensorPower, toDegree, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.codRestrict_apply]
  have h_eq : (toDirectSum (R := R) (M := M)).toLinearMap (TensorPower.toTensorAlgebra x) =
      toDirectSum (R := R) (M := M) (TensorPower.toTensorAlgebra x) := rfl
  rw [h_eq, toDirectSum_toTensorAlgebra_eq_of]
  have h_of_lof : DirectSum.of (fun i => TensorPower R i M) n x =
      DirectSum.lof R ℕ (fun i => TensorPower R i M) n x := by
    rw [DirectSum.lof_eq_of]
  rw [h_of_lof]
  simp

/-- Right inverse: `toDegree` after `degreeToTensorPower` is identity. -/
private theorem toDegree_degreeToTensorPower (n : ℕ) (y : ↥(degree R M n)) :
    toDegree (R := R) (M := M) n (degreeToTensorPower (R := R) (M := M) n y) = y := by
  set S := toDirectSum (R := R) (M := M) (y : TensorAlgebra R M)
  have h_y : (y : TensorAlgebra R M) =
      ofDirectSum (R := R) (M := M) S := by simp [S]
  have h_proj : GradedAlgebra.proj (degree R M) n (y : TensorAlgebra R M) =
      (y : TensorAlgebra R M) := GradedAlgebra.proj_eq_self y.2
  have h_eq : GradedAlgebra.proj (degree R M) n (ofDirectSum (R := R) (M := M) S) =
      TensorPower.toTensorAlgebra (R := R) (M := M)
        ((DirectSum.component R ℕ (fun i => TensorPower R i M) n) S) := by
    have h := proj_ofDirectSum_eq_lapply (R := R) (M := M) n
    exact LinearMap.congr_fun h S
  have h_combined : (y : TensorAlgebra R M) =
      TensorPower.toTensorAlgebra
        ((DirectSum.component R ℕ (fun i => TensorPower R i M) n) S) := by
    calc (y : TensorAlgebra R M) = GradedAlgebra.proj (degree R M) n (y : TensorAlgebra R M) :=
        h_proj.symm
      _ = GradedAlgebra.proj (degree R M) n (ofDirectSum S) := by rw [← h_y]
      _ = _ := h_eq
  apply Subtype.ext
  simp only [toDegree, degreeToTensorPower, LinearMap.comp_apply, LinearMap.codRestrict_apply,
    Submodule.subtype_apply]
  exact h_combined.symm

/-- Linear equivalence between `TensorPower R n M` and the degree-`n` submodule of the
tensor algebra. Uses `equivDirectSum` via `toDirectSum`. -/
noncomputable def tensorPowerEquivDegree (n : ℕ) :
    TensorPower R n M ≃ₗ[R] ↥(degree R M n) :=
  LinearEquiv.ofLinearMap
    (toDegree n)
    (degreeToTensorPower n)
    (by
      apply LinearMap.ext
      intro y
      exact toDegree_degreeToTensorPower n y)
    (by
      apply LinearMap.ext
      intro x
      exact degreeToTensorPower_toDegree n x)

/-- Forward direction sends pure tensors to `tprod`. -/
@[simp]
theorem tensorPowerEquivDegree_tprod (n : ℕ) (x : Fin n → M) :
    tensorPowerEquivDegree (R := R) (M := M) n (PiTensorProduct.tprod R x) =
      ⟨tprod R M n x, tprod_mem_degree n x⟩ := by
  calc tensorPowerEquivDegree n (PiTensorProduct.tprod R x)
      = toDegree n (PiTensorProduct.tprod R x) := rfl
    _ = _ := toDegree_tprod n x

/-- As an element of `TensorAlgebra R M`, the forward equivalence sends pure tensors to `tprod`. -/
theorem tensorPowerEquivDegree_apply_coe (n : ℕ) (x : Fin n → M) :
    (tensorPowerEquivDegree (R := R) (M := M) n (PiTensorProduct.tprod R x) : TensorAlgebra R M) =
      tprod R M n x := by
  rw [tensorPowerEquivDegree_tprod]

/-- Backward direction sends `⟨tprod R M n x, _⟩` back to the pure tensor. -/
@[simp]
theorem degreeToTensorPower_tprod (n : ℕ) (x : Fin n → M) :
    degreeToTensorPower (R := R) (M := M) n ⟨tprod R M n x, tprod_mem_degree n x⟩ =
      PiTensorProduct.tprod R x := by
  have h : degreeToTensorPower (R := R) (M := M) n
      (toDegree (R := R) (M := M) n (PiTensorProduct.tprod R x)) =
      PiTensorProduct.tprod R x :=
    degreeToTensorPower_toDegree n (PiTensorProduct.tprod R x)
  rw [toDegree_tprod] at h
  exact h

/-- Inverse equivalence sends `⟨tprod, _⟩` to the pure tensor. -/
theorem tensorPowerEquivDegree_symm_tprod (n : ℕ) (x : Fin n → M) :
    (tensorPowerEquivDegree (R := R) (M := M) n).symm ⟨tprod R M n x, tprod_mem_degree n x⟩ =
      PiTensorProduct.tprod R x := by
  calc (tensorPowerEquivDegree n).symm ⟨tprod R M n x, tprod_mem_degree n x⟩
      = degreeToTensorPower n ⟨tprod R M n x, tprod_mem_degree n x⟩ := rfl
    _ = _ := degreeToTensorPower_tprod n x

/-- Range of `TensorPower.toTensorAlgebra` is exactly the degree-`n` submodule. -/
theorem range_toTensorAlgebra_eq_degree (n : ℕ) :
    LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n)) =
      degree R M n := by
  have h_eq : (degree R M n).subtype.comp (toDegree (R := R) (M := M) n) =
      TensorPower.toTensorAlgebra (R := R) (M := M) (n := n) := by
    ext x
    rfl
  have h_range_top : LinearMap.range (toDegree (R := R) (M := M) n) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨degreeToTensorPower n y, toDegree_degreeToTensorPower n y⟩
  calc LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n))
      = LinearMap.range ((degree R M n).subtype.comp (toDegree (R := R) (M := M) n)) := by
        rw [h_eq]
    _ = Submodule.map (degree R M n).subtype
        (LinearMap.range (toDegree (R := R) (M := M) n)) := by
        rw [LinearMap.range_comp]
    _ = Submodule.map (degree R M n).subtype ⊤ := by rw [h_range_top]
    _ = degree R M n := by rw [Submodule.map_subtype_top]

/-- Degree-`n` submodule is spanned by pure tensor products `tprod R M n x`. -/
theorem degree_eq_span_range_tprod (n : ℕ) :
    degree R M n = Submodule.span R (Set.range (tprod R M n)) := by
  have h_range_span : LinearMap.range
      (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n)) =
      Submodule.span R (Set.range (tprod R M n)) := by
    calc LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n))
        = Submodule.map (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n)) ⊤ := by
          rw [LinearMap.range_eq_map]
      _ = Submodule.map (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n))
          (Submodule.span R (Set.range (PiTensorProduct.tprod (R := R)
            (s := fun _ : Fin n => M)))) := by
          rw [PiTensorProduct.span_tprod_eq_top]
      _ = Submodule.span R
          (TensorPower.toTensorAlgebra (R := R) (M := M) ''
            Set.range (PiTensorProduct.tprod (R := R)
              (s := fun _ : Fin n => M))) := by
          rw [Submodule.map_span]
      _ = Submodule.span R
          (Set.range (TensorPower.toTensorAlgebra (R := R) (M := M) ∘
            PiTensorProduct.tprod (R := R) (s := fun _ : Fin n => M))) := by
          rw [Set.range_comp]
      _ = Submodule.span R (Set.range (tprod R M n)) := by
          have h_eq : (TensorPower.toTensorAlgebra (R := R) (M := M) ∘
              PiTensorProduct.tprod (R := R) (s := fun _ : Fin n => M)) =
              tprod R M n := by
            funext x
            exact TensorPower.toTensorAlgebra_tprod x
          rw [h_eq]
  calc degree R M n = LinearMap.range
        (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n)) := by
        rw [range_toTensorAlgebra_eq_degree]
    _ = Submodule.span R (Set.range (tprod R M n)) := h_range_span

/-! ### Graded lift -/

section Lift

variable {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [Semiring A] [Algebra R A]

private lemma algebraMap_mem_degree_zero_of_graded
    {ℬ : ℕ → Submodule R A} [GradedAlgebra ℬ] (r : R) : algebraMap R A r ∈ ℬ 0 := by
  have h1 : (1 : A) ∈ ℬ 0 := SetLike.one_mem_graded ℬ
  have h2 : r • (1 : A) ∈ ℬ 0 := Submodule.smul_mem _ r h1
  have h_eq : algebraMap R A r = r • (1 : A) := Algebra.algebraMap_eq_smul_one r
  rw [h_eq]
  exact h2

/-- `TensorAlgebra.lift` sends the degree-`n` piece to degree-`n` when the generators land in
degree one. This is the direct component-membership theorem usable by clients. -/
theorem lift_mem_degree {ℬ : ℕ → Submodule R A} [GradedAlgebra ℬ]
    (f : M →ₗ[R] A) (hf : ∀ m : M, f m ∈ ℬ 1)
    {n : ℕ} {x : TensorAlgebra R M} (hx : x ∈ degree R M n) :
    (lift R (M := M) f) x ∈ ℬ n := by
  -- Use pow induction on `degree = (range ι)^n`
  let M₀ : Submodule R (TensorAlgebra R M) := LinearMap.range (ι R : M →ₗ[R] _)
  change x ∈ M₀ ^ n at hx
  -- motive for pow induction
  have motive : ∀ (k : ℕ) (y : TensorAlgebra R M), y ∈ M₀ ^ k →
      (lift R f) y ∈ ℬ k := by
    intro k y hy
    induction hy using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      -- lift of algebraMap is algebraMap, which lies in degree 0
      have h_lift : (lift R (M := M) f) (algebraMap R (TensorAlgebra R M) r) =
          algebraMap R A r := by simp
      rw [h_lift]
      exact algebraMap_mem_degree_zero_of_graded r
    | add u v k hu hv ih_u ih_v =>
      rw [map_add]
      exact Submodule.add_mem _ ih_u ih_v
    | mem_mul m hm k y hy ih =>
      -- m ∈ M₀ means ∃ a, m = ι a
      obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hm
      have h_lift_ι : (lift R (M := M) f) (ι R a) = f a := lift_ι_apply _ _
      have hf_mem : (lift R (M := M) f) (ι R a) ∈ ℬ 1 := by rw [h_lift_ι]; exact hf a
      have h_mul : (lift R (M := M) f) (ι R a * y) =
          (lift R (M := M) f) (ι R a) * (lift R (M := M) f) y := by rw [map_mul]
      rw [h_mul]
      have h_prod_mem : (lift R (M := M) f) (ι R a) * (lift R (M := M) f) y ∈ ℬ (1 + k) :=
        SetLike.GradedMul.mul_mem hf_mem ih
      have h_eq : ℬ (1 + k) = ℬ (k + 1) := by congr 1; exact Nat.add_comm 1 k
      rw [h_eq] at h_prod_mem
      exact h_prod_mem
  exact motive n x hx

/-- `TensorAlgebra.lift` packaged as a graded algebra homomorphism when generators land in
degree one. Uses `degree R M` as source grading. -/
noncomputable def liftGradedAlgHom {ℬ : ℕ → Submodule R A} [GradedAlgebra ℬ]
    (f : M →ₗ[R] A) (hf : ∀ m : M, f m ∈ ℬ 1) :
    (degree R M) →ₐᵍ[R] ℬ :=
  ⟨lift R (M := M) f, fun hx => lift_mem_degree f hf hx⟩

/-- The underlying map of `liftGradedAlgHom` is `lift`. -/
@[simp]
theorem liftGradedAlgHom_apply {ℬ : ℕ → Submodule R A} [GradedAlgebra ℬ]
    (f : M →ₗ[R] A) (hf : ∀ m : M, f m ∈ ℬ 1) (x : TensorAlgebra R M) :
    (liftGradedAlgHom (ℬ := ℬ) f hf) x = (lift R f) x :=
  rfl

/-- `liftGradedAlgHom` agrees with `f` on generators. -/
theorem liftGradedAlgHom_ι {ℬ : ℕ → Submodule R A} [GradedAlgebra ℬ]
    (f : M →ₗ[R] A) (hf : ∀ m : M, f m ∈ ℬ 1) (m : M) :
    (liftGradedAlgHom (ℬ := ℬ) f hf) (ι R m) = f m := by
  simp [liftGradedAlgHom, lift_ι_apply]

end Lift

end TensorAlgebra
