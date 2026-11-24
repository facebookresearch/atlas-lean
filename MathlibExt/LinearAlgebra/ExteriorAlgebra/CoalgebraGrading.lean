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

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.Coalgebra
public import MathlibExt.LinearAlgebra.ExteriorPower.Projection

/-!
# Total-degree homogeneity of the actual exterior coproduct

The actual coproduct preserves total exterior degree. Homogeneous tensors
are spanned by pure tensors of complementary degrees. Their bidegree
projections vanish outside the antidiagonal, and the finite antidiagonal
reconstruction recovers the original tensor. No tensor-flatness hypothesis
or basis is needed.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R M
local notation "γ" => (CliffordAlgebra.involute : E →ₐ[R] E)
local notation "π" => exteriorPower.projection R M

/-- The native grade involution preserves every full exterior degree. -/
theorem involute_mem_exteriorPower (n : ℕ) (a : E) (ha : a ∈ ⋀[R]^n M) :
    γ a ∈ ⋀[R]^n M := by
  rw [← ιMulti_span_fixedDegree R n] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨v, rfl⟩ := ha
      rw [exteriorPower.involute_ιMulti]
      exact Submodule.smul_mem _ _ (ιMulti_range R n ⟨v, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb iha ihb => rw [map_add]; exact Submodule.add_mem _ iha ihb
  | smul r a ha ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

private theorem ι_mul_mem_degree (x : M) (n : ℕ) (a : E) (ha : a ∈ ⋀[R]^n M) :
    ι R x * a ∈ ⋀[R]^(n + 1) M := by
  change ι R x * a ∈ (LinearMap.range (ι R : M →ₗ[R] E)) ^ (n + 1)
  rw [pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ x) ha

private theorem one_mem_degree_zero : (1 : E) ∈ ⋀[R]^0 M := by
  change (1 : E) ∈ (LinearMap.range (ι R : M →ₗ[R] E)) ^ 0
  rw [pow_zero]
  exact Submodule.mem_one.mpr ⟨(1 : R), by simp only [map_one]⟩

/-- The total-degree-`n` tensors are spanned by homogeneous pure tensors
whose factor degrees add to `n`. -/
def coproductDegree (n : ℕ) : Submodule R (E ⊗[R] E) :=
  Submodule.span R {t | ∃ (p q : ℕ) (a b : E),
    p + q = n ∧ a ∈ ⋀[R]^p M ∧ b ∈ ⋀[R]^q M ∧ a ⊗ₜ[R] b = t}

theorem tmul_mem_coproductDegree (n p q : ℕ) (hpq : p + q = n)
    (a b : E) (ha : a ∈ ⋀[R]^p M) (hb : b ∈ ⋀[R]^q M) :
    a ⊗ₜ[R] b ∈ coproductDegree R M n :=
  Submodule.subset_span ⟨p, q, a, b, hpq, ha, hb, rfl⟩

/-- Signed insertion raises the actual total tensor degree by one. -/
theorem signedInsertion_mem_coproductDegree (x : M) (n : ℕ) (t : E ⊗[R] E)
    (ht : t ∈ coproductDegree R M n) :
    signedInsertion R M x t ∈ coproductDegree R M (n + 1) := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨p, q, a, b, hpq, ha, hb, rfl⟩ := ht
      rw [signedInsertion_tmul]
      apply Submodule.add_mem
      · apply tmul_mem_coproductDegree R M (n + 1) (p + 1) q
        · rw [Nat.add_right_comm, hpq]
        · exact ι_mul_mem_degree R M x p a ha
        · exact hb
      · apply tmul_mem_coproductDegree R M (n + 1) p (q + 1)
        · omega
        · exact involute_mem_exteriorPower R M p a ha
        · exact ι_mul_mem_degree R M x q b hb
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add t s ht hs iht ihs => rw [map_add]; exact Submodule.add_mem _ iht ihs
  | smul r t ht ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

theorem coproduct_ιMulti_mem_degree (n : ℕ) (v : Fin n → M) :
    coproduct R M (ιMulti R n v) ∈ coproductDegree R M n := by
  induction n with
  | zero =>
      rw [ιMulti_zero_apply, coproduct_one]
      exact tmul_mem_coproductDegree R M 0 0 0 rfl 1 1
        (one_mem_degree_zero R M) (one_mem_degree_zero R M)
  | succ n ih =>
      rw [ιMulti_succ_apply, coproduct_ι_mul]
      exact signedInsertion_mem_coproductDegree R M (v 0) n _ (ih (Matrix.vecTail v))

/-- The genuine exterior coproduct is homogeneous for the total degree. -/
theorem coproduct_mem_degree (n : ℕ) (a : E) (ha : a ∈ ⋀[R]^n M) :
    coproduct R M a ∈ coproductDegree R M n := by
  rw [← ιMulti_span_fixedDegree R n] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨v, rfl⟩ := ha
      exact coproduct_ιMulti_mem_degree R M n v
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb iha ihb => rw [map_add]; exact Submodule.add_mem _ iha ihb
  | smul r a ha ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

/-- Bidegree projections outside the actual antidiagonal vanish. -/
theorem projection_tensor_eq_zero_of_mem_degree (n p q : ℕ) (hpq : p + q ≠ n)
    (t : E ⊗[R] E) (ht : t ∈ coproductDegree R M n) :
    TensorProduct.map (π p) (π q) t = 0 := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨i, j, a, b, hij, ha, hb, rfl⟩ := ht
      by_cases hi : i = p
      · subst i
        have hj : j ≠ q := fun hj => hpq (hj ▸ hij)
        rw [TensorProduct.map_tmul,
          exteriorPower.projection_eq_zero_of_mem R M q j hj b hb, TensorProduct.tmul_zero]
      · rw [TensorProduct.map_tmul,
          exteriorPower.projection_eq_zero_of_mem R M p i hi a ha, TensorProduct.zero_tmul]
  | zero => rw [map_zero]
  | add t s ht hs iht ihs => rw [map_add, iht, ihs, zero_add]
  | smul r t ht ih => rw [map_smul, ih, smul_zero]

private theorem subtype_projection_of_mem (n : ℕ) (a : E) (ha : a ∈ ⋀[R]^n M) :
    (π n a : E) = a :=
  congrArg Subtype.val (exteriorPower.projection_subtype_apply R M n ⟨a, ha⟩)

/-- The finite antidiagonal reconstruction as an actual linear map. -/
def degreeTensorReconstruction (n : ℕ) : Module.End R (E ⊗[R] E) :=
  ∑ p : Fin (n + 1),
    (TensorProduct.map (⋀[R]^p.val M).subtype (⋀[R]^(n - p.val) M).subtype).comp
      (TensorProduct.map (π p.val) (π (n - p.val)))

/-- Every homogeneous total-degree tensor is recovered from its finitely
many bidegree components. -/
theorem degreeTensorReconstruction_of_mem (n : ℕ) (t : E ⊗[R] E)
    (ht : t ∈ coproductDegree R M n) : degreeTensorReconstruction R M n t = t := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨i, j, a, b, hij, ha, hb, rfl⟩ := ht
      have hi : i < n + 1 := Nat.lt_succ_of_le (Nat.le.intro hij)
      let r : Fin (n + 1) := ⟨i, hi⟩
      have hni : n - i = j := by rw [← hij, Nat.add_sub_cancel_left]
      have hother (p : Fin (n + 1)) (hp : p ≠ r) : π p.val a = 0 := by
        apply exteriorPower.projection_eq_zero_of_mem R M p.val i
        · intro hip
          exact hp (Fin.ext hip.symm)
        · exact ha
      rw [degreeTensorReconstruction, LinearMap.sum_apply]
      rw [Finset.sum_eq_single r]
      · simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Submodule.subtype_apply]
        change (π i a : E) ⊗ₜ[R] (π (n - i) b : E) = a ⊗ₜ[R] b
        rw [hni, subtype_projection_of_mem R M i a ha,
          subtype_projection_of_mem R M j b hb]
      · intro p hp hpr
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul]
        simp only [hother p hpr, map_zero, TensorProduct.zero_tmul]
      · intro hr
        exact False.elim (hr (Finset.mem_univ r))
  | zero => rw [map_zero]
  | add t s ht hs iht ihs => rw [map_add, iht, ihs]
  | smul r t ht ih => rw [map_smul, ih]

/-- In every exterior degree, the actual coproduct is the finite antidiagonal sum. -/
theorem coproduct_degreeTensorReconstruction (n : ℕ) (a : ⋀[R]^n M) :
    degreeTensorReconstruction R M n (coproduct R M (a : E)) = coproduct R M (a : E) :=
  degreeTensorReconstruction_of_mem R M n _ (coproduct_mem_degree R M n a a.property)

end ExteriorAlgebra
