/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.Coalgebra
public import MathlibExt.LinearAlgebra.ExteriorPower.Projection

/-!
# Total-degree homogeneity of the exterior coproduct

For `E=ExteriorAlgebra R M`, let `D_n ⊆ E ⊗[R] E` be spanned by homogeneous pure tensors of
bidegrees `(p,q)` with `p+q=n`. The exterior coproduct maps `Λ^n_R M` into `D_n`.

Projection to a bidegree off this antidiagonal is zero. Summing the included bidegree
projections over `p=0,...,n` recovers every tensor in `D_n`, and hence every coproduct of a
homogeneous degree-`n` element.

References: Bourbaki, *Algebra*, Chapter III; Loday, *Cyclic Homology*, Section 4.5.
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

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For `n : ℕ` and `a ∈ Λ^n_R M`, the grade involution satisfies `γ(a) ∈
Λ^n_R M`. -/
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

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For `n : ℕ`, `coproductDegree R M n` is the submodule spanned by `a⊗b`
with `a ∈ Λ^p_R M`, `b ∈ Λ^q_R M`, and `p+q=n`. -/
def coproductDegree (n : ℕ) : Submodule R (E ⊗[R] E) :=
  Submodule.span R {t | ∃ (p q : ℕ) (a b : E),
    p + q = n ∧ a ∈ ⋀[R]^p M ∧ b ∈ ⋀[R]^q M ∧ a ⊗ₜ[R] b = t}

theorem tmul_mem_coproductDegree (n p q : ℕ) (hpq : p + q = n)
    (a b : E) (ha : a ∈ ⋀[R]^p M) (hb : b ∈ ⋀[R]^q M) :
    a ⊗ₜ[R] b ∈ coproductDegree R M n :=
  Submodule.subset_span ⟨p, q, a, b, hpq, ha, hb, rfl⟩

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Write `E_r = Λ^r_R M`, `π_r : E → E_r` for degree projection, and `j_r :
E_r → E` for inclusion. Let `D_n` be the span of `a_p ⊗ b_q` with `p+q=n`. For `x : M`, `n :
ℕ`, and `t ∈ D_n`, `signedInsertion R M x t ∈ D_(n+1)`. -/
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

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Write `E_r = Λ^r_R M`, `π_r : E → E_r` for degree projection, and `j_r :
E_r → E` for inclusion. Let `D_n` be the span of `a_p ⊗ b_q` with `p+q=n`. For `n : ℕ` and `a
∈ E_n`, `Δ a ∈ D_n`. -/
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

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Write `E_r = Λ^r_R M`, `π_r : E → E_r` for degree projection, and `j_r :
E_r → E` for inclusion. Let `D_n` be the span of `a_p ⊗ b_q` with `p+q=n`. For `n,p,q : ℕ`,
`p+q≠n`, and `t ∈ D_n`, `(π_p ⊗ π_q)(t)=0` in `E_p ⊗[R] E_q`. -/
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

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Write `E_r = Λ^r_R M`, `π_r : E → E_r` for degree projection, and `j_r :
E_r → E` for inclusion. Let `D_n` be the span of `a_p ⊗ b_q` with `p+q=n`. For `n : ℕ`, the
reconstruction endomorphism of `E⊗E` is `R_n=∑ p : Fin(n+1), (j_p ⊗ j_(n-p)) ∘ (π_p ⊗
π_(n-p))`. -/
def degreeTensorReconstruction (n : ℕ) : Module.End R (E ⊗[R] E) :=
  ∑ p : Fin (n + 1),
    (TensorProduct.map (⋀[R]^p.val M).subtype (⋀[R]^(n - p.val) M).subtype).comp
      (TensorProduct.map (π p.val) (π (n - p.val)))

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Write `E_r = Λ^r_R M`, `π_r : E → E_r` for degree projection, and `j_r :
E_r → E` for inclusion. Let `D_n` be the span of `a_p ⊗ b_q` with `p+q=n`. For `n : ℕ` and `t
∈ D_n`, `degreeTensorReconstruction R M n t=t`. -/
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

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Write `E_r = Λ^r_R M`, `π_r : E → E_r` for degree projection, and `j_r :
E_r → E` for inclusion. Let `D_n` be the span of `a_p ⊗ b_q` with `p+q=n`. For `n : ℕ` and `a
: E_n`, `degreeTensorReconstruction R M n (Δ(a : E))=Δ(a : E)`. -/
theorem coproduct_degreeTensorReconstruction (n : ℕ) (a : ⋀[R]^n M) :
    degreeTensorReconstruction R M n (coproduct R M (a : E)) = coproduct R M (a : E) :=
  degreeTensorReconstruction_of_mem R M n _ (coproduct_mem_degree R M n a a.property)

end ExteriorAlgebra
