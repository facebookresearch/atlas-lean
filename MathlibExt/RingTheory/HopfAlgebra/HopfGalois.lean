/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HopfAlgebra_canMap_surjective_of_surjective.lean`,
`P2M/Sol/S_HopfAlgebra_canMap_surjective_of_surjective.lean`,
`Theorems/Thm_HopfAlgebra_isHopfGalois_of_surjective.lean`,
`P2M/Sol/S_HopfAlgebra_isHopfGalois_of_surjective.lean`,
`Theorems/Thm_HopfAlgebra_finite_projective_hopfKer_of_surjective.lean`, and
`P2M/Sol/S_HopfAlgebra_finite_projective_hopfKer_of_surjective.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.HopfKer
public import MathlibExt.RingTheory.HopfAlgebra.LeftIntegral
public import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Coalgebra.CoassocSimps

/-!
# Surjections onto finite free Hopf algebras are Hopf-Galois

For a surjective bialgebra map `π : A →ₐc[R] B` out of a commutative Hopf algebra, the
canonical map `HopfAlgebra.canMap π` is surjective. When moreover `B` is a finite free
commutative Hopf algebra, left integrals on `B` give a dual-basis formula over the Hopf
kernel; it shows that `π` is Hopf-Galois and that `A` is a finite projective module over
`HopfAlgebra.hopfKer π`.
-/

@[expose] public section

open scoped TensorProduct
open HopfAlgebra Coalgebra

universe u v w

namespace HopfAlgebra

section Surjective

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
  {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B)

private theorem canAlgHom_antipode_comul (a' : A) :
    canAlgHom π ((HopfAlgebra.antipode R).rTensor A (Coalgebra.comul a'))
      = (1 : A) ⊗ₜ[R] π a' := by
  set Φ : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] B :=
    (π : A →ₐ[R] B).toLinearMap.lTensor A ∘ₗ
      (LinearMap.mul' R A).rTensor A ∘ₗ
      ((HopfAlgebra.antipode R (A := A)).rTensor A).rTensor A with hΦ
  have step1 : (canAlgHom π : A ⊗[R] A →ₐ[R] A ⊗[R] B).toLinearMap
        ∘ₗ (HopfAlgebra.antipode R (A := A)).rTensor A
      = Φ ∘ₗ (TensorProduct.assoc R A A A).symm.toLinearMap
          ∘ₗ (Coalgebra.comul (R := R) (A := A)).lTensor A :=
    TensorProduct.ext' fun u v => by
      have inner : ∀ z : A ⊗[R] A,
          ((HopfAlgebra.antipode R u : A) ⊗ₜ[R] (1 : B)) *
              (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B)) z
            = Φ ((TensorProduct.assoc R A A A).symm (u ⊗ₜ[R] z)) := fun z => by
        induction z with
        | add x y hx hy =>
            simp only [map_add, mul_add, TensorProduct.tmul_add] at *; rw [hx, hy]
        | tmul x y =>
            simp only [hΦ, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
              Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.assoc_symm_tmul,
              LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul,
              LinearMap.lTensor_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
        canAlgHom_tmul, HopfAlgebra.coaction, AlgHom.comp_apply]
      exact inner _
  have step2 : canAlgHom π ((HopfAlgebra.antipode R).rTensor A (Coalgebra.comul a'))
      = Φ ((Coalgebra.comul (R := R) (A := A)).rTensor A (Coalgebra.comul a')) := by
    have h := LinearMap.congr_fun step1 (Coalgebra.comul (R := R) a')
    have hco := LinearMap.congr_fun (Coalgebra.coassoc (R := R) (A := A)) a'
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_coe] at h hco
    rw [h, ← hco, LinearEquiv.symm_apply_apply]
  rw [step2, hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
    ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, LinearMap.comp_assoc,
    HopfAlgebra.mul_antipode_rTensor_comul (R := R) (A := A),
    LinearMap.rTensor_comp_apply, Coalgebra.rTensor_counit_comul,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  simp

/-- **The canonical map of a surjection is surjective.** Let `R` be a commutative ring, `A` a
commutative Hopf algebra over `R` and `B` a commutative bialgebra over `R`. For a surjective
bialgebra map `π : A →ₐc[R] B`, the canonical map `HopfAlgebra.canMap π : A ⊗[R] A → A ⊗[R] B`,
`a ⊗ a' ↦ (a ⊗ 1) * coaction π a'`, is surjective. -/
theorem canMap_surjective_of_surjective (hπ : Function.Surjective π) :
    Function.Surjective (canMap π) := fun z => by
  induction z with
  | tmul a c =>
      obtain ⟨a', ha'⟩ := hπ c
      exact ⟨(a ⊗ₜ[R] (1 : A)) *
          ((HopfAlgebra.antipode R).rTensor A (Coalgebra.comul a')), by
        rw [canMap_apply, _root_.map_mul, ← canMap_apply π (a ⊗ₜ[R] 1), canMap_tmul_one,
          canAlgHom_antipode_comul, ha', Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]⟩
  | add y z hy hz =>
      obtain ⟨py, hy⟩ := hy; obtain ⟨pz, hz⟩ := hz
      exact ⟨py + pz, by rw [map_add, hy, hz]⟩

end Surjective

end HopfAlgebra

namespace HopfAlgebra.HopfGaloisAux

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B]
variable (π : A →ₐc[R] B)

private noncomputable def G (φ : Module.Dual R B) : A ⊗[R] B →ₗ[R] A :=
  (TensorProduct.rid R A).toLinearMap ∘ₗ φ.lTensor A

@[local simp] private theorem G_tmul (φ : Module.Dual R B) (x : A) (b : B) :
    G (A := A) φ (x ⊗ₜ[R] b) = φ b • x := by
  simp [G]

private theorem G_includeLeft_mul (φ : Module.Dual R B) (c : A) (w : A ⊗[R] B) :
    G φ ((c ⊗ₜ[R] (1 : B)) * w) = c * G φ w := by
  induction w with
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]
  | tmul x b => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, G_tmul, G_tmul, mul_smul_comm]

private noncomputable def T (φ : Module.Dual R B) : A →ₗ[R] A := G φ ∘ₗ (coaction π).toLinearMap

private theorem T_apply (φ : Module.Dual R B) (a : A) : T π φ a = G φ (coaction π a) := rfl

private theorem T_repr (φ : Module.Dual R B) {a : A} {ι : Type*} (𝓡 : Coalgebra.Repr R a ι) :
    T π φ a = ∑ i ∈ 𝓡.index, φ (π (𝓡.right i)) • 𝓡.left i := by
  rw [T_apply, HopfKerHopf.coaction_repr π 𝓡, map_sum]
  simp

private theorem T_mul_of_mem (φ : Module.Dual R B) {s : A} (hs : s ∈ hopfKer π) (a : A) :
    T π φ (s * a) = s * T π φ a := by
  rw [T_apply, T_apply, map_mul, coaction_eq_of_mem π hs, G_includeLeft_mul]

private theorem T_mem_hopfKer (φ : Module.Dual R B)
    (hφ : ∀ b : B, (TensorProduct.rid R B) (φ.lTensor B (Coalgebra.comul b)) = φ b •
        (1 : B)) (a : A) :
    T π φ a ∈ hopfKer π := by
  rw [mem_hopfKer_iff]
  set 𝓡 := ℛ R a
  let a₁ : (i : _) → Coalgebra.Repr R (𝓡.left i) (_ × _) := fun i => ℛ R (𝓡.left i)
  let a₂ : (i : _) → Coalgebra.Repr R (𝓡.right i) (_ × _) := fun i => ℛ R (𝓡.right i)
  let ψ : A ⊗[R] A →ₗ[R] B := (TensorProduct.rid R B).toLinearMap
    ∘ₗ TensorProduct.map (π : A →ₐc[R] B).toLinearMap (φ ∘ₗ (π : A →ₐc[R] B).toLinearMap)
  have hψ : ∀ y z : A, ψ (y ⊗ₜ[R] z) = φ (π z) • π y := by intro y z; simp [ψ]; rfl
  have key := congr((ψ.lTensor A) $(sum_tmul_tmul_eq 𝓡 a₁ a₂))
  simp only [map_sum, LinearMap.lTensor_tmul, hψ] at key
  have lhs : coaction π (T π φ a)
      = ∑ i ∈ 𝓡.index, ∑ k ∈ (a₁ i).index,
          (a₁ i).left k ⊗ₜ[R] (φ (π (𝓡.right i)) • π ((a₁ i).right k)) := by
    rw [T_repr π φ 𝓡, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, HopfKerHopf.coaction_repr π (a₁ i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul]
  have rhs : ∀ i ∈ 𝓡.index, ∑ k ∈ (a₂ i).index,
        𝓡.left i ⊗ₜ[R] (φ (π ((a₂ i).right k)) • π ((a₂ i).left k))
      = (φ (π (𝓡.right i)) • 𝓡.left i) ⊗ₜ[R] (1 : B) := by
    intro i _
    rw [← TensorProduct.tmul_sum, TensorProduct.smul_tmul]
    congr 1
    rw [← hφ (π (𝓡.right i)), ← CoalgHomClass.map_comp_comul_apply, ← (a₂ i).eq]
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    rfl
  rw [lhs, key, Finset.sum_congr rfl rhs, T_repr π φ 𝓡, TensorProduct.sum_tmul]

section DualBasis

variable [Module.Finite R B] [Module.Free R B] (hπ : Function.Surjective π)

private noncomputable def nΛ :
    ℕ := (HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit (R := R) (B := B)).choose
private noncomputable def Λ : Fin (nΛ (R := R) (B := B)) → Module.Dual R B :=
  (HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit (R := R) (B := B)).choose_spec.choose
private noncomputable def uΛ : Fin (nΛ (R := R) (B := B)) → B :=
  (HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit (R := R)
      (B := B)).choose_spec.choose_spec.choose
private theorem Λ_integral (j : Fin (nΛ (R := R) (B := B))) (b : B) :
    (TensorProduct.rid R B) ((Λ j).lTensor B (Coalgebra.comul b)) = (Λ (R := R) j b) • (1 : B) :=
  (HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit (R := R)
      (B := B)).choose_spec.choose_spec.choose_spec.1 j b
private theorem Λ_frob (b : B) : ∑ j, Λ (R := R) j (uΛ j * b) = Coalgebra.counit b :=
  (HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit (R := R)
      (B := B)).choose_spec.choose_spec.choose_spec.2 b

include hπ in
private theorem exists_w (j : Fin (nΛ (R := R) (B := B))) : ∃ w :
    A ⊗[R] A, canMap π w = (1 : A) ⊗ₜ[R] uΛ j :=
  HopfAlgebra.canMap_surjective_of_surjective π hπ _

private noncomputable def sw (j : Fin (nΛ (R := R) (B := B))) : Finset (A × A) :=
  (TensorProduct.exists_finset (exists_w π hπ j).choose).choose

private theorem canMap_sw (j : Fin (nΛ (R := R) (B := B))) :
    canMap π (∑ p ∈ sw π hπ j, p.1 ⊗ₜ[R] p.2) = (1 : A) ⊗ₜ[R] uΛ j := by
  change canMap π (∑ p ∈ (TensorProduct.exists_finset (exists_w π hπ j).choose).choose,
      p.1 ⊗ₜ[R] p.2) = _
  rw [← (TensorProduct.exists_finset (exists_w π hπ j).choose).choose_spec]
  exact (exists_w π hπ j).choose_spec

private theorem T_Λ_mem (j : Fin (nΛ (R := R) (B := B))) (a : A) : T π (Λ j) a ∈ hopfKer π :=
  T_mem_hopfKer π (Λ j) (Λ_integral j) a

private theorem sum_sw (j : Fin (nΛ (R := R) (B := B))) (a : A) :
    ∑ p ∈ sw π hπ j, p.1 * T π (Λ j) (p.2 * a) = G (Λ j) (((1 : A) ⊗ₜ[R] uΛ j) * coaction π a) := by
  have : ∀ p ∈ sw π hπ j, p.1 * T π (Λ j) (p.2 * a) = G (Λ j) (canMap π (p.1 ⊗ₜ[R] p.2)
      * coaction π a) := by
    intro p _
    rw [canMap_tmul, mul_assoc, G_includeLeft_mul, T_apply, _root_.map_mul (coaction π)]
  rw [Finset.sum_congr rfl this, ← canMap_sw π hπ j, map_sum, Finset.sum_mul, map_sum]

private theorem dualBasis (a : A) : ∑ j, ∑ p ∈ sw π hπ j, p.1 * T π (Λ j) (p.2 * a) = a := by
  simp_rw [sum_sw π hπ]
  set 𝓡 := ℛ R a
  have h1 : ∀ j, G (Λ (R := R) j) (((1 : A) ⊗ₜ[R] uΛ j) * coaction π a)
      = ∑ i ∈ 𝓡.index, Λ (R := R) j (uΛ j * π (𝓡.right i)) • 𝓡.left i := by
    intro j
    rw [HopfKerHopf.coaction_repr π 𝓡, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, G_tmul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, Λ_frob, CoalgHomClass.counit_comp_apply]
  simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using
    congr(TensorProduct.rid R A $(sum_tmul_counit_eq (R := R) 𝓡))

end DualBasis



section Galois

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
variable (π : A →ₐc[R] B) (hπ : Function.Surjective π)

private noncomputable def Θ : A ⊗[R] B →ₗ[R] A ⊗[R] A :=
  ∑ j, ∑ p ∈ sw π hπ j, (TensorProduct.mk R A A).flip p.1 ∘ₗ G (Λ
      j) ∘ₗ LinearMap.mulLeft R (coaction π p.2)

private theorem Θ_canMap_tmul (x y : A) :
    Θ π hπ (canMap π (x ⊗ₜ[R] y)) = ∑ j, ∑ p ∈ sw π hπ j, (x * T π (Λ j) (p.2 * y)) ⊗ₜ[R] p.1 := by
  simp only [Θ, LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [canMap_tmul, mul_left_comm, G_includeLeft_mul, T_apply, _root_.map_mul (coaction π)]

private theorem Θ_canMap_sub_mem (z : A ⊗[R] A) :
    Θ π hπ (canMap π z) - z ∈ Submodule.span R (balancingRelations π) := by
  induction z with
  | add x y hx hy =>
      have : Θ π hπ (canMap π (x + y)) - (x + y)
          = (Θ π hπ (canMap π x) - x) + (Θ π hπ (canMap π y) - y) := by
        rw [map_add, map_add]; abel
      rw [this]; exact Submodule.add_mem _ hx hy
  | tmul x y =>
      have hxy : x ⊗ₜ[R] y = ∑ j, ∑ p ∈ sw π hπ j, x ⊗ₜ[R] (p.1 * T π (Λ j) (p.2 * y)) := by
        conv_lhs => rw [← dualBasis π hπ y]
        simp only [TensorProduct.tmul_sum]
      rw [Θ_canMap_tmul, hxy, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun p _ => ?_
      refine Submodule.subset_span ⟨x, T π (Λ j) (p.2 * y), p.1, T_Λ_mem π j (p.2 * y), ?_⟩
      rw [mul_comm p.1]

include hπ in
private theorem isHopfGalois : IsHopfGalois π := by
  refine ⟨HopfAlgebra.canMap_surjective_of_surjective π hπ, fun z hz => ?_⟩
  have h := Θ_canMap_sub_mem π hπ z
  rw [hz, map_zero, zero_sub] at h
  simpa using Submodule.neg_mem _ h



end Galois

section Projective

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
variable (π : A →ₐc[R] B) (hπ : Function.Surjective π)

private abbrev K : Type v := Σ j : Fin (nΛ (R := R) (B := B)), ↥(sw π hπ j)

private noncomputable def tK (k : K π hπ) : A →ₗ[↥(hopfKer π)] ↥(hopfKer π) where
  toFun a := ⟨T π (Λ k.1) (k.2.1.2 * a), T_Λ_mem π k.1 _⟩
  map_add' a a' := by ext; simp [mul_add, map_add]
  map_smul' s a := by
    ext
    simp only [Subalgebra.smul_def, smul_eq_mul, RingHom.id_apply, Subalgebra.coe_mul]
    rw [mul_left_comm, T_mul_of_mem π (Λ k.1) s.2]

@[local simp] private theorem tK_apply_coe (k : K π hπ) (a : A) :
    (tK π hπ k a : A) = T π (Λ k.1) (k.2.1.2 * a) := rfl

private noncomputable def coordK : A →ₗ[↥(hopfKer π)] (K π hπ → ↥(hopfKer π)) :=
  LinearMap.pi (tK π hπ)

private noncomputable def recombK : (K π hπ → ↥(hopfKer π)) →ₗ[↥(hopfKer π)] A :=
  ∑ k : K π hπ, (LinearMap.proj k :
      (K π hπ → ↥(hopfKer π)) →ₗ[↥(hopfKer π)] ↥(hopfKer π)).smulRight (k.2.1.1 : A)

private theorem recombK_coordK : (recombK π hπ).comp (coordK π hπ) = LinearMap.id := by
  ext a
  simp only [recombK, coordK, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, LinearMap.pi_apply, LinearMap.id_apply,
    Subalgebra.smul_def, tK_apply_coe, smul_eq_mul]
  rw [Fintype.sum_sigma]
  conv_rhs => rw [← dualBasis π hπ a]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_coe_sort (sw π hπ j)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_comm]

include hπ in
private theorem finite_projective :
    Module.Finite ↥(hopfKer π) A ∧ Module.Projective ↥(hopfKer π) A :=
  ⟨Module.Finite.of_surjective (recombK π hπ)
      (fun a => ⟨coordK π hπ a, congr($(recombK_coordK π hπ) a)⟩),
    Module.Projective.of_split (coordK π hπ) (recombK π hπ) (recombK_coordK π hπ)⟩

end Projective

end HopfAlgebra.HopfGaloisAux

namespace HopfAlgebra

open HopfGaloisAux

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
  {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]

/-- **Surjections onto finite free Hopf algebras are Hopf–Galois.** Let `R` be a commutative
ring, and `A`, `B` commutative Hopf algebras over `R` with `B` finite and free as an `R`-module.
Every surjective bialgebra map `π : A →ₐc[R] B` is Hopf–Galois (`HopfAlgebra.IsHopfGalois`): its
canonical map is surjective and its kernel is spanned by the balancing relations over the Hopf
kernel of `π`. -/
theorem isHopfGalois_of_surjective (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    IsHopfGalois π :=
  isHopfGalois π hπ

/-- **Finite projectivity over the Hopf kernel.** Let `R` be a commutative ring, and `A`, `B`
commutative Hopf algebras over `R` with `B` finite and free as an `R`-module. For a surjective
bialgebra map `π : A →ₐc[R] B`, `A` is a finite projective module over the Hopf kernel
`HopfAlgebra.hopfKer π`. -/
theorem finite_projective_hopfKer_of_surjective (π : A →ₐc[R] B)
    (hπ : Function.Surjective π) :
    Module.Finite ↥(hopfKer π) A ∧ Module.Projective ↥(hopfKer π) A :=
  finite_projective π hπ

end HopfAlgebra
