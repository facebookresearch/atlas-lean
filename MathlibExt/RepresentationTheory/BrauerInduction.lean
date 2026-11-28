/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean`
and
`P2M/Sol/S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.RepresentationTheory.ClassFunctionInduced
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
import MathlibExt.RepresentationTheory.MonomialCharacter
import MathlibExt.RepresentationTheory.SolomonInduction

/-!
# Brauer's induction theorem

Every character of a finite group `G` is an integer combination of characters induced from
linear characters of subgroups: for every representation `ρ : G →* GL (Fin n) ℂ` there are
subgroups `H i`, homomorphisms `ψ i : H i →* ℂˣ` and integers `a i` with
`trace (ρ g) = ∑ i, a i * Ind_{H i}^G (ψ i) g` for all `g`. The subgroups `H i` are arbitrary;
they are not required to be elementary.

The proof combines Solomon's induction theorem
(`ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary`), which writes `1` as
an integer combination of permutation characters `Ind_H^G 1` over hyperelementary `H`, with the
projection formula `Ind_H^G 1 * χ = Ind_H^G (χ|_H)` and the monomial theorem for
hyperelementary groups
(`ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem`,
applied with the cyclic normal subgroup), followed by transitivity of induction.

## Main results

* `BrauerInduction.exists_trace_eq_sum_zsmul_induced`: the statement in terms of
  `ClassFunction.induced`.
* `BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter`: the same statement with
  the Frobenius formula for the induced characters written out.
-/

@[expose] public section

noncomputable section

universe u

open scoped MatrixGroups

namespace BrauerInduction

namespace BrauerProof

variable {G : Type u} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ)

private def chi : G → ℂ := fun g => ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace

omit [Fintype G] in
private theorem chi_conj (x g : G) : chi ρ (x⁻¹ * g * x) = chi ρ g := by
  simp only [chi, map_mul, Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
    mul_inv_cancel, one_mul]

open scoped Classical in
private def ext (L : Subgroup G) (ψ : L →* ℂˣ) : G → ℂ :=
  fun x => if hx : x ∈ L then ((ψ ⟨x, hx⟩ : ℂˣ) : ℂ) else 0

open scoped Classical in
private theorem induced_ext_apply (L : Subgroup G) (ψ : L →* ℂˣ) (g : G) :
    ClassFunction.induced L (ext L ψ) g =
      (Nat.card L : ℂ)⁻¹ *
        ∑ x : G, if hx : x⁻¹ * g * x ∈ L then (((ψ ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ)) else 0 := by
  rw [ClassFunction.induced_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x⁻¹ * g * x ∈ L
  · rw [ite_eq_left hx, dite_eq_left hx, ext]
    rw [dite_eq_left hx]
  · rw [ite_eq_right hx, dite_eq_right hx]

open scoped Classical in
private theorem solomon_complex :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (a : Fin k → ℤ),
      (∀ i, ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H i ∧ IsCyclic C ∧ (Nat.card C).Coprime q ∧
        (∀ h ∈ H i, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H i, ∃ m : ℕ, h ^ q ^ m ∈ C)) ∧
      ∀ g : G, (1 : ℂ) = ∑ i, (a i : ℂ) * ClassFunction.induced (H i) (fun _ => (1 : ℂ)) g := by
  obtain ⟨k, H, a, hH, h1⟩ :=
    ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary (G := G)
  refine ⟨k, H, a, hH, fun g => ?_⟩
  have hcast : ∀ i, ((ClassFunction.induced (H i) (fun _ => (1 : ℚ)) g : ℚ) : ℂ) =
      ClassFunction.induced (H i) (fun _ => (1 : ℂ)) g := by
    intro i
    rw [ClassFunction.induced_apply, ClassFunction.induced_apply]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have := congrArg (fun r : ℚ => (r : ℂ)) (h1 g)
  simp only [Rat.cast_one, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, hcast] at this
  exact this

open scoped Classical in
private theorem induced_chi_hyper (H : Subgroup G)
    (hH : ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H ∧ IsCyclic C ∧ (Nat.card C).Coprime q ∧
      (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H, ∃ m : ℕ, h ^ q ^ m ∈ C)) :
    ∃ (k : ℕ) (L : Fin k → Subgroup G) (ψ : (j : Fin k) → (L j →* ℂˣ)),
      ∀ g : G, ClassFunction.induced H (chi ρ) g =
        ∑ j, ClassFunction.induced (L j) (ext (L j) (ψ j)) g := by
  obtain ⟨q, hq, C, hCH, hCcyc, -, hCnorm, hCpow⟩ := hH
  let A : Subgroup H := C.subgroupOf H
  have hAn : A.Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hCnorm h h.2 a ha
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    have := hCcyc
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := C)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ ⟨b, hb⟩)
    have hc : (⟨a, ha⟩ : C) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      rw [← hi, ← hj]; exact zpow_mul_comm g₀ i j
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at hc'
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hc')
  have hApow : ∀ h : H, ∃ m : ℕ, h ^ q ^ m ∈ A := by
    intro h
    obtain ⟨m, hm⟩ := hCpow h h.2
    exact ⟨m, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact hm⟩
  obtain ⟨k, L, ψ, hL⟩ :=
    ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
      hq A hAn hAcomm hApow (ρ.comp H.subtype)
  set extH : (j : Fin k) → (H → ℂ) := fun j x =>
    if hx : x ∈ L j then (((ψ j) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0 with hextH
  let L' : Fin k → Subgroup G := fun j => (L j).map H.subtype
  let ψ' : (j : Fin k) → (L' j →* ℂˣ) := fun j =>
    (ψ j).comp ((L j).equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom
  refine ⟨k, L', ψ', fun g => ?_⟩
  have step1 : ClassFunction.induced H (chi ρ) =
      ClassFunction.induced H (fun x => ∑ j, (fun y : G =>
        if hy : y ∈ H then ClassFunction.induced (L j) (extH j) ⟨y, hy⟩ else 0) x) := by
    apply ClassFunction.induced_congr
    intro y hy
    have := hL ⟨y, hy⟩
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at this
    rw [chi]
    beta_reduce
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dite_eq_left hy]
  rw [step1, ClassFunction.induced_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ClassFunction.induced_induced H (L j) (extH j)]
  apply congrFun (ClassFunction.induced_congr _ ?_) g
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  simp only [Subgroup.coe_subtype, SetLike.coe_mem, ↓reduceDIte]
  have hz' : (⟨(z : G), z.2⟩ : H) ∈ L j := by simpa using hz
  have hmem : (z : G) ∈ L' j := ⟨z, hz, rfl⟩
  simp only [hextH, ext, dite_eq_left hz', dite_eq_left hmem]
  change _ = (((ψ j) (((L j).equivMapOfInjective H.subtype H.subtype_injective).symm
    ⟨(z : G), hmem⟩) : ℂˣ) : ℂ)
  congr 2
  apply ((L j).equivMapOfInjective H.subtype H.subtype_injective).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rfl

private theorem main :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, chi ρ g = ∑ i, (a i : ℂ) * ClassFunction.induced (H i) (ext (H i) (ψ i)) g := by
  obtain ⟨k, H, a, hH, h1⟩ := solomon_complex (G := G)
  have h2 : ∀ g : G, chi ρ g = ∑ i, (a i : ℂ) * ClassFunction.induced (H i) (chi ρ) g := by
    intro g
    have := congrArg (fun t => t * chi ρ g) (h1 g)
    simp only [one_mul, Finset.sum_mul, mul_assoc] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ClassFunction.induced_mul_of_conj_invariant (H i) _ _ (chi_conj ρ) g]
    simp only [one_mul]
  have h3 := fun i => induced_chi_hyper ρ (H i) (hH i)
  choose kf Lf ψf hf using h3
  let ι := Σ i : Fin k, Fin (kf i)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun m => Lf (e.symm m).1 (e.symm m).2,
    fun m => ψf (e.symm m).1 (e.symm m).2, fun m => a (e.symm m).1, fun g => ?_⟩
  rw [h2 g]
  simp_rw [hf]
  rw [Equiv.sum_comp e.symm (fun s : ι => (a s.1 : ℂ) *
      ClassFunction.induced (Lf s.1 s.2) (ext (Lf s.1 s.2) (ψf s.1 s.2)) g)]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

end BrauerProof

open scoped Classical in
/-- **Brauer's induction theorem for arbitrary subgroups.** For a finite group `G` and a
complex representation `ρ : G →* GL (Fin n) ℂ`, there are finitely many subgroups `H i`, linear
characters `ψ i : H i →* ℂˣ` and integers `a i : ℤ` such that the character `g ↦ trace (ρ g)`
is `∑ i, a i * induced (H i) (ψ i)`, each `ψ i` extended by zero off `H i` and induced over
`ℂ`. Written out by the Frobenius formula, this says that for all `g : G`,
`trace (ρ g) = ∑ i, a i * (|H i|⁻¹ * ∑ x : G, [x⁻¹ * g * x ∈ H i] * ψ i (x⁻¹ * g * x))`,
which is `BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter`. The subgroups
`H i` need not be elementary. -/
public theorem exists_trace_eq_sum_zsmul_induced
    {G : Type u} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, (a i : ℂ) * ClassFunction.induced (H i)
          (fun x => if hx : x ∈ H i then (((ψ i) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0) g :=
  BrauerProof.main ρ

/- The statement of `BrauerInduction.exists_trace_eq_sum_zsmul_induced` with
`ClassFunction.induced` written out by the Frobenius formula, as the cited source states
Brauer's induction theorem: the same hypotheses and the same witnesses. -/
open scoped Classical in
public theorem exists_trace_eq_sum_zsmul_induced_linearCharacter
    {G : Type u} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
          ∑ x : G, if hx : x⁻¹ * g * x ∈ H i then (((ψ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ)
            else 0) := by
  obtain ⟨k, H, ψ, a, h⟩ := BrauerProof.main ρ
  refine ⟨k, H, ψ, a, fun g => ?_⟩
  have := h g
  rw [BrauerProof.chi] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BrauerProof.induced_ext_apply]

end BrauerInduction

end
