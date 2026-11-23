/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow.lean`
and
`P2M/Sol/S_MvPolynomial_finrank_piece_succ_le_macaulayPow.lean`
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

public import MathlibExt.AlgebraicGeometry.HilbertFunctorPoint
public import MathlibExt.Combinatorics.Enumerative.MacaulayPow
public import Mathlib.LinearAlgebra.Dimension.Finrank
import MathlibExt.Combinatorics.Enumerative.MacaulayBound
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Tactic.Push

/-!
# Macaulay's bound on the growth of Hilbert functions

For an ideal `J` of the polynomial ring `K[X₀, …, Xₙ]` over a field, closed under homogeneous
components, let `h(d)` be the dimension of `AlgebraicGeometry.HilbertFunctor.piece J d`, the
degree-`d` homogeneous polynomials modulo those lying in `J`. Macaulay's theorem bounds the next
value: `h(d + 1) ≤ h(d)^⟨d⟩` for `d ≥ 1`, where `·^⟨d⟩` is `Nat.macaulayPow d`.

The proof passes to lexicographic leading monomials: the standard monomials of degree `d + 1`
have all their degree-`d` divisors standard, so the bound follows from
`Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem`.

## Main declarations

* `MvPolynomial.finrank_piece_succ_le_macaulayPow`: Macaulay's bound.
-/

namespace MvPolynomial

namespace MacaulayGrowthAux

open AlgebraicGeometry.HilbertFunctor

variable (n : ℕ)

/-- The monomials of degree `e` in `n + 1` variables. -/
private noncomputable def Mon (e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
    (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm)).toFinset

private theorem mem_Mon (e : ℕ) (m : Fin (n + 1) →₀ ℕ) : m ∈ Mon n e ↔ m.degree = e := by
  simp [Mon]

/-- The lexicographic monomial order on `n + 1` variables. -/
private noncomputable def lex : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex

variable (K : Type*) [Field K]

private theorem degree_eq_of_mem_support {e : ℕ} {p : MvPolynomial (Fin (n + 1)) K}
    (hp : p.IsHomogeneous e) {m : Fin (n + 1) →₀ ℕ} (hm : m ∈ p.support) : m.degree = e := by
  have h : p ∈ homogeneousSubmodule (Fin (n + 1)) K e := hp
  rw [homogeneousSubmodule_eq_finsupp_supported] at h
  exact h hm

/-- The lexicographic leading monomials of the nonzero degree-`e` homogeneous elements of `J`. -/
private noncomputable def LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Finset (Fin (n + 1) →₀ ℕ) := by
  classical
  exact (Mon n e).filter fun a => ∃ f : MvPolynomial (Fin (n + 1)) K,
    f ∈ J ∧ f.IsHomogeneous e ∧ f ≠ 0 ∧ (lex n).degree f = a

private theorem mem_LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ)
    (a : Fin (n + 1) →₀ ℕ) :
    a ∈ LM n K J e ↔ a.degree = e ∧ ∃ f : MvPolynomial (Fin (n + 1)) K,
      f ∈ J ∧ f.IsHomogeneous e ∧ f ≠ 0 ∧ (lex n).degree f = a := by
  classical
  simp [LM, mem_Mon]

private theorem LM_subset (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    LM n K J e ⊆ Mon n e := by
  classical
  intro a ha; unfold LM at ha; exact (Finset.mem_filter.1 ha).1

private theorem degree_mem_LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ)
    {f : MvPolynomial (Fin (n + 1)) K} (hfJ : f ∈ J) (hf : f.IsHomogeneous e) (hf0 : f ≠ 0) :
    (lex n).degree f ∈ LM n K J e := by
  rw [mem_LM]
  exact ⟨degree_eq_of_mem_support n K hf ((lex n).degree_mem_support hf0), f, hfJ, hf, hf0, rfl⟩

private theorem add_single_mem_LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (d : ℕ)
    {a : Fin (n + 1) →₀ ℕ} (ha : a ∈ LM n K J d) (i : Fin (n + 1)) :
    a + Finsupp.single i 1 ∈ LM n K J (d + 1) := by
  rw [mem_LM] at ha
  obtain ⟨-, f, hfJ, hf, hf0, hfa⟩ := ha
  have h1 : f * X i ∈ J := Ideal.mul_mem_right _ _ hfJ
  have h2 : (f * X i).IsHomogeneous (d + 1) := hf.mul (isHomogeneous_X K i)
  have h3 : f * X i ≠ 0 := mul_ne_zero hf0 (X_ne_zero i)
  have h4 : (lex n).degree (f * X i) = a + Finsupp.single i 1 := by
    rw [MonomialOrder.degree_mul hf0 (X_ne_zero i), MonomialOrder.degree_X, hfa]
  rw [← h4]
  exact degree_mem_LM n K J (d + 1) h1 h2 h3

/-- The degree-`e` homogeneous elements of `J`, as a subspace of the degree-`e` piece. -/
private noncomputable def W (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Submodule K ↥(homogeneousSubmodule (Fin (n + 1)) K e) :=
  Submodule.comap (homogeneousSubmodule (Fin (n + 1)) K e).subtype (J.restrictScalars K)

private theorem mem_W (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ)
    (p : ↥(homogeneousSubmodule (Fin (n + 1)) K e)) :
    p ∈ W n K J e ↔ (p : MvPolynomial _ K) ∈ J :=
  Iff.rfl

private theorem finite_homogeneousSubmodule (e : ℕ) :
    Module.Finite K ↥(homogeneousSubmodule (Fin (n + 1)) K e) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  have : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = e} :=
    ((Finsupp.finite_of_degree_le e).subset fun x (hx : x.degree = e) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis
    (MvPolynomial.basisRestrictSupport K {x : Fin (n + 1) →₀ ℕ | x.degree = e})

attribute [local instance] finite_homogeneousSubmodule

private theorem finrank_homogeneousSubmodule (e : ℕ) :
    Module.finrank K ↥(homogeneousSubmodule (Fin (n + 1)) K e) = (Mon n e).card := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  refine (Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport K {x : Fin (n + 1) →₀ ℕ | x.degree = e})).trans ?_
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _
    ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
      (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm))]
  rfl

private theorem finrank_W_le (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K ↥(W n K J e) ≤ (LM n K J e).card := by
  classical
  let ψ : ↥(W n K J e) →ₗ[K] (↥(LM n K J e) → K) :=
    { toFun := fun p a => (p.1 : MvPolynomial (Fin (n + 1)) K).coeff a.1
      map_add' := fun p q => by ext a; simp
      map_smul' := fun c p => by ext a; simp }
  have hker : LinearMap.ker ψ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun p hp => ?_
    rw [LinearMap.mem_ker] at hp
    by_contra hp0
    have hf0 : (p.1 : MvPolynomial (Fin (n + 1)) K) ≠ 0 := by
      intro h; apply hp0
      exact Subtype.ext (Subtype.ext h)
    have hmem := degree_mem_LM n K J e ((mem_W n K J e p.1).1 p.2) p.1.2 hf0
    have := congrFun hp ⟨_, hmem⟩
    rw [Pi.zero_apply] at this
    change (p.1 : MvPolynomial (Fin (n + 1)) K).coeff
      ((lex n).degree (p.1 : MvPolynomial (Fin (n + 1)) K)) = 0 at this
    exact ((lex n).leadingCoeff_ne_zero_iff.2 hf0) this
  have hψ : Function.Injective ψ :=
    (LinearMap.ker_eq_bot (M := ↥(W n K J e)) (M₂ := (↥(LM n K J e) → K)) (f := ψ)).1 hker
  have := LinearMap.finrank_le_finrank_of_injective hψ
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this

private theorem linearIndependent_of_degree_eq (s : Finset (Fin (n + 1) →₀ ℕ))
    (g : ↥s → MvPolynomial (Fin (n + 1)) K) (hg0 : ∀ a, g a ≠ 0)
    (hg : ∀ a, (lex n).degree (g a) = a.1) : LinearIndependent K g := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  set t : Finset ↥s := Finset.univ.filter fun a => c a ≠ 0 with ht
  have htne : t.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, by simp [ht, ha]⟩
  obtain ⟨a₀, ha₀, hmax⟩ := t.exists_max_image (fun a => (lex n).toSyn a.1) htne
  have hca₀ : c a₀ ≠ 0 := by simpa [ht] using ha₀
  have hcoeff : (∑ a, c a • g a).coeff a₀.1 = c a₀ * (lex n).leadingCoeff (g a₀) := by
    rw [coeff_sum, Finset.sum_eq_single a₀]
    · rw [coeff_smul, smul_eq_mul, MonomialOrder.leadingCoeff, hg a₀]
    · intro a _ haa
      by_cases hca : c a = 0
      · simp [hca]
      · have hle : (lex n).toSyn a.1 ≤ (lex n).toSyn a₀.1 := hmax a (by simp [ht, hca])
        have hlt : (lex n).toSyn a.1 < (lex n).toSyn a₀.1 := by
          refine lt_of_le_of_ne hle fun h => haa ?_
          exact Subtype.ext ((lex n).toSyn.injective h)
        rw [coeff_smul, (lex n).coeff_eq_zero_of_lt (by rw [hg a]; exact hlt), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hc, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
  exact mul_ne_zero hca₀ ((lex n).leadingCoeff_ne_zero_iff.2 (hg0 a₀)) hcoeff.symm

private theorem card_LM_le (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    (LM n K J e).card ≤ Module.finrank K ↥(W n K J e) := by
  classical
  have hex : ∀ a : ↥(LM n K J e), ∃ f : MvPolynomial (Fin (n + 1)) K,
      f ∈ J ∧ f.IsHomogeneous e ∧ f ≠ 0 ∧ (lex n).degree f = a.1 := fun a =>
    ((mem_LM n K J e a.1).1 a.2).2
  choose f hfJ hfh hf0 hfd using hex
  let g : ↥(LM n K J e) → ↥(W n K J e) := fun a =>
    ⟨⟨f a, hfh a⟩, (mem_W n K J e _).2 (hfJ a)⟩
  have hli : LinearIndependent K g := by
    apply LinearIndependent.of_comp
      ((homogeneousSubmodule (Fin (n + 1)) K e).subtype.comp (W n K J e).subtype)
    exact linearIndependent_of_degree_eq n K _ (fun a => f a) hf0 hfd
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_coe] at this

private theorem finrank_W (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K ↥(W n K J e) = (LM n K J e).card :=
  le_antisymm (finrank_W_le n K J e) (card_LM_le n K J e)

private theorem finrank_piece_add (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K (piece J e) + (LM n K J e).card = (Mon n e).card := by
  rw [← finrank_W n K J e, ← finrank_homogeneousSubmodule n K e]
  exact Submodule.finrank_quotient_add_finrank (W n K J e)

end MacaulayGrowthAux

end MvPolynomial

@[expose] public section

namespace MvPolynomial

open AlgebraicGeometry.HilbertFunctor MacaulayGrowthAux in
/-- **Macaulay's bound** on the growth of the Hilbert function: for an ideal `J` of
`K[X₀, …, Xₙ]` closed under homogeneous components and `d ≥ 1`, the dimension of the
degree-`(d + 1)` piece of the quotient is at most `h^⟨d⟩`, where `h` is the dimension of the
degree-`d` piece. The proof does not use the homogeneity hypothesis, which is kept to match the
source statement. -/
public theorem finrank_piece_succ_le_macaulayPow
    (n d : ℕ) (hd : 1 ≤ d) (K : Type*) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (_hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    Module.finrank K (piece J (d + 1)) ≤ Nat.macaulayPow d (Module.finrank K (piece J d)) := by
  classical
  set B : Finset (Fin (n + 1) →₀ ℕ) := Mon n d \ LM n K J d with hB
  set C : Finset (Fin (n + 1) →₀ ℕ) := Mon n (d + 1) \ LM n K J (d + 1) with hC
  have hBcard : B.card + (LM n K J d).card = (Mon n d).card := by
    rw [hB, Finset.card_sdiff_add_card_eq_card (LM_subset n K J d)]
  have hCcard : C.card + (LM n K J (d + 1)).card = (Mon n (d + 1)).card := by
    rw [hC, Finset.card_sdiff_add_card_eq_card (LM_subset n K J (d + 1))]
  have hd₀ := finrank_piece_add n K J d
  have hd₁ := finrank_piece_add n K J (d + 1)
  have h1 : Module.finrank K (piece J (d + 1)) = C.card := by omega
  have h2 : Module.finrank K (piece J d) = B.card := by omega
  rw [h1, h2]
  refine Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem n d hd B
    (fun m hm => (mem_Mon n d m).1 (Finset.mem_sdiff.1 hm).1) C
    (fun u hu => (mem_Mon n (d + 1) u).1 (Finset.mem_sdiff.1 hu).1) fun u hu i hi => ?_
  obtain ⟨hu, huA⟩ := Finset.mem_sdiff.1 hu
  rw [mem_Mon] at hu
  refine Finset.mem_sdiff.2 ⟨(mem_Mon n d _).2 ?_, fun hA => huA ?_⟩
  · have h := Finsupp.sub_add_single_one_cancel (u := u) (i := i) (by omega)
    have := congrArg Finsupp.degree h
    rw [map_add, Finsupp.degree_single, hu] at this
    omega
  · have := add_single_mem_LM n K J d hA i
    rwa [Finsupp.sub_add_single_one_cancel (by omega)] at this

end MvPolynomial
