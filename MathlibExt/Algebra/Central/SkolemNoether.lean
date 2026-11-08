/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Skolem–Noether theorem

Every automorphism of a finite-dimensional central simple algebra is inner.

Proves `Wanted` entry `skolem_noether`.
-/

open TensorProduct

@[expose] public section

namespace MathlibExt.Algebra.Central.SkolemNoether

/-- `A ⊗[k] B` is simple when `A` is central simple over `k` and `B` is simple. -/
private theorem tensor_simple_of_central_simple
    {k : Type*} {A : Type*} {B : Type*} [Field k]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
    [Ring B] [Algebra k B] [IsSimpleRing B] :
    IsSimpleRing (A ⊗[k] B) := by
  classical
  set e : Module.Basis (Module.Free.ChooseBasisIndex k B) k B :=
    Module.Free.chooseBasis k B with he
  have hnt : Nontrivial (A ⊗[k] B) := by
    obtain ⟨a0, ha0⟩ := exists_ne (0 : A)
    obtain ⟨b0, hb0⟩ := exists_ne (0 : B)
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hb0
    refine ⟨a0 ⊗ₜ[k] b0, 0, fun h => ha0 ?_⟩
    have h2 := congrArg (TensorProduct.map LinearMap.id φ) h
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hφ] at h2
    have h3 := congrArg (TensorProduct.rid k A) h2
    rw [map_zero] at h3
    simpa using h3
  have := hnt
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    obtain ⟨z, hzI, hz0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
    have hz : z ≠ 0 := fun h => hz0 ((TwoSidedIdeal.mem_bot _).mpr h)
    obtain ⟨d, hd⟩ := TensorProduct.eq_repr_basis_right e z
    have H : ∃ n : ℕ, ∃ y : A ⊗[k] B, ∃ s : Finset (Module.Free.ChooseBasisIndex k B),
        ∃ c : (Module.Free.ChooseBasisIndex k B) → A,
        y ∈ I ∧ y ≠ 0 ∧ s.sum (fun i => c i ⊗ₜ[k] e i) = y ∧ s.card = n :=
      ⟨d.support.card, z, d.support, (fun i => d i), hzI, hz, hd, rfl⟩
    set N := Nat.find H with hN
    obtain ⟨y0, s0, c0, hy0I, hy0ne, hs0, hcard0⟩ := Nat.find_spec H
    have hmin : ∀ (y : A ⊗[k] B) (s : Finset (Module.Free.ChooseBasisIndex k B))
        (c : (Module.Free.ChooseBasisIndex k B) → A),
        y ∈ I → y ≠ 0 → s.sum (fun i => c i ⊗ₜ[k] e i) = y → N ≤ s.card := by
      intro y s c hyI hyne hys
      by_contra hle
      push Not at hle
      exact Nat.find_min H hle ⟨y, s, c, hyI, hyne, hys, rfl⟩
    have hsne : s0.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.sum_empty] at hs0
      exact hy0ne hs0.symm
    have hcoeff : ∀ i ∈ s0, c0 i ≠ 0 := by
      intro i hi hcon
      have her : y0 = (s0.erase i).sum (fun j => c0 j ⊗ₜ[k] e j) := by
        rw [← hs0, ← Finset.add_sum_erase _ _ hi, hcon, TensorProduct.zero_tmul,
          zero_add]
      have hcard : (s0.erase i).card < N := by
        have h1 : (s0.erase i).card = s0.card - 1 := Finset.card_erase_of_mem hi
        have h2 : 0 < s0.card := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      have hle := hmin y0 (s0.erase i) c0 hy0I hy0ne her.symm
      omega
    obtain ⟨i0, hi0⟩ := hsne
    have hdi0 : c0 i0 ≠ 0 := hcoeff i0 hi0
    have hspan : TwoSidedIdeal.span ({c0 i0} : Set A) = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top (TwoSidedIdeal.span {c0 i0}) with h | h
      · exfalso
        have hmem : c0 i0 ∈ TwoSidedIdeal.span ({c0 i0} : Set A) :=
          TwoSidedIdeal.subset_span rfl
        rw [h] at hmem
        exact hdi0 ((TwoSidedIdeal.mem_bot A).mp hmem)
      · exact h
    have h1mem : (1 : A) ∈ TwoSidedIdeal.span ({c0 i0} : Set A) := by
      rw [hspan]; exact TwoSidedIdeal.mem_top A
    obtain ⟨n, pp, qq, h1⟩ := TwoSidedIdeal.span_induction (s := ({c0 i0} : Set A))
      (p := fun x _ => ∃ n : ℕ, ∃ p q : Fin n → A, x = ∑ j, p j * c0 i0 * q j)
      (mem := fun x hx => ⟨1, ![1], ![1], by
        rw [Set.mem_singleton_iff.mp hx]; simp⟩)
      (zero := ⟨1, ![0], ![0], by simp⟩)
      (add := fun x y _ _ ⟨n₁, p₁, q₁, hx⟩ ⟨n₂, p₂, q₂, hy⟩ =>
        ⟨n₁ + n₂, Fin.append p₁ p₂, Fin.append q₁ q₂, by
          rw [hx, hy, Fin.sum_univ_add]
          simp [Fin.append_left, Fin.append_right]⟩)
      (neg := fun x _ ⟨nn, ppp, qqq, hx⟩ =>
        ⟨nn, fun j => -ppp j, qqq, by
          rw [hx]; simp_rw [neg_mul]; rw [Finset.sum_neg_distrib]⟩)
      (left_absorb := fun a x _ ⟨nn, ppp, qqq, hx⟩ =>
        ⟨nn, fun j => a * ppp j, qqq, by
          rw [hx, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [mul_assoc]⟩)
      (right_absorb := fun b x _ ⟨nn, ppp, qqq, hx⟩ =>
        ⟨nn, ppp, fun j => qqq j * b, by
          rw [hx, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          simp only [mul_assoc]⟩)
      h1mem
    -- uniqueness of coefficients in basis e
    have uniq : ∀ (s : Finset (Module.Free.ChooseBasisIndex k B))
        (c : (Module.Free.ChooseBasisIndex k B) → A),
        s.sum (fun i => c i ⊗ₜ[k] e i) = 0 → ∀ i ∈ s, c i = 0 := by
      intro s c h i hi
      have h2 := congrArg (TensorProduct.equivFinsuppOfBasisRight e) h
      rw [map_sum] at h2
      have h3 := congrArg (fun f : (Module.Free.ChooseBasisIndex k B) →₀ A => f i) h2
      simp only [Finsupp.finsetSum_apply, map_zero, Finsupp.zero_apply] at h3
      simp_rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        Module.Basis.repr_self] at h3
      have hterm : ∀ j ∈ s, j ≠ i → (Finsupp.single j (1 : k)) i • c j = 0 := by
        intro j _ hji
        simp only [Finsupp.single_apply, hji, ite_false, zero_smul]
      rw [Finset.sum_eq_single i hterm (fun h' => (h' hi).elim)] at h3
      rw [Finsupp.single_eq_same, one_smul] at h3
      exact h3
    -- the normalized element y1, with i0-coefficient 1
    have hcoeff1 : (∑ j : Fin n, pp j * c0 i0 * qq j) = 1 := h1.symm
    set y1 : A ⊗[k] B :=
      ∑ j : Fin n, ((pp j ⊗ₜ[k] (1 : B)) * y0 * (qq j ⊗ₜ[k] (1 : B))) with hy1
    have hy1I : y1 ∈ I := by
      rw [hy1]
      exact sum_mem fun j _ =>
        TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hy0I)
    have hy1exp : y1
        = s0.sum (fun i => (∑ j : Fin n, pp j * c0 i * qq j) ⊗ₜ[k] e i) := by
      rw [hy1, ← hs0]
      simp_rw [Finset.mul_sum, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← TensorProduct.sum_tmul]
    have hy1ne : y1 ≠ 0 := by
      intro hcon
      have h0' : (∑ j : Fin n, pp j * c0 i0 * qq j) = 0 :=
        uniq s0 (fun i => ∑ j : Fin n, pp j * c0 i * qq j) (hy1exp.symm.trans hcon) i0 hi0
      rw [hcoeff1] at h0'
      exact one_ne_zero h0'
    -- commutator representation
    have hrep : ∀ c : A, (c ⊗ₜ[k] (1 : B)) * y1 - y1 * (c ⊗ₜ[k] (1 : B))
        = (s0.erase i0).sum (fun i => (c * (∑ j : Fin n, pp j * c0 i * qq j)
          - (∑ j : Fin n, pp j * c0 i * qq j) * c) ⊗ₜ[k] e i) := by
      intro c
      have hstep : (c ⊗ₜ[k] (1 : B)) * y1 - y1 * (c ⊗ₜ[k] (1 : B))
          = s0.sum (fun i => (c * (∑ j : Fin n, pp j * c0 i * qq j)
            - (∑ j : Fin n, pp j * c0 i * qq j) * c) ⊗ₜ[k] e i) := by
        rw [hy1exp, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul, mul_one, ← TensorProduct.sub_tmul]
      have hi0term : (c * (∑ j : Fin n, pp j * c0 i0 * qq j)
          - (∑ j : Fin n, pp j * c0 i0 * qq j) * c) ⊗ₜ[k] e i0 = 0 := by
        rw [hcoeff1, mul_one, one_mul, sub_self, TensorProduct.zero_tmul]
      rw [hstep, ← Finset.add_sum_erase _ _ hi0, hi0term, zero_add]
    have hcomm0 : ∀ c : A, (c ⊗ₜ[k] (1 : B)) * y1 - y1 * (c ⊗ₜ[k] (1 : B)) = 0 := by
      intro c
      by_contra hcon
      have hmemI : (c ⊗ₜ[k] (1 : B)) * y1 - y1 * (c ⊗ₜ[k] (1 : B)) ∈ I :=
        sub_mem (TwoSidedIdeal.mul_mem_left _ _ _ hy1I)
          (TwoSidedIdeal.mul_mem_right _ _ _ hy1I)
      have hle := hmin _ _ _ hmemI hcon (hrep c).symm
      have hcard : (s0.erase i0).card < N := by
        have h1c : (s0.erase i0).card = s0.card - 1 := Finset.card_erase_of_mem hi0
        have h2c : 0 < s0.card := Finset.card_pos.mpr ⟨i0, hi0⟩
        omega
      omega
    -- coefficients are central
    have hcent : ∀ i ∈ s0, ∀ c : A, c * (∑ j : Fin n, pp j * c0 i * qq j)
        = (∑ j : Fin n, pp j * c0 i * qq j) * c := by
      intro i hi c
      by_cases hii : i = i0
      · subst hii; rw [hcoeff1, mul_one, one_mul]
      · have hmem_erase : i ∈ s0.erase i0 := Finset.mem_erase.mpr ⟨hii, hi⟩
        have h0 := uniq (s0.erase i0)
          (fun i => c * (∑ j : Fin n, pp j * c0 i * qq j)
            - (∑ j : Fin n, pp j * c0 i * qq j) * c)
          ((hrep c).symm.trans (hcomm0 c)) i hmem_erase
        exact sub_eq_zero.mp h0
    have hscal : ∀ i ∈ s0, ∃ r : k,
        (∑ j : Fin n, pp j * c0 i * qq j) = algebraMap k A r := by
      intro i hi
      have hmem : (∑ j : Fin n, pp j * c0 i * qq j) ∈ Subalgebra.center k A := by
        rw [Subalgebra.mem_center_iff]
        exact hcent i hi
      obtain ⟨r, hr⟩ := (Algebra.IsCentral.mem_center_iff k).mp hmem
      exact ⟨r, hr⟩
    -- y1 = 1 ⊗ b1
    have hb1 : ∃ b1 : B, y1 = 1 ⊗ₜ[k] b1 := by
      have hex : ∀ i, ∃ r : k, i ∈ s0 →
          (∑ j : Fin n, pp j * c0 i * qq j) = algebraMap k A r := by
        intro i
        by_cases hi : i ∈ s0
        · obtain ⟨r, hr⟩ := hscal i hi
          exact ⟨r, fun _ => hr⟩
        · exact ⟨0, fun h => absurd h hi⟩
      choose r hr using hex
      refine ⟨s0.sum (fun i => r i • e i), ?_⟩
      rw [hy1exp, TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hr i hi, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul]
    obtain ⟨b1, hb1⟩ := hb1
    have hb1ne : b1 ≠ 0 := by
      intro hcon
      rw [hcon, TensorProduct.tmul_zero] at hb1
      exact hy1ne hb1
    set J : TwoSidedIdeal B := TwoSidedIdeal.comap
      (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)).toRingHom I with hJ
    have hb1J : b1 ∈ J := by
      rw [hJ, TwoSidedIdeal.mem_comap]
      have hmem : (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)) b1
        ∈ I := by
        rw [Algebra.TensorProduct.includeRight_apply, ← hb1]
        exact hy1I
      exact hmem
    have hJtop : J = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top J with h | h
      · exfalso
        rw [h] at hb1J
        exact hb1ne ((TwoSidedIdeal.mem_bot B).mp hb1J)
      · exact h
    have h1I : (1 : A ⊗[k] B) ∈ I := by
      have hmem : (1 : B) ∈ J := by
        rw [hJtop]; exact TwoSidedIdeal.mem_top B
      rw [hJ, TwoSidedIdeal.mem_comap] at hmem
      have h1t : ((Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)).toRingHom
        (1 : B) : A ⊗[k] B) = 1 := by
        have hthis : (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)) (1 : B)
            = 1 ⊗ₜ[k] (1 : B) := Algebra.TensorProduct.includeRight_apply 1
        rw [Algebra.TensorProduct.one_def]
        exact hthis
      rw [h1t] at hmem
      exact hmem
    have htop : I = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x = x * 1 := (mul_one x).symm
      rw [hx]
      exact TwoSidedIdeal.mul_mem_left _ _ _ h1I
    exact htop

private theorem mulLeftRight_bijective_of_central_simple
    {k : Type*} {A : Type*} [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A] :
    Function.Bijective (AlgHom.mulLeftRight k A) := by
  have : IsSimpleRing (A ⊗[k] Aᵐᵒᵖ) := tensor_simple_of_central_simple
  have : Nontrivial (Module.End k A) := by
    obtain ⟨a0, ha0⟩ := exists_ne (0 : A)
    refine ⟨1, 0, fun h => ha0 ?_⟩
    have h2 := congrArg (fun f : Module.End k A => f a0) h
    simpa using h2
  have hinj : Function.Injective (AlgHom.mulLeftRight k A) :=
    RingHom.injective (AlgHom.mulLeftRight k A).toRingHom
  have hsurj : Function.Surjective (AlgHom.mulLeftRight k A) := by
    set f : (A ⊗[k] Aᵐᵒᵖ) →ₗ[k] Module.End k A :=
      (AlgHom.mulLeftRight k A).toLinearMap with hf
    have hker : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
    have hfin : Module.finrank k (A ⊗[k] Aᵐᵒᵖ)
        = Module.finrank k (Module.End k A) := by
      have h3 : Module.finrank k Aᵐᵒᵖ = Module.finrank k A :=
        LinearEquiv.finrank_eq (MulOpposite.opLinearEquiv k).symm
      calc Module.finrank k (A ⊗[k] Aᵐᵒᵖ)
          = Module.finrank k A * Module.finrank k Aᵐᵒᵖ :=
            Module.finrank_tensorProduct
        _ = Module.finrank k A * Module.finrank k A := by rw [h3]
        _ = Module.finrank k (A →ₗ[k] A) := (Module.finrank_linearMap k k A A).symm
        _ = Module.finrank k (Module.End k A) := rfl
    have hfin2 : Module.finrank k f.range = Module.finrank k (Module.End k A) := by
      have h := LinearMap.finrank_range_add_finrank_ker f
      rw [hker, finrank_bot] at h
      rw [hfin] at h
      omega
    have hrange : f.range = ⊤ := Submodule.eq_top_of_finrank_eq hfin2
    exact LinearMap.range_eq_top.mp hrange
  exact ⟨hinj, hsurj⟩

/--
Every k-algebra automorphism of a finite-dimensional central simple algebra is inner.
Source: T. Skolem, Zur Theorie der assoziativen Zahlensysteme, Skrifter Vidensk. Kristiania I
(1927), no. 12; E. Noether, Nichtkommutative Algebra, Math. Z. 37 (1933), 514-541, DOI
10.1007/BF01474591.
Proves `Wanted` entry `skolem_noether`.
-/
theorem skolem_noether
    {k : Type*} {A : Type*} [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]
    (σ : A ≃ₐ[k] A) : ∃ u : Aˣ, ∀ x : A, σ x = (u : A) * x * (↑(u⁻¹ : Aˣ) : A) := by
  set Φ : (A ⊗[k] Aᵐᵒᵖ) ≃ₐ[k] Module.End k A :=
    AlgEquiv.ofBijective (AlgHom.mulLeftRight k A)
      (mulLeftRight_bijective_of_central_simple) with hΦ
  set τ : (A ⊗[k] Aᵐᵒᵖ) ≃ₐ[k] (A ⊗[k] Aᵐᵒᵖ) :=
    Algebra.TensorProduct.congr σ (AlgEquiv.refl) with hτ
  set F : Module.End k A ≃ₐ[k] Module.End k A := Φ.symm.trans (τ.trans Φ) with hF
  set R : A → Module.End k A := fun b =>
    { toFun := fun x => x * b
      map_add' := fun x y => add_mul x y b
      map_smul' := fun r x => by
        change (r • x) * b = r • (x * b)
        rw [Algebra.smul_def, Algebra.smul_def, mul_assoc] } with hR
  set L : A → Module.End k A := fun a =>
    { toFun := fun x => a * x
      map_add' := fun x y => mul_add a x y
      map_smul' := fun r x => by
        change a * (r • x) = r • (a * x)
        rw [Algebra.smul_def, Algebra.smul_def, Algebra.left_comm] } with hL
  have hΦR : ∀ b : A, Φ (1 ⊗ₜ[k] (MulOpposite.op b : Aᵐᵒᵖ)) = R b := by
    intro b
    apply LinearMap.ext
    intro x
    change ((AlgHom.mulLeftRight k A) (1 ⊗ₜ[k] MulOpposite.op b)) x = (R b) x
    rw [AlgHom.mulLeftRight_apply, MulOpposite.unop_op, one_mul]
    rfl
  have hΦL : ∀ a : A, Φ (a ⊗ₜ[k] (1 : Aᵐᵒᵖ)) = L a := by
    intro a
    apply LinearMap.ext
    intro x
    change ((AlgHom.mulLeftRight k A) (a ⊗ₜ[k] (1 : Aᵐᵒᵖ))) x = (L a) x
    rw [AlgHom.mulLeftRight_apply, MulOpposite.unop_one, mul_one]
    rfl
  have hτR : ∀ b : A, τ (1 ⊗ₜ[k] (MulOpposite.op b : Aᵐᵒᵖ))
      = 1 ⊗ₜ[k] MulOpposite.op b := by
    intro b
    change (Algebra.TensorProduct.congr σ (AlgEquiv.refl)) _ = _
    simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  have hτL : ∀ a : A, τ (a ⊗ₜ[k] (1 : Aᵐᵒᵖ)) = σ a ⊗ₜ[k] 1 := by
    intro a
    change (Algebra.TensorProduct.congr σ (AlgEquiv.refl)) _ = _
    simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  have hFR : ∀ b : A, F (R b) = R b := by
    intro b
    change (Φ.symm.trans (τ.trans Φ)) (R b) = R b
    have h1 : Φ.symm (R b) = 1 ⊗ₜ[k] MulOpposite.op b := by
      rw [← hΦR b, AlgEquiv.symm_apply_apply]
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, h1, hτR, hΦR]
  have hFL : ∀ a : A, F (L a) = L (σ a) := by
    intro a
    change (Φ.symm.trans (τ.trans Φ)) (L a) = L (σ a)
    have h1 : Φ.symm (L a) = a ⊗ₜ[k] (1 : Aᵐᵒᵖ) := by
      rw [← hΦL a, AlgEquiv.symm_apply_apply]
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, h1, hτL, hΦL]
  obtain ⟨T, hT⟩ := AlgEquiv.eq_linearEquivConjAlgEquiv F
  have hTR : ∀ (b x : A), T (x * b) = T x * b := by
    intro b x
    have hFb := hFR b
    rw [hT, LinearEquiv.conjAlgEquiv_apply] at hFb
    have hTx : T.symm (T x) = x := LinearEquiv.symm_apply_apply T x
    have hxe : T ((R b) (T.symm (T x))) = (R b) (T x) :=
      congrArg (fun f : Module.End k A => f (T x)) hFb
    rw [hTx] at hxe
    exact hxe
  have hTL : ∀ (a x : A), T (a * x) = σ a * T x := by
    intro a x
    have hFa := hFL a
    rw [hT, LinearEquiv.conjAlgEquiv_apply] at hFa
    have hTx : T.symm (T x) = x := LinearEquiv.symm_apply_apply T x
    have hxe : T ((L a) (T.symm (T x))) = (L (σ a)) (T x) :=
      congrArg (fun f : Module.End k A => f (T x)) hFa
    rw [hTx] at hxe
    exact hxe
  set u : A := T 1 with hu
  have hTu : ∀ x : A, T x = u * x := by
    intro x
    have h := hTR x 1
    rwa [one_mul] at h
  have hTσ : ∀ a : A, T a = σ a * u := by
    intro a
    have h := hTL a 1
    rwa [mul_one] at h
  have hcomm : ∀ a : A, u * a = σ a * u := by
    intro a
    rw [← hTσ a, hTu a]
  obtain ⟨v, hv⟩ := T.surjective 1
  have hvu1 : u * v = 1 := by
    have h := hTu v
    rw [hv] at h
    exact h.symm
  have hvu2 : v * u = 1 := by
    have h1 : T (v * u) = T 1 := by
      rw [hTu, hTu, ← mul_assoc, hvu1, one_mul, mul_one]
    exact T.injective h1
  refine ⟨⟨u, v, hvu1, hvu2⟩, fun x => ?_⟩
  change σ x = u * x * v
  have h := hcomm x
  calc σ x = σ x * (u * v) := by rw [hvu1, mul_one]
    _ = σ x * u * v := by rw [mul_assoc]
    _ = u * x * v := by rw [h]

end MathlibExt.Algebra.Central.SkolemNoether
