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

`Theorems/Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_
hyperelementary.lean`
and
`P2M/Sol/S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_
hyperelementary.lean`
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
public import Mathlib.Algebra.Field.Rat
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Solomon's induction theorem

For a finite group `G`, the constant function `1` is an integer combination of the
permutation characters `ClassFunction.induced H 1` of `G` acting on `G ⧸ H`, where every
`H` is *hyperelementary*: `H` has a cyclic normal subgroup `C` of order prime to a prime `q`
such that every element of `H` has a `q`-power in `C`, so that `H ⧸ C` is a `q`-group.

The proof follows the classical argument: the integer span of the permutation characters
`g ↦ |(G ⧸ H)^g|` is a subring (products decompose along orbits of `G` on
`G ⧸ H × G ⧸ K`), the span of the hyperelementary ones is an ideal of it, and that ideal
is the whole ring because no maximal ideal can contain it: for each prime `p` and element
`x` there is a hyperelementary `H` with `|(G ⧸ H)^x|` prime to `p`.

## Main result

* `ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary`
-/

@[expose] public section

noncomputable section

open MulAction

namespace ClassFunction

namespace SolomonProof

variable {G : Type*} [Group G] [Fintype G]

private def IsHyper (H : Subgroup G) : Prop :=
  ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H ∧ IsCyclic C ∧ (Nat.card C).Coprime q ∧
    (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H, ∃ n : ℕ, h ^ q ^ n ∈ C)

omit [Fintype G] in
private theorem conj_pow' (a s : G) (m : ℕ) : (a⁻¹ * s * a) ^ m = a⁻¹ * s ^ m * a := by
  have := @conj_pow G _ m a⁻¹ s
  simpa using this

omit [Fintype G] in
private theorem IsHyper.of_le_conj {K : Subgroup G} (hK : IsHyper K) (a : G) (S : Subgroup G)
    (hS : ∀ s ∈ S, a⁻¹ * s * a ∈ K) : IsHyper S := by
  obtain ⟨q, hq, C, hCK, hCcyc, hCcop, hCnorm, hCpow⟩ := hK
  let aC : Subgroup G := C.map (MulAut.conj a).toMonoidHom
  have hmem_aC : ∀ y : G, y ∈ aC ↔ a⁻¹ * y * a ∈ C := by
    intro y
    constructor
    · rintro ⟨c, hc, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hc
    · intro hy
      exact ⟨a⁻¹ * y * a, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  refine ⟨q, hq, aC ⊓ S, inf_le_right, ?_, ?_, ?_, ?_⟩
  · have : IsCyclic aC :=
      isCyclic_of_surjective (C.equivMapOfInjective _ (MulAut.conj a).injective).toMonoidHom
        (C.equivMapOfInjective _ (MulAut.conj a).injective).surjective
    exact Subgroup.isCyclic_of_le inf_le_left
  · have hdvd : Nat.card (aC ⊓ S : Subgroup G) ∣ Nat.card C := by
      have h1 : Nat.card (aC ⊓ S : Subgroup G) ∣ Nat.card aC :=
        Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card aC = Nat.card C :=
        Subgroup.card_map_of_injective (MulAut.conj a).injective
      rwa [h2] at h1
    exact Nat.Coprime.coprime_dvd_left hdvd hCcop
  · intro s hs c hc
    rw [Subgroup.mem_inf] at hc ⊢
    refine ⟨?_, ?_⟩
    · apply (hmem_aC _).2
      have hc' : a⁻¹ * c * a ∈ C := (hmem_aC c).1 hc.1
      have := hCnorm (a⁻¹ * s * a) (hS s hs) (a⁻¹ * c * a) hc'
      have e : a⁻¹ * s * a * (a⁻¹ * c * a) * (a⁻¹ * s * a)⁻¹ = a⁻¹ * (s * c * s⁻¹) * a := by group
      rwa [e] at this
    · exact S.mul_mem (S.mul_mem hs hc.2) (S.inv_mem hs)
  · intro s hs
    obtain ⟨n, hn⟩ := hCpow (a⁻¹ * s * a) (hS s hs)
    refine ⟨n, ?_⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, S.pow_mem hs _⟩
    apply (hmem_aC _).2
    rw [← conj_pow']
    exact hn

private def pc (H : Subgroup G) : G → ℤ := fun g => (Nat.card {c : G ⧸ H // g • c = c} : ℤ)

omit [Fintype G] in
private theorem pc_apply (H : Subgroup G) (g : G) :
    pc H g = Nat.card {c : G ⧸ H // g • c = c} := rfl

omit [Fintype G] in
private theorem card_mul_pc (H : Subgroup G) (g : G) :
    (Nat.card H : ℤ) * pc H g = Nat.card {x : G // x⁻¹ * g * x ∈ H} := by
  have h := QuotientGroup.card_preimage_mk H (fixedBy (G ⧸ H) g)
  have hset : (QuotientGroup.mk ⁻¹' fixedBy (G ⧸ H) g : Set G) = {x : G | x⁻¹ * g * x ∈ H} := by
    ext x
    simp only [Set.mem_preimage, mem_fixedBy, Set.mem_ofPred_eq]
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    rw [show (g * x)⁻¹ * x = (x⁻¹ * g * x)⁻¹ by group, inv_mem_iff]
  rw [hset] at h
  rw [pc]
  rw [← Nat.cast_mul]
  have h' : Nat.card {x : G // x⁻¹ * g * x ∈ H} =
      Nat.card H * Nat.card {c : G ⧸ H // g • c = c} := h
  rw [h']

omit [Fintype G] in
private theorem pc_top : pc (⊤ : Subgroup G) = 1 := by
  funext g
  rw [pc_apply, Pi.one_apply]
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  have : Nat.card {c : G ⧸ (⊤ : Subgroup G) // g • c = c} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance, ⟨⟨((1 : G) : G ⧸ (⊤ : Subgroup G)), Subsingleton.elim _ _⟩⟩⟩
  rw [this, Nat.cast_one]

open scoped Classical in
private theorem induced_one_eq_pc (H : Subgroup G) (g : G) :
    ClassFunction.induced H (fun _ => (1 : ℚ)) g = pc H g := by
  rw [ClassFunction.induced_apply, Finset.sum_boole]
  have hH : (Nat.card H : ℚ) ≠ 0 := by
    have : 0 < Nat.card H := Nat.card_pos
    exact_mod_cast this.ne'
  have h := card_mul_pc H g
  have hc : Nat.card {x : G // x⁻¹ * g * x ∈ H} =
      (Finset.univ.filter fun x : G => x⁻¹ * g * x ∈ H).card :=
    Nat.subtype_card _ (by simp)
  rw [hc] at h
  have h' : (Nat.card H : ℚ) * (pc H g : ℚ) =
      ((Finset.univ.filter fun x : G => x⁻¹ * g * x ∈ H).card : ℚ) := by
    exact_mod_cast h
  rw [← h']
  field_simp

omit [Fintype G] in
private theorem conj_mem_of_mem_stabilizer (K : Subgroup G) (a : G) {s : G}
    (hs : s ∈ stabilizer G (a : G ⧸ K)) : a⁻¹ * s * a ∈ K := by
  rw [mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hs
  rw [show (s * a)⁻¹ * a = (a⁻¹ * s * a)⁻¹ by group, inv_mem_iff] at hs
  exact hs

open scoped Classical in
private theorem pc_mul_pc_eq_sum (H K : Subgroup G) (g : G) :
    pc H g * pc K g =
      ∑ ω : orbitRel.Quotient G ((G ⧸ H) × (G ⧸ K)), pc (stabilizer G ω.out) g := by
  set X := (G ⧸ H) × (G ⧸ K) with hX
  have hprod : pc H g * pc K g = Nat.card {x : X // g • x = x} := by
    rw [pc_apply, pc_apply, ← Nat.cast_mul]
    congr 1
    rw [← Nat.card_prod]
    exact Nat.card_congr
      { toFun := fun p => ⟨(p.1.1, p.2.1), Prod.ext p.1.2 p.2.2⟩
        invFun := fun x => (⟨x.1.1, (Prod.ext_iff.1 x.2).1⟩, ⟨x.1.2, (Prod.ext_iff.1 x.2).2⟩)
        left_inv := fun p => rfl
        right_inv := fun x => rfl }
  rw [hprod]
  have hsigma : Nat.card {x : X // g • x = x} =
      ∑ ω : orbitRel.Quotient G X, Nat.card {x : X // g • x = x ∧ Quotient.mk'' x = ω} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr
      { toFun := fun x => ⟨Quotient.mk'' x.1, ⟨x.1, x.2, rfl⟩⟩
        invFun := fun s => ⟨s.2.1, s.2.2.1⟩
        left_inv := fun x => rfl
        right_inv := fun s => by
          obtain ⟨ω, x, hx, rfl⟩ := s
          rfl }
  rw [hsigma]
  push_cast
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [pc_apply]
  congr 1
  set b := ω.out with hb
  let e := orbitEquivQuotientStabilizer G b
  have horb : ∀ x : X, Quotient.mk'' x = ω ↔ x ∈ orbit G b := by
    intro x
    rw [← orbitRel.Quotient.mem_orbit, orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
  have hequiv : ∀ c : G ⧸ stabilizer G b,
      ((e.symm (g • c) : orbit G b) : X) = g • (e.symm c : X) := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H a =>
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
      rw [orbitEquivQuotientStabilizer_symm_apply, orbitEquivQuotientStabilizer_symm_apply,
        mul_smul]
  refine Nat.card_congr
    { toFun := fun x => ⟨e ⟨x.1, (horb x.1).1 x.2.2⟩, ?_⟩
      invFun := fun c => ⟨(e.symm c.1 : X), ?_, (horb _).2 (e.symm c.1).2⟩
      left_inv := fun x => by simp
      right_inv := fun c => by simp }
  · apply e.symm.injective
    apply Subtype.ext
    rw [hequiv, Equiv.symm_apply_apply]
    exact x.2.1
  · rw [← hequiv, c.2]

open scoped Classical in
omit [Fintype G] in
private theorem pc_mul_pc_mem_span [Finite G] (H K : Subgroup G) (T : Set (Subgroup G))
    (hT : ∀ (a : G) (S : Subgroup G), (∀ s ∈ S, a⁻¹ * s * a ∈ K) → S ∈ T) :
    pc H * pc K ∈ Submodule.span ℤ (pc '' T) := by
  have := Fintype.ofFinite G
  have : pc H * pc K = ∑ ω : orbitRel.Quotient G ((G ⧸ H) × (G ⧸ K)),
      pc (stabilizer G ω.out) := by
    funext g
    rw [Pi.mul_apply, pc_mul_pc_eq_sum, Finset.sum_apply]
  rw [this]
  refine Submodule.sum_mem _ fun ω _ => Submodule.subset_span ⟨_, ?_, rfl⟩
  apply hT ω.out.2.out
  intro s hs
  apply conj_mem_of_mem_stabilizer K
  rw [mem_stabilizer_iff] at hs ⊢
  have h2 := (Prod.ext_iff.1 hs).2
  simpa using h2

private def P : Submodule ℤ (G → ℤ) := Submodule.span ℤ (pc '' (Set.univ : Set (Subgroup G)))

private def I : Submodule ℤ (G → ℤ) := Submodule.span ℤ (pc '' {S : Subgroup G | IsHyper S})

omit [Fintype G] in
private theorem I_le_P : (I : Submodule ℤ (G → ℤ)) ≤ P :=
  Submodule.span_mono (Set.image_mono (Set.subset_univ _))

omit [Fintype G] in
private theorem pc_mem_P (H : Subgroup G) : pc H ∈ (P : Submodule ℤ (G → ℤ)) :=
  Submodule.subset_span ⟨H, Set.mem_univ _, rfl⟩

omit [Fintype G] in
private theorem one_mem_P : (1 : G → ℤ) ∈ (P : Submodule ℤ (G → ℤ)) := by
  rw [← pc_top]; exact pc_mem_P ⊤

omit [Fintype G] in
private theorem mul_mem_span_of_gen (T₁ T₂ : Set (Subgroup G))
    (h : ∀ H ∈ T₁, ∀ K ∈ T₂, pc H * pc K ∈ Submodule.span ℤ (pc '' T₂))
    {f g : G → ℤ} (hf : f ∈ Submodule.span ℤ (pc '' T₁)) (hg : g ∈ Submodule.span ℤ (pc '' T₂)) :
    f * g ∈ Submodule.span ℤ (pc '' T₂) := by
  induction hf using Submodule.span_induction generalizing g with
  | mem x hx =>
    obtain ⟨H, hH, rfl⟩ := hx
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨K, hK, rfl⟩ := hy
      exact h H hH K hK
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul n y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ n hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ (hx hg) (hy hg)
  | smul n x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n (hx hg)

omit [Fintype G] in
private theorem mul_mem_P [Finite G] {f g : G → ℤ} (hf : f ∈ (P : Submodule ℤ (G → ℤ)))
    (hg : g ∈ (P : Submodule ℤ (G → ℤ))) : f * g ∈ (P : Submodule ℤ (G → ℤ)) :=
  mul_mem_span_of_gen _ _
    (fun H _ K _ => pc_mul_pc_mem_span H K _ fun _ S _ => Set.mem_univ S) hf hg

omit [Fintype G] in
private theorem mul_mem_I [Finite G] {f g : G → ℤ} (hf : f ∈ (P : Submodule ℤ (G → ℤ)))
    (hg : g ∈ (I : Submodule ℤ (G → ℤ))) : f * g ∈ (I : Submodule ℤ (G → ℤ)) :=
  mul_mem_span_of_gen _ {S : Subgroup G | IsHyper S}
    (fun H _ K hK => pc_mul_pc_mem_span H K _ fun a S hS => IsHyper.of_le_conj hK a S hS) hf hg

private def Psub : Subring (G → ℤ) where
  carrier := (P : Submodule ℤ (G → ℤ))
  mul_mem' := mul_mem_P
  one_mem' := one_mem_P
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  neg_mem' := fun ha => Submodule.neg_mem _ ha

section Arith

variable (q : ℕ) [hq : Fact q.Prime]

omit [Fintype G] in
omit hq in
private theorem mem_of_orderOf_coprime {H C : Subgroup G} (hpow : ∀ h ∈ H, ∃ n : ℕ, h ^ q ^ n ∈ C)
    {y : G} (hy : y ∈ H) (hcop : (orderOf y).Coprime q) : y ∈ C := by
  obtain ⟨n, hn⟩ := hpow y hy
  have hcop' : (orderOf y).Coprime (q ^ n) := Nat.Coprime.pow_right n hcop
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hcop'.symm)
  have : y = (y ^ q ^ n) ^ u := by
    rw [← zpow_natCast, ← zpow_mul]
    have e : ((q ^ n : ℕ) : ℤ) * u = 1 - v * orderOf y := by push_cast at huv ⊢; linarith
    rw [e, zpow_sub, zpow_one, zpow_mul, zpow_natCast]
    simp []
  rw [this]
  exact C.zpow_mem hn u

omit [Fintype G] in
private theorem orderOf_conj' (y z : G) : orderOf (y⁻¹ * z * y) = orderOf z := by
  have := orderOf_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective z
  simpa [MulAut.conj_apply] using this

omit [Fintype G] in
private theorem exists_isHyper_not_dvd [Finite G] (x : G) :
    ∃ H : Subgroup G, IsHyper H ∧ ¬ (q : ℤ) ∣ pc H x := by
  have hq' : q.Prime := hq.out
  set m := orderOf x with hm
  have hm0 : m ≠ 0 := (orderOf_pos x).ne'
  set a := m.factorization q with ha
  set qa := q ^ a with hqa
  set m' := m / qa with hm'
  have hmm : qa * m' = m := Nat.ordProj_mul_ordCompl_eq_self m q
  have hcop : q.Coprime m' := Nat.coprime_ordCompl hq' hm0
  have hqa0 : qa ≠ 0 := pow_ne_zero _ hq'.ne_zero
  set xr := x ^ qa with hxr
  have hxr_ord : orderOf xr = m' := by
    rw [hxr, orderOf_pow_of_dvd hqa0 (Nat.ordProj_dvd m q)]
  set C := Subgroup.zpowers xr with hC
  have hCcard : Nat.card C = m' := by rw [hC, Nat.card_zpowers, hxr_ord]
  have hCcop : (Nat.card C).Coprime q := by rw [hCcard]; exact hcop.symm
  have hCcomm : ∀ c ∈ C, x * c = c * x := by
    intro c hc
    rw [hC, Subgroup.mem_zpowers_iff] at hc
    obtain ⟨k, rfl⟩ := hc
    rw [hxr, ← zpow_natCast, ← zpow_mul]
    exact (Commute.self_zpow x _).eq
  set N := Subgroup.normalizer (C : Set G) with hN
  have hCN : C ≤ N := Subgroup.le_normalizer
  have hmemN : ∀ y : G, y ∈ N ↔ ∀ h : G, h ∈ C ↔ y * h * y⁻¹ ∈ C := fun y =>
    Subgroup.mem_normalizer_iff
  have hxN : x ∈ N := by
    rw [hmemN]
    intro h
    constructor
    · intro hh
      rwa [hCcomm h hh, mul_inv_cancel_right]
    · intro hh
      have hc := hCcomm _ hh
      have e : h = x * h * x⁻¹ := by
        calc h = x⁻¹ * ((x * h * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [hc]
          _ = x * h * x⁻¹ := by group
      rw [e]; exact hh
  set CN : Subgroup N := C.subgroupOf N with hCN'
  have hCNnormal : CN.Normal := Subgroup.normal_in_normalizer
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow q N))
  set HN : Subgroup N := CN ⊔ (Q : Subgroup N) with hHN
  set H : Subgroup G := HN.map N.subtype with hH
  have hHN_le : H ≤ N := by
    rintro y ⟨z, -, rfl⟩; exact z.2
  have hmemH : ∀ y : G, y ∈ H ↔ ∃ hy : y ∈ N, (⟨y, hy⟩ : N) ∈ HN := by
    intro y; constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z.2, by simpa using hz⟩
    · rintro ⟨hy, hz⟩; exact ⟨⟨y, hy⟩, hz, rfl⟩
  have hCH : C ≤ H := by
    intro c hc
    rw [hmemH]
    refine ⟨hCN hc, Subgroup.mem_sup_left ?_⟩
    rw [Subgroup.mem_subgroupOf]; exact hc
  have hHNmem : ∀ z : N, z ∈ HN → ∃ c ∈ CN, ∃ u ∈ (Q : Subgroup N), c * u = z := by
    intro z hz
    have : (z : N) ∈ ((CN ⊔ (Q : Subgroup N) : Subgroup N) : Set N) := hz
    rw [Subgroup.normal_mul] at this
    obtain ⟨c, hc, u, hu, hcu⟩ := Set.mem_mul.1 this
    exact ⟨c, hc, u, hu, hcu⟩
  have hHnorm : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C := fun h hh c hc =>
    ((hmemN h).1 (hHN_le hh) c).1 hc
  have hHpow : ∀ h ∈ H, ∃ n : ℕ, h ^ q ^ n ∈ C := by
    intro h hh
    obtain ⟨hN', hz⟩ := (hmemH h).1 hh
    obtain ⟨c, hc, u, hu, hcu⟩ := hHNmem _ hz
    obtain ⟨n, hn⟩ := Q.isPGroup ⟨u, hu⟩
    refine ⟨n, ?_⟩
    have hun : u ^ q ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hq1 : ((⟨h, hN'⟩ : N) : N ⧸ CN) ^ q ^ n = 1 := by
      rw [← hcu, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).2 hc, one_mul,
        ← QuotientGroup.mk_pow, hun, QuotientGroup.mk_one]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hCN', Subgroup.mem_subgroupOf] at hq1
    simpa using hq1
  have hHyper : IsHyper H := ⟨q, hq', C, hCH, inferInstance, hCcop, hHnorm, hHpow⟩
  refine ⟨H, hHyper, ?_⟩
  have hyN : ∀ y : G, y⁻¹ * x * y ∈ H → y ∈ N := by
    intro y hy
    have hw : y⁻¹ * xr * y ∈ H := by rw [hxr, ← conj_pow']; exact H.pow_mem hy _
    have hword : orderOf (y⁻¹ * xr * y) = m' := by rw [orderOf_conj', hxr_ord]
    have hwC : y⁻¹ * xr * y ∈ C :=
      mem_of_orderOf_coprime q hHpow hw (by rw [hword]; exact hcop.symm)
    have hmap : C.map (MulAut.conj y⁻¹).toMonoidHom = C := by
      have e1 : C.map (MulAut.conj y⁻¹).toMonoidHom = Subgroup.zpowers (y⁻¹ * xr * y) := by
        rw [hC, MonoidHom.map_zpowers]
        congr 1
        simp []
      rw [e1]
      apply Subgroup.eq_of_le_of_card_ge
      · exact (Subgroup.zpowers_le).2 hwC
      · have h1 : Nat.card (Subgroup.zpowers (y⁻¹ * xr * y)) = m' := by
          rw [Nat.card_zpowers, hword]
        have h2 : Nat.card C = m' := hCcard
        simp only [h1]
        rw [hC] at h2
        rw [h2]
    have hy' : y⁻¹ ∈ N := by
      rw [hmemN]
      intro h
      constructor
      · intro hh
        have : (MulAut.conj y⁻¹).toMonoidHom h ∈ C.map (MulAut.conj y⁻¹).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hh
        rw [hmap] at this
        simpa [MulAut.conj_apply] using this
      · intro hh
        have hh' : (MulAut.conj y⁻¹).toMonoidHom h ∈ C.map (MulAut.conj y⁻¹).toMonoidHom := by
          rw [hmap]; simpa [MulAut.conj_apply] using hh
        exact (Subgroup.mem_map_iff_mem (MulAut.conj y⁻¹).injective).1 hh'
    simpa using N.inv_mem hy'
  set xN : N := ⟨x, hxN⟩ with hxN'
  have hcount : Nat.card {y : G // y⁻¹ * x * y ∈ H} =
      Nat.card {y : N // y⁻¹ * xN * y ∈ HN} := by
    apply Nat.card_congr
    exact
      { toFun := fun y => ⟨⟨y.1, hyN y.1 y.2⟩, by
          obtain ⟨hy', hz⟩ := (hmemH _).1 y.2
          have e : (⟨y.1, hyN y.1 y.2⟩ : N)⁻¹ * xN * ⟨y.1, hyN y.1 y.2⟩ = ⟨y.1⁻¹ * x * y.1, hy'⟩ :=
            Subtype.ext rfl
          rw [e]; exact hz⟩
        invFun := fun z => ⟨z.1, (hmemH _).2 ⟨(z.1⁻¹ * xN * z.1).2, by
          have e : (⟨(z.1 : G)⁻¹ * x * z.1, (z.1⁻¹ * xN * z.1).2⟩ : N) = z.1⁻¹ * xN * z.1 :=
            Subtype.ext rfl
          rw [e]; exact z.2⟩⟩
        left_inv := fun y => rfl
        right_inv := fun z => rfl }
  have hHcard : Nat.card H = Nat.card HN := Subgroup.card_map_of_injective N.subtype_injective
  have hpc : pc H x = pc (G := N) HN xN := by
    have h1 := card_mul_pc H x
    have h2 := card_mul_pc (G := N) HN xN
    rw [hcount, ← h2, hHcard] at h1
    have hne : (Nat.card HN : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    exact mul_left_cancel₀ hne h1
  rw [hpc, pc_apply]
  have hcop' : Nat.Coprime m' qa := Nat.Coprime.pow_right a hcop.symm
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop'
  set gq : G := (x ^ m') ^ u with hgq
  set c₀ : G := xr ^ v with hc₀
  have hc₀C : c₀ ∈ C := by rw [hC]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) v
  have hxdec : x = gq * c₀ := by
    rw [hgq, hc₀, hxr, ← zpow_natCast x m', ← zpow_natCast x qa, ← zpow_mul, ← zpow_mul,
      ← zpow_add]
    have : (m' : ℤ) * u + (qa : ℤ) * v = 1 := by linarith [huv]
    rw [this, zpow_one]
  have hgq_pow : gq ^ qa = 1 := by
    rw [← zpow_natCast gq, hgq, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul,
      Nat.mul_comm, hmm, hm, pow_orderOf_eq_one, one_zpow]
  have hgqN : gq ∈ N := by rw [hgq]; exact N.zpow_mem (N.pow_mem hxN _) _
  set gqN : N := ⟨gq, hgqN⟩ with hgqN'
  have hxNdec : xN = gqN * ⟨c₀, hCN hc₀C⟩ := Subtype.ext hxdec
  have htriv : ∀ (c : G) (hc : c ∈ C) (t : N ⧸ HN), (⟨c, hCN hc⟩ : N) • t = t := by
    intro c hc t
    induction t using QuotientGroup.induction_on with
    | H y =>
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      apply Subgroup.mem_sup_left
      rw [hCN', Subgroup.mem_subgroupOf]
      have hy := (hmemN y).1 y.2
      have e : (((⟨c, hCN hc⟩ * y)⁻¹ * y : N) : G) = (y : G)⁻¹ * c⁻¹ * y := by
        simp [mul_assoc]
      rw [e]
      apply (hy _).2
      rw [show (y : G) * ((y : G)⁻¹ * c⁻¹ * y) * (y : G)⁻¹ = c⁻¹ by group]
      exact C.inv_mem hc
  have hfix : ∀ t : N ⧸ HN, xN • t = t ↔ gqN • t = t := by
    intro t; rw [hxNdec, mul_smul, htriv c₀ hc₀C]
  have hcardfix : Nat.card {t : N ⧸ HN // xN • t = t} =
      Nat.card (fixedPoints (Subgroup.zpowers gqN) (N ⧸ HN)) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro t
    rw [hfix, MulAction.mem_fixedPoints]
    constructor
    · intro ht g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
      have := MulAction.fixedBy_subset_fixedBy_zpow (N ⧸ HN) gqN k
        (show t ∈ fixedBy _ gqN from ht)
      rw [hk] at this
      exact this
    · intro ht
      exact ht ⟨gqN, Subgroup.mem_zpowers _⟩
  have hPgrp : IsPGroup q (Subgroup.zpowers gqN) := by
    intro g
    refine ⟨a, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext
    have hgqNpow : gqN ^ qa = 1 := Subtype.ext (by
      change gq ^ qa = 1
      exact hgq_pow)
    change ((g : N)) ^ q ^ a = 1
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    change (gqN ^ qa) ^ k = 1
    rw [hgqNpow, one_zpow]
  have hmod := hPgrp.card_modEq_card_fixedPoints (N ⧸ HN)
  have hindex : ¬ q ∣ Nat.card (N ⧸ HN) := by
    rw [← Subgroup.index_eq_card]
    intro hdvd
    exact Sylow.not_dvd_index Q (hdvd.trans (Subgroup.index_dvd_of_le le_sup_right))
  rw [hcardfix]
  intro hdvd
  apply hindex
  have hdvd' : q ∣ Nat.card (fixedPoints (Subgroup.zpowers gqN) (N ⧸ HN)) := by
    exact_mod_cast hdvd
  exact (hmod.dvd_iff dvd_rfl).2 hdvd'

end Arith

open scoped Classical in
omit [Fintype G] in
private theorem one_mem_I [Finite G] : (1 : G → ℤ) ∈ (I : Submodule ℤ (G → ℤ)) := by
  have := Fintype.ofFinite G
  by_contra h1
  set R := ↥(Psub : Subring (G → ℤ)) with hR
  let J : Ideal R :=
    { carrier := {r | (r : G → ℤ) ∈ (I : Submodule ℤ (G → ℤ))}
      add_mem' := fun {a b} ha hb => by
        change ((a + b : R) : G → ℤ) ∈ (I : Submodule ℤ (G → ℤ))
        rw [AddMemClass.coe_add]; exact Submodule.add_mem _ ha hb
      zero_mem' := by
        change ((0 : R) : G → ℤ) ∈ (I : Submodule ℤ (G → ℤ))
        rw [ZeroMemClass.coe_zero]; exact Submodule.zero_mem _
      smul_mem' := fun c r hr => by
        change ((c * r : R) : G → ℤ) ∈ (I : Submodule ℤ (G → ℤ))
        rw [MulMemClass.coe_mul]; exact mul_mem_I c.2 hr }
  have hJ : J ≠ ⊤ := by
    intro h
    apply h1
    have : (1 : R) ∈ J := h ▸ Submodule.mem_top
    exact this
  obtain ⟨𝔪, h𝔪, hJ𝔪⟩ := Ideal.exists_le_maximal J hJ
  have := h𝔪
  let kf : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  obtain ⟨p, hp⟩ := CharP.exists (R ⧸ 𝔪)
  have := hp
  have hp' : p.Prime ∨ p = 0 := CharP.char_is_prime_or_zero (R ⧸ 𝔪) p
  have : Module.Finite ℤ R :=
    Module.Finite.of_injective (Psub : Subring (G → ℤ)).subtype.toAddMonoidHom.toIntLinearMap
      Subtype.val_injective
  have : Algebra.IsIntegral ℤ R := Algebra.IsIntegral.of_finite ℤ R
  have hcomap : (𝔪.comap (algebraMap ℤ R)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap ℤ R)
      (fun x => Algebra.IsIntegral.isIntegral x) 𝔪
  have hp0 : p ≠ 0 := by
    rintro rfl
    have : CharZero (R ⧸ 𝔪) := CharP.charP_to_charZero (R ⧸ 𝔪)
    have hbot : 𝔪.comap (algebraMap ℤ R) = ⊥ := by
      ext n
      rw [Ideal.mem_comap, Ideal.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem, eq_intCast,
        map_intCast, Int.cast_eq_zero]
    rw [hbot] at hcomap
    have h2 : (Ideal.span {(2 : ℤ)} : Ideal ℤ) = ⊤ := by
      apply hcomap.1.2
      rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      norm_num
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton] at h2
    norm_num at h2
  have hpprime : p.Prime := hp'.resolve_right hp0
  have : Fact p.Prime := ⟨hpprime⟩
  have hpm : (algebraMap ℤ R p) ∈ 𝔪 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, eq_intCast, map_intCast, Int.cast_natCast]
    exact CharP.cast_eq_zero (R ⧸ 𝔪) p
  have : Algebra.IsIntegral ℤ (G → ℤ) := Algebra.IsIntegral.of_finite ℤ _
  have : Algebra.IsIntegral R (G → ℤ) := Algebra.IsIntegral.tower_top (R := ℤ)
  have hker : RingHom.ker (algebraMap R (G → ℤ)) ≤ 𝔪 := by
    have : RingHom.ker (algebraMap R (G → ℤ)) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective
    rw [this]; exact bot_le
  obtain ⟨𝔐, h𝔐max, h𝔐⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔪 hker
  have h𝔐prime : 𝔐.IsPrime := h𝔐max.isPrime
  have hmem𝔐 : ∀ r : R, r ∈ 𝔪 ↔ (r : G → ℤ) ∈ 𝔐 := by
    intro r
    rw [← h𝔐, Ideal.mem_comap]
    rfl
  set e : G → (G → ℤ) := fun x => Pi.single x 1 with he
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, e x₀ ∉ 𝔐 := by
    by_contra hall
    push Not at hall
    apply h𝔐max.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : G → ℤ) = ∑ x : G, e x := by
      funext y
      rw [Finset.sum_apply]
      simp [he, Pi.single_apply]
    rw [this]
    exact Ideal.sum_mem _ fun x _ => hall x
  have hp𝔐 : (algebraMap ℤ (G → ℤ) p) ∈ 𝔐 := by
    have := (hmem𝔐 _).1 hpm
    simp only [map_natCast] at this
    exact this
  have hconst : ∀ n : ℤ, algebraMap ℤ (G → ℤ) n ∈ 𝔐 ↔ (p : ℤ) ∣ n := by
    intro n
    constructor
    · intro hn
      by_contra hnd
      have hcop : IsCoprime (p : ℤ) n :=
        (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hpprime).irreducible).2 hnd
      obtain ⟨c, d, hcd⟩ := hcop
      apply h𝔐max.ne_top
      rw [Ideal.eq_top_iff_one]
      have : (1 : G → ℤ) = algebraMap ℤ (G → ℤ) c * algebraMap ℤ (G → ℤ) p +
          algebraMap ℤ (G → ℤ) d * algebraMap ℤ (G → ℤ) n := by
        rw [← map_mul, ← map_mul, ← map_add, hcd, map_one]
      rw [this]
      exact 𝔐.add_mem (𝔐.mul_mem_left _ hp𝔐) (𝔐.mul_mem_left _ hn)
    · rintro ⟨t, rfl⟩
      rw [map_mul]
      exact 𝔐.mul_mem_right _ hp𝔐
  have key : ∀ f : G → ℤ, f ∈ 𝔐 ↔ (p : ℤ) ∣ f x₀ := by
    intro f
    have hfe : f * e x₀ = algebraMap ℤ (G → ℤ) (f x₀) * e x₀ := by
      funext y
      by_cases hy : y = x₀
      · subst hy; simp [he]
      · simp [he, hy]
    have h1e : 1 - e x₀ ∈ 𝔐 := by
      have hz : (1 - e x₀) * e x₀ = 0 := by
        funext y
        by_cases hy : y = x₀
        · subst hy; simp [he]
        · simp [he, hy]
      rcases h𝔐prime.mem_or_mem (hz ▸ 𝔐.zero_mem : (1 - e x₀) * e x₀ ∈ 𝔐) with h | h
      · exact h
      · exact absurd h hx₀
    rw [← hconst]
    constructor
    · intro hf
      have : algebraMap ℤ (G → ℤ) (f x₀) * e x₀ ∈ 𝔐 := hfe ▸ 𝔐.mul_mem_right _ hf
      rcases h𝔐prime.mem_or_mem this with h | h
      · exact h
      · exact absurd h hx₀
    · intro hf
      have h2 : f * e x₀ ∈ 𝔐 := hfe ▸ 𝔐.mul_mem_right _ hf
      have h3 : f * (1 - e x₀) ∈ 𝔐 := 𝔐.mul_mem_left _ h1e
      have : f = f * e x₀ + f * (1 - e x₀) := by ring
      rw [this]
      exact 𝔐.add_mem h2 h3
  obtain ⟨H, hH, hndvd⟩ := exists_isHyper_not_dvd p x₀
  have hI : pc H ∈ (I : Submodule ℤ (G → ℤ)) := Submodule.subset_span ⟨H, hH, rfl⟩
  have hm : (⟨pc H, I_le_P hI⟩ : R) ∈ 𝔪 := hJ𝔪 hI
  rw [hmem𝔐] at hm
  exact hndvd ((key _).1 hm)

private theorem main : ∃ (k : ℕ) (H : Fin k → Subgroup G) (a : Fin k → ℤ),
    (∀ i, IsHyper (H i)) ∧
    ∀ g : G, (1 : ℚ) = ∑ i, (a i : ℚ) * ClassFunction.induced (H i) (fun _ => (1 : ℚ)) g := by
  have h1 := (one_mem_I : (1 : G → ℤ) ∈ (I : Submodule ℤ (G → ℤ)))
  rw [I, Set.image_eq_range] at h1
  set T := {S : Subgroup G | IsHyper S} with hT
  have : Fintype T := Fintype.ofFinite _
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h1
  set k := Fintype.card T
  let ε : T ≃ Fin k := Fintype.equivFin T
  refine ⟨k, fun i => (ε.symm i).1, fun i => c (ε.symm i), fun i => (ε.symm i).2, fun g => ?_⟩
  have hg := congrFun hc g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at hg
  simp_rw [induced_one_eq_pc]
  rw [Fintype.sum_equiv ε.symm (fun i => (c (ε.symm i) : ℚ) * (pc (ε.symm i).1 g : ℚ))
    (fun t => (c t : ℚ) * (pc t.1 g : ℚ)) (fun _ => rfl)]
  exact_mod_cast hg.symm

end SolomonProof

/-- **Solomon's induction theorem.** For a finite group `G` there are finitely many subgroups
`H i` and integers `a i : ℤ` with `1 = ∑ i, a i * induced (H i) 1` as functions `G → ℚ`, where
`induced (H i) 1` is the permutation character of `G` on `G ⧸ H i`, induced over `ℚ`. Each `H i`
is hyperelementary for some prime `q`: it contains a cyclic subgroup `C` of order prime to `q`,
normalized by `H i`, such that every element of `H i` has a `q`-power in `C`. -/
public theorem exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
    {G : Type*} [Group G] [Fintype G] :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (a : Fin k → ℤ),
      (∀ i, ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H i ∧ IsCyclic C ∧
        (Nat.card C).Coprime q ∧
        (∀ h ∈ H i, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H i, ∃ n : ℕ, h ^ q ^ n ∈ C)) ∧
      ∀ g : G, (1 : ℚ) = ∑ i, (a i : ℚ) * ClassFunction.induced (H i) (fun _ => (1 : ℚ)) g := by
  obtain ⟨k, H, a, hH, h1⟩ := SolomonProof.main (G := G)
  exact ⟨k, H, a, hH, h1⟩

end ClassFunction

end
