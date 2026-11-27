/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Large automorphisms of `p`-groups and cyclic subgroups (Kourovka Notebook Problem 15.32)

Kourovka Notebook, Problem 15.32 (Ya. G. Berkovich): does there exist a function `f(k)` (possibly
depending also on `p`) such that if a finite `p`-group `G` of order `pᵐ` with `m ≥ f(k)` has an
automorphism of order `p^(m-k)`, then `G` possesses a cyclic subgroup of index `pᵏ`?

The main theorem proves the stated threshold using iterated Frattini subgroups and transfer
from the centralizer of a characteristic cyclic subgroup.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.32 (Ya. G. Berkovich). UnsolvedMath
record UM-00701120 (`KOU-15.32`), dataset ulamai/UnsolvedMath v1.8.0.

The function is replaced by the explicit threshold `f(k) = 64k + 2` of the resolution, which does
not depend on `p` and implies the existential reading. `m - k` is natural subtraction, harmless
since `m > k`.
-/

namespace MathlibExt.GroupTheory.LargeAutomorphismCyclicSubgroupKourovka15Problem32Wanted

/-- **Kourovka Problem 15.32: large automorphisms and cyclic subgroups.** For every prime $p$ and
all natural numbers $k$ and $m$ with $m \ge 64k + 2$, every finite group $G$ of order $p^m$ that
has an automorphism of order $p^{m-k}$ has a cyclic subgroup of index $p^k$.

Kourovka 15.32 (Ya. G. Berkovich) asks for some threshold $f(k)$ beyond which this holds; the
threshold $f(k) = 64k + 2$ is the one of its resolution. -/
@[expose] public def cyclicSubgroupOfIndexFromLargeAutomorphism : Prop :=
  ∀ p k m : ℕ, p.Prime → 64 * k + 2 ≤ m → ∀ (G : Type) [Group G] [Finite G], Nat.card G = p ^ m →
    (∃ φ : MulAut G, orderOf φ = p ^ (m - k)) → ∃ C : Subgroup G, IsCyclic C ∧ C.index = p ^ k

open Equiv Equiv.Perm Subgroup
open scoped IsMulCommutative

universe u

private def quotientAut {G : Type*} [Group G] (N : Subgroup G) [N.Characteristic] :
    MulAut G →* MulAut (G ⧸ N) where
  toFun f := QuotientGroup.congr N N f (characteristic_iff_map_eq.mp inferInstance f)
  map_one' := DFunLike.ext _ _ (QuotientGroup.mk_surjective.forall.mpr fun _ => rfl)
  map_mul' _ _ := DFunLike.ext _ _ (QuotientGroup.mk_surjective.forall.mpr fun _ => rfl)

private theorem frattini_pow_mem {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (x : G) : x ^ p ∈ frattini G := by
  have := hG.isNilpotent
  change x ^ p ∈ ⨅ H : Subgroup G, ⨅ _ : IsCoatom H, H
  simp only [Subgroup.mem_iInf]
  intro H hH
  have := Group.normalizerCondition_of_isNilpotent.normal_of_coatom H hH
  rw [← hG.isCoatom_iff_index_eq_prime.mp hH]
  exact H.pow_index_mem x

private theorem frattini_quot_comm {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (x y : G ⧸ frattini G) : x * y = y * x := by
  have := hG.isNilpotent
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  change (x * y)⁻¹ * (y * x) ∈ ⨅ H : Subgroup G, ⨅ _ : IsCoatom H, H
  simp only [Subgroup.mem_iInf]
  intro H hH
  have hN := Group.normalizerCondition_of_isNilpotent.normal_of_coatom H hH
  have hcyc : IsCyclic (G ⧸ H) :=
    isCyclic_of_prime_card (H.index_eq_card.symm.trans (hG.isCoatom_iff_index_eq_prime.mp hH))
  apply (QuotientGroup.eq_one_iff _).mp
  let f := QuotientGroup.mk' H
  change f ((x * y)⁻¹ * (y * x)) = 1
  have hc := hcyc.isMulCommutative.is_comm.comm (f x) (f y)
  simp only [map_mul, map_inv]
  rw [hc, inv_mul_cancel]

private theorem isCyclic_of_frattini_quot {G : Type*} [Group G] [Finite G]
    (h : IsCyclic (G ⧸ frattini G)) : IsCyclic G := by
  obtain ⟨y, hy⟩ := isCyclic_iff_exists_zpowers_eq_top.mp h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, frattini_nongenerating ?_⟩
  rw [← QuotientGroup.ker_mk' (frattini G), ← Subgroup.comap_map_eq, MonoidHom.map_zpowers]
  change (zpowers (QuotientGroup.mk x)).comap _ = ⊤
  rw [hy, Subgroup.comap_top]

/-- A linear automorphism of p-power order over `ZMod p` is unipotent. -/
private theorem linear_p_power_eq_one {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] [Nontrivial V] {a b : ℕ}
    (f : Module.End (ZMod p) V) (hf : f ^ p ^ a = 1)
    (hbd : Module.finrank (ZMod p) V ≤ p ^ b) : f ^ p ^ b = 1 := by
  have : CharP (Module.End (ZMod p) V) p :=
    charP_of_injective_ringHom (algebraMap (ZMod p) (Module.End (ZMod p) V)).injective p
  let N : Module.End (ZMod p) V := f - 1
  have hN (n : ℕ) : N ^ p ^ n = f ^ p ^ n - 1 := by
    dsimp only [N]
    rw [sub_pow_char_pow_of_commute p n (Commute.one_right _), one_pow]
  have hNa : N ^ p ^ a = 0 := by rw [hN, hf, sub_self]
  have hNb : N ^ p ^ b = 0 := by
    apply LinearMap.ker_eq_top.mp
    have hle := Module.End.ker_pow_le_ker_pow_finrank N (p ^ a)
    rw [hNa, LinearMap.ker_zero] at hle
    rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hbd]
    exact top_le_iff.mp hle
  exact sub_eq_zero.mp ((hN b).symm.trans hNb)

private def elementaryAutEnd {p : ℕ} {G : Type*} [CommGroup G]
    [Module (ZMod p) (Additive G)] : MulAut G →* Module.End (ZMod p) (Additive G) where
  toFun f := AddMonoidHom.toZModLinearMap p (MulEquiv.toAdditive f).toAddMonoidHom
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

private theorem elementary_aut_bound_aux {G : Type*} [CommGroup G] [Finite G]
    [Nontrivial G] {p d a b : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive G)]
    [Module.Finite (ZMod p) (Additive G)] (hcard : Nat.card G = p ^ d)
    (f : MulAut G) (hf : f ^ p ^ a = 1) (hbd : d ≤ p ^ b) : f ^ p ^ b = 1 := by
  have : Nontrivial (Additive G) := ‹Nontrivial G›
  let lift : MulAut G →* Module.End (ZMod p) (Additive G) := elementaryAutEnd
  have hdim : Module.finrank (ZMod p) (Additive G) = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive G)
    rw [Nat.card_zmod] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le) (h.symm.trans hcard)
  have hf' : (lift f) ^ p ^ a = 1 := by rw [← map_pow, hf, map_one]
  have hb' := linear_p_power_eq_one (lift f) hf' (hdim.symm ▸ hbd)
  rw [← map_pow] at hb'
  apply DFunLike.ext
  intro x
  have he := DFunLike.congr_fun hb' (Additive.ofMul x)
  change Additive.ofMul ((f ^ p ^ b) x) = Additive.ofMul x at he
  exact congrArg Additive.toMul he

private theorem elementary_aut_bound {G : Type*} [CommGroup G] [Finite G]
    {p d a b : ℕ} [Fact p.Prime] (hexp : ∀ x : G, x ^ p = 1) (hcard : Nat.card G = p ^ d)
    (f : MulAut G) (hf : f ^ p ^ a = 1) (hbd : d ≤ p ^ b) : f ^ p ^ b = 1 := by
  rcases subsingleton_or_nontrivial G with hG | hG
  · exact DFunLike.ext _ _ fun _ => Subsingleton.elim _ _
  let addModule : Module (ZMod p) (Additive G) := AddCommGroup.zmodModule hexp
  have finiteModule : Module.Finite (ZMod p) (Additive G) := Module.Finite.of_finite
  exact @elementary_aut_bound_aux G _ _ hG p d a b _ addModule finiteModule hcard f hf hbd

private def affinePerm {G : Type*} [Group G] (f : MulAut G) (c : G) : Perm G :=
  Equiv.mulLeft c * MulAut.toPerm G f

private theorem affine_pow_mul {G : Type*} [Group G] (f : MulAut G) (c x y : G) (n : ℕ) :
    (affinePerm f c ^ n) (x * y) = (affinePerm f c ^ n) x * (f ^ n) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', MulAut.mul_apply, Perm.mul_apply]
    change c * f ((affinePerm f c ^ n) x * (f ^ n) y) =
      c * f ((affinePerm f c ^ n) x) * f ((f ^ n) y)
    rw [map_mul, mul_assoc]

private theorem affine_perm_isP {G : Type*} [Group G] {p a m : ℕ}
    (hG : ∀ g : G, g ^ p ^ m = 1) (f : MulAut G) (hf : f ^ p ^ a = 1) (c : G) :
    affinePerm f c ^ p ^ (a + m) = 1 := by
  have h (x : G) : (affinePerm f c ^ p ^ a) x = (affinePerm f c ^ p ^ a) 1 * x := by
    simpa [hf] using affine_pow_mul f c 1 x (p ^ a)
  have h' : affinePerm f c ^ p ^ a = Equiv.mulLeft ((affinePerm f c ^ p ^ a) 1) :=
    Equiv.ext h
  rw [pow_add, pow_mul, h']
  apply Equiv.ext
  intro x
  have heq (g : G) (n : ℕ) : (Equiv.mulLeft g ^ n) x = g ^ n * x := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih, pow_succ']; exact (mul_assoc _ _ _).symm
  rw [heq, hG, one_mul, Perm.one_apply]

private theorem perm_bound_by_support {X : Type*} [Fintype X] [DecidableEq X] {p a t : ℕ}
    (hp : p.Prime) (s : Perm X) (hs : s ^ p ^ a = 1)
    (hsize : s.cycleType.sum < p ^ (t + 1)) : s ^ p ^ t = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have hd := (dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hs)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  refine pow_dvd_pow _ (Nat.lt_succ_iff.mp ?_)
  exact (pow_lt_pow_iff_right₀ hp.one_lt).mp ((Multiset.le_sum_of_mem hn).trans_lt hsize)

private theorem perm_bound {X : Type*} [Finite X] {p a t : ℕ}
    (hp : p.Prime) (s : Perm X) (hs : s ^ p ^ a = 1)
    (hsize : Nat.card X < p ^ (t + 1)) : s ^ p ^ t = 1 := by
  classical
  let := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card] at hsize
  exact perm_bound_by_support hp s hs (s.sum_cycleType_le.trans_lt hsize)

private theorem affine_pow_frattini {G : Type*} [Group G] [Finite G] {p : ℕ}
    (c x : G) {f : MulAut G} (hf : quotientAut (frattini G) f = 1)
    (hc : c ^ p ∈ frattini G) :
    x⁻¹ * (affinePerm f c ^ p) x ∈ frattini G := by
  let F := frattini G
  let π := QuotientGroup.mk' F
  have hf' (z : G) : π (f z) = π z :=
    DFunLike.congr_fun hf (π z)
  have h (n : ℕ) : π ((affinePerm f c ^ n) x) = π c ^ n * π x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, pow_succ']
      change π (c * f ((affinePerm f c ^ n) x)) = _
      rw [map_mul, hf', ih, mul_assoc]
  apply (QuotientGroup.eq_one_iff _).mp
  change π (x⁻¹ * (affinePerm f c ^ p) x) = 1
  rw [map_mul, map_inv, h, ← map_pow]
  have hcard : π (c ^ p) = 1 := (QuotientGroup.eq_one_iff _).mpr hc
  simp [hcard]

private theorem affine_pow_on_coset {G : Type*} [Group G] (F : Subgroup G)
    [F.Characteristic] (f : MulAut G) (c x : G) (n : ℕ)
    (hx : x⁻¹ * (affinePerm f c ^ n) x ∈ F) :
    ∀ (j : ℕ) (y : F),
      ((affinePerm f c ^ n) ^ j) (x * y) =
        x * (↑((affinePerm (MulAut.characteristic F (f ^ n)) ⟨_, hx⟩ ^ j) y) : G) := by
  intro j y
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Perm.mul_apply, ih, affine_pow_mul, pow_succ', Perm.mul_apply]
    change (affinePerm f c ^ n) x * (f ^ n) _ = x * ((x⁻¹ * (affinePerm f c ^ n) x) * (f ^ n) _)
    simp [← mul_assoc]

/-- Iterate the Frattini subgroup down to the first cyclic term. Each earlier factor of
order `p ^ d` contributes `d - 1` to `D`. Once the linear action on each such factor is
trivial, each step takes one p-th power to fix the cosets of the next subgroup. -/
private theorem exists_characteristic_cyclic_frattini_bound {p m : ℕ} [hp : Fact p.Prime]
    {G : Type u} [Group G] [Finite G] (hG : Nat.card G = p ^ m) :
    ∃ (A : Subgroup G) (s D : ℕ), A.Characteristic ∧ IsCyclic A ∧ A.index = p ^ s ∧
      s ≤ 2 * D ∧ D ≤ m ∧
      ∀ (f : MulAut G) (c : G) (a b : ℕ), f ^ p ^ a = 1 → D < p ^ b →
        affinePerm (f ^ p ^ b) c ^ p ^ (m - D) = 1 := by
  induction m using Nat.strong_induction_on generalizing G with
  | ind m ih =>
    by_cases hcyc : IsCyclic G
    · have : IsCyclic (⊤ : Subgroup G) :=
        Subgroup.topEquiv.isCyclic.mpr hcyc
      refine ⟨⊤, 0, 0, inferInstance, this, by simp, by simp, by simp, ?_⟩
      intro f c a b hf _
      have hf' : (f ^ p ^ b) ^ p ^ a = 1 := by
        rw [pow_right_comm, hf, one_pow]
      have hP := affine_perm_isP (m := m) (p := p)
        (fun g => orderOf_dvd_iff_pow_eq_one.mp
          (hG ▸ _root_.orderOf_dvd_natCard g)) _ hf' c
      exact perm_bound hp.out _ hP (by rw [hG, pow_lt_pow_iff_right₀ hp.out.one_lt]; omega)
    · let F := frattini G
      have hP : IsPGroup p G := IsPGroup.of_card hG
      obtain ⟨n, hn⟩ := (hP.to_subgroup F).exists_card_eq
      obtain ⟨d, hd⟩ := (hP.to_quotient F).exists_card_eq
      have hnd : n + d = m := by
        apply Nat.pow_right_injective hp.out.two_le
        change p ^ (n + d) = p ^ m
        rw [pow_add, ← hn, ← hd, ← F.index_eq_card, mul_comm, F.index_mul_card, hG]
      have hd₂ : 2 ≤ d := by
        by_contra! hlt
        apply hcyc
        apply isCyclic_of_frattini_quot
        interval_cases d
        · have : Subsingleton (G ⧸ F) :=
            Finite.card_le_one_iff_subsingleton.mp (by simpa using hd.le)
          exact isCyclic_of_subsingleton
        · exact isCyclic_of_prime_card (by simpa using hd)
      obtain ⟨A, s, D, hchar, hcycA, hi, hs, hm, hpow⟩ := ih n (by omega) hn
      let A' := A.map F.subtype
      refine ⟨A', s + d, D + (d - 1), inferInstance, ?_, ?_, by omega, by omega, ?_⟩
      · exact (A.equivMapOfInjective F.subtype Subtype.coe_injective).isCyclic.mp hcycA
      · have hindex : F.index = p ^ d := F.index_eq_card.trans hd
        rw [Subgroup.index_map_of_injective A Subtype.coe_injective, Subgroup.range_subtype,
          hi, hindex, pow_add]
      intro f c a b hf hD
      have hoff : d ≤ p ^ b := by omega
      have hqexp (x : G ⧸ F) : x ^ p = 1 := by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
        change (QuotientGroup.mk' F x) ^ p = 1
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr (frattini_pow_mem hP x)
      let : CommGroup (G ⧸ F) :=
        { (inferInstance : Group (G ⧸ F)) with mul_comm := frattini_quot_comm hP }
      have hq := elementary_aut_bound hqexp hd (quotientAut F f)
        (by rw [← map_pow, hf, map_one]) hoff
      let g := f ^ p ^ b
      let gF := MulAut.characteristic F f
      have hqg : quotientAut F g = 1 := by rw [map_pow]; exact hq
      have hFpow : gF ^ p ^ a = 1 := by rw [← map_pow, hf, map_one]
      have hsizes : m - (D + (d - 1)) = 1 + (n - D) := by omega
      rw [hsizes, pow_add, pow_one, pow_mul]
      apply Equiv.ext
      intro x
      have hx := affine_pow_frattini c x hqg (frattini_pow_mem hP c)
      let z : F := ⟨x⁻¹ * (affinePerm g c ^ p) x, hx⟩
      have hy := affine_pow_on_coset F g c x p hx (p ^ (n - D)) (1 : F)
      have hgF : MulAut.characteristic F (g ^ p) = gF ^ p ^ (b + 1) := by
        rw [pow_succ, pow_mul, ← map_pow, ← map_pow]
      suffices ((affinePerm g c ^ p) ^ p ^ (n - D)) (x * (↑(1 : F) : G)) = x by
        simpa using this
      rw [hy, hgF, hpow gF z a (b + 1) hFpow]
      · simp
      · exact lt_of_lt_of_le (by omega : D < p ^ b) (pow_le_pow_right₀ hp.out.one_le (by omega))

private theorem cyclic_subgroup_characteristic {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (B : Subgroup A) : B.Characteristic := by
  apply characteristic_iff_map_eq.mpr
  intro f
  apply IsCyclic.subgroup_eq_iff_card_eq.mpr
  exact (Nat.card_congr (B.equivMapOfInjective f.toMonoidHom f.injective)).symm

private theorem cyclic_aut_fixes_order_p {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {p a : ℕ} (hp : p.Prime) (f : MulAut A) (hf : f ^ p ^ a = 1)
    {x : A} (hx : x ^ p = 1) : f x = x := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases heq : x = 1
  · simp [heq]
  let B := zpowers x
  have : B.Characteristic := cyclic_subgroup_characteristic B
  let g := MulAut.characteristic B f
  have hg : g ^ p ^ a = 1 := by rw [← map_pow, hf, map_one]
  have hcard : Nat.card B = p := (Nat.card_zpowers x).trans (orderOf_eq_prime hx heq)
  have ht : Nat.card (MulAut B) = p - 1 := by rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime hp]
  have hd : orderOf g ∣ p - 1 := ht ▸ _root_.orderOf_dvd_natCard g
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hg)
  have := hp.two_le
  have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hd
  have hj0 : j = 0 := by
    by_contra hj0
    have hge : p ≤ p ^ j := by
      simpa using pow_le_pow_right₀ hp.one_le (Nat.one_le_iff_ne_zero.mpr hj0)
    omega
  have hgone : g = 1 := orderOf_eq_one_iff.mp (by simp [hj, hj0])
  exact congrArg Subtype.val (DFunLike.congr_fun hgone ⟨x, mem_zpowers x⟩)

private theorem affine_pow_eq {A : Type*} [Group A] (f : MulAut A) (x : A) (n : ℕ) :
    affinePerm f x ^ n = affinePerm (f ^ n) ((affinePerm f x ^ n) 1) := by
  apply Equiv.ext
  intro y
  change (affinePerm f x ^ n) y = (affinePerm f x ^ n) 1 * (f ^ n) y
  simpa using affine_pow_mul f x 1 y n

/-- Each p-th power of an affine permutation of a cyclic p-group lowers the bound on the
order of its translation part by a factor of `p`. -/
private theorem cyclic_affine_translation_bound {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {p a : ℕ} (hp : p.Prime) (s : ℕ) {f : MulAut A} (hf : f ^ p ^ a = 1)
    {x : A} {r : ℕ} (hx : x ^ p ^ (r + s) = 1) :
    ((affinePerm f x ^ p ^ s) 1) ^ p ^ r = 1 := by
  induction s generalizing f x r with
  | zero =>
    rw [pow_zero, pow_one]
    change (x * f 1) ^ p ^ r = 1
    simpa using hx
  | succ s ih =>
    let T := affinePerm f x
    have hpx : (x ^ p ^ (r + s)) ^ p = 1 := by
      rw [← pow_mul, ← pow_succ, Nat.add_assoc]
      exact hx
    have hfix := cyclic_aut_fixes_order_p hp f hf hpx
    have hiter (n : ℕ) : ((T ^ n) 1) ^ p ^ (r + s) = (x ^ p ^ (r + s)) ^ n := by
      induction n with
      | zero => simp
      | succ n h =>
        rw [pow_succ', Perm.mul_apply]
        change (x * f ((T ^ n) 1)) ^ p ^ (r + s) = _
        rw [mul_pow, ← map_pow, h, map_pow, hfix, pow_succ']
    have hy : ((T ^ p) 1) ^ p ^ (r + s) = 1 := (hiter p).trans hpx
    have hf' : (f ^ p) ^ p ^ a = 1 := by rw [pow_right_comm, hf, one_pow]
    rw [pow_succ', pow_mul, affine_pow_eq f x p]
    exact ih hf' hy

private theorem cyclic_aut_comm {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (f g : MulAut A) : f * g = g * f := by
  apply (IsCyclic.mulAutMulEquiv A).injective
  simp only [map_mul, mul_comm]

private theorem conj_cyclic_invariant {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [A.Characteristic] [IsCyclic A] (f : MulAut G) (x : G) :
    (MulAut.conjNormal (H := A)) (f x) = MulAut.conjNormal x := by
  let F := MulAut.characteristic A f
  apply mul_right_cancel (b := F)
  rw [cyclic_aut_comm (MulAut.conjNormal x) F]
  apply DFunLike.ext _ _
  intro y
  apply Subtype.coe_injective
  simp only [MulAut.mul_apply]
  change (↑(MulAut.conjNormal (f x) (F y)) : G) = f (↑(MulAut.conjNormal x y) : G)
  simp [F]

private theorem displacement_affine {G A : Type*} [Group G] [Group A]
    (C : Subgroup G) [C.Characteristic] (V : C →* A) (f : MulAut G) (g : MulAut A)
    (hV : ∀ c : C, V (MulAut.characteristic C f c) = g (V c)) (x : G)
    (h : ∀ n : ℕ, x⁻¹ * (f ^ n) x ∈ C) (n : ℕ) :
    V ⟨x⁻¹ * (f ^ n) x, h n⟩ =
      (affinePerm g (V ⟨x⁻¹ * f x, by simpa using h 1⟩) ^ n) 1 := by
  let d (n : ℕ) : C := ⟨x⁻¹ * (f ^ n) x, h n⟩
  let y : C := ⟨x⁻¹ * f x, by simpa using h 1⟩
  change V (d n) = (affinePerm g (V y) ^ n) 1
  induction n with
  | zero =>
    rw [pow_zero, Perm.one_apply, ← map_one V]
    congr 1
    apply Subtype.ext
    change x⁻¹ * (f ^ 0) x = 1
    simp
  | succ n ih =>
    have hd : d (n + 1) = y * MulAut.characteristic C f (d n) := by
      apply Subtype.ext
      change x⁻¹ * (f ^ (n + 1)) x = (x⁻¹ * f x) * f (x⁻¹ * (f ^ n) x)
      simp only [pow_succ', MulAut.mul_apply, map_mul, map_inv]
      simp [mul_assoc]
    rw [hd, map_mul, hV, ih, pow_succ', Perm.mul_apply]
    rfl

/-- Transfer from the centralizer of the cyclic subgroup is a power map. Applying it to
the displacement of each point bounds the translation part of the automorphism on every
coset after the quotient action is killed. -/
private theorem aut_pow_eq_one_of_cyclic_index {G : Type*} [Group G] [Finite G]
    {p a e s : ℕ} (hp : p.Prime)
    (A : Subgroup G) [A.Characteristic] [IsCyclic A] (hA : A.index = p ^ s)
    (hE : ∀ x : G, x ^ p ^ e = 1) (he : 2 * s ≤ e)
    (f : MulAut G) (hf : f ^ p ^ a = 1) : f ^ p ^ e = 1 := by
  let χ := MulAut.conjNormal (H := A)
  let C := χ.ker
  have hχ (g : MulAut G) (x : G) : χ (g x) = χ x := conj_cyclic_invariant A g x
  have hC : C.Characteristic := characteristic_iff_le_comap.mpr fun g x hx => by
    change χ (g x) = 1
    rw [hχ]
    exact hx
  have hdis (g : MulAut G) (x : G) : x⁻¹ * g x ∈ C := by
    change χ (x⁻¹ * g x) = 1
    rw [map_mul, map_inv, hχ, inv_mul_cancel]
  have hAC : A ≤ C := by
    intro x hx
    change χ x = 1
    apply DFunLike.ext _ _
    intro y
    apply Subtype.ext
    change x * (y : G) * x⁻¹ = y
    have hm := congrArg Subtype.val (mul_comm (⟨x, hx⟩ : A) y)
    change x * (y : G) = y * x at hm
    rw [hm, mul_inv_cancel_right]
  let B := A.subgroupOf C
  have hB : B.index ∣ p ^ s := hA ▸ Subgroup.relIndex_dvd_index_of_le hAC
  obtain ⟨t, ht, htB⟩ := (Nat.dvd_prime_pow hp).mp hB
  let E := Subgroup.subgroupOfEquivOfLe hAC
  let V := MonoidHom.transfer E.toMonoidHom
  have hcentral (g : C) (b : B) : Commute g (b : C) := by
    have hfix := congrArg Subtype.val (DFunLike.congr_fun (show χ g = 1 from g.2)
      (⟨(b : C), b.2⟩ : A))
    change (g : G) * ((b : C) : G) * (g : G)⁻¹ = ((b : C) : G) at hfix
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hfix)
  have hV (g : C) : (V g : G) = (g : G) ^ p ^ t := by
    have hkey (n : ℕ) (b : C) (hb : b⁻¹ * g ^ n * b ∈ B) :
        b⁻¹ * g ^ n * b = g ^ n := by
      have hcomm := hcentral b ⟨b⁻¹ * g ^ n * b, hb⟩
      change Commute b (b⁻¹ * g ^ n * b) at hcomm
      calc
        b⁻¹ * g ^ n * b = b * (b⁻¹ * g ^ n * b) * b⁻¹ := by
          rw [hcomm.eq, mul_inv_cancel_right]
        _ = g ^ n := by simp [mul_assoc]
    change ((MonoidHom.transfer E.toMonoidHom) g : G) = _
    rw [MonoidHom.transfer_eq_pow _ _ hkey, ← htB]
    rfl
  let fA := MulAut.characteristic A f
  have hfA : fA ^ p ^ a = 1 := by rw [← map_pow, hf, map_one]
  have hVA (c : C) : V (MulAut.characteristic C f c) = fA (V c) := by
    apply Subtype.ext
    rw [hV]
    change f (c : G) ^ p ^ t = f (V c : G)
    rw [hV, map_pow]
  let q := quotientAut A f
  let σ := MulAut.toPerm (G ⧸ A) q
  have hq : σ ^ p ^ a = 1 := by simp [σ, q, ← map_pow, hf]
  have hsiz : Nat.card (G ⧸ A) < p ^ (s + 1) := by
    change A.index < _
    rw [hA]
    exact (pow_lt_pow_iff_right₀ hp.one_lt).mpr (Nat.lt_succ_self s)
  have hfix := perm_bound hp σ hq hsiz
  let β := f ^ p ^ s
  have hβquot : quotientAut A β = 1 := by
    rw [map_pow]
    change (MulAut.toPerm (G ⧸ A) q) ^ p ^ s = 1 at hfix
    rw [← map_pow] at hfix
    exact DFunLike.ext _ _ (fun x => DFunLike.congr_fun hfix x)
  have hβδ (x : G) (n : ℕ) : x⁻¹ * (β ^ n) x ∈ A := by
    let π := QuotientGroup.mk' A
    have hn : quotientAut A (β ^ n) = 1 := by rw [map_pow, hβquot, one_pow]
    have hk : π ((β ^ n) x) = π x := DFunLike.congr_fun hn (π x)
    apply (QuotientGroup.eq_one_iff _).mp
    change π (x⁻¹ * (β ^ n) x) = 1
    rw [map_mul, map_inv, hk, inv_mul_cancel]
  have hs' : s ≤ e := by omega
  have ht' : t + s ≤ e := by omega
  have hfβA : (MulAut.characteristic A β) ^ p ^ a = 1 := by
    rw [← map_pow]
    change MulAut.characteristic A ((f ^ p ^ s) ^ p ^ a) = 1
    rw [pow_right_comm, hf, one_pow, map_one]
  rw [← Nat.add_sub_of_le hs', pow_add, pow_mul]
  apply DFunLike.ext
  intro x
  let c : C := ⟨x⁻¹ * f x, hdis f x⟩
  let z : A := ⟨x⁻¹ * β x, by simpa using hβδ x 1⟩
  have hVc : (V c) ^ p ^ (e - (t + s) + s) = 1 := by
    apply Subtype.ext
    change ((V c : G) ^ p ^ (e - (t + s) + s)) = 1
    rw [hV, ← pow_mul, ← pow_add, show t + (e - (t + s) + s) = e by omega]
    exact hE c
  have hnorm := displacement_affine C V f fA hVA x (fun n => hdis (f ^ n) x) (p ^ s)
  have hδ :
      (V ⟨x⁻¹ * (f ^ p ^ s) x, hdis (f ^ p ^ s) x⟩) ^ p ^ (e - (t + s)) = 1 := by
    rw [hnorm]
    exact cyclic_affine_translation_bound hp s hfA hVc
  have hz : z ^ p ^ (e - s) = 1 := by
    apply Subtype.ext
    have hw := congrArg Subtype.val hδ
    change ((V ⟨x⁻¹ * (f ^ p ^ s) x, hdis (f ^ p ^ s) x⟩ : G) ^ p ^ (e - (t + s))) = 1 at hw
    rw [hV, ← pow_mul, ← pow_add, show t + (e - (t + s)) = e - s by omega] at hw
    exact hw
  have hnorm' := displacement_affine A (MonoidHom.id A) β (MulAut.characteristic A β)
    (fun _ => rfl) x (hβδ x) (p ^ (e - s))
  have hkill := cyclic_affine_translation_bound hp (e - s) hfβA (r := 0) (by simpa using hz)
  have hδone : (⟨x⁻¹ * (β ^ p ^ (e - s)) x, hβδ x _⟩ : A) = 1 :=
    hnorm'.trans (by simpa [MonoidHom.id_apply] using hkill)
  have hk := congrArg Subtype.val hδone
  change x⁻¹ * (β ^ p ^ (e - s)) x = 1 at hk
  exact (inv_mul_eq_one.mp hk).symm

private theorem aut_order_ne_group_card {G : Type*} [Group G] [Finite G]
    {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hG : Nat.card G = p ^ m) (φ : MulAut G) :
    orderOf φ ≠ p ^ m := by
  classical
  let := Fintype.ofFinite G
  intro hφ
  let s := MulAut.toPerm G φ
  have hsize : s.cycleType.sum < p ^ m := by
    rw [sum_cycleType, ← hG, Nat.card_eq_fintype_card, ← Finset.card_univ]
    apply Finset.card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, fun heq => by
        have hmem : (1 : G) ∈ s.support := heq ▸ Finset.mem_univ 1
        exact mem_support.mp hmem (map_one φ)⟩
  have hord : orderOf s = p ^ m :=
    (orderOf_injective (MulAut.toPerm G) (fun _ _ h => DFunLike.ext _ _ fun x =>
      DFunLike.congr_fun h x) φ).trans hφ
  have hpow : s ^ p ^ m = 1 := by rw [← hord, pow_orderOf_eq_one]
  have hpred := perm_bound_by_support (t := m - 1) hp s hpow (by
    rwa [Nat.sub_add_cancel hm])
  have hle := Nat.le_of_dvd (pow_pos hp.pos _) (orderOf_dvd_of_pow_eq_one hpred)
  rw [hord, pow_le_pow_iff_right₀ hp.one_lt] at hle
  omega

private theorem exists_cyclic_of_order {G : Type*} [Group G] [Finite G] {p k m : ℕ}
    (hp : p.Prime) (hkm : k ≤ m) (hG : Nat.card G = p ^ m)
    {x : G} (hx : orderOf x = p ^ (m - k)) :
    ∃ C : Subgroup G, IsCyclic C ∧ C.index = p ^ k := by
  let C := Subgroup.zpowers x
  have hc : Nat.card C = p ^ (m - k) := (Nat.card_zpowers x).trans hx
  have hpow : p ^ k * p ^ (m - k) = p ^ m := by rw [← pow_add, Nat.add_sub_of_le hkm]
  exact ⟨C, inferInstance, Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) (by
    rw [← hc, C.index_mul_card, hG, hc, hpow])⟩

private theorem exists_cyclic_of_large_aut {G : Type*} [Group G] [Finite G]
    {p k m : ℕ} (hp : p.Prime) (hm : 64 * k + 2 ≤ m) (hG : Nat.card G = p ^ m)
    (f : MulAut G) (hf : orderOf f = p ^ (m - k)) :
    ∃ C : Subgroup G, IsCyclic C ∧ C.index = p ^ k := by
  have hkm : k ≤ m := by omega
  by_cases hk0 : k = 0
  · subst k
    exact (aut_order_ne_group_card hp (by omega) hG f (by simpa using hf)).elim
  have : Fact p.Prime := ⟨hp⟩
  have hfp : f ^ p ^ (m - k) = 1 := by rw [← hf, pow_orderOf_eq_one]
  obtain ⟨A, s, D, hchar, hcyc, hindex, hsD, hDm, hpow⟩ :=
    exists_characteristic_cyclic_frattini_bound hG
  let b := D / 2 + 1
  have hDb : D < p ^ b := by
    have hq : D / 2 + 1 ≤ p ^ (D / 2) := Nat.lt_pow_self hp.one_lt
    have hprod := Nat.mul_le_mul hp.two_le hq
    rw [← pow_succ'] at hprod
    exact (show D < 2 * (D / 2 + 1) by omega).trans_le hprod
  have hfb := hpow f 1 (m - k) b hfp hDb
  have hleft (g : MulAut G) : affinePerm g 1 = MulAut.toPerm G g := by
    apply Equiv.ext
    intro x
    change 1 * g x = g x
    rw [one_mul]
  rw [hleft, ← map_pow] at hfb
  have hpowf : f ^ p ^ (b + (m - D)) = 1 := by
    rw [pow_add, pow_mul]
    exact DFunLike.ext _ _ (fun x => DFunLike.congr_fun hfb x)
  have ha := Nat.le_of_dvd (pow_pos hp.pos _) (orderOf_dvd_of_pow_eq_one hpowf)
  rw [hf, pow_le_pow_iff_right₀ hp.one_lt] at ha
  have hs : s ≤ 8 * k := by dsimp [b] at ha; omega
  have hP := IsPGroup.of_card hG
  choose ord hord using hP.exists_orderOf_eq_pow
  obtain ⟨g, hmax⟩ := Finite.exists_max ord
  let e := ord g
  have hE (x : G) : x ^ p ^ e = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hord]
    exact pow_dvd_pow _ (hmax x)
  obtain ⟨d, hd⟩ := (hP.to_subgroup A).exists_card_eq
  have hsd : s + d = m := by
    apply Nat.pow_right_injective hp.two_le
    change p ^ (s + d) = p ^ m
    rw [pow_add, ← hindex, ← hd, A.index_mul_card, hG]
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
  have hdx : orderOf (x : G) = p ^ d := (Subgroup.orderOf_coe x).trans (hx.trans hd)
  have hde := Nat.le_of_dvd (pow_pos hp.pos _) (orderOf_dvd_of_pow_eq_one (hE x))
  rw [hdx, pow_le_pow_iff_right₀ hp.one_lt] at hde
  have hkill := aut_pow_eq_one_of_cyclic_index hp A hindex hE (by omega : 2 * s ≤ e) f hfp
  have hae := Nat.le_of_dvd (pow_pos hp.pos _) (orderOf_dvd_of_pow_eq_one hkill)
  rw [hf, pow_le_pow_iff_right₀ hp.one_lt] at hae
  refine exists_cyclic_of_order hp hkm hG (x := g ^ p ^ (e - (m - k))) ?_
  have hv : p ^ (e - (m - k)) ∣ orderOf g := by
    rw [hord]
    exact pow_dvd_pow _ (Nat.sub_le _ _)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hv, hord,
    Nat.pow_div (Nat.sub_le _ _) hp.pos, Nat.sub_sub_self hae]

/--
**Large automorphisms of p-groups force cyclic subgroups of given index.** For every prime $p$ and
all natural numbers $k$ and $m$ with $m \ge 64k + 2$, if a finite group $G$ of order $p^m$ has an
automorphism of order $p^{m-k}$, then $G$ has a cyclic subgroup of index $p^k$.

Resolved true: Jayadevan proved this with the threshold $f(k) = 64k + 2$; the Kourovka Notebook
(21st issue) marks 15.32 solved, "Yes, one can take $f(k) = 64k + 2$" (AI solution confirmed by
A. Caranti).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.32 (Ya. G.
Berkovich); resolution: A. Jayadevan, Large-order automorphisms of finite p-groups force cyclic
subgroups of prescribed index, preprint, Zenodo record 22910914 (2026), AI-generated solution
confirmed by A. Caranti, main theorem (for every k ≥ 0, a group of order p^m with m ≥ 64k + 2 and an
automorphism of order p^(m-k) has a cyclic subgroup of index exactly p^k); the Kourovka Notebook
(21st issue) marks 15.32 solved, https://zenodo.org/records/22910914.
-/
public theorem cyclicSubgroupOfIndexFromLargeAutomorphism_holds :
    cyclicSubgroupOfIndexFromLargeAutomorphism := by
  rintro p k m hp hm G _ _ hG ⟨f, hf⟩
  exact exists_cyclic_of_large_aut hp hm hG f hf

end MathlibExt.GroupTheory.LargeAutomorphismCyclicSubgroupKourovka15Problem32Wanted
