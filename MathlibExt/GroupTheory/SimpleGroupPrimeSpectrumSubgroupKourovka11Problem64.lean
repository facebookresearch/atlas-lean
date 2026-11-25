/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Proper subgroups with the same prime divisors as a simple group (Kourovka Notebook Problem 11.64)

Four-dimensional symplectic groups in characteristic two give unbounded examples of
non-alternating finite simple groups with a proper subgroup of the same prime set.

Kourovka Notebook, Archive of Solved Problems, Problem 11.64 (V. S. Monakhov): are there only
finitely many finite simple groups `G`, other than alternating groups, with a proper subgroup `H`
such that `π(H) = π(G)` (`π` the set of prime divisors of the order)?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.64 (V. S.
Monakhov). UnsolvedMath record UM-00700756 (`KOU-11.64`), dataset ulamai/UnsolvedMath v1.8.0.

"Finitely many" up to isomorphism is a bound on `|G|`, an equivalent form since there are finitely
many groups of each order. "Different from alternating groups" excludes every `G` isomorphic to some
`Alt(n)`. `π(X)` is `(Nat.card X).primeFactors`.
-/

open LinearMap (BilinForm)
open MulAction Projectivization
open scoped Pointwise commutatorElement LinearAlgebra.Projectivization

namespace MathlibExt.GroupTheory.SimpleGroupPrimeSpectrumSubgroupKourovka11Problem64Wanted

/-- **Kourovka Problem 11.64 (Monakhov).** The statement that there is a natural number $N$ such
that every finite simple group $G$ that is not isomorphic to the alternating group $A_n$ for any
natural number $n$ and has a proper subgroup $H$ with $\pi(H) = \pi(G)$ satisfies $|G| \le N$,
where $\pi(X)$ denotes the set of prime divisors of the order $|X|$.

Since there are finitely many groups of each order, this says that only finitely many such groups
$G$ exist up to isomorphism. -/
@[expose] public def finitelyManySimpleWithFullSpectrumSubgroup : Prop :=
  ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∀ n : ℕ, IsEmpty (G ≃* alternatingGroup (Fin n))) →
    (∃ H : Subgroup G, H ≠ ⊤ ∧ (Nat.card H).primeFactors = (Nat.card G).primeFactors) →
    Nat.card G ≤ N

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm K V}

private def sp (B : BilinForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, B (g x) (g y) = B x y}
  one_mem' := fun _ _ => rfl
  mul_mem' hg hh x y := (hg _ _).trans (hh _ _)
  inv_mem' {g} hg x y := by
    change B (g.symm x) (g.symm y) = B x y
    simpa only [LinearEquiv.apply_symm_apply] using (hg (g.symm x) (g.symm y)).symm

private instance spDistribMulAction : DistribMulAction (sp B) V :=
  DistribMulAction.compHom V (sp B).subtype

private instance spSMulCommClass : SMulCommClass (sp B) K V :=
  ⟨fun g a x => g.val.map_smul a x⟩

private lemma sp_one_smul (x : V) : (1 : sp B) • x = x := rfl

private lemma sp_mul_smul (g h : sp B) (x : V) : (g * h) • x = g • (h • x) := rfl

private lemma sp_smul_comm (g : sp B) (c : K) (x : V) : g • (c • x) = c • (g • x) :=
  g.val.map_smul c x

private lemma sp_smul_add (g : sp B) (x y : V) : g • (x + y) = g • x + g • y :=
  g.val.map_add x y

private lemma form_smul (g : sp B) (x y : V) : B (g • x) (g • y) = B x y :=
  g.property x y

private lemma sp_ext {g h : sp B} (e : ∀ x : V, g • x = h • x) : g = h :=
  Subtype.ext (LinearEquiv.ext e)

private def transv (hB : B.IsAlt) (v : V) (c : K) : sp B :=
  ⟨LinearEquiv.transvection (f := c • B v) (v := v) (by simp [hB.self_eq_zero]), by
    intro x y
    simp only [LinearEquiv.transvection.apply, LinearMap.smul_apply,
      BilinForm.add_left, BilinForm.add_right, BilinForm.smul_left, BilinForm.smul_right,
      hB.self_eq_zero, smul_eq_mul, mul_zero, add_zero, ← hB.neg_eq v x]
    ring⟩

private lemma transv_apply (hB : B.IsAlt) (v : V) (c : K) (x : V) :
    transv hB v c • x = x + (c * B v x) • v := rfl

private lemma transv_same (hB : B.IsAlt) (v : V) (a b : K) :
    transv hB v (a + b) = transv hB v a * transv hB v b := by
  apply sp_ext
  intro x
  rw [sp_mul_smul]
  simp [transv_apply, hB.self_eq_zero, add_mul, add_smul, add_assoc, add_comm]

private lemma transv_transport (hB : B.IsAlt) (g : sp B) (v : V) (c : K) :
    transv hB (g • v) c * g = g * transv hB v c := by
  apply sp_ext
  intro x
  simp only [sp_mul_smul, transv_apply, form_smul, sp_smul_add, sp_smul_comm]

private lemma transv_scale (hB : B.IsAlt) (v : V) (a c : K) :
    transv hB (a • v) c = transv hB v (c * a ^ 2) := by
  apply sp_ext
  intro x
  simp only [transv_apply, BilinForm.smul_left, smul_smul]
  congr 2
  ring

private lemma transv_send (hB : B.IsAlt) {x y : V} (h : B y x ≠ 0) :
    transv hB (y - x) (B y x)⁻¹ • x = y := by
  have hxy : B (y - x) x = B y x := by simp [hB.self_eq_zero]
  rw [transv_apply, hxy, inv_mul_cancel₀ h, one_smul, add_sub_cancel]

private lemma exists_both_ne_zero {f g : V →ₗ[K] K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ x, f x ≠ 0 ∧ g x ≠ 0 := by
  have exists_ne {f : V →ₗ[K] K} (h : f ≠ 0) : ∃ x, f x ≠ 0 := by
    by_contra! hz
    exact h (LinearMap.ext hz)
  obtain ⟨x, hx⟩ := exists_ne hf
  obtain ⟨y, hy⟩ := exists_ne hg
  by_cases hx' : g x = 0
  · by_cases hy' : f y = 0
    · exact ⟨x + y, by simpa [map_add, hy'] using hx, by simpa [map_add, hx'] using hy⟩
    · exact ⟨y, hy', hy⟩
  · exact ⟨x, hx, hx'⟩

private lemma exists_pairing_ne_zero (hnd : B.Nondegenerate) {x : V} (hx : x ≠ 0) :
    ∃ y, B x y ≠ 0 := by
  by_contra! h
  exact hx (hnd.1 x h)

private lemma sp_transitive_vectors (hB : B.IsAlt) (hnd : B.Nondegenerate)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : ∃ g : sp B, g • x = y := by
  by_cases h : B y x = 0
  · obtain ⟨z, hz₁, hz₂⟩ := exists_both_ne_zero (f := B x) (g := B y)
      (fun e => hx (hnd.1 x fun w => LinearMap.congr_fun e w))
      (fun e => hy (hnd.1 y fun w => LinearMap.congr_fun e w))
    have hz₁' : B z x ≠ 0 := (hB.eq_iff).not.mp hz₁
    exact ⟨transv hB (y - z) (B y z)⁻¹ * transv hB (z - x) (B z x)⁻¹,
      by rw [sp_mul_smul, transv_send hB hz₁', transv_send hB hz₂]⟩
  · exact ⟨_, transv_send hB h⟩

/- A transvection can increase the fixed subspace. If every vector is orthogonal to
its image, a preliminary transvection fixes the old fixed subspace and makes
a second transvection possible. -/
private lemma transv_generate [Module.Finite K V] (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (T : Subgroup (sp B)) (ht : ∀ v c, transv hB v c ∈ T) : T = ⊤ := by
  let Fix (g : sp B) := g.val.toLinearMap.fixedSubmodule
  have fix_iff (g : sp B) (u : V) : u ∈ Fix g ↔ g • u = u := Iff.rfl
  have reduce {g : sp B} {x : V} (hx : B x (g • x) ≠ 0) :
      ∃ t ∈ T, Fix g < Fix (t * g) := by
    let t := transv hB (x - g • x) (B x (g • x))⁻¹
    have fix_le : Fix g ≤ Fix (t * g) := by
      intro u hu
      have e := (fix_iff g u).mp hu
      have hz : B (x - g • x) u = 0 := by
        rw [BilinForm.sub_left, ← e, form_smul, e, sub_self]
      rw [fix_iff, sp_mul_smul, e, transv_apply, hz, mul_zero, zero_smul, add_zero]
    refine ⟨t, ht _ _, lt_of_le_not_ge fix_le fun hle => hx ?_⟩
    have hx' : x ∈ Fix (t * g) := by
      rw [fix_iff, sp_mul_smul, transv_send hB hx]
    rw [(fix_iff g x).mp (hle hx'), hB.self_eq_zero]
  have step {g : sp B} (hg : g ≠ 1) : ∃ t ∈ T, Fix g < Fix (t * g) := by
    by_cases h : ∃ x, B x (g • x) ≠ 0
    · obtain ⟨x, hx⟩ := h
      exact reduce hx
    push Not at h
    obtain ⟨x, hx⟩ : ∃ x : V, g • x ≠ x := by
      by_contra! hn
      exact hg (sp_ext hn)
    let u := x - g • x
    have hu : u ≠ 0 := sub_ne_zero.mpr hx.symm
    let t := transv hB u 1
    have fix_le : Fix g ≤ Fix (t * g) := by
      intro w hw
      have e := (fix_iff g w).mp hw
      have hz : B u w = 0 := by
        dsimp [u]
        rw [BilinForm.sub_left, ← e, form_smul, e, sub_self]
      rw [fix_iff, sp_mul_smul, e, transv_apply, hz, mul_zero, zero_smul, add_zero]
    have hu' : g⁻¹ • u ≠ 0 := (smul_ne_zero_iff_ne _).2 hu
    obtain ⟨w, hw, hw'⟩ := exists_both_ne_zero (f := B u) (g := B (g⁻¹ • u))
      (fun e => hu (hnd.1 u fun v => LinearMap.congr_fun e v))
      (fun e => hu' (hnd.1 _ fun v => LinearMap.congr_fun e v))
    have hw'' : B u (g • w) ≠ 0 := by
      have e : g • (g⁻¹ • u) = u := g.val.apply_symm_apply u
      nth_rw 1 [← e]
      rwa [form_smul]
    have hpair : B w ((t * g) • w) ≠ 0 := by
      rw [sp_mul_smul, transv_apply, BilinForm.add_right, BilinForm.smul_right, h, zero_add,
        one_mul]
      exact mul_ne_zero hw'' ((hB.eq_iff).not.mp hw)
    obtain ⟨s, hs, hlt⟩ := reduce hpair
    exact ⟨s * t, T.mul_mem hs (ht _ _), by rw [mul_assoc]; exact fix_le.trans_lt hlt⟩
  suffices ∀ g : sp B, g ∈ T from eq_top_iff.mpr fun g _ => this g
  intro g
  induction hm : Module.finrank K V - Module.finrank K (Fix g) using Nat.strong_induction_on
    generalizing g with
  | ind n ih =>
    by_cases hg : g = 1
    · simp [hg]
    obtain ⟨t, ht', hlt⟩ := step hg
    have hdim := Submodule.finrank_lt_finrank_of_lt hlt
    have hbound := Submodule.finrank_le (Fix (t * g))
    have he : Module.finrank K V - Module.finrank K (Fix (t * g)) < n := by omega
    have hmem := ih _ he (t * g) rfl
    simpa using T.mul_mem (T.inv_mem ht') hmem

private lemma sp_projective_smul_mk (g : sp B) (x : V) (hx : x ≠ 0) :
    g • mk K x hx = mk K (g • x) ((smul_ne_zero_iff_ne g).mpr hx) :=
  smul_mk g hx

private lemma sp_projective_transitive (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    IsPretransitive (sp B) (ℙ K V) where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := sp_transitive_vectors hB hnd x.rep_ne_zero y.rep_ne_zero
    refine ⟨g, ?_⟩
    nth_rw 1 [← x.mk_rep]
    rw [sp_projective_smul_mk, ← y.mk_rep, mk_eq_mk_iff']
    exact ⟨1, by simp [hg]⟩

/- A nontrivial block contains two nonorthogonal lines. Their span contains a line
fixed by each transvection, so every transvection stabilizes the block. -/
private lemma sp_projective_primitive [Module.Finite K V] (hB : B.IsAlt)
    (hnd : B.Nondegenerate) : IsPreprimitive (sp B) (ℙ K V) where
  toIsPretransitive := sp_projective_transitive hB hnd
  isTrivialBlock_of_isBlock {S} hS := by
    classical
    by_cases hs : S.Subsingleton
    · exact Or.inl hs
    obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hs
    have apply_of_fixed {g : sp B} {a b : ℙ K V} (ha : a ∈ S) (hb : b ∈ S)
        (hg : g • a = a) : g • b ∈ S := by
      have he := hS.smul_eq_of_mem ha (hg.symm ▸ ha : g • a ∈ S)
      rw [← he]
      exact Set.smul_mem_smul_set hb
    have fixed_line {x z : V} (hx : x ≠ 0) (c : K) (hz : B z x = 0) :
        transv hB z c • mk K x hx = mk K x hx := by
      rw [sp_projective_smul_mk, mk_eq_mk_iff']
      exact ⟨1, by simp [transv_apply, hz]⟩
    have nonorthogonal : ∃ x y : ℙ K V, x ∈ S ∧ y ∈ S ∧ B x.rep y.rep ≠ 0 := by
      by_cases he : B a.rep b.rep = 0
      · have hz : ∃ z, B a.rep z = 0 ∧ B b.rep z ≠ 0 := by
          by_contra! hc
          have hle : (B a.rep).ker ≤ (B b.rep).ker := fun z hz =>
            LinearMap.mem_ker.mpr (hc _ (LinearMap.mem_ker.mp hz))
          have hspan := mem_span_of_iInf_ker_le_ker
            (L := fun _ : Unit => B a.rep) (K := B b.rep) (by simpa using hle)
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (by simpa using hspan)
          apply hab.symm
          rw [← a.mk_rep, ← b.mk_rep, mk_eq_mk_iff']
          have e : c • a.rep - b.rep ∈ B.ker := by
            rw [LinearMap.mem_ker, map_sub, map_smul, hc, sub_self]
          rw [hnd.ker_eq_bot, Submodule.mem_bot, sub_eq_zero] at e
          exact ⟨c, e⟩
        obtain ⟨z, hza, hzb⟩ := hz
        have hza' := (hB.eq_iff).mp hza
        have hzb' := (hB.eq_iff).not.mp hzb
        let t := transv hB z 1
        have hta : t • a = a := by
          nth_rw 1 [← a.mk_rep]
          exact (fixed_line a.rep_ne_zero 1 hza').trans a.mk_rep
        refine ⟨b, t • b, hb, apply_of_fixed ha hb hta, ?_⟩
        have htb : t • b = mk K (t • b.rep) ((smul_ne_zero_iff_ne t).mpr b.rep_ne_zero) := by
          conv_lhs => rw [← b.mk_rep]
          exact sp_projective_smul_mk _ _ _
        rw [htb]
        obtain ⟨c, hc⟩ := exists_smul_eq_mk_rep (K := K) (t • b.rep)
          ((smul_ne_zero_iff_ne t).mpr b.rep_ne_zero)
        rw [← hc, Units.smul_def, BilinForm.smul_right, transv_apply, BilinForm.add_right,
          BilinForm.smul_right, hB.self_eq_zero, zero_add, one_mul]
        exact mul_ne_zero (Units.ne_zero c) (mul_ne_zero hzb' hzb)
      · exact ⟨a, b, ha, hb, he⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := nonorthogonal
    have fixed_point (z : V) (c : K) :
        ∃ a ∈ S, transv hB z c • a = a := by
      by_cases hz : B z x.rep = 0
      · exact ⟨x, hx, by
          nth_rw 1 [← x.mk_rep]
          exact (fixed_line x.rep_ne_zero c hz).trans x.mk_rep⟩
      let t := transv hB x.rep (-(B z y.rep) / (B x.rep y.rep * B z x.rep))
      have ht : t • x = x := by
        nth_rw 1 [← x.mk_rep]
        exact (fixed_line x.rep_ne_zero _ (hB.self_eq_zero _)).trans x.mk_rep
      have hzy : B z (t • y.rep) = 0 := by
        rw [transv_apply, BilinForm.add_right, BilinForm.smul_right]
        field_simp
        ring
      refine ⟨t • y, apply_of_fixed hx hy ht, ?_⟩
      have hy' : t • y = mk K (t • y.rep) ((smul_ne_zero_iff_ne t).mpr y.rep_ne_zero) := by
        conv_lhs => rw [← y.mk_rep]
        exact sp_projective_smul_mk _ _ _
      rw [hy']
      exact fixed_line _ c hzy
    let T := stabilizer (sp B) S
    have hT : T = ⊤ := by
      apply transv_generate hB hnd
      intro z c
      obtain ⟨a, ha, he⟩ := fixed_point z c
      exact hS.smul_eq_of_mem ha (he.symm ▸ ha : transv hB z c • a ∈ S)
    right
    apply Set.eq_univ_of_forall
    intro z
    have := sp_projective_transitive hB hnd
    obtain ⟨g, rfl⟩ := exists_smul_eq (sp B) x z
    have he : g • S = S := show g ∈ T from hT.symm ▸ Subgroup.mem_top g
    rw [← he]
    exact Set.smul_mem_smul_set hx

private def transvSubgroup (hB : B.IsAlt) (v : V) : Subgroup (sp B) := by
  refine
    { carrier := Set.range (transv hB v)
      one_mem' := ?_
      mul_mem' := ?_
      inv_mem' := ?_ }
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, transv_same hB v a b⟩
  · exact ⟨0, sp_ext (by simp [transv_apply, sp_one_smul])⟩
  · rintro _ ⟨a, rfl⟩
    refine ⟨-a, eq_inv_of_mul_eq_one_left ?_⟩
    rw [← transv_same, neg_add_cancel]
    exact sp_ext (by simp [transv_apply, sp_one_smul])

private lemma transv_conj (hB : B.IsAlt) (g : sp B) (v : V) (c : K) :
    MulAut.conj g (transv hB v c) = transv hB (g • v) c := by
  rw [MulAut.conj_apply, eq_comm, eq_mul_inv_iff_mul_eq]
  exact transv_transport hB g v c

private def spIwasawa [Module.Finite K V] (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    IwasawaStructure (sp B) (ℙ K V) where
  T x := transvSubgroup hB x.rep
  is_comm x := ⟨⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    change transv hB x.rep a * transv hB x.rep b = transv hB x.rep b * transv hB x.rep a
    rw [← transv_same, ← transv_same, add_comm]⟩⟩
  is_conj g x := by
    have hx : g • x = mk K (g • x.rep) ((smul_ne_zero_iff_ne g).mpr x.rep_ne_zero) := by
      conv_lhs => rw [← x.mk_rep]
      exact sp_projective_smul_mk _ _ _
    obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep (K := K) (g • x.rep)
      ((smul_ne_zero_iff_ne g).mpr x.rep_ne_zero)
    ext f
    rw [Subgroup.pointwise_smul_def]
    change (∃ b, transv hB (g • x).rep b = f) ↔
      ∃ h, (∃ b, transv hB x.rep b = h) ∧ MulAut.conj g h = f
    rw [hx, ← ha, Units.smul_def]
    simp only [transv_scale, transv_conj, exists_exists_eq_and]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b / (a : K)^2, by rw [div_mul_cancel₀ _ (pow_ne_zero _ (Units.ne_zero a))]⟩
  is_generator := by
    apply transv_generate hB hnd
    intro v c
    by_cases hv : v = 0
    · rw [show transv hB v c = 1 from sp_ext (by simp [hv, transv_apply, sp_one_smul])]
      exact Subgroup.one_mem _
    obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep (K := K) v hv
    apply le_iSup (fun x : ℙ K V => transvSubgroup hB x.rep) (mk K v hv)
    change ∃ b, transv hB (mk K v hv).rep b = _
    simp_rw [← ha, Units.smul_def, transv_scale]
    exact ⟨c / (a : K)^2, by rw [div_mul_cancel₀ _ (pow_ne_zero _ (Units.ne_zero a))]⟩

private lemma sq_eq_one_of_char_two [CharP K 2] {a : K} (ha : a ^ 2 = 1) : a = 1 := by
  have hc : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hz : (a - 1)^2 = 0 := by
    calc
      (a - 1)^2 = a^2 - 2 * a + 1 := by ring
      _ = 0 := by rw [ha, hc, zero_mul, sub_zero, one_add_one_eq_two, hc]
  exact sub_eq_zero.mp (by simpa [pow_two, mul_eq_zero] using hz)

private lemma sp_perfect [Module.Finite K V] (hB : B.IsAlt) (hnd : B.Nondegenerate)
    {a : K} (ha : a ≠ 0) (has : a ^ 2 ≠ 1) : commutator (sp B) = ⊤ := by
  apply transv_generate hB hnd
  intro v c
  by_cases hv : v = 0
  · rw [show transv hB v c = 1 from sp_ext (by simp [hv, transv_apply, sp_one_smul])]
    exact Subgroup.one_mem _
  obtain ⟨g, hg⟩ := sp_transitive_vectors hB hnd hv (smul_ne_zero ha hv)
  let b := c / (a^2 - 1)
  have hb : b * (a^2 - 1) = c := div_mul_cancel₀ _ (sub_ne_zero.mpr has)
  have hba : b * a^2 = c + b := by linear_combination hb
  have he := transv_conj hB g v b
  rw [hg, transv_scale, hba, transv_same] at he
  have hcomm : ⁅g, transv hB v b⁆ = transv hB v c := by
    rw [commutatorElement_def]
    change MulAut.conj g (transv hB v b) * (transv hB v b)⁻¹ = _
    rw [he, mul_inv_cancel_right]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private lemma sp_projective_faithful [Nontrivial V] [CharP K 2] (hnd : B.Nondegenerate) :
    FaithfulSMul (sp B) (ℙ K V) := by
  have trivial_kernel (g : sp B) (h : ∀ x : ℙ K V, g • x = x) : g = 1 := by
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
      (f := g.val.toLinearMap) fun v => by
        by_cases hv : v = 0
        · simp [hv, linearIndependent_fin2]
        · have hr := h (mk K v hv)
          rw [sp_projective_smul_mk, mk_eq_mk_iff'] at hr
          obtain ⟨c, hc⟩ := hr
          exact fun hi => (LinearIndependent.pair_iff' hv).mp hi c hc
    have hscale (x : V) : g • x = a • x := LinearMap.congr_fun ha x
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ := exists_pairing_ne_zero hnd hv
    have he := form_smul g v w
    rw [hscale, hscale, BilinForm.smul_left, BilinForm.smul_right] at he
    have ha' : a ^ 2 = 1 := by
      apply mul_right_cancel₀ hw
      simpa only [pow_two, mul_assoc, one_mul] using he
    apply sp_ext
    intro x
    rw [hscale, sq_eq_one_of_char_two ha', one_smul, sp_one_smul]
  constructor
  intro g h hgh
  have he : h⁻¹ * g = 1 := trivial_kernel _ fun x => by
    rw [mul_smul, hgh, inv_smul_smul]
  exact (inv_mul_eq_one.mp he).symm

private lemma sp_simple [Nontrivial V] [Module.Finite K V] [CharP K 2] (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : IsSimpleGroup (sp B) := by
  have : Nontrivial (sp B) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ := exists_pairing_ne_zero hnd hv
    refine ⟨⟨transv hB v 1, 1, fun he => ?_⟩⟩
    have h := congrArg (fun g : sp B => g • w) he
    rw [transv_apply, sp_one_smul, one_mul, add_eq_left] at h
    exact (smul_ne_zero hw hv) h
  have := sp_projective_primitive hB hnd
  exact (spIwasawa hB hnd).isSimpleGroup
    (sp_perfect hB hnd ha0 (ha1 ∘ sq_eq_one_of_char_two)) (sp_projective_faithful hnd)

private lemma exists_pairing_eq_one (hnd : B.Nondegenerate) {x : V} (hx : x ≠ 0) :
    ∃ y, B x y = 1 := by
  obtain ⟨y, hy⟩ := exists_pairing_ne_zero hnd hx
  exact ⟨(B x y)⁻¹ • y, by rw [BilinForm.smul_right, inv_mul_cancel₀ hy]⟩

private abbrev HyperbolicPair (B : BilinForm K V) := { p : V × V // B p.1 p.2 = 1 }

private instance hyperbolicPairFinite [Finite V] : Finite (HyperbolicPair B) :=
  inferInstanceAs (Finite { p : V × V // B p.1 p.2 = 1 })

private instance hyperbolicPairAction : MulAction (sp B) (HyperbolicPair B) where
  smul g p := ⟨(g • p.val.1, g • p.val.2), (form_smul g _ _).trans p.property⟩
  one_smul _ := Subtype.ext (Prod.ext (sp_one_smul _) (sp_one_smul _))
  mul_smul g h _ := Subtype.ext (Prod.ext (sp_mul_smul g h _) (sp_mul_smul g h _))

private lemma hyperbolicPair_transitive (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    IsPretransitive (sp B) (HyperbolicPair B) where
  exists_smul_eq p q := by
    have nonzero (p : HyperbolicPair B) : p.val.1 ≠ 0 := by
      intro h
      simpa [h] using p.property
    obtain ⟨g, hg⟩ := sp_transitive_vectors hB hnd (nonzero p) (nonzero q)
    let x := q.val.1
    let y := g • p.val.2
    let z := q.val.2
    have hz : B x z = 1 := q.property
    have hy : B x y = 1 := by rw [show x = g • p.val.1 from hg.symm, form_smul, p.property]
    have send {y z : V} (hy : B x y = 1) (hz : B x z = 1) (hn : B z y ≠ 0) :
        ∃ t : sp B, t • x = x ∧ t • y = z := by
      refine ⟨transv hB (z - y) (B z y)⁻¹, ?_, transv_send hB hn⟩
      have he : B (z - y) x = 0 := by
        rw [← hB.eq_iff, BilinForm.sub_right, hz, hy, sub_self]
      rw [transv_apply, he, mul_zero, zero_smul, add_zero]
    obtain ⟨t, ht, hty⟩ : ∃ t : sp B, t • x = x ∧ t • y = z := by
      by_cases hn : B z y = 0
      · let w := z + x
        have hw : B x w = 1 := by simp [w, hz, hB.self_eq_zero]
        have hwy : B w y ≠ 0 := by simp [w, hy, hn]
        have hzw : B z w ≠ 0 := by simp [w, hB.self_eq_zero, ← hB.neg_eq x z, hz]
        obtain ⟨t, ht, hty⟩ := send hy hw hwy
        obtain ⟨s, hs, hsw⟩ := send hw hz hzw
        exact ⟨s * t, by rw [sp_mul_smul, ht, hs], by rw [sp_mul_smul, hty, hsw]⟩
      · exact send hy hz hn
    exact ⟨t * g, Subtype.ext (Prod.ext (show (t * g) • p.val.1 = q.val.1 by
      rw [sp_mul_smul, hg]
      exact ht) (show (t * g) • p.val.2 = q.val.2 from (sp_mul_smul _ _ _).trans hty))⟩

private def pairProjection (p : HyperbolicPair B) : V →ₗ[K] K × K :=
  (B.flip p.val.2).prod (B p.val.1)

private def pairEmbed (p : HyperbolicPair B) : K × K →ₗ[K] V :=
  (LinearMap.fst K K K).smulRight p.val.1 + (LinearMap.snd K K K).smulRight p.val.2

private lemma pairProjection_embed (hB : B.IsAlt) (p : HyperbolicPair B) (a : K × K) :
    pairProjection p (pairEmbed p a) = a := by
  ext <;> simp [pairProjection, pairEmbed, hB.self_eq_zero, p.property]

private def pairSplit (hB : B.IsAlt) (p : HyperbolicPair B) :
    ((K × K) × (pairProjection p).ker) ≃ₗ[K] V := by
  let r : V →ₗ[K] V := LinearMap.id - (pairEmbed p).comp (pairProjection p)
  let rest := r.codRestrict (pairProjection p).ker (fun x => by
    simp [r, LinearMap.mem_ker, pairProjection_embed hB])
  refine LinearEquiv.ofLinearMap ((pairEmbed p).coprod (pairProjection p).ker.subtype)
    ((pairProjection p).prod rest) ?_ ?_
  · ext x
    simp [rest, r]
  · ext x <;> simp [rest, r, pairProjection_embed hB]

private lemma pairSplit_apply (hB : B.IsAlt) (p : HyperbolicPair B)
    (a : K × K) (w : (pairProjection p).ker) :
    pairSplit hB p (a, w) = a.1 • p.val.1 + a.2 • p.val.2 + w.val := rfl

private def pairComplementForm (p : HyperbolicPair B) :
    BilinForm K (pairProjection p).ker := B.restrict _

private lemma pairComplement_alt (hB : B.IsAlt) (p : HyperbolicPair B) :
    (pairComplementForm p).IsAlt := fun w => hB.self_eq_zero w.val

private lemma pairComplement_orth (p : HyperbolicPair B) (v : (pairProjection p).ker) :
    B v.val p.val.2 = 0 ∧ B p.val.1 v.val = 0 := by
  have hp := LinearMap.mem_ker.mp v.property
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

private lemma pairComplement_nd (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (p : HyperbolicPair B) : (pairComplementForm p).Nondegenerate := by
  have hsep : ∀ v : (pairProjection p).ker,
      (∀ w, pairComplementForm p v w = 0) → v = 0 := by
    intro v hv
    apply Subtype.ext
    apply hnd.1
    intro x
    obtain ⟨⟨a, w⟩, rfl⟩ := (pairSplit hB p).surjective x
    have ht := pairComplement_orth p v
    rw [pairSplit_apply, BilinForm.add_right, BilinForm.add_right,
      BilinForm.smul_right, BilinForm.smul_right, ht.1, (hB.eq_iff).mp ht.2]
    simpa [pairComplementForm] using hv w
  exact ⟨hsep, fun v hv => hsep v fun w => (pairComplement_alt hB p).eq_iff.mpr (hv w)⟩

private lemma pairStabilizer_fix (p : HyperbolicPair B)
    (g : stabilizer (sp B) p) :
    g.val • p.val.1 = p.val.1 ∧ g.val • p.val.2 = p.val.2 := by
  have e : g.val • p = p := g.property
  exact ⟨congrArg (fun a : HyperbolicPair B => a.val.1) e,
    congrArg (fun a : HyperbolicPair B => a.val.2) e⟩

private lemma pairStabilizer_mem_ker (p : HyperbolicPair B)
    (g : stabilizer (sp B) p) (w : (pairProjection p).ker) :
    g.val • w.val ∈ (pairProjection p).ker := by
  rw [LinearMap.mem_ker]
  apply Prod.ext
  · change B (g.val • w.val) p.val.2 = 0
    rw [← (pairStabilizer_fix p g).2, form_smul]
    exact (pairComplement_orth p w).1
  · change B p.val.1 (g.val • w.val) = 0
    rw [← (pairStabilizer_fix p g).1, form_smul]
    exact (pairComplement_orth p w).2

private def pairStabilizerMap (p : HyperbolicPair B) :
    stabilizer (sp B) p →* sp (pairComplementForm p) := by
  let restr (g : stabilizer (sp B) p) := ((g.val.val : V →ₗ[K] V).comp
    (pairProjection p).ker.subtype).codRestrict _ (pairStabilizer_mem_ker p g)
  refine
    { toFun := fun g => ⟨LinearEquiv.ofLinearMap (restr g) (restr g⁻¹) ?_ ?_, ?_⟩
      map_one' := ?_
      map_mul' := ?_ }
  · ext w
    exact g.val.val.apply_symm_apply _
  · ext w
    exact g.val.val.symm_apply_apply _
  · exact fun v w => form_smul g.val v.val w.val
  · rfl
  · intros
    rfl

private lemma pairStabilizerMap_injective (hB : B.IsAlt) (p : HyperbolicPair B) :
    Function.Injective (pairStabilizerMap p) := by
  intro g h he
  apply Subtype.ext
  apply sp_ext
  intro x
  obtain ⟨⟨a, w⟩, rfl⟩ := (pairSplit hB p).surjective x
  have hw : g.val • w.val = h.val • w.val :=
    congrArg (fun f : sp (pairComplementForm p) => (f.val w).val) he
  simp only [pairSplit_apply, sp_smul_add, sp_smul_comm, (pairStabilizer_fix p g).1,
    (pairStabilizer_fix p g).2, (pairStabilizer_fix p h).1, (pairStabilizer_fix p h).2, hw]

private instance spFinite [Finite V] : Finite (sp B) :=
  Finite.of_injective (fun g : sp B => (g.val : V → V))
    (fun _ _ h => sp_ext (congrFun h))

private def hyperbolicPairOfNontrivial [Nontrivial V] (hnd : B.Nondegenerate) :
    HyperbolicPair B :=
  let ⟨u, hu⟩ := Classical.indefiniteDescription _ (exists_ne (0 : V))
  let ⟨v, hv⟩ := Classical.indefiniteDescription _ (exists_pairing_eq_one hnd hu)
  ⟨(u, v), hv⟩

private lemma card_pair_fiber [Finite K] [Finite V] [Module.Finite K V]
    (hnd : B.Nondegenerate) (u : {x : V // x ≠ 0}) :
    Nat.card {v : V // B u.val v = 1} = Nat.card K ^ (Module.finrank K V - 1) := by
  obtain ⟨v, hv⟩ := exists_pairing_eq_one hnd u.property
  let e : (B u.val).ker ≃ {w : V // B u.val w = 1} :=
    { toFun := fun w => ⟨w.val + v, by simp [LinearMap.mem_ker.mp w.property, hv]⟩
      invFun := fun w => ⟨w.val - v, by simp [LinearMap.mem_ker, w.property, hv]⟩
      left_inv := fun w => Subtype.ext (add_sub_cancel_right w.val v)
      right_inv := fun w => Subtype.ext (sub_add_cancel w.val v) }
  have hs : Function.Surjective (B u.val) := fun c =>
    ⟨c • v, by simp [hv]⟩
  have hr := LinearMap.finrank_range_add_finrank_ker (B u.val)
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self] at hr
  calc
    _ = Nat.card ((B u.val).ker) := Nat.card_congr e.symm
    _ = _ := by rw [Module.natCard_eq_pow_finrank (K := K)]; congr 1; omega

private lemma card_hyperbolicPair [Finite K] [Finite V] [Module.Finite K V]
    (hnd : B.Nondegenerate) :
    Nat.card (HyperbolicPair B) =
      (Nat.card K ^ Module.finrank K V - 1) * Nat.card K ^ (Module.finrank K V - 1) := by
  classical
  let e : HyperbolicPair B ≃ (Σ u : {x : V // x ≠ 0}, {v : V // B u.val v = 1}) :=
    { toFun := fun p => ⟨⟨p.val.1, by
        intro h
        simpa [h] using p.property⟩, ⟨p.val.2, p.property⟩⟩
      invFun := fun p => ⟨(p.1.val, p.2.val), p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let := Fintype.ofFinite V
  let := Fintype.ofFinite {x : V // x ≠ 0}
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [card_pair_fiber hnd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  change Fintype.card {x : V // x ≠ 0} = _
  rw [← Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun x : V => x = 0)]
  exact congrArg (Fintype.card V - ·) (Fintype.card_ofSubsingleton ⟨0, rfl⟩)

private lemma card_sp_step [Finite K] [Finite V] [Module.Finite K V]
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (p : HyperbolicPair B) :
    Nat.card (sp B) = Nat.card (HyperbolicPair B) * Nat.card (stabilizer (sp B) p) := by
  have := hyperbolicPair_transitive hB hnd
  have h : Nat.card (orbit (sp B) p) = Nat.card (HyperbolicPair B) := by
    rw [orbit_eq_univ (sp B) p]
    exact Nat.card_congr (Equiv.Set.univ _)
  rw [← Nat.card_congr (orbitProdStabilizerEquivGroup (sp B) p), Nat.card_prod, h]

private lemma finrank_pair_complement [Module.Finite K V] (hB : B.IsAlt) (p : HyperbolicPair B) :
    Module.finrank K ((pairProjection p).ker) + 2 = Module.finrank K V := by
  have h := (pairSplit hB p).finrank_eq
  simpa [Module.finrank_prod, add_comm] using h

private lemma card_sp_two [Finite K] [Finite V] [Module.Finite K V]
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hd : Module.finrank K V = 2) :
    Nat.card (sp B) = (Nat.card K ^ 2 - 1) * Nat.card K := by
  have : Nontrivial V := (Module.finrank_pos_iff (R := K) (M := V)).mp (by omega)
  let p := hyperbolicPairOfNontrivial hnd
  have hr := finrank_pair_complement hB p
  have : Subsingleton (pairProjection p).ker :=
    (Module.finrank_zero_iff (R := K) (M := (pairProjection p).ker)).mp (by omega)
  have : Subsingleton (sp (pairComplementForm p)) := by infer_instance
  have : Subsingleton (stabilizer (sp B) p) :=
    (pairStabilizerMap_injective hB p).subsingleton
  rw [card_sp_step hB hnd p, card_hyperbolicPair hnd, hd,
    Nat.card_unique (α := stabilizer (sp B) p), mul_one]
  simp

/- Count the orbit of a hyperbolic pair and embed its stabilizer in the isometry group
of the two-dimensional orthogonal complement. -/
private lemma card_sp_four_bounds [Finite K] [Finite V] [Module.Finite K V]
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hd : Module.finrank K V = 4) :
    (Nat.card K ^ 4 - 1) * Nat.card K ^ 3 ≤ Nat.card (sp B) ∧
    Nat.card (sp B) ∣ ((Nat.card K ^ 4 - 1) * Nat.card K ^ 3) *
      ((Nat.card K ^ 2 - 1) * Nat.card K) := by
  have : Nontrivial V := (Module.finrank_pos_iff (R := K) (M := V)).mp (by omega)
  let p := hyperbolicPairOfNontrivial hnd
  have hp := finrank_pair_complement hB p
  have he := card_sp_two (pairComplement_alt hB p) (pairComplement_nd hB hnd p) (by omega)
  rw [card_sp_step hB hnd p, card_hyperbolicPair hnd, hd]
  refine ⟨Nat.le_mul_of_pos_right _ Nat.card_pos, Nat.mul_dvd_mul_left _ ?_⟩
  rw [← he]
  exact Subgroup.card_dvd_of_injective _ (pairStabilizerMap_injective hB p)

section Extension

variable {E : Type*} [Field E] [Algebra K E]

private def determinantForm (E : Type*) [Field E] : BilinForm E (E × E) :=
  LinearMap.mk₂ E (fun x y => x.1 * y.2 - x.2 * y.1)
    (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring)

private lemma determinantForm_alt : (determinantForm E).IsAlt := fun x =>
  sub_eq_zero.mpr (mul_comm x.1 x.2)

private lemma determinantForm_nd : (determinantForm E).Nondegenerate := by
  have sep : ∀ x : E × E, (∀ y, determinantForm E x y = 0) → x = 0 := by
    intro x hx
    have h₁ := hx (0, 1)
    have h₂ := hx (1, 0)
    change x.1 * 1 - x.2 * 0 = 0 at h₁
    change x.1 * 0 - x.2 * 1 = 0 at h₂
    exact Prod.ext (by simpa using h₁) (by simpa using h₂)
  exact ⟨sep, fun x h => sep x fun y => determinantForm_alt.eq_iff.mpr (h y)⟩

/- Restrict the scalars of the determinant pairing and compose it with a linear
functional. This realizes the two-dimensional group over the larger field
as a subgroup of the four-dimensional group over the smaller field. -/
private def extensionForm (l : E →ₗ[K] K) : BilinForm K (E × E) :=
  LinearMap.mk₂ K (fun x y => l (determinantForm E x y))
    (by intros; simp)
    (by
      intro c x y
      rw [← algebraMap_smul E c x, map_smul, LinearMap.smul_apply, algebraMap_smul E, map_smul])
    (by intros; simp)
    (by
      intro c x y
      rw [← algebraMap_smul E c y, map_smul, algebraMap_smul E, map_smul])

private lemma extensionForm_alt (l : E →ₗ[K] K) : (extensionForm l).IsAlt :=
  fun x => show l (determinantForm E x x) = 0 by simp [determinantForm_alt.self_eq_zero]

private lemma extensionForm_nd {l : E →ₗ[K] K} (hl : l 1 = 1) :
    (extensionForm l).Nondegenerate := by
  have sep : ∀ x : E × E, (∀ y, extensionForm l x y = 0) → x = 0 := by
    intro x hx
    by_contra h
    obtain ⟨y, hy⟩ := exists_pairing_eq_one determinantForm_nd h
    have hz := hx y
    change l (determinantForm E x y) = 0 at hz
    rw [hy, hl] at hz
    exact one_ne_zero hz
  exact ⟨sep, fun x h => sep x fun y => (extensionForm_alt l).eq_iff.mpr (h y)⟩

private def extensionHom (l : E →ₗ[K] K) :
    sp (determinantForm E) →* sp (extensionForm l) where
  toFun g := ⟨g.val.restrictScalars K, fun x y => congrArg l (form_smul g x y)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private lemma extensionHom_injective (l : E →ₗ[K] K) :
    Function.Injective (extensionHom l) := fun _ _ e =>
  sp_ext (fun x => congrArg (fun t : sp (extensionForm l) => t • x) e)

end Extension

private lemma prime_dvd_subgroup_order {p q : ℕ} (hp : p.Prime) (hq : 1 < q)
    (h : p ∣ ((q ^ 4 - 1) * q ^ 3) * ((q ^ 2 - 1) * q)) :
    p ∣ (q ^ 4 - 1) * q ^ 2 := by
  have h24 : q ^ 2 - 1 ∣ q ^ 4 - 1 :=
    (Nat.pow_sub_one_dvd_pow_sub_one_iff hq).2 (by decide)
  have key (h : p ∣ q) : p ∣ (q ^ 4 - 1) * q ^ 2 :=
    dvd_mul_of_dvd_right (h.trans (dvd_pow_self _ (by decide))) _
  rcases hp.dvd_mul.mp h with hl | hr
  · rcases hp.dvd_mul.mp hl with h₄ | h₃
    · exact dvd_mul_of_dvd_left h₄ _
    · exact key (hp.dvd_of_dvd_pow h₃)
  · rcases hp.dvd_mul.mp hr with h₂ | h₁
    · exact dvd_mul_of_dvd_left (h₂.trans h24) _
    · exact key h₁

private lemma seven_not_dvd_subgroup_order {q : ℕ} (hq : 1 < q)
    (hmod : (q : ZMod 7) = 2) : ¬ 7 ∣ (q ^ 4 - 1) * q ^ 2 := by
  have hpow : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_sub hpow,
    Nat.cast_pow, Nat.cast_pow, Nat.cast_one, hmod]
  decide

private lemma nonalternating_of_order {G : Type*} [Group G] [Finite G]
    (hlarge : 720 < Nat.card G) (hseven : ¬ 7 ∣ Nat.card G) (n : ℕ) :
    IsEmpty (G ≃* alternatingGroup (Fin n)) := by
  constructor
  intro e
  have hcard := Nat.card_congr e.toEquiv
  have hn : 7 ≤ n := by
    by_contra! hs
    have hle : Nat.card (alternatingGroup (Fin n)) ≤ n.factorial := by
      calc
        _ ≤ Nat.card (Equiv.Perm (Fin n)) :=
          Nat.card_le_card_of_injective _ (alternatingGroup (Fin n)).subtype_injective
        _ = _ := by rw [Nat.card_perm, Nat.card_fin]
    have hf := Nat.factorial_le (show n ≤ 6 by omega)
    have : Nat.factorial 6 = 720 := by decide
    omega
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have he := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_fin, ← hcard] at he
  have hp : Nat.Prime 7 := by decide
  have hd := hp.dvd_factorial.mpr hn
  rw [← he] at hd
  exact hseven ((hp.dvd_mul.mp hd).resolve_left (by decide))

/- Take field sizes congruent to two modulo seven. The resulting groups lack the
prime divisor seven, which rules out every sufficiently large alternating group. -/
private lemma unbounded_examples (N : ℕ) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), IsSimpleGroup G ∧
      (∀ n : ℕ, IsEmpty (G ≃* alternatingGroup (Fin n))) ∧
      (∃ H : Subgroup G, H ≠ ⊤ ∧ (Nat.card H).primeFactors = (Nat.card G).primeFactors) ∧
      N < Nat.card G := by
  classical
  let s := 3 * (N + 2) + 1
  have hs : s ≠ 0 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 s
  let E := GaloisField 2 (s * 2)
  let q := Nat.card K
  have hq : q = 2 ^ s := GaloisField.card 2 s hs
  have hE : Nat.card E = q ^ 2 := by
    rw [show Nat.card E = 2 ^ (s * 2) from GaloisField.card 2 (s * 2) (by omega), pow_mul, hq]
  have hqlarge : 16 ≤ q := by
    rw [hq]
    exact Nat.pow_le_pow_right Nat.zero_lt_two (show 4 ≤ s by omega)
  obtain ⟨f⟩ : Nonempty (K →ₐ[ZMod 2] E) := FiniteField.nonempty_algHom_of_finrank_dvd (by
    rw [show Module.finrank (ZMod 2) K = s from GaloisField.finrank 2 hs,
      show Module.finrank (ZMod 2) E = s * 2 from GaloisField.finrank 2 (by omega)]
    exact dvd_mul_right _ _)
  let : Algebra K E := f.toRingHom.toAlgebra
  have : Module.Finite K E := Module.Finite.of_finite
  have : Module.Finite E E := Module.Finite.self E
  have hdim : Module.finrank K E = 2 :=
    Nat.pow_right_injective (show 1 < q by omega) <|
      (Module.natCard_eq_pow_finrank (K := K) (V := E)).symm.trans hE
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : E) ≠ 0)
  let G := sp (extensionForm l)
  let H : Subgroup G := (extensionHom l).range
  have hG : (q ^ 4 - 1) * q ^ 3 ≤ Nat.card G ∧
      Nat.card G ∣ ((q ^ 4 - 1) * q ^ 3) * ((q ^ 2 - 1) * q) := by
    apply card_sp_four_bounds (extensionForm_alt l) (extensionForm_nd hl)
    simp [Module.finrank_prod, hdim]
  have hH : Nat.card H = (q ^ 4 - 1) * q ^ 2 := by
    change Nat.card (extensionHom l).range = _
    rw [← Nat.card_congr (MonoidHom.ofInjective (extensionHom_injective l)).toEquiv]
    rw [card_sp_two (B := determinantForm E) determinantForm_alt determinantForm_nd
      (by simp [Module.finrank_prod]),
      hE, ← pow_mul]
  have hgreater : Nat.card H < Nat.card G := by
    rw [hH]
    refine lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left ?_ ?_) hG.1
    · exact Nat.pow_lt_pow_right (by omega) (by decide)
    · have : 1 < q ^ 4 := lt_of_lt_of_le (by decide : 1 < 16 ^ 4)
        (Nat.pow_le_pow_left hqlarge 4)
      omega
  have hcard : q ≤ Nat.card G := by
    have hpow : q ≤ q ^ 3 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < q by omega) (by decide : 1 ≤ 3)
    have h₄ : 0 < q ^ 4 - 1 := by
      have := Nat.pow_le_pow_left hqlarge 4
      omega
    exact hpow.trans ((Nat.le_mul_of_pos_left _ h₄).trans hG.1)
  have hlarge : 720 < Nat.card G := by
    have ha : 720 < q ^ 4 - 1 := by
      have ha := Nat.pow_le_pow_left hqlarge 4
      omega
    exact ha.trans_le ((Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))).trans hG.1)
  have hmod : (q : ZMod 7) = 2 := by
    rw [hq, Nat.cast_pow, show s = 3 * (N + 2) + 1 from rfl, pow_add, pow_mul]
    change ((2 : ZMod 7)^3)^(N + 2) * (2 : ZMod 7)^1 = 2
    rw [show (2 : ZMod 7)^3 = 1 by decide, one_pow, one_mul, pow_one]
  have hseven : ¬ 7 ∣ Nat.card G := fun hd =>
    seven_not_dvd_subgroup_order (by omega) hmod
      (prime_dvd_subgroup_order (by decide) (by omega) (hd.trans hG.2))
  have hqgt : N < q := by
    rw [hq]
    exact (show N ≤ s by omega).trans_lt s.lt_two_pow_self
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
    by_contra! hh
    let e : K → Bool := fun a => if a = 0 then false else true
    have he : Function.Injective e := by
      intro a b hab
      rcases eq_or_ne a 0 with rfl | ha <;> rcases eq_or_ne b 0 with rfl | hb
      · rfl
      · simp [e, hb] at hab
      · simp [e, ha] at hab
      · exact (hh a ha).trans (hh b hb).symm
    have he' := Nat.card_le_card_of_injective e he
    simp at he'
    omega
  refine ⟨G, inferInstance, inferInstance,
    sp_simple (extensionForm_alt l) (extensionForm_nd hl) ha0 ha1,
    nonalternating_of_order hlarge hseven, ⟨H, ?_, ?_⟩, hqgt.trans_le hcard⟩
  · intro he
    rw [he, Subgroup.card_top] at hgreater
    exact (lt_irrefl _) hgreater
  · apply Finset.Subset.antisymm
    · exact Nat.primeFactors_mono H.card_subgroup_dvd_card Nat.card_pos.ne'
    · intro p hp
      rw [Nat.mem_primeFactors] at hp ⊢
      refine ⟨hp.1, ?_, Nat.card_pos.ne'⟩
      rw [hH]
      exact prime_dvd_subgroup_order hp.1 (by omega) (hp.2.1.trans hG.2)

end

/--
Resolved false: the Kourovka Archive records (V. I. Zenkov) that the symplectic groups `G =
S_{4k}(2^s)` have proper subgroups `H ≅ Ω⁻_{4k}(2^s)` with `π(H) = π(G)`, an infinite family of
non-alternating finite simple groups. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 11.64 (V. S. Monakhov); resolution: V. I. Zenkov, letter of 10 March 1994,
Kourovka Archive, Problem 11.64: "No, there are infinitely many such groups. If `G = S_{4k}(2^s)`
and `H ≅ Ω⁻_{4k}(2^s)`, then `π(G) = π(H)`", https://arxiv.org/abs/1401.0300v49.
-/
public theorem finitelyManySimpleWithFullSpectrumSubgroup_refuted :
    ¬ finitelyManySimpleWithFullSpectrumSubgroup := by
  rintro ⟨N, hN⟩
  obtain ⟨G, _groupG, _finiteG, hs, ha, hsub, hlarge⟩ := unbounded_examples N
  exact hlarge.not_ge (hN G hs ha hsub)

end MathlibExt.GroupTheory.SimpleGroupPrimeSpectrumSubgroupKourovka11Problem64Wanted
