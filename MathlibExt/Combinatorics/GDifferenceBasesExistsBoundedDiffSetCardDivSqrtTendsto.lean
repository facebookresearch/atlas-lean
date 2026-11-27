/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.GDifferenceBases
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.LSeries.WeakPNT

namespace MetaMathlibExt

open Filter Topology
open scoped BigOperators

@[expose] public section

private theorem ruzsa_graph_bound (M d g : ℕ) [NeZero M] [NeZero d] (hd : 0 < d)
    (hMd : M = g * d) (K : Type*) [Field K] [DecidableEq K]
    (f : ZMod M → K) (hf : Function.Injective f)
    (hfadd : ∀ a b, f (a + b) = f a * f b) (hf0 : f 0 = 1) :
    let φ := ZMod.castHom (show d ∣ M from hMd ▸ dvd_mul_left d g) (ZMod d)
    let A := Finset.univ.image (fun a : ZMod M => (φ a, f a))
    A.card = M ∧ ∀ x : ZMod d × K, x ≠ 0 → subRepCount A x ≤ g := by
  classical
  let φ := ZMod.castHom (show d ∣ M from hMd ▸ dvd_mul_left d g) (ZMod d)
  let v := fun a : ZMod M => (φ a, f a)
  let A := Finset.univ.image v
  have hvinj : Function.Injective v := fun a b h => hf (congrArg Prod.snd h)
  change A.card = M ∧ _
  constructor
  · simp only [A, Finset.card_image_of_injective _ hvinj, Finset.card_univ, ZMod.card]
  · intro x hx
    let R := (Finset.univ ×ˢ Finset.univ).filter
      (fun ab : ZMod M × ZMod M => v ab.1 - v ab.2 = x)
    have hR : subRepCount A x = R.card := by
      have heq : ((A ×ˢ A).filter (fun ab => ab.1 - ab.2 = x)) =
          R.image (fun ab => (v ab.1, v ab.2)) := by
        ext ab
        rcases ab with ⟨u, w⟩
        constructor
        · intro hab
          obtain ⟨hab, heq⟩ := Finset.mem_filter.mp hab
          obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
          obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hb
          exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, heq⟩, rfl⟩
        · rintro hab
          obtain ⟨⟨a, b⟩, hmem, heqpair⟩ := Finset.mem_image.mp hab
          have hu : v a = u := congrArg Prod.fst heqpair
          have hw : v b = w := congrArg Prod.snd heqpair
          subst u w
          obtain ⟨_, heq⟩ := Finset.mem_filter.mp hmem
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_image_of_mem v (Finset.mem_univ a),
              Finset.mem_image_of_mem v (Finset.mem_univ b)⟩, heq⟩
      rw [subRepCount, heq, Finset.card_image_of_injective]
      intro a b h
      exact Prod.ext (hvinj (congrArg Prod.fst h)) (hvinj (congrArg Prod.snd h))
    rw [hR]
    let index := fun ab : ZMod M × ZMod M => (ab.1 - ab.2).val / d
    rw [← Finset.card_range g]
    apply Finset.card_le_card_of_injOn index
    · intro ab hab
      change index ab ∈ Finset.range g
      rw [Finset.mem_range]
      dsimp only [index]
      rw [Nat.div_lt_iff_lt_mul hd, ← hMd]
      exact ZMod.val_lt _
    · intro ab hab cd hcd heq
      have habx := (Finset.mem_filter.mp hab).2
      have hcdx := (Finset.mem_filter.mp hcd).2
      have hφ : φ (ab.1 - ab.2) = φ (cd.1 - cd.2) := by
        simpa only [map_sub, v, Prod.fst_sub] using
          (congrArg Prod.fst habx).trans (congrArg Prod.fst hcdx).symm
      have hcast (t : ZMod M) : φ t = (t.val : ZMod d) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val t]
        rw [map_natCast]
      have hmod : (ab.1 - ab.2).val % d = (cd.1 - cd.2).val % d := by
        simpa only [hcast, ZMod.val_natCast] using congrArg ZMod.val hφ
      have ht : ab.1 - ab.2 = cd.1 - cd.2 := by
        apply ZMod.val_injective M
        have h1 := Nat.mod_add_div (ab.1 - ab.2).val d
        have h2 := Nat.mod_add_div (cd.1 - cd.2).val d
        change (ab.1 - ab.2).val / d = (cd.1 - cd.2).val / d at heq
        rw [heq, hmod] at h1
        omega
      have hform (a b : ZMod M) : (f (a - b) - 1) * f b = f a - f b := by
        rw [sub_mul, one_mul, ← hfadd, sub_add_cancel]
      have hy : f ab.1 - f ab.2 = f cd.1 - f cd.2 := by
        exact (congrArg Prod.snd habx).trans (congrArg Prod.snd hcdx).symm
      have htne : f (ab.1 - ab.2) - 1 ≠ 0 := by
        intro h
        have htzero : ab.1 - ab.2 = 0 := hf (by simpa only [sub_eq_zero, hf0] using h)
        have hab : ab.1 = ab.2 := sub_eq_zero.mp htzero
        apply hx
        rw [← habx, hab, sub_self]
      have hb : ab.2 = cd.2 := by
        apply hf
        apply mul_left_cancel₀ htne
        rw [hform, ht, hform]
        exact hy
      exact Prod.ext (by rw [hb] at ht; exact sub_left_inj.mp ht) hb

private theorem exists_ruzsa_graph (p g : ℕ) (hp : p.Prime)
    (hgp : g ∣ p - 1) :
    ∃ d : ℕ, 0 < d ∧ p - 1 = g * d ∧
      ∃ A : Finset (ZMod d × ZMod p), A.card = p - 1 ∧
        ∀ x, x ≠ 0 → subRepCount A x ≤ g := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let M := p - 1
  have hp2 := hp.two_le
  have hM : 0 < M := by dsimp [M]; omega
  obtain ⟨d, hd⟩ := hgp
  have hdpos : 0 < d := by
    by_contra! hn
    have hd0 : d = 0 := by omega
    simp [hd0] at hd
    omega
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero d := ⟨hdpos.ne'⟩
  let e : ZMod M ≃+ Additive ((ZMod p)ˣ) :=
    (ZMod.ringEquivCongr (show M = Nat.card (Additive ((ZMod p)ˣ)) by
      calc
        M = Nat.card ((ZMod p)ˣ) := by rw [Nat.card_eq_fintype_card, ZMod.card_units]
        _ = Nat.card (Additive ((ZMod p)ˣ)) :=
          (Nat.card_congr Additive.toMul).symm)).toAddEquiv.trans
      (zmodAddCyclicAddEquiv inferInstance)
  let f : ZMod M → ZMod p := fun a => ((Additive.toMul (e a) : (ZMod p)ˣ) : ZMod p)
  have hf : Function.Injective f := by
    intro a b h
    apply e.injective
    apply Additive.toMul.injective
    exact Units.ext h
  have hfadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    change ((Additive.toMul (e (a + b)) : (ZMod p)ˣ) : ZMod p) = _
    rw [e.map_add]
    rfl
  have hf0 : f 0 = 1 := by
    change ((Additive.toMul (e 0) : (ZMod p)ˣ) : ZMod p) = 1
    rw [e.map_zero]
    rfl
  obtain ⟨hcard, hbound⟩ := ruzsa_graph_bound M d g hdpos hd (ZMod p) f hf hfadd hf0
  exact ⟨d, hdpos, hd, _, hcard, hbound⟩

private theorem subRepCount_le_of_injOn {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] (A : Finset G) (B : Finset H) (f : G → H)
    (hinj : Set.InjOn f A) (hmem : ∀ a ∈ A, f a ∈ B) (x : G) (y : H)
    (hsub : ∀ a ∈ A, ∀ b ∈ A, a - b = x → f a - f b = y) :
    subRepCount A x ≤ subRepCount B y := by
  apply Finset.card_le_card_of_injOn (fun ab => (f ab.1, f ab.2))
  · intro ab hab
    obtain ⟨hprod, heq⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hprod
    change (f ab.1, f ab.2) ∈ (B ×ˢ B).filter (fun cd => cd.1 - cd.2 = y)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem _ ha, hmem _ hb⟩,
      hsub _ ha _ hb heq⟩
  · intro ab hab cd hcd heq
    obtain ⟨hprod1, _⟩ := Finset.mem_filter.mp hab
    obtain ⟨hprod2, _⟩ := Finset.mem_filter.mp hcd
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hprod1
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hprod2
    exact Prod.ext (hinj ha hc (congrArg Prod.fst heq))
      (hinj hb hd (congrArg Prod.snd heq))

private theorem integer_lift (N g : ℕ) [NeZero N] (D : Finset (ZMod N))
    (hD : ∀ x, x ≠ 0 → subRepCount D x ≤ g) :
    ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 N ∧ A.card = D.card ∧
      ∀ x : ℤ, x ≠ 0 → subRepCount A x ≤ g := by
  let lift : ZMod N → ℤ := fun z => (z.val : ℤ) + 1
  let A := D.image lift
  let f : ℤ → ZMod N := fun a => (a : ZMod N) - 1
  have hfl (z : ZMod N) : f (lift z) = z := by
    simp [f, lift]
  have hlinj : Function.Injective lift := by
    intro a b h
    exact (hfl a).symm.trans ((congrArg f h).trans (hfl b))
  have hmem : ∀ a ∈ A, f a ∈ D := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    simpa only [hfl] using hz
  have hfinj : Set.InjOn f A := by
    intro a ha b hb h
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
    simpa only [hfl] using congrArg lift h
  refine ⟨A, ?_, Finset.card_image_of_injective _ hlinj, ?_⟩
  · intro a ha
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp ha
    have hz := ZMod.val_lt z
    simp only [lift, Finset.mem_Icc]
    constructor <;> omega
  · intro x hx
    by_cases hxN : (x : ZMod N) = 0
    · have hempty : ((A ×ˢ A).filter (fun ab => ab.1 - ab.2 = x)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ab hab
        simp only [Finset.mem_filter, Finset.mem_product] at hab
        obtain ⟨⟨ha, hb⟩, heq⟩ := hab
        have hf : f ab.1 = f ab.2 := by
          apply sub_eq_zero.mp
          calc
            f ab.1 - f ab.2 = ((ab.1 - ab.2 : ℤ) : ZMod N) := by simp [f]
            _ = 0 := by rw [heq, hxN]
        have hab := hfinj ha hb hf
        exact hx (by rw [← heq, hab, sub_self])
      simp [subRepCount, hempty]
    · apply (subRepCount_le_of_injOn A D f hfinj hmem x (x : ZMod N) ?_).trans (hD _ hxN)
      intro a ha b hb heq
      simp [f, ← heq]

private theorem exists_ruzsa_integer (p g : ℕ) (hp : p.Prime) (hg : 0 < g)
    (hgp : g ∣ p - 1) :
    ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 ((p * ((p - 1) / g) : ℕ) : ℤ) ∧ A.card = p - 1 ∧
      ∀ x : ℤ, x ≠ 0 → subRepCount A x ≤ g := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, hpd, D, hDcard, hD⟩ := exists_ruzsa_graph p g hp hgp
  have hdiv : (p - 1) / g = d := by rw [hpd, Nat.mul_div_cancel_left d hg]
  have hcop : d.Coprime p := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    have hdp : d < p := by
      have hgd : d ≤ g * d := Nat.le_mul_of_pos_left d hg
      omega
    exact (Nat.not_dvd_of_pos_of_lt hd hdp) h
  let : NeZero d := ⟨hd.ne'⟩
  let : NeZero (d * p) := ⟨Nat.ne_of_gt (Nat.mul_pos hd hp.pos)⟩
  let e := ZMod.chineseRemainder hcop
  let B := D.image e.symm
  have hB : ∀ x : ZMod (d * p), x ≠ 0 → subRepCount B x ≤ g := by
    intro x hx
    apply (subRepCount_le_of_injOn B D e e.injective.injOn ?_ x (e x) ?_).trans
      (hD (e x) (by simpa using hx))
    · intro a ha
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
      simpa only [e.apply_symm_apply] using hz
    · intro a ha b hb heq
      simp only [← e.map_sub, heq]
  obtain ⟨A, hA, hcard, hbound⟩ := integer_lift (d * p) g B hB
  refine ⟨A, ?_, ?_, hbound⟩
  · simpa only [hdiv, Nat.mul_comm d p] using hA
  · rw [hcard, Finset.card_image_of_injective _ e.symm.injective, hDcard]

private theorem exists_max_prime_set (g n : ℕ) (hg : 0 < g) :
    ∃ A : Finset ℤ,
      A ⊆ Finset.Icc 1 n ∧ (∀ x : ℤ, x ≠ 0 → subRepCount A x ≤ g) ∧
      (A.card : ℝ) ≤ Real.sqrt (g * n) ∧
      ∀ p : ℕ, p.Prime → p ≡ 1 [MOD g] → p ^ 2 ≤ g * n → p - 1 ≤ A.card := by
  classical
  let S := (Finset.range (g * n + 1)).filter
    (fun p => p.Prime ∧ p ≡ 1 [MOD g] ∧ p ^ 2 ≤ g * n)
  have hmem (p : ℕ) (hp : p.Prime) (hpm : p ≡ 1 [MOD g]) (hpn : p ^ 2 ≤ g * n) :
      p ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hp, hpm, hpn⟩
    have hpp : p ≤ p ^ 2 := by nlinarith
    omega
  by_cases hS : S.Nonempty
  · let p := S.max' hS
    have hpS : p ∈ S := S.max'_mem hS
    obtain ⟨_, hp, hpm, hpn⟩ := Finset.mem_filter.mp hpS
    have hgp : g ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_le).mp hpm.symm
    obtain ⟨A, hA, hcard, hbound⟩ := exists_ruzsa_integer p g hp hg hgp
    refine ⟨A, ?_, hbound, ?_, ?_⟩
    · apply hA.trans
      apply Finset.Icc_subset_Icc_right
      have hle : p * ((p - 1) / g) ≤ n := by
        apply Nat.le_of_mul_le_mul_left (c := g) _ hg
        calc
          g * (p * ((p - 1) / g)) = p * (p - 1) := by
            rw [mul_left_comm, Nat.mul_div_cancel' hgp]
          _ ≤ p ^ 2 := by nlinarith [Nat.sub_le p 1]
          _ ≤ g * n := hpn
      exact_mod_cast hle
    · rw [hcard]
      have hsq : (p : ℝ) ^ 2 ≤ (g : ℝ) * n := by exact_mod_cast hpn
      have hpbound : (p : ℝ) ≤ Real.sqrt (g * n) :=
        (Real.le_sqrt (by positivity) (by positivity)).mpr hsq
      exact (show ((p - 1 : ℕ) : ℝ) ≤ p by exact_mod_cast Nat.sub_le p 1).trans hpbound
    · intro q hq hqm hqn
      rw [hcard]
      exact Nat.sub_le_sub_right (S.le_max' q (hmem q hq hqm hqn)) 1
  · refine ⟨∅, by simp, by simp [subRepCount], ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · intro p hp hpm hpn
      exact False.elim (hS ⟨p, hmem p hp hpm hpn⟩)

private theorem exists_prime_modEq_of_sum_lt (g : ℕ) (a b : ℝ)
    (h : (∑ p ∈ Finset.Ioc 0 ⌊a⌋₊ with p.Prime ∧ p ≡ 1 [MOD g], Real.log p) <
      ∑ p ∈ Finset.Ioc 0 ⌊b⌋₊ with p.Prime ∧ p ≡ 1 [MOD g], Real.log p) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD g] ∧ a < p ∧ (p : ℝ) ≤ b := by
  classical
  by_contra! hn
  have hsub : (Finset.Ioc 0 ⌊b⌋₊).filter (fun p => p.Prime ∧ p ≡ 1 [MOD g]) ⊆
      (Finset.Ioc 0 ⌊a⌋₊).filter (fun p => p.Prime ∧ p ≡ 1 [MOD g]) := by
    intro p hp
    obtain ⟨hpI, hpprime, hpmod⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp0, hpb⟩ := Finset.mem_Ioc.mp hpI
    have hb0 : 0 ≤ b := by
      by_contra! hb0
      rw [Nat.floor_of_nonpos hb0.le] at hpb
      omega
    have hpb' : (p : ℝ) ≤ b := (Nat.le_floor_iff hb0).mp hpb
    have hpa : (p : ℝ) ≤ a := by
      by_contra! hpa
      exact (hn p hpprime hpmod hpa).not_ge hpb'
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp0, Nat.le_floor hpa⟩,
      hpprime, hpmod⟩
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => Real.log_natCast_nonneg p)
  exact (not_lt_of_ge hle) h

private theorem eventually_exists_good_prime (g : ℕ) (hg : 0 < g) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD g] ∧
      (1 - ε) * x < p ∧ (p : ℝ) ≤ x := by
  let : NeZero g := ⟨hg.ne'⟩
  let S := fun x : ℝ =>
    ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime ∧ p ≡ 1 [MOD g], Real.log p
  have hS : Tendsto (fun x => S x / x) atTop (𝓝 ((Nat.totient g : ℝ)⁻¹)) :=
    Chebyshev.tendsto_sum_log_prime_modEq_div_atTop (by simp)
  have hlow := hS.comp (tendsto_id.const_mul_atTop (by linarith : 0 < 1 - ε))
  have hlow' : Tendsto (fun x => S ((1 - ε) * x) / x) atTop
      (𝓝 ((Nat.totient g : ℝ)⁻¹ * (1 - ε))) := by
    convert (hlow.mul_const (1 - ε)).congr' ?_ using 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    change S ((1 - ε) * x) / ((1 - ε) * x) * (1 - ε) =
      S ((1 - ε) * x) / x
    field_simp [hx.ne', (sub_pos.mpr hε1).ne']
  have hdiff : Tendsto (fun x => (S x - S ((1 - ε) * x)) / x) atTop
      (𝓝 ((Nat.totient g : ℝ)⁻¹ * ε)) := by
    have hc : (Nat.totient g : ℝ)⁻¹ - (Nat.totient g : ℝ)⁻¹ * (1 - ε) =
        (Nat.totient g : ℝ)⁻¹ * ε := by ring
    simpa only [← sub_div, hc] using hS.sub hlow'
  have hpos : 0 < (Nat.totient g : ℝ)⁻¹ * ε := by
    have ht : 0 < Nat.totient g := Nat.totient_pos.mpr hg
    positivity
  filter_upwards [hdiff.eventually_const_lt hpos, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  apply exists_prime_modEq_of_sum_lt g ((1 - ε) * x) x
  change S ((1 - ε) * x) < S x
  have := (lt_div_iff₀ hx0).mp hx
  linarith

/-- **Lower-bound construction for sets with bounded difference multiplicities.** For every
integer $g \ge 1$ there are finite sets $A_n \subseteq \{1, \dots, n\}$ of integers, one for each
$n \in \mathbb{N}$, such that for every $n$ each nonzero integer $x$ equals $a - a'$ for at most
$g$ ordered pairs $(a, a') \in A_n \times A_n$, and $|A_n| / \sqrt{gn} \to 1$ as $n \to \infty$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Proposition 2 (`integers-2025-A77-prop-2`). -/
public theorem exists_boundedDiffSet_card_div_sqrt_tendsto (g : ℕ) (hg : 0 < g) :
    ∃ A : ℕ → Finset ℤ,
      (∀ n, A n ⊆ Finset.Icc (1 : ℤ) n ∧ ∀ x : ℤ, x ≠ 0 → subRepCount (A n) x ≤ g) ∧
      Tendsto (fun n : ℕ => ((A n).card : ℝ) / Real.sqrt (g * n)) atTop (𝓝 1) := by
  classical
  choose A hsubset hbound hupper hlower using fun n => exists_max_prime_set g n hg
  refine ⟨A, fun n => ⟨hsubset n, hbound n⟩, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro c hc
    by_cases hc0 : c < 0
    · exact Eventually.of_forall fun n => hc0.trans_le (by positivity)
    let ε := (1 - c) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hε1 : ε < 1 := by dsimp [ε]; linarith
    have hεc : c = 1 - 2 * ε := by dsimp [ε]; ring
    have hs : Tendsto (fun n : ℕ => Real.sqrt ((g : ℝ) * n)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by exact_mod_cast hg))
    filter_upwards [hs.eventually (eventually_exists_good_prime g hg ε hε hε1),
      hs.eventually (eventually_gt_atTop (1 / ε + 1))] with n hprime hslarge
    obtain ⟨p, hp, hpm, hplow, hpup⟩ := hprime
    have hspos : 0 < Real.sqrt ((g : ℝ) * n) := by
      have hεinv := one_div_pos.mpr hε
      linarith
    have hpn : p ^ 2 ≤ g * n := by
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      have hsq : (p : ℝ) ^ 2 ≤ (g : ℝ) * n := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (g : ℝ) * n by positivity)]
      exact_mod_cast hsq
    have hcard : (p : ℝ) - 1 ≤ (A n).card := by
      have h := hlower n p hp hpm hpn
      have h' : ((p - 1 : ℕ) : ℝ) ≤ (A n).card := by exact_mod_cast h
      rwa [Nat.cast_sub hp.one_le, Nat.cast_one] at h'
    have hεs : 1 < ε * Real.sqrt ((g : ℝ) * n) := by
      have hm := mul_lt_mul_of_pos_left hslarge hε
      rw [mul_add, mul_one, mul_one_div_cancel hε.ne'] at hm
      linarith
    apply (lt_div_iff₀ hspos).mpr
    rw [hεc]
    nlinarith
  · intro c hc
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hspos : 0 < Real.sqrt ((g : ℝ) * n) := by positivity
    have hratio : ((A n).card : ℝ) / Real.sqrt (g * n) ≤ 1 :=
      (div_le_one hspos).mpr (hupper n)
    exact hratio.trans_lt hc

end

end MetaMathlibExt
