/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.GaloisField
public import MathlibExt.Combinatorics.Additive.BoseChowlaSubgroup
public import MathlibExt.Combinatorics.Additive.FiniteFieldDifferenceBases
public import MathlibExt.Combinatorics.Additive.GDifferenceBasisScaling
public import MathlibExt.Combinatorics.Additive.ZModDifferenceBasis

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Real

/-!
# Even and odd limits for difference bases

The normalized difference basis numbers of even and odd dimensional vector spaces over an odd
prime field each converge to a positive limit.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 2.
-/

namespace MetaMathlibExt

open Filter Topology

private theorem transport_basis {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] (e : G ≃+ H) (g : ℕ) (A : Finset G)
    (hA : ∀ x, g ≤ subRepCount A x) : ∀ y, g ≤ subRepCount (A.map e.toEmbedding) y := by
  intro y
  refine (hA (e.symm y)).trans ?_
  apply Finset.card_le_card_of_injOn (fun ab : G × G => (e ab.1, e ab.2))
  · intro ab hab
    obtain ⟨hab, hx⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_map.mpr ⟨ab.1, ha, rfl⟩, Finset.mem_map.mpr ⟨ab.2, hb, rfl⟩⟩, ?_⟩
    simp only [← map_sub, hx, e.apply_symm_apply]
  · intro ab _ cd _ h
    exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))

private theorem basisNumber_congr {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] (e : G ≃+ H) (g : ℕ) :
    groupDiffBasisNumber g G = groupDiffBasisNumber g H := by
  unfold groupDiffBasisNumber
  congr 1
  ext k
  constructor
  · rintro ⟨A, hcard, hA⟩
    exact ⟨A.map e.toEmbedding, (Finset.card_map _).trans hcard, transport_basis e g A hA⟩
  · rintro ⟨A, hcard, hA⟩
    exact ⟨A.map e.symm.toEmbedding, (Finset.card_map _).trans hcard,
      transport_basis e.symm g A hA⟩

private theorem count_le_card {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (x : G) : subRepCount A x ≤ A.card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro ab hab
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).2
  · intro ab hab cd hcd h
    have ha := (Finset.mem_filter.mp hab).2
    have hc := (Finset.mem_filter.mp hcd).2
    exact Prod.ext (sub_left_injective (by simpa only [h] using ha.trans hc.symm)) h

private theorem count_univ {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (x : G) : subRepCount (Finset.univ : Finset G) x = Fintype.card G := by
  apply le_antisymm (by simpa using count_le_card (Finset.univ : Finset G) x)
  rw [← Finset.card_univ]
  apply Finset.card_le_card_of_injOn (fun a : G => (x + a, a))
  · intro a _
    simp
  · intro a _ b _ h
    exact congrArg Prod.snd h

private theorem min_basis (g : ℕ) (G : Type*) [AddCommGroup G] [Finite G]
    [DecidableEq G] (hg : g ≤ Nat.card G) :
    ∃ A : Finset G, A.card = groupDiffBasisNumber g G ∧ ∀ x, g ≤ subRepCount A x := by
  let : Fintype G := Fintype.ofFinite G
  apply Nat.sInf_mem (s := {k | ∃ A : Finset G, A.card = k ∧ ∀ x, g ≤ subRepCount A x})
  refine ⟨Fintype.card G, Finset.univ, Finset.card_univ, fun x => ?_⟩
  simpa only [count_univ, Nat.card_eq_fintype_card] using hg

private theorem basisNumber_prod_le (g : ℕ) (G H : Type*)
    [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    [DecidableEq G] [DecidableEq H] (hg : g ≤ Nat.card G) :
    groupDiffBasisNumber g (G × H) ≤ groupDiffBasisNumber g G * groupDiffBasisNumber 1 H := by
  obtain ⟨A, ha, hA⟩ := min_basis g G hg
  obtain ⟨B, hb, hB⟩ := min_basis 1 H (Nat.succ_le_of_lt Nat.card_pos)
  apply Nat.sInf_le
  exact ⟨A ×ˢ B, by rw [Finset.card_product, ha, hb],
    by simpa only [mul_one] using subRepCount_prod_ge g 1 A B hA hB⟩

private noncomputable def pi_split (p n m : ℕ) [Fact p.Prime] :
    (Fin (n + m) → ZMod p) ≃+ ((Fin n → ZMod p) × (Fin m → ZMod p)) :=
  (LinearEquiv.ofFinrankEq (R := ZMod p) (Fin (n + m) → ZMod p)
    ((Fin n → ZMod p) × (Fin m → ZMod p)) (by simp)).toAddEquiv

private noncomputable def field_equiv (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    (Fin n → ZMod p) ≃+ GaloisField p n :=
  (LinearEquiv.ofFinrankEq (R := ZMod p) (Fin n → ZMod p) (GaloisField p n)
    (by simp [GaloisField.finrank p hn])).toAddEquiv

private theorem pi_card (p n : ℕ) [Fact p.Prime] :
    Nat.card (Fin n → ZMod p) = p ^ n := by
  rw [Nat.card_eq_fintype_card]
  simp

private theorem axes_bound (G H : Type*) [AddCommGroup G] [AddCommGroup H]
    [Finite G] [Finite H] [DecidableEq G] [DecidableEq H] :
    groupDiffBasisNumber 1 (G × H) ≤ Nat.card G + Nat.card H := by
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  let A := (Finset.univ : Finset G).image (fun x => (x, (0 : H))) ∪
    (Finset.univ : Finset H).image (fun y => ((0 : G), y))
  calc
    groupDiffBasisNumber 1 (G × H) ≤ A.card := by
      apply Nat.sInf_le
      refine ⟨A, rfl, fun x => Finset.card_pos.mpr ?_⟩
      refine ⟨((x.1, 0), (0, -x.2)), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x.1, Finset.mem_univ _, rfl⟩),
            Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-x.2, Finset.mem_univ _, rfl⟩)⟩
      · simp
    _ ≤ Nat.card G + Nat.card H := by
      exact (Finset.card_union_le _ _).trans (by
        simpa only [Nat.card_eq_fintype_card, ← Finset.card_univ] using
          Nat.add_le_add (Finset.card_image_le (f := fun x : G => (x, (0 : H))))
            (Finset.card_image_le (f := fun y : H => ((0 : G), y))))

private theorem pi_one_bound (p n : ℕ) [Fact p.Prime] :
    groupDiffBasisNumber 1 (Fin n → ZMod p) ≤ 2 * p ^ (n - n / 2) := by
  have hn : n / 2 + (n - n / 2) = n := by omega
  conv_lhs => rw [← hn, basisNumber_congr (pi_split p (n / 2) (n - n / 2)) 1]
  calc
    _ ≤ Nat.card (Fin (n / 2) → ZMod p) + Nat.card (Fin (n - n / 2) → ZMod p) :=
      axes_bound _ _
    _ ≤ 2 * p ^ (n - n / 2) := by
      rw [pi_card, pi_card]
      have h := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (show n / 2 ≤ n - n / 2 by omega)
      omega

private theorem basisNumber_sqrt_lower (g : ℕ) (G : Type*) [AddCommGroup G]
    [Finite G] [DecidableEq G] (hg : 0 < g) (hsize : g ≤ Nat.card G) :
    Real.sqrt (Nat.card G) ≤ (groupDiffBasisNumber g G : ℝ) := by
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨A, hcard, hA⟩ := min_basis g G hsize
  have hsum : ∑ x : G, subRepCount A x = A.card ^ 2 := by
    change ∑ x ∈ Finset.univ, ((A ×ˢ A).filter (fun ab => ab.1 - ab.2 = x)).card = _
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp [Finset.card_product, pow_two]
  have hsq : Nat.card G ≤ A.card ^ 2 := calc
    Nat.card G = ∑ _x : G, 1 := by simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ x : G, subRepCount A x := Finset.sum_le_sum fun x _ => (show 1 ≤ g from hg).trans (hA x)
    _ = A.card ^ 2 := hsum
  rw [Real.sqrt_le_iff]
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast hcard ▸ hsq⟩

private theorem even_one_bound (p t : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ht : t ≠ 0) :
    (groupDiffBasisNumber 1 (Fin (2 * t) → ZMod p) : ℝ) ≤
      (p : ℝ) ^ t * (1 + 2 / (p : ℝ) ^ (t / 2)) := by
  classical
  let e := (pi_split p t t).trans
    (AddEquiv.prodCongr (field_equiv p t ht) (field_equiv p t ht))
  have hfield : groupDiffBasisNumber 1 (GaloisField p t) ≤ 2 * p ^ (t - t / 2) := by
    rw [← basisNumber_congr (field_equiv p t ht) 1]
    exact pi_one_bound p t
  have hchar : ringChar (GaloisField p t) ≠ 2 := by
    simpa only [ringChar.eq (GaloisField p t) p] using hp
  have hbound : groupDiffBasisNumber 1 (Fin (2 * t) → ZMod p) ≤
      p ^ t + 2 * p ^ (t - t / 2) := by
    rw [two_mul, basisNumber_congr e 1]
    exact (groupDiffBasisNumber_prod_self_le hchar).trans (by
      rw [GaloisField.card p t ht]
      exact Nat.add_le_add_left hfield _)
  have hpow : (p : ℝ) ^ t = (p : ℝ) ^ (t - t / 2) * (p : ℝ) ^ (t / 2) := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.div_le_self _ _)]
  have hpos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have heq : (p : ℝ) ^ t * (1 + 2 / (p : ℝ) ^ (t / 2)) =
      (p : ℝ) ^ t + 2 * (p : ℝ) ^ (t - t / 2) := by
    rw [mul_add, mul_one, hpow, mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ hpos.ne')]
    ring
  rw [heq]
  exact_mod_cast hbound

private theorem factor_tendsto (p : ℕ) [Fact p.Prime] :
    Tendsto (fun t : ℕ => 1 + 2 / (p : ℝ) ^ (t / 2)) atTop (𝓝 1) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt hp).comp
    (Nat.tendsto_div_const_atTop (by decide : 2 ≠ 0))
  simpa only [Function.comp_def, add_zero] using (hpow.const_div_atTop 2).const_add 1

private theorem convergence_of_product_bound (f b : ℕ → ℝ) (N : ℕ)
    (hlower : ∀ n, N ≤ n → 1 ≤ f n)
    (hprod : ∀ n t, N ≤ n → 0 < t → f (n + t) ≤ f n * b t)
    (hb : Tendsto b atTop (𝓝 1)) : ∃ L : ℝ, 0 < L ∧ Tendsto f atTop (𝓝 L) := by
  let S := f '' Set.Ici N
  have hS : S.Nonempty := ⟨f N, N, Set.mem_Ici.mpr le_rfl, rfl⟩
  have hbelow : BddBelow S := ⟨1, by rintro x ⟨n, hn, rfl⟩; exact hlower n hn⟩
  have hL : 1 ≤ sInf S := le_csInf hS (by rintro x ⟨n, hn, rfl⟩; exact hlower n hn)
  refine ⟨sInf S, lt_of_lt_of_le zero_lt_one hL, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro a ha
    filter_upwards [eventually_ge_atTop N] with n hn
    exact ha.trans_le (csInf_le hbelow ⟨n, hn, rfl⟩)
  · intro a ha
    obtain ⟨x, ⟨n, hn, rfl⟩, hx⟩ := exists_lt_of_csInf_lt hS ha
    have ht : Tendsto (fun t => f n * b t) atTop (𝓝 (f n)) := by
      simpa only [mul_one] using hb.const_mul (f n)
    obtain ⟨M, hM⟩ := eventually_atTop.mp (ht.eventually_lt_const hx)
    filter_upwards [eventually_ge_atTop (n + max M 1)] with k hk
    have hkn : n + (k - n) = k := by omega
    calc
      f k = f (n + (k - n)) := congrArg f hkn.symm
      _ ≤ f n * b (k - n) := hprod n (k - n) hn (by omega)
      _ < a := hM (k - n) (by omega)

private noncomputable def normalized (p : ℕ) [Fact p.Prime] (g r k : ℕ) : ℝ :=
  (groupDiffBasisNumber g (Fin (2 * k + r) → ZMod p) : ℝ) /
    Real.sqrt ((p : ℝ) ^ (2 * k + r))

private theorem normalized_lower (p g r k : ℕ) [Fact p.Prime]
    (hg : 0 < g) (hsize : g ≤ p ^ (2 * k + r)) : 1 ≤ normalized p g r k := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [normalized, le_div_iff₀ (Real.sqrt_pos.mpr (pow_pos hp _)), one_mul]
  simpa only [pi_card, Nat.cast_pow] using
    basisNumber_sqrt_lower g (Fin (2 * k + r) → ZMod p) hg (by rwa [pi_card])

private theorem normalized_product_bound (p g r n t : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hsize : g ≤ p ^ (2 * n + r)) (ht : 0 < t) :
    normalized p g r (n + t) ≤ normalized p g r n * (1 + 2 / (p : ℝ) ^ (t / 2)) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnum : groupDiffBasisNumber g (Fin (2 * (n + t) + r) → ZMod p) ≤
      groupDiffBasisNumber g (Fin (2 * n + r) → ZMod p) *
        groupDiffBasisNumber 1 (Fin (2 * t) → ZMod p) := by
    rw [show 2 * (n + t) + r = (2 * n + r) + 2 * t by omega,
      basisNumber_congr (pi_split p (2 * n + r) (2 * t)) g]
    exact basisNumber_prod_le g _ _ (by rwa [pi_card])
  have hden : Real.sqrt ((p : ℝ) ^ (2 * (n + t) + r)) =
      Real.sqrt ((p : ℝ) ^ (2 * n + r)) * (p : ℝ) ^ t := by
    rw [show 2 * (n + t) + r = (2 * n + r) + 2 * t by omega, pow_add,
      Real.sqrt_mul (by positivity), show 2 * t = t * 2 by omega, pow_mul,
      Real.sqrt_sq (by positivity)]
  have hbound := mul_le_mul_of_nonneg_left (even_one_bound p t hp ht.ne')
    (Nat.cast_nonneg (groupDiffBasisNumber g (Fin (2 * n + r) → ZMod p)))
  have hnumReal : (groupDiffBasisNumber g (Fin (2 * (n + t) + r) → ZMod p) : ℝ) ≤
      (groupDiffBasisNumber g (Fin (2 * n + r) → ZMod p) : ℝ) *
        (groupDiffBasisNumber 1 (Fin (2 * t) → ZMod p) : ℝ) := by exact_mod_cast hnum
  have hnum' : (groupDiffBasisNumber g (Fin (2 * (n + t) + r) → ZMod p) : ℝ) ≤
      (groupDiffBasisNumber g (Fin (2 * n + r) → ZMod p) : ℝ) *
        ((p : ℝ) ^ t * (1 + 2 / (p : ℝ) ^ (t / 2))) :=
    hnumReal.trans hbound
  rw [normalized, normalized, hden]
  rw [div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr (pow_pos hp₀ _)) (pow_pos hp₀ _))]
  calc
    _ ≤ _ := hnum'
    _ = _ := by
      field_simp [hp₀.ne', Real.sqrt_ne_zero'.mpr (pow_pos hp₀ _)]

private theorem parity_limit (p g r : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hg : 0 < g) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (fun k => normalized p g r k) atTop (𝓝 L) := by
  have hsize (n : ℕ) (hn : g ≤ n) : g ≤ p ^ (2 * n + r) := by
    exact (show g ≤ 2 * n + r by omega).trans (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  exact convergence_of_product_bound (normalized p g r)
    (fun t => 1 + 2 / (p : ℝ) ^ (t / 2)) g
    (fun n hn => normalized_lower p g r n hg (hsize n hn))
    (fun n t hn ht => normalized_product_bound p g r n t hp (hsize n hn) ht)
    (factor_tendsto p)

@[expose] public section

/-- **Even and odd limits for difference bases of $\mathbb{F}_p^n$.** Let $p$ be an odd prime and
$g \ge 1$ an integer. For a finite abelian group $G$, a set $A \subseteq G$ and $x \in G$, write
$r_{A-A}(x)$ for the number of ordered pairs $(a, a') \in A \times A$ with $a - a' = x$, and let
$\eta_g(G)$ be the least size of a set $A \subseteq G$ with $r_{A-A}(x) \ge g$ for every $x \in G$.
Then there are real numbers $L_e > 0$ and $L_o > 0$ such that, as $k \to \infty$,
$\eta_g(\mathbb{F}_p^{2k}) / \sqrt{p^{2k}} \to L_e$ and
$\eta_g(\mathbb{F}_p^{2k+1}) / \sqrt{p^{2k+1}} \to L_o$, where $\mathbb{F}_p^n$ is the additive
group of $n$-tuples over the field $\mathbb{F}_p$ with $p$ elements.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 2 (`integers-2025-A77-thm-2`). -/
public theorem tendsto_groupDiffBasisNumber_even_odd (p g : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hg : 0 < g) :
    (∃ Le : ℝ, 0 < Le ∧ Tendsto (fun k : ℕ =>
        (groupDiffBasisNumber g (Fin (2 * k) → ZMod p) : ℝ) / Real.sqrt ((p : ℝ) ^ (2 * k)))
      atTop (𝓝 Le)) ∧
    (∃ Lo : ℝ, 0 < Lo ∧ Tendsto (fun k : ℕ =>
        (groupDiffBasisNumber g (Fin (2 * k + 1) → ZMod p) : ℝ) /
          Real.sqrt ((p : ℝ) ^ (2 * k + 1)))
      atTop (𝓝 Lo)) := by
  constructor
  · simpa only [normalized, Nat.add_zero] using parity_limit p g 0 hp hg
  · exact parity_limit p g 1 hp hg

end

end MetaMathlibExt
