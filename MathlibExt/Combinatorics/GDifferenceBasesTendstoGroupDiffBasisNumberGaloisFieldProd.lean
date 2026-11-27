/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Analysis.SpecificLimits.Basic
public import MathlibExt.Combinatorics.Additive.GDifferenceBases
import MathlibExt.Combinatorics.Additive.FiniteFieldDifferenceBases
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic

/-!
# Difference bases of squares of finite fields

For each fixed odd prime $p$, as $t\to\infty$, the normalized $1$-difference basis numbers of
$\mathbb{F}_{p^t} \times \mathbb{F}_{p^t}$ converge to $1$: a counting lower bound and the
parabola construction give the squeeze.
-/

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- The whole finite group represents every element as a difference. -/
private theorem one_le_subRepCount_univ (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (x : G) : 1 ≤ subRepCount Finset.univ x := by
  refine Finset.card_pos.mpr ⟨(x, 0), Finset.mem_filter.mpr ⟨?_, sub_zero x⟩⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩

/-- A `1`-difference basis covers the group by its pairs, so the group size is at most the
square of the basis size. -/
private theorem natCard_le_card_sq_of_basis (G : Type*) [AddCommGroup G]
    [DecidableEq G] (A : Finset G) (hA : ∀ x, 1 ≤ subRepCount A x) :
    Nat.card G ≤ A.card ^ 2 := by
  have hsurj : Function.Surjective (fun p : ↥(A ×ˢ A) => p.1.1 - p.1.2) := by
    intro x
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (hA x)
    exact ⟨⟨p, (Finset.mem_filter.mp hp).1⟩, (Finset.mem_filter.mp hp).2⟩
  have hcard := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_finsetCard, Finset.card_product] at hcard
  calc Nat.card G ≤ A.card * A.card := hcard
    _ = A.card ^ 2 := (pow_two _).symm

/-- If a finite abelian group has $q^2$ elements, every $1$-difference basis has at least $q$
elements. -/
private theorem le_groupDiffBasisNumber_of_card_sq (G : Type*) [AddCommGroup G] [Finite G]
    [DecidableEq G] (q : ℕ) (hcard : Nat.card G = q ^ 2) :
    q ≤ groupDiffBasisNumber 1 G := by
  let : Fintype G := Fintype.ofFinite G
  refine le_csInf ⟨Finset.univ.card, Finset.univ, rfl, one_le_subRepCount_univ G⟩ ?_
  rintro k ⟨A, rfl, hA⟩
  have h := natCard_le_card_sq_of_basis G A hA
  rw [hcard] at h
  exact (Nat.pow_le_pow_iff_left two_ne_zero).mp h

/-- A product of finite abelian groups has a $1$-difference basis formed by the two axes:
every pair $(x_1, x_2)$ is $(x_1, 0) - (0, -x_2)$. -/
private theorem groupDiffBasisNumber_prod_le (G₁ G₂ : Type*) [AddCommGroup G₁]
    [AddCommGroup G₂] [Fintype G₁] [Fintype G₂] [DecidableEq G₁] [DecidableEq G₂] :
    groupDiffBasisNumber 1 (G₁ × G₂) ≤ Fintype.card G₁ + Fintype.card G₂ := by
  let A : Finset (G₁ × G₂) := (Finset.univ ×ˢ {0}) ∪ ({0} ×ˢ Finset.univ)
  calc groupDiffBasisNumber 1 (G₁ × G₂) ≤ A.card := by
        apply Nat.sInf_le
        refine ⟨A, rfl, ?_⟩
        rintro ⟨x₁, x₂⟩
        refine Finset.card_pos.mpr ⟨((x₁, 0), (0, -x₂)), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
        · exact Finset.mem_product.mpr
            ⟨Finset.mem_union_left _ (Finset.mem_product.mpr
              ⟨Finset.mem_univ _, Finset.mem_singleton_self 0⟩),
              Finset.mem_union_right _ (Finset.mem_product.mpr
              ⟨Finset.mem_singleton_self 0, Finset.mem_univ _⟩)⟩
        · exact Prod.ext (sub_zero x₁) (by simp)
    _ ≤ (Finset.univ ×ˢ {0}).card + ({0} ×ˢ Finset.univ).card :=
        Finset.card_union_le _ _
    _ = Fintype.card G₁ + Fintype.card G₂ := by
        rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
          Finset.card_singleton, Finset.card_singleton, mul_one, one_mul]

/-- The $1$-difference basis number does not increase along an additive equivalence: push a
basis forward along the map. -/
private theorem groupDiffBasisNumber_le_of_addEquiv (G H : Type*) [AddCommGroup G]
    [AddCommGroup H] [Finite G] [DecidableEq G] [DecidableEq H] (e : G ≃+ H) :
    groupDiffBasisNumber 1 H ≤ groupDiffBasisNumber 1 G := by
  let : Fintype G := Fintype.ofFinite G
  refine le_csInf ⟨Finset.univ.card, Finset.univ, rfl, one_le_subRepCount_univ G⟩ ?_
  rintro k ⟨B, rfl, hB⟩
  calc groupDiffBasisNumber 1 H ≤ (B.image ⇑e).card := by
        apply Nat.sInf_le
        refine ⟨B.image e, rfl, ?_⟩
        intro y
        obtain ⟨x, rfl⟩ := e.toEquiv.surjective y
        calc 1 ≤ subRepCount B x := hB x
          _ ≤ subRepCount (B.image ⇑e) (e x) := by
              apply Finset.card_le_card_of_injOn (fun p : G × G => (e p.1, e p.2))
              · intro p hp
                obtain ⟨hmem, hpx⟩ := Finset.mem_filter.mp hp
                obtain ⟨ha, hb⟩ := Finset.mem_product.mp hmem
                refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
                · exact Finset.mem_image.mpr ⟨p.1, ha, rfl⟩
                · exact Finset.mem_image.mpr ⟨p.2, hb, rfl⟩
                · rw [← map_sub e p.1 p.2, hpx]
              · intro p _ r _ hpr
                exact Prod.ext (e.injective (congrArg Prod.fst hpr))
                  (e.injective (congrArg Prod.snd hpr))
    _ ≤ B.card := Finset.card_image_le

/-- For $t \ge 1$, the additive group of `GaloisField p t` is a `t`-dimensional vector space over
`ZMod p`, hence additively equivalent to a product of two function spaces whose dimensions add
to `t`. -/
private noncomputable def addEquiv_pi_fin_galoisField (p t : ℕ) [Fact p.Prime] (ht : t ≠ 0) :
    ((Fin (t / 2) → ZMod p) × (Fin (t - t / 2) → ZMod p)) ≃+ GaloisField p t := by
  have hfr : Module.finrank (ZMod p) ((Fin (t / 2) → ZMod p) × (Fin (t - t / 2) → ZMod p))
      = Module.finrank (ZMod p) (GaloisField p t) := by
    rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi, GaloisField.finrank p ht,
      Fintype.card_fin, Fintype.card_fin]
    exact Nat.add_sub_of_le (Nat.div_le_self t 2)
  exact (LinearEquiv.ofFinrankEq _ _ hfr).toAddEquiv

open Classical in
/-- For $t \ge 1$, a difference basis of `GaloisField p t` from the two-axes construction on an
equivalent product: at most $p^{\lfloor t/2\rfloor} + p^{\lceil t/2\rceil}$ elements. -/
private theorem groupDiffBasisNumber_galoisField_le (p t : ℕ) [Fact p.Prime] (ht : t ≠ 0) :
    groupDiffBasisNumber 1 (GaloisField p t) ≤ p ^ (t / 2) + p ^ (t - t / 2) := by
  calc groupDiffBasisNumber 1 (GaloisField p t)
      ≤ groupDiffBasisNumber 1 ((Fin (t / 2) → ZMod p) × (Fin (t - t / 2) → ZMod p)) :=
        groupDiffBasisNumber_le_of_addEquiv _ _ (addEquiv_pi_fin_galoisField p t ht)
    _ ≤ Fintype.card (Fin (t / 2) → ZMod p) + Fintype.card (Fin (t - t / 2) → ZMod p) :=
        groupDiffBasisNumber_prod_le _ _
    _ = p ^ (t / 2) + p ^ (t - t / 2) := by
        congr 1 <;> simp [Fintype.card_pi, ZMod.card, Finset.prod_const]

/-- The error terms $p^{\lfloor t/2\rfloor}/p^t$ and $p^{\lceil t/2\rceil}/p^t$ both tend to
zero. -/
private theorem tendsto_err (p : ℕ) (hp1 : (1 : ℝ) < p) :
    Tendsto (fun t : ℕ => ((p ^ (t / 2) + p ^ (t - t / 2) : ℕ) : ℝ) / (p : ℝ) ^ t)
      atTop (𝓝 0) := by
  have hp0 : (0:ℝ) < p := zero_lt_one.trans hp1
  have hbase : Tendsto (fun n : ℕ => ((p:ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hp0.le) (inv_lt_one_of_one_lt₀ hp1)
  have hlim1 : Tendsto (fun t : ℕ => t / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    exact ⟨2 * M, fun t ht => by omega⟩
  have hlim2 : Tendsto (fun t : ℕ => t - t / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    exact ⟨2 * M, fun t ht => by omega⟩
  have e1 : Tendsto (fun t : ℕ => (p:ℝ)^(t/2) / (p:ℝ)^t) atTop (𝓝 0) := by
    refine Tendsto.congr (fun t => ?_) (hbase.comp hlim2)
    simp only [Function.comp_apply]
    have hpt : (p:ℝ)^t = (p:ℝ)^(t/2) * (p:ℝ)^(t-t/2) := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self t 2)]
    have ha : (p:ℝ)^(t/2) ≠ 0 := (pow_pos hp0 _).ne'
    have hb : (p:ℝ)^(t-t/2) ≠ 0 := (pow_pos hp0 _).ne'
    rw [hpt, inv_pow, ← one_div, div_eq_div_iff hb (mul_ne_zero ha hb), one_mul]
  have e2 : Tendsto (fun t : ℕ => (p:ℝ)^(t-t/2) / (p:ℝ)^t) atTop (𝓝 0) := by
    refine Tendsto.congr (fun t => ?_) (hbase.comp hlim1)
    simp only [Function.comp_apply]
    have hpt : (p:ℝ)^t = (p:ℝ)^(t-t/2) * (p:ℝ)^(t/2) := by
      rw [← pow_add, Nat.sub_add_cancel (Nat.div_le_self t 2)]
    have ha : (p:ℝ)^(t/2) ≠ 0 := (pow_pos hp0 _).ne'
    have hb : (p:ℝ)^(t-t/2) ≠ 0 := (pow_pos hp0 _).ne'
    rw [hpt, inv_pow, ← one_div, div_eq_div_iff ha (mul_ne_zero hb ha), one_mul]
  have hadd := e1.add e2
  rw [add_zero] at hadd
  refine Tendsto.congr (fun t => ?_) hadd
  push_cast
  rw [add_div]

open Classical in
/-- **Difference bases of $\mathbb{F}_{p^t} \times \mathbb{F}_{p^t}$.** Let $p$ be an odd prime.
For a finite abelian group $G$, a set $A \subseteq G$ and $x \in G$, write $r_{A-A}(x)$ for the
number of ordered pairs $(a, a') \in A \times A$ with $a - a' = x$, and let $\eta_1(G)$ be the
least size of a set $A \subseteq G$ with $r_{A-A}(x) \ge 1$ for every $x \in G$. Then
$\eta_1(\mathbb{F}_{p^t} \times \mathbb{F}_{p^t}) / p^t \to 1$ as $t \to \infty$, that is,
$\eta_1(\mathbb{F}_{p^t} \times \mathbb{F}_{p^t}) = (1 + o(1))\, p^t$, where $\mathbb{F}_{p^t}$
is the field with $p^t$ elements.

The restriction to odd $p$ is deliberate: for $p = 2$ the claim fails.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 8 (`integers-2025-A77-lem-8`). -/
public theorem tendsto_groupDiffBasisNumber_galoisField_prod (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) :
    Tendsto (fun t : ℕ =>
        (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) / (p : ℝ) ^ t)
      atTop (𝓝 1) := by
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    omega
  have hp1 : (1:ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have herr : Tendsto (fun t : ℕ => ((p ^ (t / 2) + p ^ (t - t / 2) : ℕ) : ℝ) / (p : ℝ) ^ t)
      atTop (𝓝 0) := tendsto_err p hp1
  have hmain : Tendsto (fun t : ℕ =>
        (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) / (p : ℝ) ^ t - 1)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [Filter.eventually_ge_atTop 1] with t ht
    have ht0 : t ≠ 0 := by omega
    have hp0 : (0:ℝ) < (p:ℝ) := zero_lt_one.trans hp1
    have hpos : (0:ℝ) < (p:ℝ)^t := pow_pos hp0 t
    have hcard : Nat.card (GaloisField p t × GaloisField p t) = (p ^ t) ^ 2 := by
      rw [Nat.card_prod, GaloisField.card p t ht0]
      ring
    have hlower : (p:ℝ)^t ≤
        (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) := by
      have h : p ^ t ≤ groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) :=
        le_groupDiffBasisNumber_of_card_sq _ _ hcard
      calc (p:ℝ)^t = ((p ^ t : ℕ) : ℝ) := (Nat.cast_pow _ _).symm
        _ ≤ _ := by exact_mod_cast h
    have hchar : ringChar (GaloisField p t) ≠ 2 := by
      rw [ringChar.eq (GaloisField p t) p]
      exact hp
    have hupper : (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ)
        ≤ (p:ℝ)^t + ((p ^ (t / 2) + p ^ (t - t / 2) : ℕ) : ℝ) := by
      have h6 := groupDiffBasisNumber_prod_self_le (K := GaloisField p t) hchar
      rw [GaloisField.card p t ht0] at h6
      have hsmall := groupDiffBasisNumber_galoisField_le p t ht0
      have hN : groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t)
          ≤ p ^ t + (p ^ (t / 2) + p ^ (t - t / 2)) := by omega
      calc (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ)
          ≤ ((p ^ t + (p ^ (t / 2) + p ^ (t - t / 2)) : ℕ) : ℝ) := by exact_mod_cast hN
        _ = (p:ℝ)^t + ((p ^ (t / 2) + p ^ (t - t / 2) : ℕ) : ℝ) := by
            simp only [Nat.cast_add, Nat.cast_pow]
    have hnn : (0:ℝ) ≤
        (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) / (p : ℝ) ^ t - 1 := by
      have h1 : (1:ℝ) ≤
          (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) / (p : ℝ) ^ t := by
        rw [le_div_iff₀ hpos, one_mul]
        exact hlower
      exact sub_nonneg.mpr h1
    have heq : (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) / (p:ℝ)^t - 1
        = ((groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) - (p:ℝ)^t) /
          (p:ℝ)^t := by
      rw [eq_div_iff (ne_of_gt hpos), sub_mul, div_mul_cancel₀ _ (ne_of_gt hpos), one_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, heq]
    simp only [div_eq_mul_inv]
    have hsub : (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) - (p:ℝ)^t
        ≤ ((p ^ (t / 2) + p ^ (t - t / 2) : ℕ) : ℝ) := by linarith [hupper]
    exact mul_le_mul_of_nonneg_right hsub (inv_nonneg.mpr hpos.le)
  have h2 := hmain.add_const 1
  simp only [sub_add_cancel, zero_add] at h2
  exact h2

end

end MetaMathlibExt
