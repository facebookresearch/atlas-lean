/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTree
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.WellQuasiOrder

/-!
# Counting arithmetical structures on stars

Partitioning arithmetical structures by the set of leaves with `d = 1` gives their number
on a star in terms of the numbers of smooth structures on stars with the remaining leaves.
-/

namespace MetaMathlibExt

namespace ArithmeticalStructureStar

open Finset

-- The leaf equations make the central r-label a common multiple of the leaf d-labels.
-- Primitivity says precisely that it is their least common multiple.
private theorem primitive_iff {ι : Type*} [Fintype ι] {a b : ι → ℕ} {c : ℕ}
    (ha : ∀ i, 0 < a i) (hc : 0 < c) (h : ∀ i, a i * b i = c) :
    (∀ g, g ∣ c → (∀ i, g ∣ b i) → g = 1) ↔ c = univ.lcm a := by
  have hd (i : ι) : a i ∣ univ.lcm a := dvd_lcm (mem_univ i)
  constructor
  · intro hprim
    obtain ⟨q, hq⟩ : univ.lcm a ∣ c :=
      lcm_dvd fun i _ => ⟨b i, (h i).symm⟩
    have hone : q = 1 := by
      apply hprim q
      · exact ⟨_, hq.trans (Nat.mul_comm ..)⟩
      · intro i
        obtain ⟨t, ht⟩ := hd i
        refine ⟨t, Nat.eq_of_mul_eq_mul_left (ha i) ?_⟩
        rw [h i, hq, ht]
        ac_rfl
    simpa [hone] using hq
  · rintro rfl g hg hgb
    have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hg hc
    obtain ⟨q, hq⟩ := hg
    have hq' : univ.lcm a ∣ q := by
      apply Finset.lcm_dvd
      intro i _
      obtain ⟨t, ht⟩ := hgb i
      refine ⟨t, Nat.eq_of_mul_eq_mul_left hgpos ?_⟩
      rw [← hq, ← h i, ht]
      ac_rfl
    have hqpos : 0 < q := Nat.pos_of_mul_pos_left (hq ▸ hc)
    have hle := Nat.le_of_dvd hqpos hq'
    by_contra! hne
    have := Nat.mul_lt_mul_of_pos_right (show 1 < g by omega) hqpos
    omega

private abbrev Vertex (s : ℕ) := Fin 1 ⊕ Fin s
private abbrev Labels (s : ℕ) := (Vertex s → ℕ) × (Vertex s → ℕ)

private theorem star_iff {s : ℕ} (d r : Vertex s → ℕ) :
    IsArithmeticalStructure (coconutTree 1 s) d r ↔
      (∀ v, 0 < d v) ∧ (∀ v, 0 < r v) ∧
      d (.inl 0) * r (.inl 0) = ∑ i, r (.inr i) ∧
      (∀ i, d (.inr i) * r (.inr i) = r (.inl 0)) ∧
      r (.inl 0) = univ.lcm (fun i => d (.inr i)) := by
  have center : {w | (coconutTree 1 s).Adj (.inl 0) w} = Set.range Sum.inr := by
    ext (i | i)
    · simp [Subsingleton.elim i 0]
    · simp [coconutTree_adj_inl_inr]
  have leaf (i : Fin s) : {w | (coconutTree 1 s).Adj (.inr i) w} = {Sum.inl 0} := by
    ext (j | j)
    · rw [Set.mem_ofPred_eq, SimpleGraph.adj_comm, coconutTree_adj_inl_inr]
      simp [Subsingleton.elim j 0]
    · simp [coconutTree_not_adj_inr_inr]
  have heq : (∀ v, d v * r v = ∑ᶠ w ∈ {w | (coconutTree 1 s).Adj v w}, r w) ↔
      d (.inl 0) * r (.inl 0) = ∑ i, r (.inr i) ∧
      ∀ i, d (.inr i) * r (.inr i) = r (.inl 0) := by
    rw [Sum.forall, Unique.forall_iff]
    change (_ = ∑ᶠ w ∈ {w | (coconutTree 1 s).Adj (.inl 0) w}, r w) ∧ _ ↔ _
    simp only [center, leaf, finsum_mem_singleton, finsum_mem_range Sum.inr_injective]
    rw [finsum_eq_sum_of_fintype, Subsingleton.elim (default : Fin 1) 0]
  unfold IsArithmeticalStructure
  rw [heq]
  constructor
  · rintro ⟨hd, hr, ⟨hk, hl⟩, hp⟩
    refine ⟨hd, hr, hk, hl, (primitive_iff (fun i => hd (.inr i)) (hr _) hl).mp ?_⟩
    intro g hg hg'
    apply hp
    simpa [Sum.forall] using And.intro hg hg'
  · rintro ⟨hd, hr, hk, hl, hp⟩
    exact ⟨hd, hr, ⟨hk, hl⟩, fun g hg =>
      (primitive_iff (fun i => hd (.inr i)) (hr _) hl).mpr hp g (hg _) (fun i => hg (.inr i))⟩

-- A tuple records the central d-label and the denominators in its unit fraction expansion.
private def Tuples (ι : Type*) [Fintype ι] (m : ℕ) :=
  {x : ℕ × (ι → ℕ) // (∀ i, m ≤ x.2 i) ∧ ∑ i, (1 / (x.2 i : ℚ)) = x.1}

-- Increasing any denominator strictly decreases the sum when the others do not decrease.
-- Thus the tuples form an antichain in a finite product of copies of the naturals.
private theorem tuples_finite {ι : Type*} [Fintype ι] {m : ℕ} (hm : 0 < m) :
    Finite (Tuples ι m) := by
  apply WellQuasiOrderedLE.finite_of_isAntichain (s := {x : ℕ × (ι → ℕ) |
    (∀ i, m ≤ x.2 i) ∧ ∑ i, (1 / (x.2 i : ℚ)) = x.1})
  intro x hx y hy hne hxy
  have hpos (i : ι) : (0 : ℚ) < x.2 i := by exact_mod_cast hm.trans_le (hx.1 i)
  have hle (i : ι) : (1 : ℚ) / y.2 i ≤ 1 / x.2 i :=
    one_div_le_one_div_of_le (hpos i) (by exact_mod_cast hxy.2 i)
  have he : x.2 = y.2 := by
    by_contra hn
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
    have hlt : (1 : ℚ) / y.2 i < 1 / x.2 i :=
      one_div_lt_one_div_of_lt (hpos i) (by exact_mod_cast (hxy.2 i).lt_of_ne hi)
    have hsum := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, mem_univ _, hlt⟩
    rw [hx.2, hy.2] at hsum
    exact (not_lt_of_ge hxy.1) (by exact_mod_cast hsum)
  apply hne
  exact Prod.ext (by exact_mod_cast hx.2.symm.trans (he ▸ hy.2)) he

private theorem sum_recip_iff {ι : Type*} [Fintype ι] {k c : ℕ} {a b : ι → ℕ}
    (hc : 0 < c) (ha : ∀ i, 0 < a i) (h : ∀ i, a i * b i = c) :
    ∑ i, (1 / (a i : ℚ)) = k ↔ k * c = ∑ i, b i := by
  have he : (∑ i, (1 / (a i : ℚ))) * c = ∑ i, (b i : ℚ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← h i, Nat.cast_mul, ← mul_assoc, div_mul_cancel₀ _ (by exact_mod_cast (ha i).ne'),
      one_mul]
  rw [← mul_left_inj' (show (c : ℚ) ≠ 0 by exact_mod_cast hc.ne'), he, eq_comm]
  norm_cast

private abbrev Structures (s m : ℕ) :=
  {x : Labels s // IsArithmeticalStructure (coconutTree 1 s) x.1 x.2 ∧
    ∀ i, m ≤ x.1 (.inr i)}

private def denominators {s m : ℕ} (x : Structures s m) : Tuples (Fin s) m := by
  obtain ⟨hd, hr, hk, hl, -⟩ := (star_iff _ _).mp x.2.1
  exact ⟨(x.val.1 (.inl 0), fun i => x.val.1 (.inr i)), x.2.2,
    (sum_recip_iff (hr _) (fun i => hd (.inr i)) hl).mpr hk⟩

private noncomputable def structuresEquiv {s m : ℕ} (hs : 0 < s) (hm : 0 < m) :
    Structures s m ≃ Tuples (Fin s) m := by
  apply Equiv.ofBijective denominators
  constructor
  · rintro ⟨⟨d, r⟩, hx⟩ ⟨⟨d', r'⟩, hy⟩ h
    have he := congrArg Subtype.val h
    change (d (.inl 0), fun i => d (.inr i)) = (d' (.inl 0), fun i => d' (.inr i)) at he
    obtain ⟨hk, ha⟩ := Prod.mk.inj he
    have hd : d = d' := by
      funext v
      rcases v with i | i
      · simpa [Subsingleton.elim i 0] using hk
      · exact congrFun ha i
    subst d'
    obtain ⟨hpos, -, -, hl, hc⟩ := (star_iff _ _).mp hx.1
    obtain ⟨-, -, -, hl', hc'⟩ := (star_iff _ _).mp hy.1
    have hcenter := hc.trans hc'.symm
    have : r = r' := by
      funext v
      rcases v with i | i
      · simpa [Subsingleton.elim i 0] using hcenter
      · exact Nat.eq_of_mul_eq_mul_left (hpos _) ((hl i).trans (hcenter.trans (hl' i).symm))
    subst r'
    rfl
  · rintro ⟨⟨k, a⟩, ha, hk⟩
    let c := univ.lcm a
    let b (i : Fin s) := c / a i
    have ha' (i) : 0 < a i := hm.trans_le (ha i)
    have hc : 0 < c := Nat.pos_of_ne_zero <| lcm_ne_zero_iff.mpr fun i _ => (ha' i).ne'
    have hl (i) : a i * b i = c := Nat.mul_div_cancel' (dvd_lcm (mem_univ i))
    have hb (i) : 0 < b i := Nat.pos_of_mul_pos_left ((hl i).symm ▸ hc)
    have he := (sum_recip_iff hc ha' hl).mp hk
    have hsum : 0 < ∑ i, b i := sum_pos (fun i _ => hb i) ⟨⟨0, hs⟩, mem_univ _⟩
    have hk' := Nat.pos_of_mul_pos_right (he.symm ▸ hsum)
    refine ⟨⟨(Sum.elim (fun _ => k) a, Sum.elim (fun _ => c) b), ?_, ha⟩, rfl⟩
    exact (star_iff _ _).mpr ⟨by simpa [Sum.forall] using And.intro hk' ha',
      by simpa [Sum.forall] using And.intro hc hb, he, hl, rfl⟩

private def ones {s : ℕ} (x : Tuples (Fin s) 1) : Finset (Fin s) :=
  univ.filter fun i => x.val.2 i = 1

private def fill {s : ℕ} (u : Finset (Fin s)) (a : {i // i ∉ u} → ℕ) (i : Fin s) : ℕ :=
  if h : i ∈ u then 1 else a ⟨i, h⟩

private theorem fill_sum {s : ℕ} (u : Finset (Fin s)) (a : {i // i ∉ u} → ℕ) :
    ∑ i, (1 / (fill u a i : ℚ)) = u.card + ∑ i, (1 / (a i : ℚ)) := by
  have hunit (i : u) : fill u a i = 1 := by simp [fill, i.property]
  have hrest (i : {i // i ∉ u}) : fill u a i = a i := by simp [fill, i.property]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ u)]
  simp [hunit, hrest]

private def extend {s : ℕ} (u : Finset (Fin s)) (x : Tuples {i // i ∉ u} 2) :
    {y : Tuples (Fin s) 1 // ones y = u} := by
  let y : Tuples (Fin s) 1 := ⟨(u.card + x.val.1, fill u x.val.2), by
    intro i
    dsimp [fill]
    split
    · rfl
    · exact (by decide : 1 ≤ 2).trans (x.property.1 _),
    by rw [fill_sum, x.property.2, Nat.cast_add]⟩
  refine ⟨y, ?_⟩
  ext i
  simp only [ones, mem_filter, mem_univ, true_and]
  change fill u x.val.2 i = 1 ↔ _
  by_cases h : i ∈ u
  · simp [fill, h]
  · have hi := x.property.1 ⟨i, h⟩
    simp [fill, h, show x.val.2 ⟨i, h⟩ ≠ 1 by omega]

-- Deleting the unit denominators subtracts their number from the central label.
private noncomputable def fiberEquiv {s : ℕ} (u : Finset (Fin s)) :
    Tuples {i // i ∉ u} 2 ≃ {y : Tuples (Fin s) 1 // ones y = u} := by
  apply Equiv.ofBijective (extend u)
  constructor
  · intro x y h
    have he := congrArg (fun z => (z.val : Tuples (Fin s) 1).val) h
    change (u.card + x.val.1, fill u x.val.2) = (u.card + y.val.1, fill u y.val.2) at he
    obtain ⟨hk, ha⟩ := Prod.mk.inj he
    apply Subtype.ext
    refine Prod.ext (Nat.add_left_cancel hk) ?_
    funext i
    simpa [fill, i.property] using congrFun ha i.val
  · rintro ⟨⟨⟨k, a⟩, ha, hk⟩, hu⟩
    have hone (i : Fin s) : i ∈ u ↔ a i = 1 := by rw [← hu]; simp [ones]
    let b (i : {i // i ∉ u}) := a i
    have hb (i : {i // i ∉ u}) : 2 ≤ b i := by
      have hne : a i.val ≠ 1 := mt (hone _).mpr i.property
      have hpos : 1 ≤ a i.val := ha i.val
      change 2 ≤ a i.val
      omega
    have he : fill u b = a := by
      funext i
      by_cases h : i ∈ u <;> simp [fill, h, b, (hone i).mp]
    have hs := fill_sum u b
    rw [he, hk] at hs
    have hn : (0 : ℚ) ≤ ∑ i, 1 / (b i : ℚ) :=
      sum_nonneg fun i _ => one_div_nonneg.mpr (Nat.cast_nonneg (b i))
    have hle : u.card ≤ k := by exact_mod_cast hs ▸ le_add_of_nonneg_right hn
    refine ⟨⟨(k - u.card, b), hb, ?_⟩, ?_⟩
    · rw [Nat.cast_sub hle, eq_sub_iff_add_eq, add_comm, ← hs]
    · apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (Nat.add_sub_of_le hle) he

private noncomputable def reindex {ι κ : Type*} [Fintype ι] [Fintype κ] {m : ℕ} (e : ι ≃ κ) :
    Tuples ι m ≃ Tuples κ m where
  toFun x := ⟨(x.val.1, x.val.2 ∘ e.symm), fun _ => x.property.1 _,
    (e.symm.sum_comp (fun i => 1 / (x.val.2 i : ℚ))).trans x.property.2⟩
  invFun y := ⟨(y.val.1, y.val.2 ∘ e), fun _ => y.property.1 _,
    (e.sum_comp (fun i => 1 / (y.val.2 i : ℚ))).trans y.property.2⟩
  left_inv x := Subtype.ext (Prod.ext rfl (funext fun i => congrArg x.val.2 (e.symm_apply_apply i)))
  right_inv y :=
    Subtype.ext (Prod.ext rfl (funext fun i => congrArg y.val.2 (e.apply_symm_apply i)))

private theorem count_tuples (s : ℕ) :
    Nat.card (Tuples (Fin s) 1) = ∑ j ∈ range (s + 1),
      s.choose j * Nat.card (Tuples (Fin (s - j)) 2) := by
  classical
  let T (u : Finset (Fin s)) := Tuples {i // i ∉ u} 2
  have e : Tuples (Fin s) 1 ≃ Σ u : Finset (Fin s), T u :=
    (Equiv.sigmaFiberEquiv ones).symm.trans (Equiv.sigmaCongrRight fun u => (fiberEquiv u).symm)
  have (u : Finset (Fin s)) : Finite (T u) := tuples_finite (by decide : 0 < 2)
  rw [Nat.card_congr e, Nat.card_sigma]
  have hcard (u : Finset (Fin s)) : Nat.card (T u) = Nat.card (Tuples (Fin (s - u.card)) 2) := by
    apply Nat.card_congr
    apply reindex
    apply Fintype.equivFinOfCardEq
    simp [Fintype.card_subtype_compl]
  simp_rw [hcard]
  rw [← powerset_univ, sum_powerset]
  simp only [card_univ, Fintype.card_fin]
  exact sum_congr rfl fun j _ =>
    (sum_powersetCard j univ (fun n => Nat.card (Tuples (Fin (s - n)) 2))).trans (by simp)

private theorem count_empty : Nat.card (Tuples (Fin 0) 2) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => Subtype.ext (Prod.ext ?_ (Subsingleton.elim _ _))⟩,
    ⟨⟨(0, Fin.elim0), fun i => i.elim0, by simp⟩⟩⟩
  have hx := x.property.2
  have hy := y.property.2
  simp only [univ_eq_empty, sum_empty, Nat.cast_eq_zero, eq_comm (a := (0 : ℚ))] at hx hy
  exact hx.trans hy.symm

private theorem count_single : Nat.card (Tuples (Fin 1) 2) = 0 := by
  have : IsEmpty (Tuples (Fin 1) 2) := ⟨fun x => by
    have ha := x.property.1 0
    have he : 1 / (x.val.2 0 : ℚ) = x.val.1 := by simpa using x.property.2
    have hpos : (0 : ℚ) < x.val.2 0 := by exact_mod_cast (by omega : 0 < x.val.2 0)
    have hk : 0 < x.val.1 := by exact_mod_cast (one_div_pos.mpr hpos).trans_eq he
    have hlt := one_div_lt_one_div_of_lt (by decide : (0 : ℚ) < 1)
      (show (1 : ℚ) < x.val.2 0 by exact_mod_cast (by omega : 1 < x.val.2 0))
    rw [he, div_one] at hlt
    have : x.val.1 < 1 := by exact_mod_cast hlt
    omega⟩
  simp

private theorem card_arith {s : ℕ} (hs : 0 < s) :
    Set.ncard {x : Labels s | IsArithmeticalStructure (coconutTree 1 s) x.1 x.2} =
      Nat.card (Tuples (Fin s) 1) := by
  rw [← Nat.card_coe_set_eq]
  apply Nat.card_congr
  refine (Equiv.subtypeEquivRight ?_).trans (structuresEquiv hs one_pos)
  intro x
  exact ⟨fun h => ⟨h, fun i => h.1 (.inr i)⟩, And.left⟩

private theorem card_smooth {s : ℕ} (hs : 0 < s) :
    Set.ncard {x : Labels s | IsSmoothCoconut 1 s x.1 x.2} =
      Nat.card (Tuples (Fin s) 2) := by
  rw [← Nat.card_coe_set_eq]
  apply Nat.card_congr
  refine (Equiv.subtypeEquivRight ?_).trans (structuresEquiv hs (by decide : 0 < 2))
  intro x
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun i hi => by omega, h.2⟩⟩

end ArithmeticalStructureStar

open ArithmeticalStructureStar in
/-- **Number of arithmetical structures on stars.** For $s \ge 2$, the number of arithmetical
structures on the star $CT(1, s)$, a centre joined to $s$ leaves, is
$$1 + \sum_{j=0}^{s-2} \binom{s}{j} N(s - j),$$
where $N(t)$ is the number of smooth arithmetical structures on the star $CT(1, t)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 3
(`integers-2025-A82-cor-3`). -/
public theorem ncard_arithmeticalStructure_coconutTree_star {s : ℕ} (hs : 2 ≤ s) :
    Set.ncard {x : (Fin 1 ⊕ Fin s → ℕ) × (Fin 1 ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree 1 s) x.1 x.2}
      = 1 + ∑ j ∈ Finset.range (s - 1), s.choose j *
          Set.ncard {z : (Fin 1 ⊕ Fin (s - j) → ℕ) × (Fin 1 ⊕ Fin (s - j) → ℕ) |
            IsSmoothCoconut 1 (s - j) z.1 z.2} := by
  rw [card_arith (by omega), count_tuples]
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 2 := ⟨s - 2, by omega⟩
  let N (t : ℕ) := Nat.card (Tuples (Fin t) 2)
  let f (j : ℕ) := (n + 2).choose j * N (n + 2 - j)
  change ∑ j ∈ Finset.range (n + 2 + 1), f j = 1 + _
  have hlast : f (n + 2) = 1 := by simp [f, show N 0 = 1 from count_empty]
  have hprev : f (n + 1) = 0 := by
    simp [f, show n + 2 - (n + 1) = 1 by omega, show N 1 = 0 from count_single]
  rw [Finset.sum_range_succ, Finset.sum_range_succ f (n + 1), hlast, hprev, add_zero,
    Nat.add_comm (∑ j ∈ Finset.range (n + 1), f j) 1]
  apply congrArg (1 + ·)
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [card_smooth (by omega)]

end MetaMathlibExt
