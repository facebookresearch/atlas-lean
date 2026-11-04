/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Tucker grid basic definitions and order lemmas -/

/-- Grid box: `z ∈ bu_tkBox n m` iff `|z i| ≤ m` for all `i`. -/
private def bu_tkBox (n m : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ : Fin n => Finset.Icc (-(m : ℤ)) (m : ℤ)

/-- Freund–Todd step order: `w` is `z` with some coordinates pushed one unit away from `0`. -/
private def bu_tkLe {n : ℕ} (z w : Fin n → ℤ) : Prop :=
  ∀ i, w i = z i ∨ (0 ≤ z i ∧ w i = z i + 1) ∨ (z i ≤ 0 ∧ w i = z i - 1)

/-- Chains: nonempty sets of pairwise comparable points (the simplices). -/
private def bu_tkChain {n : ℕ} (σ : Finset (Fin n → ℤ)) : Prop :=
  σ.Nonempty ∧ ∀ z ∈ σ, ∀ w ∈ σ, bu_tkLe z w ∨ bu_tkLe w z

/-- Label negation: flips the sign, keeps the index. -/
private def bu_tkNeg {n : ℕ} (l : Bool × Fin n) : Bool × Fin n := (!l.1, l.2)

/-- Sign set of a grid point: `(true, i)` for `z i > 0`, `(false, i)` for `z i < 0`. -/
private def bu_tkSgn {n : ℕ} (z : Fin n → ℤ) : Finset (Bool × Fin n) :=
  (Finset.univ.filter fun i => z i ≠ 0).image fun i => (decide (0 < z i), i)

/-- Sign set of a chain (the sign set of its top vertex). -/
private def bu_tkS {n : ℕ} (σ : Finset (Fin n → ℤ)) : Finset (Bool × Fin n) :=
  σ.sup bu_tkSgn

/-- Boundary: every point of `σ` has some coordinate of absolute value `m`. -/
private def bu_tkBdry {n : ℕ} (m : ℕ) (σ : Finset (Fin n → ℤ)) : Prop :=
  ∀ z ∈ σ, ∃ i, |z i| = (m : ℤ)

/-- Happy chain: inside the box, a chain, and every sign is witnessed by a label. -/
private def bu_tkHappy {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (σ : Finset (Fin n → ℤ)) : Prop :=
  σ ⊆ bu_tkBox n m ∧ bu_tkChain σ ∧ bu_tkS σ ⊆ σ.image L

/-- No complementary edge: no comparable pair in the box carries opposite labels. -/
private def bu_tkNoCompl {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n) : Prop :=
  ∀ z ∈ bu_tkBox n m, ∀ w ∈ bu_tkBox n m, bu_tkLe z w → L w ≠ bu_tkNeg (L z)

/-- Height: sum of absolute values. Strictly increases along `bu_tkLe`. -/
private def bu_tkH {n : ℕ} (z : Fin n → ℤ) : ℕ := ∑ i, (z i).natAbs

private theorem bu_mem_tkBox {n m : ℕ} {z : Fin n → ℤ} :
    z ∈ bu_tkBox n m ↔ ∀ i, |z i| ≤ (m : ℤ) := by
  rw [bu_tkBox, Fintype.mem_piFinset]
  constructor
  · intro h i
    have hi := h i
    rw [Finset.mem_Icc] at hi
    rw [abs_le]
    exact hi
  · intro h i
    rw [Finset.mem_Icc, ← abs_le]
    exact h i

private theorem bu_zero_mem_tkBox {n m : ℕ} : (0 : Fin n → ℤ) ∈ bu_tkBox n m := by
  rw [bu_mem_tkBox]
  intro i
  simp

private theorem bu_neg_mem_tkBox {n m : ℕ} {z : Fin n → ℤ} (hz : z ∈ bu_tkBox n m) :
    -z ∈ bu_tkBox n m := by
  rw [bu_mem_tkBox] at hz ⊢
  intro i
  rw [Pi.neg_apply, abs_neg]
  exact hz i

private theorem bu_tkLe_refl {n : ℕ} (z : Fin n → ℤ) : bu_tkLe z z := fun _ =>
  Or.inl rfl

private theorem bu_tkLe_natAbs {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w)
    (i : Fin n) : (z i).natAbs ≤ (w i).natAbs := by
  rcases h i with hcon | ⟨h0, hw⟩ | ⟨h0, hw⟩ <;> omega

private theorem bu_tkLe_height {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w) :
    bu_tkH z ≤ bu_tkH w :=
  Finset.sum_le_sum fun i _ => bu_tkLe_natAbs h i

private theorem bu_tkLe_height_lt {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w)
    (hne : z ≠ w) : bu_tkH z < bu_tkH w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine Finset.sum_lt_sum (fun j _ => bu_tkLe_natAbs h j) ⟨i, Finset.mem_univ i, ?_⟩
  rcases h i with hcon | ⟨h0, hw⟩ | ⟨h0, hw⟩
  · exact (hi hcon.symm).elim
  · simp only [hw]; omega
  · simp only [hw]; omega

private theorem bu_tkLe_of_height_eq {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w)
    (he : bu_tkH z = bu_tkH w) : z = w := by
  by_contra hne
  exact absurd he (ne_of_lt (bu_tkLe_height_lt h hne))

private theorem bu_tkLe_antisymm {n : ℕ} {z w : Fin n → ℤ} (h1 : bu_tkLe z w)
    (h2 : bu_tkLe w z) : z = w := by
  by_contra hne
  have hlt := bu_tkLe_height_lt h1 hne
  have hle := bu_tkLe_height h2
  omega

/-- Membership characterization of the sign set. -/
private theorem bu_mem_tkSgn {n : ℕ} {z : Fin n → ℤ} {l : Bool × Fin n} :
    l ∈ bu_tkSgn z ↔ z l.2 ≠ 0 ∧ l.1 = decide (0 < z l.2) := by
  rw [bu_tkSgn, Finset.mem_image]
  constructor
  · rintro ⟨j, hjmem, hjl⟩
    rw [Finset.mem_filter] at hjmem
    obtain ⟨_, hj0⟩ := hjmem
    rw [← hjl]
    exact ⟨hj0, rfl⟩
  · rintro ⟨hz, hb⟩
    exact ⟨l.2, Finset.mem_filter.mpr ⟨Finset.mem_univ l.2, hz⟩,
      Prod.ext_iff.mpr ⟨hb.symm, rfl⟩⟩

private theorem bu_tkSgn_mono {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w) :
    bu_tkSgn z ⊆ bu_tkSgn w := by
  intro l hl
  have hl' : z l.2 ≠ 0 ∧ l.1 = decide (0 < z l.2) := bu_mem_tkSgn.mp hl
  obtain ⟨hz0, hbl⟩ := hl'
  have hw0 : w l.2 ≠ 0 := by
    have hle := bu_tkLe_natAbs h l.2
    omega
  have hsign : (0 < w l.2) ↔ (0 < z l.2) := by
    rcases h l.2 with heq | ⟨h0, hw⟩ | ⟨h0, hw⟩
    · rw [heq]
    · constructor <;> intro <;> omega
    · constructor <;> intro <;> omega
  have hdec : decide (0 < w l.2) = decide (0 < z l.2) := by
    simp only [hsign]
  have hbl' : l.1 = decide (0 < w l.2) := by rw [hdec]; exact hbl
  exact bu_mem_tkSgn.mpr ⟨hw0, hbl'⟩

private theorem bu_tkNeg_invol {n : ℕ} : Function.Involutive (@bu_tkNeg n) := by
  intro l
  obtain ⟨b, i⟩ := l
  cases b <;> rfl

private theorem bu_tkNeg_inj {n : ℕ} : Function.Injective (@bu_tkNeg n) :=
  bu_tkNeg_invol.injective

private theorem bu_decide_neg {a : ℤ} (ha : a ≠ 0) :
    decide (0 < -a) = !decide (0 < a) := by
  by_cases h : 0 < a
  · simp [h]; omega
  · simp [h]; omega

private theorem bu_tkSgn_neg {n : ℕ} (z : Fin n → ℤ) :
    bu_tkSgn (-z) = (bu_tkSgn z).image bu_tkNeg := by
  ext ⟨b, i⟩
  rw [bu_mem_tkSgn, Finset.mem_image]
  constructor
  · intro h
    have h' : -z i ≠ 0 ∧ b = decide (0 < -z i) := h
    obtain ⟨hz, hb⟩ := h'
    have hz0 : z i ≠ 0 := by simpa using hz
    refine ⟨(!b, i), bu_mem_tkSgn.mpr ⟨hz0, ?_⟩, ?_⟩
    · change (!b) = decide (0 < z i)
      have hb2 : (!b) = !(decide (0 < -z i)) := congrArg Bool.not hb
      rw [hb2, bu_decide_neg hz0, Bool.not_not]
    · change ((!(!b)), i) = (b, i)
      rw [Bool.not_not]
  · rintro ⟨⟨b', j⟩, hmem, heq⟩
    have hmem' : z j ≠ 0 ∧ b' = decide (0 < z j) := bu_mem_tkSgn.mp hmem
    obtain ⟨hz0, hb'⟩ := hmem'
    have h1 : (!b') = b := congrArg Prod.fst heq
    have h2 : j = i := congrArg Prod.snd heq
    rw [h2] at hz0 hb'
    refine ⟨by simpa using hz0, ?_⟩
    change b = decide (0 < -z i)
    rw [← h1, hb', bu_decide_neg hz0]

private theorem bu_tkLe_neg {n : ℕ} {z w : Fin n → ℤ} :
    bu_tkLe (-z) (-w) ↔ bu_tkLe z w := by
  simp only [bu_tkLe, Pi.neg_apply]
  constructor
  · intro h i
    rcases h i with hcon | ⟨h0, hw⟩ | ⟨h0, hw⟩
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · intro h i
    rcases h i with hcon | ⟨h0, hw⟩ | ⟨h0, hw⟩
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)

private theorem bu_tkSgn_consistent {n : ℕ} {z : Fin n → ℤ} {b : Bool} {i : Fin n}
    (h : (b, i) ∈ bu_tkSgn z) : (!b, i) ∉ bu_tkSgn z := by
  have h' : z i ≠ 0 ∧ b = decide (0 < z i) := bu_mem_tkSgn.mp h
  obtain ⟨hz, hb⟩ := h'
  intro hcon
  have hcon' : z i ≠ 0 ∧ (!b) = decide (0 < z i) := bu_mem_tkSgn.mp hcon
  rw [hb] at hcon'
  exact absurd hcon'.2 (by cases b <;> simp)

private theorem bu_tkSgn_snd_injective {n : ℕ} {z : Fin n → ℤ} :
    Set.InjOn Prod.snd (↑(bu_tkSgn z) : Set (Bool × Fin n)) := by
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  have hab2 : a2 = b2 := hab
  subst hab2
  have ha' : z a2 ≠ 0 ∧ a1 = decide (0 < z a2) := bu_mem_tkSgn.mp ha
  have hb' : z a2 ≠ 0 ∧ b1 = decide (0 < z a2) := bu_mem_tkSgn.mp hb
  rw [ha'.2, hb'.2]

private theorem bu_tkSgn_card {n : ℕ} (z : Fin n → ℤ) :
    (bu_tkSgn z).card = (Finset.univ.filter fun i => z i ≠ 0).card := by
  rw [bu_tkSgn]
  apply Finset.card_image_of_injOn
  intro a _ b _ hab
  simp only at hab
  exact congrArg Prod.snd hab

/-- Quasi-transitivity: two steps collapse when the endpoints are comparable. -/
private theorem bu_tkLe_trans_of_comparable {n : ℕ} {z w u : Fin n → ℤ}
    (h1 : bu_tkLe z w) (h2 : bu_tkLe w u) (hc : bu_tkLe z u ∨ bu_tkLe u z) :
    bu_tkLe z u := by
  rcases hc with h | h
  · exact h
  · have e1 := bu_tkLe_height h1
    have e2 := bu_tkLe_height h2
    have e3 := bu_tkLe_height h
    have hzw : z = w := bu_tkLe_of_height_eq h1 (by omega)
    subst hzw
    exact h2

/-! ## Chains have a bottom and a top -/

private theorem bu_chain_bot_top {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) :
    ∃ b ∈ σ, ∃ t ∈ σ, (∀ z ∈ σ, bu_tkLe b z) ∧ (∀ z ∈ σ, bu_tkLe z t) ∧
      bu_tkS σ = bu_tkSgn t := by
  obtain ⟨hne, hcomp⟩ := hσ
  obtain ⟨b, hbσ, hbmin⟩ := Finset.exists_min_image σ bu_tkH hne
  obtain ⟨t, htσ, htmax⟩ := Finset.exists_max_image σ bu_tkH hne
  have hbot : ∀ z ∈ σ, bu_tkLe b z := by
    intro z hz
    rcases hcomp b hbσ z hz with h | h
    · exact h
    · have he : bu_tkH z = bu_tkH b :=
        le_antisymm (bu_tkLe_height h) (hbmin z hz)
      have e : z = b := bu_tkLe_of_height_eq h he
      rw [e]
      exact bu_tkLe_refl b
  have htop : ∀ z ∈ σ, bu_tkLe z t := by
    intro z hz
    rcases hcomp z hz t htσ with h | h
    · exact h
    · have he : bu_tkH t = bu_tkH z :=
        le_antisymm (bu_tkLe_height h) (htmax z hz)
      have e : t = z := bu_tkLe_of_height_eq h he
      rw [e]
      exact bu_tkLe_refl z
  refine ⟨b, hbσ, t, htσ, hbot, htop, ?_⟩
  apply le_antisymm
  · simp only [bu_tkS, Finset.sup_le_iff]
    intro z hz
    exact bu_tkSgn_mono (htop z hz)
  · exact Finset.le_sup htσ

/-- Within a chain, the order is the height order. -/
private theorem bu_chain_height_iff {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) {z w : Fin n → ℤ} (hz : z ∈ σ) (hw : w ∈ σ) :
    bu_tkLe z w ↔ bu_tkH z ≤ bu_tkH w := by
  constructor
  · exact bu_tkLe_height
  · intro hle
    rcases hσ.2 z hz w hw with h | h
    · exact h
    · have he : bu_tkH z = bu_tkH w := le_antisymm hle (bu_tkLe_height h)
      have e : z = w := (bu_tkLe_of_height_eq h he.symm).symm
      rw [e]
      exact bu_tkLe_refl w

/-- The height is injective on a chain. -/
private theorem bu_chain_height_inj {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) {z w : Fin n → ℤ} (hz : z ∈ σ) (hw : w ∈ σ)
    (he : bu_tkH z = bu_tkH w) : z = w := by
  rcases hσ.2 z hz w hw with h | h
  · exact bu_tkLe_of_height_eq h he
  · exact (bu_tkLe_of_height_eq h he.symm).symm

/-! ## Moved-set normal form -/

/-- Moved set: coordinates where `z` differs from the bottom `b`. -/
private def bu_tkMv {n : ℕ} (b z : Fin n → ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun i => z i ≠ b i

/-- Point with moved set `M`: take `t` on `M`, `b` off `M`. -/
private def bu_tkPt {n : ℕ} (b t : Fin n → ℤ) (M : Finset (Fin n)) :
    Fin n → ℤ :=
  fun i => if i ∈ M then t i else b i

private theorem bu_tkMv_normal_a {n : ℕ} {b t z : Fin n → ℤ}
    (hbt : bu_tkLe b t) (hbz : bu_tkLe b z) (hzt : bu_tkLe z t) :
    bu_tkMv b z ⊆ bu_tkMv b t ∧ z = bu_tkPt b t (bu_tkMv b z) := by
  have hsub : bu_tkMv b z ⊆ bu_tkMv b t := by
    intro i hi
    have hne : z i ≠ b i := by
      have hm := hi
      rw [bu_tkMv, Finset.mem_filter] at hm
      exact hm.2
    have hmem : t i ≠ b i := by
      have h1 := hbz i
      have h2 := hzt i
      have h3 := hbt i
      rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
      · exact absurd c1 hne
      · rcases h2 with c2 | ⟨s2, e2⟩ | ⟨s2, e2⟩ <;>
          rcases h3 with c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega
      · rcases h2 with c2 | ⟨s2, e2⟩ | ⟨s2, e2⟩ <;>
          rcases h3 with c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmem⟩
  refine ⟨hsub, ?_⟩
  funext i
  by_cases h : z i = b i
  · have hi : i ∉ bu_tkMv b z := by
      rw [bu_tkMv, Finset.mem_filter]
      simp [h]
    have e : (bu_tkPt b t (bu_tkMv b z)) i = b i := by simp [bu_tkPt, hi]
    rw [e]
    exact h
  · have hi : i ∈ bu_tkMv b z :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
    have e : (bu_tkPt b t (bu_tkMv b z)) i = t i := by simp [bu_tkPt, hi]
    rw [e]
    have h1 := hbz i
    have h2 := hzt i
    have h3 := hbt i
    rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
    · exact absurd c1 h
    · rcases h2 with c2 | ⟨s2, e2⟩ | ⟨s2, e2⟩ <;>
        rcases h3 with c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega
    · rcases h2 with c2 | ⟨s2, e2⟩ | ⟨s2, e2⟩ <;>
        rcases h3 with c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega

/-- The point constructor is monotone in the moved set. -/
private theorem bu_tkPt_mono {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
    {M1 M2 : Finset (Fin n)} (h : M1 ⊆ M2) :
    bu_tkLe (bu_tkPt b t M1) (bu_tkPt b t M2) := by
  intro i
  have h5 := hbt i
  by_cases h1 : i ∈ M1
  · have h2 : i ∈ M2 := h h1
    have e1 : (bu_tkPt b t M1) i = t i := by simp [bu_tkPt, h1]
    have e2 : (bu_tkPt b t M2) i = t i := by simp [bu_tkPt, h2]
    rw [e1, e2]
    exact Or.inl rfl
  · by_cases h3 : i ∈ M2
    · have e1 : (bu_tkPt b t M1) i = b i := by simp [bu_tkPt, h1]
      have e2 : (bu_tkPt b t M2) i = t i := by simp [bu_tkPt, h3]
      rw [e1, e2]
      exact h5
    · have e1 : (bu_tkPt b t M1) i = b i := by simp [bu_tkPt, h1]
      have e2 : (bu_tkPt b t M2) i = b i := by simp [bu_tkPt, h3]
      rw [e1, e2]
      exact Or.inl rfl

private theorem bu_tkMv_mono_of_le {n : ℕ} {b z w : Fin n → ℤ}
    (hbz : bu_tkLe b z) (hbw : bu_tkLe b w) (hzw : bu_tkLe z w) :
    bu_tkMv b z ⊆ bu_tkMv b w := by
  intro i hi
  have hne : z i ≠ b i := by
    have hm := hi
    rw [bu_tkMv, Finset.mem_filter] at hm
    exact hm.2
  have hmem : w i ≠ b i := by
    have h1 := hbz i
    have h0 := hzw i
    have h3 := hbw i
    rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
    · exact absurd c1 hne
    · rcases h0 with c0 | ⟨s0, e0⟩ | ⟨s0, e0⟩ <;>
        rcases h3 with c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega
    · rcases h0 with c0 | ⟨s0, e0⟩ | ⟨s0, e0⟩ <;>
        rcases h3 with c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmem⟩

/-- Comparability of two points between `b` and `t` is inclusion of moved sets. -/
private theorem bu_tkMv_le_iff {n : ℕ} {b t z w : Fin n → ℤ}
    (hbt : bu_tkLe b t) (hbz : bu_tkLe b z) (hzt : bu_tkLe z t)
    (hbw : bu_tkLe b w) (hwt : bu_tkLe w t) :
    bu_tkLe z w ↔ bu_tkMv b z ⊆ bu_tkMv b w := by
  constructor
  · intro hzw
    exact bu_tkMv_mono_of_le hbz hbw hzw
  · intro hsub
    have ez : z = bu_tkPt b t (bu_tkMv b z) :=
      (bu_tkMv_normal_a hbt hbz hzt).2
    have ew : w = bu_tkPt b t (bu_tkMv b w) :=
      (bu_tkMv_normal_a hbt hbw hwt).2
    rw [ez, ew]
    exact bu_tkPt_mono hbt hsub

/-- Every subset of the top moved set gives a point between `b` and `t`. -/
private theorem bu_tkPt_mem_of_mem {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
    {M : Finset (Fin n)} (hM : M ⊆ bu_tkMv b t) :
    bu_tkLe b (bu_tkPt b t M) ∧ bu_tkLe (bu_tkPt b t M) t ∧
      bu_tkMv b (bu_tkPt b t M) = M := by
  have h1 : bu_tkLe b (bu_tkPt b t M) := by
    intro i
    have h5 := hbt i
    by_cases hM' : i ∈ M
    · have e : (bu_tkPt b t M) i = t i := by simp [bu_tkPt, hM']
      rw [e]
      exact h5
    · have e : (bu_tkPt b t M) i = b i := by simp [bu_tkPt, hM']
      rw [e]
      exact Or.inl rfl
  have h2 : bu_tkLe (bu_tkPt b t M) t := by
    intro i
    have h5 := hbt i
    by_cases hM' : i ∈ M
    · have e : (bu_tkPt b t M) i = t i := by simp [bu_tkPt, hM']
      rw [e]
      exact Or.inl rfl
    · have e : (bu_tkPt b t M) i = b i := by simp [bu_tkPt, hM']
      rw [e]
      exact h5
  refine ⟨h1, h2, ?_⟩
  ext i
  rw [bu_tkMv, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  by_cases hM' : i ∈ M
  · have e : (bu_tkPt b t M) i = t i := by simp [bu_tkPt, hM']
    rw [e]
    have ht : t i ≠ b i := by
      have hmem := hM hM'
      rw [bu_tkMv, Finset.mem_filter] at hmem
      exact hmem.2
    simp [hM', ht]
  · have e : (bu_tkPt b t M) i = b i := by simp [bu_tkPt, hM']
    rw [e]
    simp [hM']

/-- The top moved set is contained in the support of the top. -/
private theorem bu_tkMv_sub_support {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
    (i : Fin n) (hi : t i ≠ b i) : t i ≠ 0 := by
  have h5 := hbt i
  rcases h5 with c5 | ⟨s5, e5⟩ | ⟨s5, e5⟩
  · exact absurd c5 hi
  · omega
  · omega

/-- Moved coordinates strictly grow in absolute value. -/
private theorem bu_tkMv_abs_lt {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
    (i : Fin n) (hi : t i ≠ b i) : |b i| < |t i| := by
  have h5 := hbt i
  rcases h5 with c5 | ⟨s5, e5⟩ | ⟨s5, e5⟩
  · exact absurd c5 hi
  · rw [e5, abs_of_nonneg s5, abs_of_nonneg (by omega : (0 : ℤ) ≤ b i + 1)]
    omega
  · rw [e5, abs_of_nonpos s5, abs_of_nonpos (by omega : b i - 1 ≤ (0 : ℤ))]
    omega

/-- Off the moved set, the top agrees with the bottom. -/
private theorem bu_tkMv_eq_off {n : ℕ} {b t : Fin n → ℤ}
    (i : Fin n) (hi : i ∉ bu_tkMv b t) : t i = b i := by
  by_contra h
  have hm := hi
  rw [bu_tkMv, Finset.mem_filter] at hm
  exact hm ⟨Finset.mem_univ i, h⟩

/-- The support of the bottom is contained in the support of the top. -/
private theorem bu_tkMv_support_mono {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
    (i : Fin n) (hi : b i ≠ 0) : t i ≠ 0 := by
  have h5 := hbt i
  rcases h5 with c5 | ⟨s5, e5⟩ | ⟨s5, e5⟩
  · rw [c5]
    exact hi
  · omega
  · omega

/-! ## Chain cardinality bound -/

/-- The moved sets of a chain form a chain of subsets with the extremal
properties needed for the counting argument. -/
private theorem bu_chain_card_bound {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) :
    ∃ b ∈ σ, ∃ t ∈ σ, (∀ z ∈ σ, bu_tkLe b z) ∧ (∀ z ∈ σ, bu_tkLe z t) ∧
      bu_tkS σ = bu_tkSgn t ∧
      (σ.image (bu_tkMv b)).card = σ.card ∧
      (∀ A ∈ σ.image (bu_tkMv b), A ⊆ bu_tkMv b t) ∧
      σ.card ≤ (bu_tkMv b t).card + 1 ∧
      (bu_tkMv b t).card ≤ (bu_tkS σ).card ∧
      (σ.card = (bu_tkS σ).card + 1 →
        bu_tkMv b t = Finset.univ.filter (fun i => t i ≠ 0) ∧
        (σ.image (bu_tkMv b)).card = (bu_tkMv b t).card + 1) ∧
      (σ.card = (bu_tkS σ).card →
        (bu_tkMv b t = Finset.univ.filter (fun i => t i ≠ 0) ∧
          (σ.image (bu_tkMv b)).card = (bu_tkMv b t).card) ∨
        (∃ c, Finset.univ.filter (fun i => t i ≠ 0) = insert c (bu_tkMv b t) ∧
          c ∉ bu_tkMv b t ∧
          (σ.image (bu_tkMv b)).card = (bu_tkMv b t).card + 1)) := by
  obtain ⟨b, hbσ, t, htσ, hbot, htop, hSeq⟩ := bu_chain_bot_top hσ
  have hbt : bu_tkLe b t := htop b hbσ
  have hinj : Set.InjOn (bu_tkMv b) (↑σ : Set (Fin n → ℤ)) := by
    intro z hz w hw he
    have hz' : z ∈ σ := Finset.mem_coe.mp hz
    have hw' : w ∈ σ := Finset.mem_coe.mp hw
    have ez : z = bu_tkPt b t (bu_tkMv b z) :=
      (bu_tkMv_normal_a hbt (hbot z hz') (htop z hz')).2
    have ew : w = bu_tkPt b t (bu_tkMv b w) :=
      (bu_tkMv_normal_a hbt (hbot w hw') (htop w hw')).2
    rw [ez, he]
    exact ew.symm
  have hC : (σ.image (bu_tkMv b)).card = σ.card :=
    Finset.card_image_of_injOn hinj
  have hmemC : ∀ A ∈ σ.image (bu_tkMv b), ∀ B ∈ σ.image (bu_tkMv b),
      A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB
    rw [Finset.mem_image] at hA hB
    obtain ⟨z, hz, rfl⟩ := hA
    obtain ⟨w, hw, rfl⟩ := hB
    rcases hσ.2 z hz w hw with h | h
    · exact Or.inl ((bu_tkMv_le_iff hbt (hbot z hz) (htop z hz)
        (hbot w hw) (htop w hw)).mp h)
    · exact Or.inr ((bu_tkMv_le_iff hbt (hbot w hw) (htop w hw)
        (hbot z hz) (htop z hz)).mp h)
  have hsubX : ∀ A ∈ σ.image (bu_tkMv b), A ⊆ bu_tkMv b t := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨z, hz, rfl⟩ := hA
    exact bu_tkMv_mono_of_le (hbot z hz) hbt (htop z hz)
  have hcard_inj : Set.InjOn Finset.card
      (↑(σ.image (bu_tkMv b)) : Set (Finset (Fin n))) := by
    intro A hA B hB he
    have hA' : A ∈ σ.image (bu_tkMv b) := Finset.mem_coe.mp hA
    have hB' : B ∈ σ.image (bu_tkMv b) := Finset.mem_coe.mp hB
    rcases hmemC A hA' B hB' with h | h
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq he.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq he)).symm
  have hcle : (σ.image (bu_tkMv b)).card ≤ (bu_tkMv b t).card + 1 := by
    have himg : (σ.image (bu_tkMv b)).image Finset.card ⊆
        Finset.range ((bu_tkMv b t).card + 1) := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨A, hA, rfl⟩ := hk
      rw [Finset.mem_range]
      have hAle : A.card ≤ (bu_tkMv b t).card :=
        Finset.card_le_card (hsubX A hA)
      omega
    calc (σ.image (bu_tkMv b)).card = ((σ.image (bu_tkMv b)).image Finset.card).card :=
          (Finset.card_image_of_injOn hcard_inj).symm
      _ ≤ (Finset.range ((bu_tkMv b t).card + 1)).card :=
          Finset.card_le_card himg
      _ = (bu_tkMv b t).card + 1 := Finset.card_range _
  have hXT : bu_tkMv b t ⊆ Finset.univ.filter (fun i => t i ≠ 0) := by
    intro i hi
    rw [bu_tkMv, Finset.mem_filter] at hi
    obtain ⟨_, hne⟩ := hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, bu_tkMv_sub_support hbt i hne⟩
  have hST : (bu_tkS σ).card = (Finset.univ.filter fun i => t i ≠ 0).card := by
    rw [hSeq, bu_tkSgn_card]
  have h1 : σ.card ≤ (bu_tkMv b t).card + 1 := by omega
  have h2 : (bu_tkMv b t).card ≤ (bu_tkS σ).card := by
    calc (bu_tkMv b t).card ≤ (Finset.univ.filter fun i => t i ≠ 0).card :=
          Finset.card_le_card hXT
      _ = (bu_tkS σ).card := hST.symm
  refine ⟨b, hbσ, t, htσ, hbot, htop, hSeq, hC, hsubX, h1, h2, ?_, ?_⟩
  · intro hc
    have hXeq : (bu_tkMv b t).card = (bu_tkS σ).card := by omega
    have hXeqT : bu_tkMv b t = Finset.univ.filter (fun i => t i ≠ 0) :=
      Finset.eq_of_subset_of_card_le hXT (by omega)
    refine ⟨hXeqT, by omega⟩
  · intro hc
    by_cases hXTcard : (bu_tkMv b t).card = (bu_tkS σ).card
    · left
      refine ⟨Finset.eq_of_subset_of_card_le hXT (by omega), by omega⟩
    · right
      have hlt : (bu_tkMv b t).card + 1 = (bu_tkS σ).card := by omega
      have hsd : (Finset.univ.filter (fun i => t i ≠ 0) \ bu_tkMv b t).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff_of_subset hXT]
        omega
      obtain ⟨c, hc⟩ := hsd
      obtain ⟨hcT, hcX⟩ := Finset.mem_sdiff.mp hc
      refine ⟨c, ?_, hcX, by omega⟩
      have hsub : insert c (bu_tkMv b t) ⊆
          Finset.univ.filter (fun i => t i ≠ 0) :=
        Finset.insert_subset hcT hXT
      have hcard : (Finset.univ.filter fun i => t i ≠ 0).card ≤
          (insert c (bu_tkMv b t)).card := by
        rw [Finset.card_insert_of_notMem hcX]
        omega
      exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-! ## Gap lemma (pure finset combinatorics) -/

/-- Comparable extensions of a chain of subsets: members of the powerset
missing from `C` but comparable with all of `C`. -/
private def bu_tkExt {α : Type*} [DecidableEq α] (C : Finset (Finset α))
    (X : Finset α) : Finset (Finset α) :=
  X.powerset.filter fun M => M ∉ C ∧ ∀ A ∈ C, A ⊆ M ∨ M ⊆ A

/-- Membership in the extension set (stable interface for concrete `C`, `X`). -/
private theorem bu_mem_tkExt {α : Type*} [DecidableEq α] {C : Finset (Finset α)}
    {X : Finset α} {M : Finset α} :
    M ∈ bu_tkExt C X ↔ M ∈ X.powerset ∧ M ∉ C ∧ ∀ A ∈ C, A ⊆ M ∨ M ⊆ A := by
  rw [bu_tkExt, Finset.mem_filter]

private theorem bu_gap_lemma {α : Type*} [DecidableEq α] {X : Finset α}
    {C : Finset (Finset α)} (hsubX : ∀ A ∈ C, A ⊆ X) (hempty : ∅ ∈ C)
    (hX : X ∈ C) (hcomp : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) :
    C.card ≤ X.card + 1 ∧
    (C.card = X.card + 1 → bu_tkExt C X = ∅) ∧
    (C.card = X.card → (bu_tkExt C X).card = 2) := by
  have hinj : Set.InjOn Finset.card (↑C : Set (Finset α)) := by
    intro A hA B hB he
    have hA' : A ∈ C := Finset.mem_coe.mp hA
    have hB' : B ∈ C := Finset.mem_coe.mp hB
    rcases hcomp A hA' B hB' with h | h
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq he.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq he)).symm
  have himg : C.image Finset.card ⊆ Finset.range (X.card + 1) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨A, hA, rfl⟩ := hk
    rw [Finset.mem_range]
    have hAle : A.card ≤ X.card := Finset.card_le_card (hsubX A hA)
    omega
  have hcardle : C.card ≤ X.card + 1 := by
    calc C.card = (C.image Finset.card).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (X.card + 1)).card := Finset.card_le_card himg
      _ = X.card + 1 := Finset.card_range _
  have hle_sub : ∀ A ∈ C, ∀ D ∈ C, A.card ≤ D.card → A ⊆ D := by
    intro A hA D hD hle
    rcases hcomp A hA D hD with h | h
    · exact h
    · have e : D = A := Finset.eq_of_subset_of_card_le h hle
      rw [e]
  refine ⟨hcardle, ?_, ?_⟩
  · intro hc
    rw [Finset.eq_empty_iff_forall_notMem]
    intro M hM
    rw [bu_tkExt, Finset.mem_filter] at hM
    obtain ⟨hMX, hMnot, hMcomp⟩ := hM
    have hMcard : M.card ≤ X.card :=
      Finset.card_le_card (Finset.mem_powerset.mp hMX)
    have himgeq : C.image Finset.card = Finset.range (X.card + 1) := by
      apply Finset.eq_of_subset_of_card_le himg
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      omega
    have hmem : M.card ∈ C.image Finset.card := by
      rw [himgeq, Finset.mem_range]
      omega
    obtain ⟨D, hD, hDcard⟩ := Finset.mem_image.mp hmem
    have e : D = M := by
      rcases hMcomp D hD with h | h
      · exact Finset.eq_of_subset_of_card_le h (by omega)
      · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm
    have hMC : M ∈ C := by
      rw [← e]
      exact hD
    exact hMnot hMC
  · intro hc
    have himgcard : (C.image Finset.card).card = X.card := by
      rw [Finset.card_image_of_injOn hinj, hc]
    have hsd1 : (Finset.range (X.card + 1) \ C.image Finset.card).card = 1 := by
      rw [Finset.card_sdiff_of_subset himg, Finset.card_range, himgcard]
      omega
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hsd1
    have hknot : k ∉ C.image Finset.card := by
      have hkmem : k ∈ Finset.range (X.card + 1) \ C.image Finset.card := by
        rw [hk]
        exact Finset.mem_singleton_self k
      exact (Finset.mem_sdiff.mp hkmem).2
    have hkrange : k ∈ Finset.range (X.card + 1) := by
      have hkmem : k ∈ Finset.range (X.card + 1) \ C.image Finset.card := by
        rw [hk]
        exact Finset.mem_singleton_self k
      exact (Finset.mem_sdiff.mp hkmem).1
    have h0mem : (0 : ℕ) ∈ C.image Finset.card :=
      Finset.mem_image.mpr ⟨∅, hempty, Finset.card_empty⟩
    have hXmem : X.card ∈ C.image Finset.card :=
      Finset.mem_image.mpr ⟨X, hX, rfl⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hknot h0mem
    have hkX : k < X.card := by
      rw [Finset.mem_range] at hkrange
      by_contra hcon
      have hkk : k = X.card := by omega
      rw [hkk] at hknot
      exact hknot hXmem
    have hkpos : 0 < k := by omega
    have hslot : ∀ j, j ∈ Finset.range (X.card + 1) → j ≠ k → ∃ D ∈ C, D.card = j := by
      intro j hj hjk
      have hj' : j ∈ C.image Finset.card := by
        by_contra hcon
        have hjsd : j ∈ Finset.range (X.card + 1) \ C.image Finset.card :=
          Finset.mem_sdiff.mpr ⟨hj, hcon⟩
        rw [hk] at hjsd
        exact hjk (Finset.mem_singleton.mp hjsd)
      exact Finset.mem_image.mp hj'
    obtain ⟨A, hA, hAcard⟩ := hslot (k - 1) (by
      rw [Finset.mem_range]; omega) (by omega)
    obtain ⟨B, hB, hBcard⟩ := hslot (k + 1) (by
      rw [Finset.mem_range]; omega) (by omega)
    have hAB : A ⊆ B := hle_sub A hA B hB (by omega)
    have hBAcard : (B \ A).card = 2 := by
      rw [Finset.card_sdiff_of_subset hAB, hBcard, hAcard]
      omega
    obtain ⟨a, a', haa', haa'B⟩ := Finset.card_eq_two.mp hBAcard
    have haBA : a ∈ B \ A := by
      rw [haa'B]
      exact Finset.mem_insert_self a {a'}
    have haB : a ∈ B := (Finset.mem_sdiff.mp haBA).1
    have haA : a ∉ A := (Finset.mem_sdiff.mp haBA).2
    have haBA' : a' ∈ B \ A := by
      rw [haa'B]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self a')
    have haB' : a' ∈ B := (Finset.mem_sdiff.mp haBA').1
    have haA' : a' ∉ A := (Finset.mem_sdiff.mp haBA').2
    have hBX : B ⊆ X := hsubX B hB
    have haX : a ∈ X := hBX haB
    have haX' : a' ∈ X := hBX haB'
    have hAX : A ⊆ X := Finset.Subset.trans (hle_sub A hA B hB (by omega)) hBX
    have hcardA : (insert a A).card = k := by
      rw [Finset.card_insert_of_notMem haA, hAcard]
      omega
    have hcardA' : (insert a' A).card = k := by
      rw [Finset.card_insert_of_notMem haA', hAcard]
      omega
    have hnotC : insert a A ∉ C := by
      intro hcon
      exact hknot (Finset.mem_image.mpr ⟨insert a A, hcon, hcardA⟩)
    have hnotC' : insert a' A ∉ C := by
      intro hcon
      exact hknot (Finset.mem_image.mpr ⟨insert a' A, hcon, hcardA'⟩)
    have hcompA : ∀ D ∈ C, D ⊆ insert a A ∨ insert a A ⊆ D := by
      intro D hD
      have hDcardle : D.card ≤ X.card := Finset.card_le_card (hsubX D hD)
      by_cases hDk : D.card = k
      · exfalso
        have hmemD : D.card ∈ C.image Finset.card :=
          Finset.mem_image.mpr ⟨D, hD, rfl⟩
        rw [hDk] at hmemD
        exact hknot hmemD
      · by_cases hle : D.card ≤ k - 1
        · left
          have hDA : D ⊆ A := hle_sub D hD A hA (by omega)
          exact Finset.Subset.trans hDA (Finset.subset_insert a A)
        · right
          have hge : k + 1 ≤ D.card := by omega
          have hBD : B ⊆ D := hle_sub B hB D hD (by omega)
          have hAD : A ⊆ D := Finset.Subset.trans
            (hle_sub A hA B hB (by omega)) hBD
          exact Finset.insert_subset (hBD haB) hAD
    have hcompA' : ∀ D ∈ C, D ⊆ insert a' A ∨ insert a' A ⊆ D := by
      intro D hD
      have hDcardle : D.card ≤ X.card := Finset.card_le_card (hsubX D hD)
      by_cases hDk : D.card = k
      · exfalso
        have hmemD : D.card ∈ C.image Finset.card :=
          Finset.mem_image.mpr ⟨D, hD, rfl⟩
        rw [hDk] at hmemD
        exact hknot hmemD
      · by_cases hle : D.card ≤ k - 1
        · left
          have hDA : D ⊆ A := hle_sub D hD A hA (by omega)
          exact Finset.Subset.trans hDA (Finset.subset_insert a' A)
        · right
          have hge : k + 1 ≤ D.card := by omega
          have hBD : B ⊆ D := hle_sub B hB D hD (by omega)
          have hAD : A ⊆ D := Finset.Subset.trans
            (hle_sub A hA B hB (by omega)) hBD
          exact Finset.insert_subset (hBD haB') hAD
    have hinsAX : insert a A ∈ bu_tkExt C X := by
      rw [bu_tkExt, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset haX hAX, hnotC, hcompA⟩
    have hinsa'X : insert a' A ∈ bu_tkExt C X := by
      rw [bu_tkExt, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset haX' hAX, hnotC', hcompA'⟩
    have hne : insert a A ≠ insert a' A := by
      intro hcon
      have hmem : a ∈ insert a' A := by
        rw [← hcon]
        exact Finset.mem_insert_self a A
      rw [Finset.mem_insert] at hmem
      rcases hmem with h | h
      · exact haa' h
      · exact haA h
    have hExt : bu_tkExt C X = {insert a A, insert a' A} := by
      ext M
      constructor
      · intro hM
        rw [bu_tkExt, Finset.mem_filter] at hM
        obtain ⟨hMX, hMnot, hMcomp⟩ := hM
        have hMcardle : M.card ≤ X.card :=
          Finset.card_le_card (Finset.mem_powerset.mp hMX)
        have hMkrange : M.card ∈ Finset.range (X.card + 1) := by
          rw [Finset.mem_range]
          omega
        have hMcard : M.card = k := by
          by_contra hcon
          obtain ⟨D, hD, hDcard⟩ := hslot M.card hMkrange hcon
          have e : D = M := by
            rcases hMcomp D hD with h | h
            · exact Finset.eq_of_subset_of_card_le h (by omega)
            · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm
          have hMC : M ∈ C := by
            rw [← e]
            exact hD
          exact hMnot hMC
        have hAM : A ⊆ M := by
          rcases hMcomp A hA with h | h
          · exact h
          · exfalso
            have hle := Finset.card_le_card h
            omega
        have hMB : M ⊆ B := by
          rcases hMcomp B hB with h | h
          · exfalso
            have hle := Finset.card_le_card h
            omega
          · exact h
        have hMAd : (M \ A).card = 1 := by
          rw [Finset.card_sdiff_of_subset hAM, hMcard, hAcard]
          omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hMAd
        have hxmem : x ∈ M \ A := by
          rw [hx]
          exact Finset.mem_singleton_self x
        have hxM : x ∈ M := (Finset.mem_sdiff.mp hxmem).1
        have hxA : x ∉ A := (Finset.mem_sdiff.mp hxmem).2
        have hxB : x ∈ B \ A :=
          Finset.mem_sdiff.mpr ⟨hMB hxM, hxA⟩
        rw [haa'B, Finset.mem_insert, Finset.mem_singleton] at hxB
        have hMxA : M = insert x A := by
          have hcc : (insert x A).card = M.card := by
            rw [Finset.card_insert_of_notMem hxA, hAcard, hMcard]
            omega
          have hsub : insert x A ⊆ M := Finset.insert_subset hxM hAM
          have hle : M.card ≤ (insert x A).card := le_of_eq hcc.symm
          exact (Finset.eq_of_subset_of_card_le hsub hle).symm
        rw [hMxA]
        rcases hxB with hxa | hxa
        · rw [hxa]
          exact Finset.mem_insert_self _ _
        · rw [hxa]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · intro hM
        rw [Finset.mem_insert, Finset.mem_singleton] at hM
        rcases hM with rfl | rfl
        · exact hinsAX
        · exact hinsa'X
    rw [hExt, Finset.card_pair_eq_two_iff.mpr hne]

/-! ## Cofacet classification -/

/-- Decidability of the chain predicate (for the counter filters). -/
private noncomputable instance bu_tkChain_dec {n : ℕ} (σ : Finset (Fin n → ℤ)) :
    Decidable (bu_tkChain σ) :=
  Classical.dec _

/-- Upward extensions with the same sign set (tight-chain counters). -/
private noncomputable def bu_tkUp {n : ℕ} (m : ℕ)
    (σ : Finset (Fin n → ℤ)) : Finset (Fin n → ℤ) :=
  (bu_tkBox n m).filter fun v => v ∉ σ ∧ bu_tkChain (insert v σ) ∧
    bu_tkS (insert v σ) ⊆ bu_tkS σ

private theorem bu_mem_tkUp {n m : ℕ} {σ : Finset (Fin n → ℤ)} {v : Fin n → ℤ} :
    v ∈ bu_tkUp m σ ↔ v ∈ bu_tkBox n m ∧ v ∉ σ ∧ bu_tkChain (insert v σ) ∧
      bu_tkS (insert v σ) ⊆ bu_tkS σ := by
  rw [bu_tkUp, Finset.mem_filter]

/-- Upward extensions gaining exactly the new sign `ℓ` (loose-chain counters). -/
private noncomputable def bu_tkUpL {n : ℕ} (m : ℕ) (σ : Finset (Fin n → ℤ))
    (ℓ : Bool × Fin n) : Finset (Fin n → ℤ) :=
  (bu_tkBox n m).filter fun v => v ∉ σ ∧ bu_tkChain (insert v σ) ∧
    bu_tkS (insert v σ) = insert ℓ (bu_tkS σ)

private theorem bu_mem_tkUpL {n m : ℕ} {σ : Finset (Fin n → ℤ)}
    {v : Fin n → ℤ} {ℓ : Bool × Fin n} :
    v ∈ bu_tkUpL m σ ℓ ↔ v ∈ bu_tkBox n m ∧ v ∉ σ ∧ bu_tkChain (insert v σ) ∧
      bu_tkS (insert v σ) = insert ℓ (bu_tkS σ) := by
  rw [bu_tkUpL, Finset.mem_filter]

/-- Trichotomy of cofacet positions relative to bottom and top. -/
private theorem bu_cofacet_pos {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t v : Fin n → ℤ}
    (hbσ : b ∈ σ) (htσ : t ∈ σ)
    (hchain : bu_tkChain (insert v σ)) (hv : v ∉ σ) :
    (bu_tkLe b v ∧ bu_tkLe v t) ∨ (bu_tkLe v b ∧ v ≠ b) ∨ (bu_tkLe t v ∧ v ≠ t) := by
  have hbv : bu_tkLe b v ∨ bu_tkLe v b := by
    have h := hchain.2 v (Finset.mem_insert_self v σ) b
      (Finset.mem_insert_of_mem hbσ)
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases hbv with hle | hle
  · have hvt : bu_tkLe v t ∨ bu_tkLe t v := by
      have h := hchain.2 v (Finset.mem_insert_self v σ) t
        (Finset.mem_insert_of_mem htσ)
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hvt with h | h
    · exact Or.inl ⟨hle, h⟩
    · have hne : v ≠ t := by
        rintro rfl
        exact hv htσ
      exact Or.inr (Or.inr ⟨h, hne⟩)
  · have hne : v ≠ b := by
      rintro rfl
      exact hv hbσ
    exact Or.inr (Or.inl ⟨hle, hne⟩)

/-- The sign set of a chain is the sign set of any top element. -/
private theorem bu_tkS_of_top {n : ℕ} {τ : Finset (Fin n → ℤ)} {t : Fin n → ℤ}
    (hτ : bu_tkChain τ) (ht : t ∈ τ) (hall : ∀ z ∈ τ, bu_tkLe z t) :
    bu_tkS τ = bu_tkSgn t := by
  obtain ⟨_, _, t', ht', _, htop', hSeq'⟩ := bu_chain_bot_top hτ
  have h1 : bu_tkSgn t' ⊆ bu_tkSgn t := bu_tkSgn_mono (hall t' ht')
  have h2 : bu_tkSgn t ⊆ bu_tkSgn t' := bu_tkSgn_mono (htop' t ht)
  rw [hSeq', le_antisymm h1 h2]

/-- Pull `c`: the bottom with coordinate `c` moved one step toward `0`. -/
private def bu_tkPull {n : ℕ} (b : Fin n → ℤ) (c : Fin n) : Fin n → ℤ :=
  fun i => if i = c then (if 0 < b c then b c - 1 else b c + 1) else b i

private theorem bu_tkPull_le {n : ℕ} {b : Fin n → ℤ} {c : Fin n} (hne : b c ≠ 0) :
    bu_tkLe (bu_tkPull b c) b ∧ bu_tkPull b c ≠ b := by
  have hle : bu_tkLe (bu_tkPull b c) b := by
    intro i
    by_cases hic : i = c
    · rw [hic]
      by_cases hpos : 0 < b c
      · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
        rw [e]
        exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
        rw [e]
        exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · have e : (bu_tkPull b c) i = b i := by simp [bu_tkPull, hic]
      rw [e]
      exact Or.inl rfl
  refine ⟨hle, ?_⟩
  intro hcon
  have hc := congrArg (fun z => z c) hcon
  by_cases hpos : 0 < b c
  · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
    omega
  · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
    omega

private theorem bu_tkPull_abs {n : ℕ} {b : Fin n → ℤ} {c : Fin n} (hne : b c ≠ 0) :
    |bu_tkPull b c c| ≤ |b c| := by
  by_cases hpos : 0 < b c
  · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
    rw [e, abs_of_nonneg (by omega : (0 : ℤ) ≤ b c - 1),
      abs_of_nonneg (by omega : (0 : ℤ) ≤ b c)]
    omega
  · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
    have h1 : b c + 1 ≤ (0 : ℤ) := by omega
    have h2 : b c ≤ (0 : ℤ) := by omega
    rw [e, abs_of_nonpos h1, abs_of_nonpos h2]
    omega

private theorem bu_tkPull_mem_box {n m : ℕ} {b : Fin n → ℤ} {c : Fin n}
    (hb : b ∈ bu_tkBox n m) (hne : b c ≠ 0) : bu_tkPull b c ∈ bu_tkBox n m := by
  rw [bu_mem_tkBox] at hb ⊢
  intro i
  by_cases hic : i = c
  · rw [hic]
    exact le_trans (bu_tkPull_abs hne) (hb c)
  · have e : (bu_tkPull b c) i = b i := by simp [bu_tkPull, hic]
    rw [e]
    exact hb i

/-- Push `j` up by one. -/
private def bu_tkPush {n : ℕ} (t : Fin n → ℤ) (j : Fin n) (s : ℤ) : Fin n → ℤ :=
  fun i => if i = j then t j + s else t i

private theorem bu_tkPush_up {n : ℕ} {t : Fin n → ℤ} {j : Fin n} (h0 : 0 ≤ t j) :
    bu_tkLe t (bu_tkPush t j 1) ∧ bu_tkPush t j 1 ≠ t := by
  have hle : bu_tkLe t (bu_tkPush t j 1) := by
    intro i
    by_cases hij : i = j
    · rw [hij]
      have e : (bu_tkPush t j 1) j = t j + 1 := by simp [bu_tkPush]
      rw [e]
      exact Or.inr (Or.inl ⟨h0, rfl⟩)
    · have e : (bu_tkPush t j 1) i = t i := by simp [bu_tkPush, hij]
      rw [e]
      exact Or.inl rfl
  refine ⟨hle, ?_⟩
  intro hcon
  have hc := congrArg (fun z => z j) hcon
  have e : (bu_tkPush t j 1) j = t j + 1 := by simp [bu_tkPush]
  rw [e] at hc
  omega

private theorem bu_tkPush_down {n : ℕ} {t : Fin n → ℤ} {j : Fin n} (h0 : t j ≤ 0) :
    bu_tkLe t (bu_tkPush t j (-1)) ∧ bu_tkPush t j (-1) ≠ t := by
  have hle : bu_tkLe t (bu_tkPush t j (-1)) := by
    intro i
    by_cases hij : i = j
    · rw [hij]
      have e : (bu_tkPush t j (-1)) j = t j + -1 := by simp [bu_tkPush]
      rw [e]
      exact Or.inr (Or.inr ⟨h0, by omega⟩)
    · have e : (bu_tkPush t j (-1)) i = t i := by simp [bu_tkPush, hij]
      rw [e]
      exact Or.inl rfl
  refine ⟨hle, ?_⟩
  intro hcon
  have hc := congrArg (fun z => z j) hcon
  have e : (bu_tkPush t j (-1)) j = t j + -1 := by simp [bu_tkPush]
  rw [e] at hc
  omega

/-- Inside cofacets preserve the sign set. -/
private theorem bu_inside_sign {n : ℕ} {σ : Finset (Fin n → ℤ)} {t v : Fin n → ℤ}
    (htσ : t ∈ σ) (hSeq : bu_tkS σ = bu_tkSgn t)
    (hchain : bu_tkChain (insert v σ)) (htop : ∀ z ∈ σ, bu_tkLe z t)
    (hvt : bu_tkLe v t) :
    bu_tkS (insert v σ) = bu_tkS σ := by
  have hall : ∀ z ∈ insert v σ, bu_tkLe z t := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with hzv | hz
    · rw [hzv]
      exact hvt
    · exact htop z hz
  have h := bu_tkS_of_top hchain (Finset.mem_insert_of_mem htσ) hall
  rw [h, hSeq]

/-- Inside cofacets land in the extension set. -/
private theorem bu_inside_mem_ext {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t v : Fin n → ℤ}
    (hbt : bu_tkLe b t) (hbot : ∀ z ∈ σ, bu_tkLe b z) (htop : ∀ z ∈ σ, bu_tkLe z t)
    (hchain : bu_tkChain (insert v σ))
    (hbv : bu_tkLe b v) (hvt : bu_tkLe v t) (hv : v ∉ σ) :
    bu_tkMv b v ∈ bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t) := by
  rw [bu_mem_tkExt]
  refine ⟨Finset.mem_powerset.mpr (bu_tkMv_mono_of_le hbv hbt hvt), ?_, ?_⟩
  · intro hcon
    rw [Finset.mem_image] at hcon
    obtain ⟨z, hz, hze⟩ := hcon
    have ev : v = bu_tkPt b t (bu_tkMv b v) := (bu_tkMv_normal_a hbt hbv hvt).2
    have ez : z = bu_tkPt b t (bu_tkMv b z) :=
      (bu_tkMv_normal_a hbt (hbot z hz) (htop z hz)).2
    have heq : v = z := by rw [ev, ez, hze]
    subst heq
    exact hv hz
  · intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨z, hz, rfl⟩ := hA
    have hcomp : bu_tkLe v z ∨ bu_tkLe z v := hchain.2 v
      (Finset.mem_insert_self v σ) z (Finset.mem_insert_of_mem hz)
    rcases hcomp with h | h
    · exact Or.inr ((bu_tkMv_le_iff hbt hbv hvt (hbot z hz) (htop z hz)).mp h)
    · exact Or.inl ((bu_tkMv_le_iff hbt (hbot z hz) (htop z hz) hbv hvt).mp h)

/-- Every comparable extension comes from an inside point. -/
private theorem bu_ext_inside {n m : ℕ} {σ : Finset (Fin n → ℤ)} {b t : Fin n → ℤ}
    (hchainσ : bu_tkChain σ) (hbot : ∀ z ∈ σ, bu_tkLe b z)
    (htop : ∀ z ∈ σ, bu_tkLe z t) (hbt : bu_tkLe b t)
    (hSeq : bu_tkS σ = bu_tkSgn t) (hsub : σ ⊆ bu_tkBox n m)
    (hbσ : b ∈ σ) (htσ : t ∈ σ)
    {M : Finset (Fin n)}
    (hM : M ∈ bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t)) :
    bu_tkPt b t M ∈ bu_tkBox n m ∧ bu_tkPt b t M ∉ σ ∧
      bu_tkChain (insert (bu_tkPt b t M) σ) ∧
      bu_tkS (insert (bu_tkPt b t M) σ) = bu_tkS σ := by
  rw [bu_mem_tkExt] at hM
  obtain ⟨hMX, hMnot, hMcomp⟩ := hM
  have hMXs : M ⊆ bu_tkMv b t := Finset.mem_powerset.mp hMX
  have hPtm := bu_tkPt_mem_of_mem hbt hMXs
  have hPt1 : bu_tkLe b (bu_tkPt b t M) := hPtm.1
  have hPt2 : bu_tkLe (bu_tkPt b t M) t := hPtm.2.1
  have hPtMv : bu_tkMv b (bu_tkPt b t M) = M := hPtm.2.2
  have hPtbox : bu_tkPt b t M ∈ bu_tkBox n m := by
    have hbbox : b ∈ bu_tkBox n m := hsub hbσ
    have htbox : t ∈ bu_tkBox n m := hsub htσ
    rw [bu_mem_tkBox] at hbbox htbox ⊢
    intro i
    by_cases hMi : i ∈ M
    · have e : (bu_tkPt b t M) i = t i := by simp [bu_tkPt, hMi]
      rw [e]
      exact htbox i
    · have e : (bu_tkPt b t M) i = b i := by simp [bu_tkPt, hMi]
      rw [e]
      exact hbbox i
  have hPtnot : bu_tkPt b t M ∉ σ := by
    intro hcon
    have hmem : bu_tkMv b (bu_tkPt b t M) ∈ σ.image (bu_tkMv b) :=
      Finset.mem_image.mpr ⟨bu_tkPt b t M, hcon, rfl⟩
    rw [hPtMv] at hmem
    exact hMnot hmem
  have hcompPt : ∀ y ∈ σ, bu_tkLe (bu_tkPt b t M) y ∨ bu_tkLe y (bu_tkPt b t M) := by
    intro y hy
    have hMy : bu_tkMv b y ∈ σ.image (bu_tkMv b) :=
      Finset.mem_image.mpr ⟨y, hy, rfl⟩
    rcases hMcomp _ hMy with h | h
    · rw [← hPtMv] at h
      exact Or.inr ((bu_tkMv_le_iff hbt (hbot y hy) (htop y hy) hPt1 hPt2).mpr h)
    · rw [← hPtMv] at h
      exact Or.inl ((bu_tkMv_le_iff hbt hPt1 hPt2 (hbot y hy) (htop y hy)).mpr h)
  have hPtchain : bu_tkChain (insert (bu_tkPt b t M) σ) := by
    refine ⟨⟨b, Finset.mem_insert_of_mem hbσ⟩, ?_⟩
    intro x hx y hy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact Or.inl (bu_tkLe_refl _)
    · exact hcompPt y hy
    · have hsym := hcompPt x hx
      rcases hsym with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exact hchainσ.2 x hx y hy
  have hS : bu_tkS (insert (bu_tkPt b t M) σ) = bu_tkS σ := by
    have hall : ∀ z ∈ insert (bu_tkPt b t M) σ, bu_tkLe z t := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with hzv | hz
      · rw [hzv]
        exact hPt2
      · exact htop z hz
    have h := bu_tkS_of_top hPtchain (Finset.mem_insert_of_mem htσ) hall
    rw [h, hSeq]
  exact ⟨hPtbox, hPtnot, hPtchain, hS⟩

/-- Below cofacets sit over the boundary difference. -/
private theorem bu_below_mem {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t v : Fin n → ℤ}
    (hbt : bu_tkLe b t) (htσ : t ∈ σ)
    (hchain : bu_tkChain (insert v σ)) (hvb : bu_tkLe v b) (hne : v ≠ b) :
    (bu_tkMv v b).Nonempty ∧
      bu_tkMv v b ⊆ (Finset.univ.filter fun i => t i ≠ 0) \ bu_tkMv b t := by
  have hvt : bu_tkLe v t := by
    have hcomp : bu_tkLe v t ∨ bu_tkLe t v :=
      hchain.2 v (Finset.mem_insert_self v σ) t (Finset.mem_insert_of_mem htσ)
    exact bu_tkLe_trans_of_comparable hvb hbt hcomp
  have hnorm := bu_tkMv_normal_a hvt hvb hbt
  have hne_mem : (bu_tkMv v b).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Ne.symm hi⟩⟩
  refine ⟨hne_mem, ?_⟩
  intro i hi
  have hbi : b i ≠ v i := by
    have hm := hi
    rw [bu_tkMv, Finset.mem_filter] at hm
    exact hm.2
  have hbit : b i = t i := by
    have e : (bu_tkPt v t (bu_tkMv v b)) i = t i := by simp [bu_tkPt, hi]
    rw [hnorm.2]
    exact e
  have ht0 : t i ≠ 0 := by
    have h1 := hvb i
    rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
    · exact absurd c1 hbi
    · omega
    · omega
  refine Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, ht0⟩, ?_⟩
  intro hcon
  rw [bu_tkMv, Finset.mem_filter] at hcon
  exact hcon.2 hbit.symm

/-- A below cofacet over a singleton difference is the pull. -/
private theorem bu_below_eq_pull {n : ℕ} {b v : Fin n → ℤ} {c : Fin n}
    (hvb : bu_tkLe v b) (hD : bu_tkMv v b = {c}) : v = bu_tkPull b c := by
  funext i
  by_cases hic : i = c
  · rw [hic]
    have hvc : v c ≠ b c := by
      have hm : c ∈ bu_tkMv v b := by
        rw [hD]
        exact Finset.mem_singleton_self c
      rw [bu_tkMv, Finset.mem_filter] at hm
      exact Ne.symm hm.2
    have h1 := hvb c
    by_cases hpos : 0 < b c
    · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
      rw [e]
      rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
      · exact absurd c1.symm hvc
      · omega
      · omega
    · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
      rw [e]
      rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
      · exact absurd c1.symm hvc
      · omega
      · omega
  · have hvi : v i = b i := by
      have hni : i ∉ bu_tkMv v b := by
        rw [hD]
        simp [hic]
      exact (bu_tkMv_eq_off i hni).symm
    have hpi : bu_tkPull b c i = b i := by simp [bu_tkPull, hic]
    exact hvi.trans hpi.symm

/-- Above cofacets grow the sign set through fresh coordinates. -/
private theorem bu_above_E {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t v : Fin n → ℤ}
    (hbt : bu_tkLe b t) (htop : ∀ z ∈ σ, bu_tkLe z t)
    (hbσ : b ∈ σ) (hchain : bu_tkChain (insert v σ))
    (htv : bu_tkLe t v) (hne : v ≠ t) :
    (bu_tkMv t v).Nonempty ∧ (∀ i ∈ bu_tkMv t v, i ∉ bu_tkMv b t) ∧
      (∀ i ∉ bu_tkMv t v, v i = t i) ∧ bu_tkS (insert v σ) = bu_tkSgn v := by
  have hbv : bu_tkLe b v := by
    have hcomp : bu_tkLe b v ∨ bu_tkLe v b :=
      hchain.2 b (Finset.mem_insert_of_mem hbσ) v (Finset.mem_insert_self v σ)
    exact bu_tkLe_trans_of_comparable hbt htv hcomp
  have hnorm := bu_tkMv_normal_a hbv hbt htv
  have hXE : ∀ i ∈ bu_tkMv b t, i ∉ bu_tkMv t v := by
    intro i hiX
    have htiv : t i = v i := by
      have e : (bu_tkPt b v (bu_tkMv b t)) i = v i := by simp [bu_tkPt, hiX]
      rw [← hnorm.2] at e
      exact e
    intro hcon
    have hm := hcon
    rw [bu_tkMv, Finset.mem_filter] at hm
    exact hm.2 htiv.symm
  have hEX : ∀ i ∈ bu_tkMv t v, i ∉ bu_tkMv b t := fun i hiE hiX => hXE i hiX hiE
  have hneE : (bu_tkMv t v).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hoff : ∀ i ∉ bu_tkMv t v, v i = t i := fun i hi => bu_tkMv_eq_off i hi
  have hS : bu_tkS (insert v σ) = bu_tkSgn v := by
    have hall : ∀ z ∈ insert v σ, bu_tkLe z v := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with hzv | hz
      · rw [hzv]
        exact bu_tkLe_refl v
      · have hzt := htop z hz
        have hcomp := hchain.2 z (Finset.mem_insert_of_mem hz) v
          (Finset.mem_insert_self v σ)
        exact bu_tkLe_trans_of_comparable hzt htv hcomp
    exact bu_tkS_of_top hchain (Finset.mem_insert_self v σ) hall
  exact ⟨hneE, hEX, hoff, hS⟩

/-- An above cofacet over a singleton nonzero difference is the push. -/
private theorem bu_above_eq_push {n : ℕ} {t v : Fin n → ℤ} {c : Fin n}
    (htc : t c ≠ 0) (htv : bu_tkLe t v) (hE : bu_tkMv t v = {c}) :
    v = bu_tkPush t c (if 0 < t c then 1 else -1) := by
  funext i
  by_cases hic : i = c
  · rw [hic]
    have hvc : v c ≠ t c := by
      have hm : c ∈ bu_tkMv t v := by
        rw [hE]
        exact Finset.mem_singleton_self c
      rw [bu_tkMv, Finset.mem_filter] at hm
      exact hm.2
    have h1 := htv c
    by_cases hpos : 0 < t c
    · have es : (if 0 < t c then (1 : ℤ) else -1) = 1 := by simp [hpos]
      have ep : (bu_tkPush t c 1) c = t c + 1 := by simp [bu_tkPush]
      rw [es, ep]
      rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
      · exact absurd c1 hvc
      · exact e1
      · omega
    · have es : (if 0 < t c then (1 : ℤ) else -1) = -1 := by simp [hpos]
      have ep : (bu_tkPush t c (-1)) c = t c + -1 := by simp [bu_tkPush]
      rw [es, ep]
      rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
      · exact absurd c1 hvc
      · omega
      · omega
  · have hvi : v i = t i := by
      have hni : i ∉ bu_tkMv t v := by
        rw [hE]
        simp [hic]
      exact bu_tkMv_eq_off i hni
    have hpi : bu_tkPush t c (if 0 < t c then 1 else -1) i = t i := by
      simp [bu_tkPush, hic]
    exact hvi.trans hpi.symm

/-- The pull sits below every chain member when the difference avoids the top. -/
private theorem bu_pull_le_chain {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t : Fin n → ℤ}
    {c : Fin n} (hbt : bu_tkLe b t)
    (hzn : ∀ z ∈ σ, bu_tkMv b z ⊆ bu_tkMv b t ∧ z = bu_tkPt b t (bu_tkMv b z))
    (hcX : c ∉ bu_tkMv b t) (hne : b c ≠ 0)
    (z : Fin n → ℤ) (hz : z ∈ σ) :
    bu_tkLe (bu_tkPull b c) z := by
  intro i
  have hMz : bu_tkMv b z ⊆ bu_tkMv b t := (hzn z hz).1
  have ez : z = bu_tkPt b t (bu_tkMv b z) := (hzn z hz).2
  by_cases hic : i = c
  · rw [hic]
    have hcMz : c ∉ bu_tkMv b z := fun hcon => hcX (hMz hcon)
    have hzc : z c = b c := by
      have e2 : (bu_tkPt b t (bu_tkMv b z)) c = b c := by simp [bu_tkPt, hcMz]
      rw [ez]
      exact e2
    rw [hzc]
    by_cases hpos : 0 < b c
    · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
      rw [e]
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
      rw [e]
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  · have e : (bu_tkPull b c) i = b i := by simp [bu_tkPull, hic]
    rw [e]
    by_cases hmem : i ∈ bu_tkMv b z
    · have hzi : z i = t i := by
        have e2 : (bu_tkPt b t (bu_tkMv b z)) i = t i := by simp [bu_tkPt, hmem]
        rw [ez]
        exact e2
      rw [hzi]
      exact hbt i
    · have hzi : z i = b i := by
        have e2 : (bu_tkPt b t (bu_tkMv b z)) i = b i := by simp [bu_tkPt, hmem]
        rw [ez]
        exact e2
      rw [hzi]
      exact Or.inl rfl

/-- The push sits above every chain member when the difference avoids the top. -/
private theorem bu_push_le_chain {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t : Fin n → ℤ}
    {j : Fin n} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hsign : (s = 1 → 0 ≤ t j) ∧ (s = -1 → t j ≤ 0))
    (htop : ∀ z ∈ σ, bu_tkLe z t)
    (hzn : ∀ z ∈ σ, bu_tkMv b z ⊆ bu_tkMv b t ∧ z = bu_tkPt b t (bu_tkMv b z))
    (hjX : j ∉ bu_tkMv b t) (hjt : t j = b j)
    (z : Fin n → ℤ) (hz : z ∈ σ) :
    bu_tkLe z (bu_tkPush t j s) := by
  intro i
  have h1 := (htop z hz) i
  have hMz : bu_tkMv b z ⊆ bu_tkMv b t := (hzn z hz).1
  have ez : z = bu_tkPt b t (bu_tkMv b z) := (hzn z hz).2
  by_cases hij : i = j
  · rw [hij]
    have hjMz : j ∉ bu_tkMv b z := fun hcon => hjX (hMz hcon)
    have hzj : z j = t j := by
      have e2 : (bu_tkPt b t (bu_tkMv b z)) j = b j := by simp [bu_tkPt, hjMz]
      rw [ez, e2, hjt]
    have ep : (bu_tkPush t j s) j = t j + s := by simp [bu_tkPush]
    rw [hzj, ep]
    rcases hs with rfl | rfl
    · exact Or.inr (Or.inl ⟨hsign.1 rfl, by omega⟩)
    · exact Or.inr (Or.inr ⟨hsign.2 rfl, by omega⟩)
  · have ep : (bu_tkPush t j s) i = t i := by simp [bu_tkPush, hij]
    rw [ep]
    exact h1

/-! ## Helpers: natAbs bridge, singletons, push sign -/

/-- Moved coordinates strictly grow in `natAbs`. -/
private theorem bu_tkMv_natAbs_lt {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
    (i : Fin n) (hi : t i ≠ b i) : (b i).natAbs < (t i).natAbs := by
  have h5 := hbt i
  rcases h5 with c5 | ⟨s5, e5⟩ | ⟨s5, e5⟩
  · exact absurd c5 hi
  · omega
  · omega

/-- Box membership in `natAbs` form. -/
private theorem bu_mem_tkBox_natAbs {n m : ℕ} {z : Fin n → ℤ} :
    z ∈ bu_tkBox n m ↔ ∀ i, (z i).natAbs ≤ m := by
  rw [bu_mem_tkBox]
  constructor
  · intro h i
    have h1 := h i
    rw [Int.abs_eq_natAbs] at h1
    exact_mod_cast h1
  · intro h i
    have h1 := h i
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1

/-- A nonempty sub-singleton is the singleton. -/
private theorem bu_eq_singleton_of_sub {α : Type*} {s : Finset α} {c : α}
    (hsub : s ⊆ {c}) (hne : s.Nonempty) : s = {c} := by
  have hcard : s.card = 1 := by
    have h1 : s.card ≤ 1 := by
      calc s.card ≤ ({c} : Finset α).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton c
    have h2 : 0 < s.card := Finset.card_pos.mpr hne
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hxmem : x ∈ ({c} : Finset α) := by
    have h1 : x ∈ s := by
      rw [hx]
      exact Finset.mem_singleton_self x
    exact hsub h1
  have hxc : x = c := Finset.mem_singleton.mp hxmem
  rw [hx, hxc]

/-- The push preserves the sign set when the push matches the resident sign. -/
private theorem bu_push_sgn {n : ℕ} {t : Fin n → ℤ} {c : Fin n} {s : ℤ}
    (hs : s = 1 ∨ s = -1)
    (hsign : (s = 1 → 0 ≤ t c) ∧ (s = -1 → t c ≤ 0)) (htc : t c ≠ 0) :
    bu_tkSgn (bu_tkPush t c s) = bu_tkSgn t := by
  ext ⟨β, i⟩
  simp only [bu_mem_tkSgn]
  by_cases hic : i = c
  · rw [hic]
    have e : (bu_tkPush t c s) c = t c + s := by simp [bu_tkPush]
    rw [e]
    rcases hs with rfl | rfl
    · have h0 : 0 ≤ t c := hsign.1 rfl
      have h1 : t c + 1 ≠ 0 := by omega
      have h2 : decide (0 < t c + 1) = decide (0 < t c) := by
        by_cases hpos : 0 < t c
        · simp [hpos, show (0 : ℤ) < t c + 1 by omega]
        · have htc0 : t c = 0 := by omega
          rw [htc0] at htc
          exact absurd rfl htc
      constructor
      · rintro ⟨_, hβ⟩
        exact ⟨htc, by rw [h2] at hβ; exact hβ⟩
      · rintro ⟨_, hβ⟩
        exact ⟨h1, by rw [h2]; exact hβ⟩
    · have h0 : t c ≤ 0 := hsign.2 rfl
      have h1 : t c + -1 ≠ 0 := by omega
      have h2 : decide (0 < t c + -1) = decide (0 < t c) := by
        by_cases hpos : 0 < t c
        · exfalso
          omega
        · simp [hpos, show ¬ (0 : ℤ) < t c + -1 by omega]
      constructor
      · rintro ⟨_, hβ⟩
        exact ⟨htc, by rw [h2] at hβ; exact hβ⟩
      · rintro ⟨_, hβ⟩
        exact ⟨h1, by rw [h2]; exact hβ⟩
  · have e : (bu_tkPush t c s) i = t i := by simp [bu_tkPush, hic]
    rw [e]

/-- The pushed coordinate gains exactly one in `natAbs`. -/
private theorem bu_push_abs {n : ℕ} {t : Fin n → ℤ} {c : Fin n} {s : ℤ}
    (hs : s = 1 ∨ s = -1)
    (hsign : (s = 1 → 0 ≤ t c) ∧ (s = -1 → t c ≤ 0)) :
    (bu_tkPush t c s c).natAbs = (t c).natAbs + 1 := by
  have e : (bu_tkPush t c s) c = t c + s := by simp [bu_tkPush]
  rw [e]
  rcases hs with rfl | rfl
  · have h0 := hsign.1 rfl
    omega
  · have h0 := hsign.2 rfl
    omega

/-- The push is strictly taller than the top. -/
private theorem bu_push_height {n : ℕ} {t : Fin n → ℤ} {c : Fin n} {s : ℤ}
    (hs : s = 1 ∨ s = -1)
    (hsign : (s = 1 → 0 ≤ t c) ∧ (s = -1 → t c ≤ 0)) :
    bu_tkH t < bu_tkH (bu_tkPush t c s) := by
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hic : i = c
    · rw [hic]
      have e : (bu_tkPush t c s) c = t c + s := by simp [bu_tkPush]
      rw [e]
      rcases hs with rfl | rfl
      · have h0 := hsign.1 rfl
        omega
      · have h0 := hsign.2 rfl
        omega
    · have e : (bu_tkPush t c s) i = t i := by simp [bu_tkPush, hic]
      rw [e]
  · refine ⟨c, Finset.mem_univ c, ?_⟩
    have e : (bu_tkPush t c s) c = t c + s := by simp [bu_tkPush]
    rw [e]
    rcases hs with rfl | rfl
    · have h0 := hsign.1 rfl
      omega
    · have h0 := hsign.2 rfl
      omega

/-- The push is fresh (outside every chain it tops). -/
private theorem bu_push_notmem {n : ℕ} {σ : Finset (Fin n → ℤ)} {t : Fin n → ℤ}
    {c : Fin n} {s : ℤ} (htop : ∀ z ∈ σ, bu_tkLe z t)
    (hH : bu_tkH t < bu_tkH (bu_tkPush t c s)) :
    bu_tkPush t c s ∉ σ := by
  intro hcon
  have hle := bu_tkLe_height (htop _ hcon)
  omega

/-- The push keeps the chain sign set. -/
private theorem bu_push_S {n : ℕ} {σ : Finset (Fin n → ℤ)} {t : Fin n → ℤ}
    {c : Fin n} {s : ℤ}
    (hSeq : bu_tkS σ = bu_tkSgn t)
    (hchain : bu_tkChain (insert (bu_tkPush t c s) σ))
    (hle : ∀ z ∈ σ, bu_tkLe z (bu_tkPush t c s))
    (htc : t c ≠ 0) (hs : s = 1 ∨ s = -1)
    (hsign : (s = 1 → 0 ≤ t c) ∧ (s = -1 → t c ≤ 0)) :
    bu_tkS (insert (bu_tkPush t c s) σ) = bu_tkS σ := by
  have hall : ∀ z ∈ insert (bu_tkPush t c s) σ, bu_tkLe z (bu_tkPush t c s) := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with hzv | hz
    · rw [hzv]
      exact bu_tkLe_refl _
    · exact hle z hz
  have h := bu_tkS_of_top hchain (Finset.mem_insert_self _ _) hall
  have hsgn := bu_push_sgn hs hsign htc
  rw [h, hsgn, hSeq]

/-- The pull is strictly shorter than the bottom. -/
private theorem bu_pull_height {n : ℕ} {b : Fin n → ℤ} {c : Fin n}
    (hne : b c ≠ 0) : bu_tkH (bu_tkPull b c) < bu_tkH b := by
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hic : i = c
    · rw [hic]
      by_cases hpos : 0 < b c
      · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
        rw [e]
        omega
      · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
        rw [e]
        omega
    · have e : (bu_tkPull b c) i = b i := by simp [bu_tkPull, hic]
      rw [e]
  · refine ⟨c, Finset.mem_univ c, ?_⟩
    by_cases hpos : 0 < b c
    · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
      rw [e]
      omega
    · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
      rw [e]
      omega

/-! ## Tight cofacet count -/

private theorem bu_tight_cofacet_count {n m : ℕ} (hm : 1 ≤ m)
    {σ : Finset (Fin n → ℤ)} (hsub : σ ⊆ bu_tkBox n m) (hchainσ : bu_tkChain σ)
    (hc : σ.card = (bu_tkS σ).card) :
    (bu_tkBdry m σ → (bu_tkUp m σ).card = 1) ∧
    (¬ bu_tkBdry m σ → (bu_tkUp m σ).card = 2) := by
  obtain ⟨b, hbσ, t, htσ, hbot, htop, hSeq, _hC, hsubX, _h1, _h2, _hLoose,
    hTight⟩ := bu_chain_card_bound hchainσ
  have hbt : bu_tkLe b t := htop b hbσ
  have hzn : ∀ z ∈ σ, bu_tkMv b z ⊆ bu_tkMv b t ∧ z = bu_tkPt b t (bu_tkMv b z) :=
    fun z hz => bu_tkMv_normal_a hbt (hbot z hz) (htop z hz)
  have hMvbb : bu_tkMv b b = ∅ := by
    rw [bu_tkMv]
    exact Finset.filter_false_of_mem (fun x _ h => h rfl)
  have hempty : (∅ : Finset (Fin n)) ∈ σ.image (bu_tkMv b) := by
    have hmem : bu_tkMv b b ∈ σ.image (bu_tkMv b) :=
      Finset.mem_image.mpr ⟨b, hbσ, rfl⟩
    rw [hMvbb] at hmem
    exact hmem
  have hXmem : bu_tkMv b t ∈ σ.image (bu_tkMv b) :=
    Finset.mem_image.mpr ⟨t, htσ, rfl⟩
  have hcompC : ∀ A ∈ σ.image (bu_tkMv b), ∀ B ∈ σ.image (bu_tkMv b),
      A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB
    rw [Finset.mem_image] at hA hB
    obtain ⟨z, hz, rfl⟩ := hA
    obtain ⟨w, hw, rfl⟩ := hB
    rcases hchainσ.2 z hz w hw with h | h
    · exact Or.inl ((bu_tkMv_le_iff hbt (hbot z hz) (htop z hz)
        (hbot w hw) (htop w hw)).mp h)
    · exact Or.inr ((bu_tkMv_le_iff hbt (hbot w hw) (htop w hw)
        (hbot z hz) (htop z hz)).mp h)
  have hgap := bu_gap_lemma hsubX hempty hXmem hcompC
  have hPtinj : Set.InjOn (bu_tkPt b t)
      (↑(bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t)) : Set (Finset (Fin n))) := by
    intro M1 h1m M2 h2m he
    have m1 : M1 ∈ bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t) :=
      Finset.mem_coe.mp h1m
    have m2 : M2 ∈ bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t) :=
      Finset.mem_coe.mp h2m
    rw [bu_mem_tkExt] at m1 m2
    have s1 : M1 ⊆ bu_tkMv b t := Finset.mem_powerset.mp m1.1
    have s2 : M2 ⊆ bu_tkMv b t := Finset.mem_powerset.mp m2.1
    have e1 : bu_tkMv b (bu_tkPt b t M1) = M1 := (bu_tkPt_mem_of_mem hbt s1).2.2
    have e2 : bu_tkMv b (bu_tkPt b t M2) = M2 := (bu_tkPt_mem_of_mem hbt s2).2.2
    rw [← e1, ← e2, he]
  rcases hTight hc with hA | hB
  · obtain ⟨hXT, hCX⟩ := hA
    have hExt2 : (bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t)).card = 2 :=
      hgap.2.2 hCX
    have hUp : bu_tkUp m σ =
        (bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t)).image (bu_tkPt b t) := by
      ext v
      rw [bu_mem_tkUp, Finset.mem_image]
      constructor
      · rintro ⟨hvbox, hvnot, hvchain, hvsub⟩
        have htri := bu_cofacet_pos hbσ htσ hvchain hvnot
        rcases htri with ⟨hbv, hvt⟩ | ⟨hvb, hne⟩ | ⟨htv, hne⟩
        · have hmem := bu_inside_mem_ext hbt hbot htop hvchain hbv hvt hvnot
          have ev : v = bu_tkPt b t (bu_tkMv b v) :=
            (bu_tkMv_normal_a hbt hbv hvt).2
          exact ⟨bu_tkMv b v, hmem, ev.symm⟩
        · have hD := bu_below_mem hbt htσ hvchain hvb hne
          have hDe : bu_tkMv v b = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro i hi
            have h2 := hD.2 hi
            rw [Finset.mem_sdiff] at h2
            obtain ⟨hiT, hiX⟩ := h2
            rw [hXT] at hiX
            exact hiX hiT
          rw [hDe] at hD
          exact (Finset.not_nonempty_empty hD.1).elim
        · have hE := bu_above_E hbt htop hbσ hvchain htv hne
          obtain ⟨i, hiE⟩ := hE.1
          have hiX : i ∉ bu_tkMv b t := hE.2.1 i hiE
          rw [hXT] at hiX
          have hti0 : t i = 0 := by
            by_contra hcon
            exact hiX (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcon⟩)
          have hvi0 : v i ≠ 0 := by
            have hm := hiE
            rw [bu_tkMv, Finset.mem_filter] at hm
            rw [← hti0]
            exact hm.2
          have hnew : (decide (0 < v i), i) ∈ bu_tkSgn v :=
            bu_mem_tkSgn.mpr ⟨hvi0, rfl⟩
          have hnot : (decide (0 < v i), i) ∉ bu_tkSgn t := by
            intro hcon
            rw [bu_mem_tkSgn] at hcon
            exact hcon.1 hti0
          have hsub2 : bu_tkSgn v ⊆ bu_tkSgn t := by
            rw [← hE.2.2.2, ← hSeq]
            exact hvsub
          exact (hnot (hsub2 hnew)).elim
      · rintro ⟨M, hM, rfl⟩
        have h := bu_ext_inside hchainσ hbot htop hbt hSeq hsub hbσ htσ hM
        exact ⟨h.1, h.2.1, h.2.2.1, le_of_eq h.2.2.2⟩
    have hcard2 : (bu_tkUp m σ).card = 2 := by
      rw [hUp, Finset.card_image_of_injOn hPtinj, hExt2]
    have hnbd : ¬ bu_tkBdry m σ := by
      intro hbd
      obtain ⟨i, hi⟩ := hbd b hbσ
      have hiN : (b i).natAbs = m := by
        rw [Int.abs_eq_natAbs] at hi
        exact_mod_cast hi
      by_cases hiX : i ∈ bu_tkMv b t
      · have hne : t i ≠ b i := by
          have h := hiX
          rw [bu_tkMv, Finset.mem_filter] at h
          exact h.2
        have hlt : (b i).natAbs < (t i).natAbs := bu_tkMv_natAbs_lt hbt i hne
        have hle : (t i).natAbs ≤ m := (bu_mem_tkBox_natAbs.mp (hsub htσ)) i
        omega
      · rw [hXT] at hiX
        have hbi0 : b i = 0 := by
          by_contra hcon
          exact hiX (Finset.mem_filter.mpr ⟨Finset.mem_univ i,
            bu_tkMv_support_mono hbt i hcon⟩)
        have h0 : ((0 : ℤ)).natAbs = 0 := rfl
        rw [hbi0, h0] at hiN
        omega
    exact ⟨fun hbd => absurd hbd hnbd, fun _ => hcard2⟩
  · obtain ⟨c, hT, hcX, hCX⟩ := hB
    have hTX : Finset.univ.filter (fun i => t i ≠ 0) \ bu_tkMv b t = {c} := by
      ext i
      rw [hT, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd h1 h2
      · intro h
        rw [h]
        exact ⟨Or.inl rfl, hcX⟩
    have hcT : t c ≠ 0 := by
      have hmem : c ∈ Finset.univ.filter (fun i => t i ≠ 0) := by
        rw [hT]
        exact Finset.mem_insert_self c _
      exact (Finset.mem_filter.mp hmem).2
    have hcb : t c = b c := bu_tkMv_eq_off c hcX
    have hbc_ne : b c ≠ 0 := by
      rw [← hcb]
      exact hcT
    have hPull_le : bu_tkLe (bu_tkPull b c) b := (bu_tkPull_le hbc_ne).1
    have hPull_box : bu_tkPull b c ∈ bu_tkBox n m :=
      bu_tkPull_mem_box (hsub hbσ) hbc_ne
    have hPull_H := bu_pull_height hbc_ne
    have hPullnot : bu_tkPull b c ∉ σ := by
      intro hcon
      have hle := bu_tkLe_height (hbot _ hcon)
      omega
    have hPullchain : bu_tkChain (insert (bu_tkPull b c) σ) := by
      refine ⟨⟨b, Finset.mem_insert_of_mem hbσ⟩, ?_⟩
      intro x hx y hy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
      · exact Or.inl (bu_tkLe_refl _)
      · exact Or.inl (bu_pull_le_chain hbt hzn hcX hbc_ne y hy')
      · have h := bu_pull_le_chain hbt hzn hcX hbc_ne x hx'
        exact Or.inr h
      · exact hchainσ.2 x hx' y hy'
    have hPullS : bu_tkS (insert (bu_tkPull b c) σ) = bu_tkS σ := by
      have hpt : bu_tkLe (bu_tkPull b c) t := by
        have hcomp := hPullchain.2 _ (Finset.mem_insert_self _ _) _
          (Finset.mem_insert_of_mem htσ)
        exact bu_tkLe_trans_of_comparable hPull_le hbt hcomp
      have hall : ∀ z ∈ insert (bu_tkPull b c) σ, bu_tkLe z t := by
        intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with hzv | hz
        · rw [hzv]
          exact hpt
        · exact htop z hz
      have h := bu_tkS_of_top hPullchain (Finset.mem_insert_of_mem htσ) hall
      rw [h, hSeq]
    have hPullUp : bu_tkPull b c ∈ bu_tkUp m σ := by
      rw [bu_mem_tkUp]
      exact ⟨hPull_box, hPullnot, hPullchain, le_of_eq hPullS⟩
    set s0 := (if 0 < t c then (1 : ℤ) else -1) with hs0def
    have hs0 : s0 = 1 ∨ s0 = -1 := by
      rw [hs0def]
      by_cases hpos : 0 < t c
      · left
        simp [hpos]
      · right
        simp [hpos]
    have hsign : (s0 = 1 → 0 ≤ t c) ∧ (s0 = -1 → t c ≤ 0) := by
      constructor
      · intro h
        by_contra hcon
        have hval : s0 = -1 := by
          rw [hs0def]
          simp [show ¬ (0 : ℤ) < t c by omega]
        omega
      · intro h
        by_contra hcon
        have hval : s0 = 1 := by
          rw [hs0def]
          simp [show (0 : ℤ) < t c by omega]
        omega
    have hPush_le : ∀ z ∈ σ, bu_tkLe z (bu_tkPush t c s0) :=
      fun z hz => bu_push_le_chain hs0 hsign htop hzn hcX hcb z hz
    have hPushchain : bu_tkChain (insert (bu_tkPush t c s0) σ) := by
      refine ⟨⟨t, Finset.mem_insert_of_mem htσ⟩, ?_⟩
      intro x hx y hy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
      · exact Or.inl (bu_tkLe_refl _)
      · exact Or.inr (hPush_le y hy')
      · have h := hPush_le x hx'
        exact Or.inl h
      · exact hchainσ.2 x hx' y hy'
    have hPushH := bu_push_height hs0 hsign
    have hPushnot := bu_push_notmem htop hPushH
    have hPushS := bu_push_S hSeq hPushchain hPush_le hcT hs0 hsign
    have hPushbox : bu_tkPush t c s0 ∈ bu_tkBox n m ↔ (b c).natAbs < m := by
      have hbox_t : ∀ i, i ≠ c → (bu_tkPush t c s0 i).natAbs ≤ m := by
        intro i hic
        have e : (bu_tkPush t c s0) i = t i := by simp [bu_tkPush, hic]
        rw [e]
        exact (bu_mem_tkBox_natAbs.mp (hsub htσ)) i
      have hcc : (bu_tkPush t c s0 c).natAbs = (b c).natAbs + 1 := by
        rw [bu_push_abs hs0 hsign, hcb]
      constructor
      · intro h
        have h1 := (bu_mem_tkBox_natAbs.mp h) c
        rw [hcc] at h1
        omega
      · intro h
        rw [bu_mem_tkBox_natAbs]
        intro i
        by_cases hic : i = c
        · rw [hic, hcc]
          omega
        · exact hbox_t i hic
    have hbdy : bu_tkBdry m σ ↔ (b c).natAbs = m := by
      constructor
      · intro hbd
        obtain ⟨i, hi⟩ := hbd b hbσ
        have hiN : (b i).natAbs = m := by
          rw [Int.abs_eq_natAbs] at hi
          exact_mod_cast hi
        by_cases hic : i = c
        · rw [hic] at hiN
          exact hiN
        · exfalso
          by_cases hiX : i ∈ bu_tkMv b t
          · have hne : t i ≠ b i := by
              have h := hiX
              rw [bu_tkMv, Finset.mem_filter] at h
              exact h.2
            have hlt := bu_tkMv_natAbs_lt hbt i hne
            have hle := (bu_mem_tkBox_natAbs.mp (hsub htσ)) i
            omega
          · have hiT : i ∉ Finset.univ.filter (fun i => t i ≠ 0) := by
              intro hcon
              rw [hT] at hcon
              rw [Finset.mem_insert] at hcon
              rcases hcon with h | h
              · exact hic h
              · exact hiX h
            have hbi0 : b i = 0 := by
              by_contra hcon
              exact hiT (Finset.mem_filter.mpr ⟨Finset.mem_univ i,
                bu_tkMv_support_mono hbt i hcon⟩)
            have h0 : ((0 : ℤ)).natAbs = 0 := rfl
            rw [hbi0, h0] at hiN
            omega
      · intro hceq z hz
        have hzc : z c = b c := by
          have hsubz : bu_tkMv b z ⊆ bu_tkMv b t :=
            hsubX _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
          have hcMz : c ∉ bu_tkMv b z := fun hcon => hcX (hsubz hcon)
          have hznz := (hzn z hz).2
          have e2 : (bu_tkPt b t (bu_tkMv b z)) c = b c := by
            simp [bu_tkPt, hcMz]
          rw [hznz]
          exact e2
        have hmabs : |z c| = (m : ℤ) := by
          rw [hzc, Int.abs_eq_natAbs, hceq]
        exact ⟨c, hmabs⟩
    have hclass : ∀ v ∈ bu_tkUp m σ,
        v = bu_tkPull b c ∨ v = bu_tkPush t c s0 := by
      intro v hv
      rw [bu_mem_tkUp] at hv
      obtain ⟨hvbox, hvnot, hvchain, hvsub⟩ := hv
      have htri := bu_cofacet_pos hbσ htσ hvchain hvnot
      rcases htri with ⟨hbv, hvt⟩ | ⟨hvb, hne⟩ | ⟨htv, hne⟩
      · have hmem := bu_inside_mem_ext hbt hbot htop hvchain hbv hvt hvnot
        rw [hgap.2.1 hCX] at hmem
        exact absurd hmem (Finset.notMem_empty _)
      · have hD := bu_below_mem hbt htσ hvchain hvb hne
        have hDsub : bu_tkMv v b ⊆ {c} := by
          intro x hx
          have h := hD.2 hx
          rw [hTX] at h
          exact h
        have hD1 := bu_eq_singleton_of_sub hDsub hD.1
        exact Or.inl (bu_below_eq_pull hvb hD1)
      · have hE := bu_above_E hbt htop hbσ hvchain htv hne
        have hET : ∀ i ∈ bu_tkMv t v,
            i ∈ Finset.univ.filter (fun i => t i ≠ 0) := by
          intro i hiE
          by_contra hcon
          have hti0 : t i = 0 := by
            by_contra hcon2
            exact hcon (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcon2⟩)
          have hvi0 : v i ≠ 0 := by
            have hm := hiE
            rw [bu_tkMv, Finset.mem_filter] at hm
            rw [← hti0]
            exact hm.2
          have hnew : (decide (0 < v i), i) ∈ bu_tkSgn v :=
            bu_mem_tkSgn.mpr ⟨hvi0, rfl⟩
          have hnot : (decide (0 < v i), i) ∉ bu_tkSgn t := by
            intro hcon3
            rw [bu_mem_tkSgn] at hcon3
            exact hcon3.1 hti0
          have hsub2 : bu_tkSgn v ⊆ bu_tkSgn t := by
            rw [← hE.2.2.2, ← hSeq]
            exact hvsub
          exact hnot (hsub2 hnew)
        have hEsub : bu_tkMv t v ⊆ {c} := by
          intro i hiE
          have hiT := hET i hiE
          rw [hT] at hiT
          rw [Finset.mem_insert] at hiT
          rcases hiT with h | h
          · exact Finset.mem_singleton.mpr h
          · exact absurd h (hE.2.1 i hiE)
        have hE1 := bu_eq_singleton_of_sub hEsub hE.1
        have hveq := bu_above_eq_push hcT htv hE1
        rw [hs0def]
        exact Or.inr hveq
    constructor
    · intro hbd
      have hbm : (b c).natAbs = m := hbdy.mp hbd
      have hPushOut : bu_tkPush t c s0 ∉ bu_tkBox n m := by
        intro hcon
        have h1 := (bu_mem_tkBox_natAbs.mp hcon) c
        rw [bu_push_abs hs0 hsign, hcb] at h1
        omega
      have hUpEq : bu_tkUp m σ = {bu_tkPull b c} := by
        ext v
        rw [Finset.mem_singleton]
        constructor
        · intro hv
          rcases hclass v hv with h | h
          · exact h
          · exfalso
            have hvb : bu_tkPush t c s0 ∈ bu_tkBox n m := by
              rw [← h]
              exact (bu_mem_tkUp.mp hv).1
            exact hPushOut hvb
        · intro hv
          rw [hv]
          exact hPullUp
      rw [hUpEq, Finset.card_singleton]
    · intro hnbd
      have hPushIn : bu_tkPush t c s0 ∈ bu_tkBox n m := by
        rw [hPushbox]
        have hbm : (b c).natAbs ≠ m := fun h => hnbd (hbdy.mpr h)
        have hle : (b c).natAbs ≤ m := (bu_mem_tkBox_natAbs.mp (hsub hbσ)) c
        omega
      have hPushUp : bu_tkPush t c s0 ∈ bu_tkUp m σ := by
        rw [bu_mem_tkUp]
        exact ⟨hPushIn, hPushnot, hPushchain, le_of_eq hPushS⟩
      have hUpEq : bu_tkUp m σ = {bu_tkPull b c, bu_tkPush t c s0} := by
        ext v
        rw [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hv
          rcases hclass v hv with h | h
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · rw [h]
            exact hPullUp
          · rw [h]
            exact hPushUp
      have hne : bu_tkPull b c ≠ bu_tkPush t c s0 := by
        intro hcon
        have h1 := bu_pull_height hbc_ne
        have h2 := bu_push_height hs0 hsign
        have h3 := bu_tkLe_height hbt
        rw [hcon] at h1
        omega
      rw [hUpEq, Finset.card_pair_eq_two_iff.mpr hne]

/-! ## Loose-chain facts -/

private theorem bu_loose_not_bdry {n m : ℕ} (hm : 1 ≤ m)
    {σ : Finset (Fin n → ℤ)} (hsub : σ ⊆ bu_tkBox n m) (hchainσ : bu_tkChain σ)
    (hc : σ.card = (bu_tkS σ).card + 1) : ¬ bu_tkBdry m σ := by
  obtain ⟨b, hbσ, t, htσ, _hbot, htop, _hSeq, _hC, _hsubX, _h1, _h2, hLoose,
    _hTight⟩ := bu_chain_card_bound hchainσ
  obtain ⟨hXT, _hCX⟩ := hLoose hc
  have hbt : bu_tkLe b t := htop b hbσ
  intro hbd
  obtain ⟨i, hi⟩ := hbd b hbσ
  have hiN : (b i).natAbs = m := by
    rw [Int.abs_eq_natAbs] at hi
    exact_mod_cast hi
  by_cases hiX : i ∈ bu_tkMv b t
  · have hne : t i ≠ b i := by
      have h := hiX
      rw [bu_tkMv, Finset.mem_filter] at h
      exact h.2
    have hlt : (b i).natAbs < (t i).natAbs := bu_tkMv_natAbs_lt hbt i hne
    have hle : (t i).natAbs ≤ m := (bu_mem_tkBox_natAbs.mp (hsub htσ)) i
    omega
  · rw [hXT] at hiX
    have hbi0 : b i = 0 := by
      by_contra hcon
      exact hiX (Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        bu_tkMv_support_mono hbt i hcon⟩)
    have h0 : ((0 : ℤ)).natAbs = 0 := rfl
    rw [hbi0, h0] at hiN
    omega

private theorem bu_loose_strict_growth {n m : ℕ}
    {σ : Finset (Fin n → ℤ)} (_hchainσ : bu_tkChain σ)
    (hc : σ.card = (bu_tkS σ).card + 1)
    {v : Fin n → ℤ} (_hvbox : v ∈ bu_tkBox n m) (hvnot : v ∉ σ)
    (hchain : bu_tkChain (insert v σ)) :
    bu_tkS σ ⊂ bu_tkS (insert v σ) := by
  have hsub : bu_tkS σ ⊆ bu_tkS (insert v σ) :=
    Finset.sup_mono (Finset.subset_insert v σ)
  obtain ⟨_b, _hb, _t, _ht, _hbot, _htop, _hSeq, _hC, _hsubX, h1, h2, _hLoose,
    _hTight⟩ := bu_chain_card_bound hchain
  have hcardI : (insert v σ).card = σ.card + 1 :=
    Finset.card_insert_of_notMem hvnot
  have hlt : (bu_tkS σ).card < (bu_tkS (insert v σ)).card := by omega
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsub, ?_⟩
  intro hcon
  rw [hcon] at hlt
  exact lt_irrefl _ hlt

/-! ## Happy-chain trichotomy -/

private theorem bu_happy_card {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (h : bu_tkHappy m L σ) :
    σ.card = (bu_tkS σ).card ∨ σ.card = (bu_tkS σ).card + 1 := by
  obtain ⟨_hsub, hchain, hcover⟩ := h
  obtain ⟨_b, _hb, _t, _ht, _hbot, _htop, _hSeq, _hC, _hsubX, h1, h2, _hLoose,
    _hTight⟩ := bu_chain_card_bound hchain
  have hle : (bu_tkS σ).card ≤ σ.card :=
    calc (bu_tkS σ).card ≤ (σ.image L).card := Finset.card_le_card hcover
      _ ≤ σ.card := Finset.card_image_le
  omega

private theorem bu_happy_tight_image {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (h : bu_tkHappy m L σ)
    (hc : σ.card = (bu_tkS σ).card) : σ.image L = bu_tkS σ := by
  have hle : (σ.image L).card ≤ (bu_tkS σ).card := by
    calc (σ.image L).card ≤ σ.card := Finset.card_image_le
      _ = (bu_tkS σ).card := hc
  exact (Finset.eq_of_subset_of_card_le h.2.2 hle).symm

private theorem bu_happy_loose_neg {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (h : bu_tkHappy m L σ) (hN : bu_tkNoCompl m L)
    {ℓ : Bool × Fin n} (hℓnot : ℓ ∉ bu_tkS σ) (himg : σ.image L = insert ℓ (bu_tkS σ)) :
    bu_tkNeg ℓ ∉ bu_tkS σ ∧
      ∀ t : Fin n → ℤ, t ∈ σ → (∀ z ∈ σ, bu_tkLe z t) →
        bu_tkS σ = bu_tkSgn t → t ℓ.2 = 0 := by
  have hℓimg : ℓ ∈ σ.image L := by
    rw [himg]
    exact Finset.mem_insert_self ℓ _
  obtain ⟨w, hwσ, hLw⟩ := Finset.mem_image.mp hℓimg
  have hsub : σ ⊆ bu_tkBox n m := h.1
  have hchain := h.2.1
  have hneg : bu_tkNeg ℓ ∉ bu_tkS σ := by
    intro hcon
    have hmem : bu_tkNeg ℓ ∈ σ.image L := h.2.2 hcon
    obtain ⟨w', hw'σ, hLw'⟩ := Finset.mem_image.mp hmem
    rcases hchain.2 w hwσ w' hw'σ with hle | hle
    · exact hN w (hsub hwσ) w' (hsub hw'σ) hle (by rw [hLw', hLw])
    · exact hN w' (hsub hw'σ) w (hsub hwσ) hle (by
        rw [hLw, hLw']
        exact (bu_tkNeg_invol ℓ).symm)
  refine ⟨hneg, ?_⟩
  intro t _ _ hSeq
  obtain ⟨β, j⟩ := ℓ
  have h1 : (β, j) ∉ bu_tkSgn t := by
    rw [← hSeq]
    exact hℓnot
  have h2 : bu_tkNeg (β, j) ∉ bu_tkSgn t := by
    rw [← hSeq]
    exact hneg
  by_contra hcon
  have hmem : (decide (0 < t j), j) ∈ bu_tkSgn t :=
    bu_mem_tkSgn.mpr ⟨hcon, rfl⟩
  by_cases hβ : decide (0 < t j) = β
  · have he : (decide (0 < t j), j) = (β, j) := Prod.ext_iff.mpr ⟨hβ, rfl⟩
    rw [he] at hmem
    exact h1 hmem
  · have hnegb : decide (0 < t j) = !β := by
      cases β <;> cases hd : decide (0 < t j)
      · exact (hβ hd).elim
      · rfl
      · rfl
      · exact (hβ hd).elim
    have he : (decide (0 < t j), j) = bu_tkNeg (β, j) := by
      rw [bu_tkNeg]
      exact Prod.ext_iff.mpr ⟨hnegb, rfl⟩
    rw [he] at hmem
    exact h2 hmem

private theorem bu_tkSgn_zero {n : ℕ} : bu_tkSgn (0 : Fin n → ℤ) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro l hl
  rw [bu_mem_tkSgn] at hl
  exact hl.1 rfl

private theorem bu_happy_empty_iff {n : ℕ}
    {σ : Finset (Fin n → ℤ)} (hchainσ : bu_tkChain σ) :
    bu_tkS σ = ∅ ↔ σ = {0} := by
  constructor
  · intro hS
    obtain ⟨_b, _hbσ, t, htσ, _hbot, htop, hSeq, _hC, _hsubX, _h1, _h2, _hLoose,
      _hTight⟩ := bu_chain_card_bound hchainσ
    have ht0 : t = 0 := by
      by_contra hcon
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hcon
      have hi0 : t i ≠ 0 := hi
      have hmem : (decide (0 < t i), i) ∈ bu_tkSgn t :=
        bu_mem_tkSgn.mpr ⟨hi0, rfl⟩
      rw [← hSeq] at hmem
      rw [hS] at hmem
      exact Finset.notMem_empty _ hmem
    have hz0 : ∀ z ∈ σ, z = 0 := by
      intro z hz
      funext i
      have hle := htop z hz i
      rw [ht0] at hle
      have h0 : (0 : Fin n → ℤ) i = 0 := rfl
      rw [h0] at hle
      rcases hle with h | ⟨s, e⟩ | ⟨s, e⟩ <;> omega
    ext z
    constructor
    · intro hz
      rw [hz0 z hz]
      exact Finset.mem_singleton_self 0
    · intro hz
      rw [Finset.mem_singleton] at hz
      rw [hz, ← ht0]
      exact htσ
  · intro hσ
    rw [hσ, bu_tkS, Finset.sup_singleton, bu_tkSgn_zero]

private theorem bu_zero_happy {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n} :
    bu_tkHappy m L ({0} : Finset (Fin n → ℤ)) ∧
      ({0} : Finset (Fin n → ℤ)).card = (bu_tkS ({0} : Finset (Fin n → ℤ))).card + 1 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro z hz
    rw [Finset.mem_singleton] at hz
    rw [hz]
    exact bu_zero_mem_tkBox
  · refine ⟨Finset.singleton_nonempty 0, ?_⟩
    intro z hz w hw
    rw [Finset.mem_singleton] at hz hw
    rw [hz, hw]
    exact Or.inl (bu_tkLe_refl 0)
  · rw [bu_tkS, Finset.sup_singleton, bu_tkSgn_zero]
    exact Finset.empty_subset _
  · rw [bu_tkS, Finset.sup_singleton, bu_tkSgn_zero]
    rfl

private theorem bu_happy_erase {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {τ : Finset (Fin n → ℤ)} {w : Fin n → ℤ} {σ : Finset (Fin n → ℤ)}
    (hsub : τ ⊆ bu_tkBox n m) (hchain : bu_tkChain τ)
    (hσ : σ = τ.erase w) (hne : σ.Nonempty)
    (hcover : bu_tkS τ ⊆ σ.image L) : bu_tkHappy m L σ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hσ]
    exact Finset.Subset.trans (Finset.erase_subset w τ) hsub
  · refine ⟨hne, ?_⟩
    intro z hz w' hw'
    have hzτ : z ∈ τ := Finset.mem_of_mem_erase (hσ ▸ hz)
    have hwτ : w' ∈ τ := Finset.mem_of_mem_erase (hσ ▸ hw')
    exact hchain.2 z hzτ w' hwτ
  · have hmono : bu_tkS σ ⊆ bu_tkS τ :=
      Finset.sup_mono (hσ ▸ Finset.erase_subset w τ)
    exact Finset.Subset.trans hmono hcover

private theorem bu_happy_insert {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} {v : Fin n → ℤ} {τ : Finset (Fin n → ℤ)}
    (hv : v ∈ bu_tkBox n m) (hσ : bu_tkHappy m L σ)
    (hτ : τ = insert v σ) (hchain : bu_tkChain τ)
    (hcover : bu_tkS τ ⊆ σ.image L) : bu_tkHappy m L τ := by
  refine ⟨?_, hchain, ?_⟩
  · rw [hτ]
    exact Finset.insert_subset hv hσ.1
  · have hmono : σ.image L ⊆ τ.image L :=
      Finset.image_subset_image (hτ ▸ Finset.subset_insert v σ)
    exact Finset.Subset.trans hcover hmono

/-! ## The Tucker graph -/

/-- Vertices: finsets of grid points lying in the box (hence a `Fintype`). -/
private def bu_tkV (n m : ℕ) : Type :=
  { σ : Finset (Fin n → ℤ) // σ ∈ (bu_tkBox n m).powerset }

private instance bu_tkVFintype (n m : ℕ) : Fintype (bu_tkV n m) :=
  Finset.fintypeCoeSort _

/-- Door from `σ` to `τ`: `τ` adds one vertex and the old labels cover the new sign set. -/
private def bu_tkDoor {n : ℕ} (L : (Fin n → ℤ) → Bool × Fin n)
    (σ τ : Finset (Fin n → ℤ)) : Prop :=
  ∃ v, v ∉ σ ∧ τ = insert v σ ∧ bu_tkS τ ⊆ σ.image L

/-- Adjacency on underlying finsets: doors either way, or the antipodal boundary edge. -/
private def bu_tkAdj {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (σ τ : Finset (Fin n → ℤ)) : Prop :=
  bu_tkHappy m L σ ∧ bu_tkHappy m L τ ∧
    (bu_tkDoor L σ τ ∨ bu_tkDoor L τ σ ∨ (bu_tkBdry m σ ∧ τ = σ.image Neg.neg))

private theorem bu_tkBdry_neg {n m : ℕ} {σ : Finset (Fin n → ℤ)}
    (h : bu_tkBdry m σ) : bu_tkBdry m (σ.image Neg.neg) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨i, hi⟩ := h y hy
  exact ⟨i, by rw [Pi.neg_apply, abs_neg]; exact hi⟩

private theorem bu_tkS_neg {n : ℕ} {σ : Finset (Fin n → ℤ)} :
    bu_tkS (σ.image Neg.neg) = (bu_tkS σ).image bu_tkNeg := by
  ext l
  simp only [bu_tkS, Finset.mem_sup, Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, hl⟩
    rw [bu_tkSgn_neg] at hl
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hl
    exact ⟨l', ⟨y, hy, hl'⟩, rfl⟩
  · rintro ⟨l', ⟨y, hy, hl'⟩, rfl⟩
    refine ⟨-y, ⟨y, hy, rfl⟩, ?_⟩
    rw [bu_tkSgn_neg]
    exact Finset.mem_image.mpr ⟨l', hl', rfl⟩

/-- The negation image of a happy boundary chain is happy. -/
private theorem bu_tkNeg_happy {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    {σ : Finset (Fin n → ℤ)} (h : bu_tkHappy m L σ) (hb : bu_tkBdry m σ) :
    bu_tkHappy m L (σ.image Neg.neg) := by
  obtain ⟨hsub, hchain, hcover⟩ := h
  have hsubN : σ.image Neg.neg ⊆ bu_tkBox n m := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact bu_neg_mem_tkBox (hsub hz)
  have hchainN : bu_tkChain (σ.image Neg.neg) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨z, hz⟩ := hchain.1
      exact ⟨-z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    · intro y1 hy1 y2 hy2
      obtain ⟨z1, hz1, rfl⟩ := Finset.mem_image.mp hy1
      obtain ⟨z2, hz2, rfl⟩ := Finset.mem_image.mp hy2
      rcases hchain.2 z1 hz1 z2 hz2 with h | h
      · exact Or.inl (bu_tkLe_neg.mpr h)
      · exact Or.inr (bu_tkLe_neg.mpr h)
  refine ⟨hsubN, hchainN, ?_⟩
  rw [bu_tkS_neg]
  have hL : (σ.image Neg.neg).image L = (σ.image L).image bu_tkNeg := by
    ext l
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, hl⟩
      refine ⟨L y, ⟨y, hy, rfl⟩, ?_⟩
      rw [← hl]
      exact (hanti y (hsub hy) (hb y hy)).symm
    · rintro ⟨l', ⟨y, hy, rfl⟩, hl⟩
      refine ⟨-y, ⟨y, hy, rfl⟩, ?_⟩
      rw [hanti y (hsub hy) (hb y hy)]
      exact hl
  rw [hL]
  exact Finset.image_subset_image hcover

private theorem bu_tkAdj_symm {n : ℕ} {m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ τ : Finset (Fin n → ℤ)} (h : bu_tkAdj m L σ τ) : bu_tkAdj m L τ σ := by
  obtain ⟨hs, ht, hdoor⟩ := h
  refine ⟨ht, hs, ?_⟩
  rcases hdoor with h | h | ⟨hb, rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · refine Or.inr (Or.inr ⟨bu_tkBdry_neg hb, ?_⟩)
    ext y
    constructor
    · intro hy
      refine Finset.mem_image.mpr ⟨-y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, neg_neg y⟩
    · intro hy
      obtain ⟨z, hz, hzz⟩ := Finset.mem_image.mp hy
      obtain ⟨w, hw, hww⟩ := Finset.mem_image.mp hz
      rw [← hww, neg_neg] at hzz
      rw [← hzz]
      exact hw

private theorem bu_tkNeg_image_ne {n m : ℕ} (hm : 1 ≤ m)
    {σ : Finset (Fin n → ℤ)} (hchain : bu_tkChain σ) (hb : bu_tkBdry m σ) :
    σ.image Neg.neg ≠ σ := by
  intro heq
  obtain ⟨b, hbσ, _t, _ht, hbot, _htop, _hSeq⟩ := bu_chain_bot_top hchain
  have hnb : -b ∈ σ := by
    rw [← heq]
    exact Finset.mem_image.mpr ⟨b, hbσ, rfl⟩
  have hH : bu_tkH (-b) = bu_tkH b := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.neg_apply]
    exact Int.natAbs_neg _
  have hbb : b = -b := by
    rcases hchain.2 b hbσ (-b) hnb with h | h
    · exact bu_tkLe_of_height_eq h (by omega)
    · exact (bu_tkLe_of_height_eq h (by omega)).symm
  have hb0 : ∀ i, b i = 0 := by
    intro i
    have hi := congrArg (fun z => z i) hbb
    simp only [Pi.neg_apply] at hi
    omega
  obtain ⟨i, hi⟩ := hb b hbσ
  rw [hb0 i, abs_zero] at hi
  have hm0 : m = 0 := by
    have hcast : ((m : ℕ) : ℤ) = 0 := hi.symm
    exact_mod_cast hcast
  omega

private theorem bu_tkAdj_irrefl {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (h : bu_tkAdj m L σ σ) : False := by
  obtain ⟨hs, _, hdoor⟩ := h
  rcases hdoor with ⟨v, hv, heq, _⟩ | ⟨v, hv, heq, _⟩ | ⟨hb, heq⟩
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hv] at hcc
    omega
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hv] at hcc
    omega
  · exact bu_tkNeg_image_ne hm hs.2.1 hb heq.symm

private noncomputable def bu_tkG (n m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (hm : 1 ≤ m) :
    SimpleGraph (bu_tkV n m) where
  Adj σ τ := bu_tkAdj m L σ.val τ.val
  symm := ⟨fun _ _ h => bu_tkAdj_symm h⟩
  loopless := ⟨fun _ h => bu_tkAdj_irrefl hm h⟩

private noncomputable instance bu_tkGDec {n m : ℕ} (L : (Fin n → ℤ) → Bool × Fin n)
    (hm : 1 ≤ m) :
    DecidableRel (bu_tkG n m L hm).Adj :=
  Classical.decRel _

/-! ## Degree count -/

/-- Decidability of the boundary predicate (for the antipodal counter). -/
private noncomputable instance bu_tkBdry_dec {n m : ℕ} (σ : Finset (Fin n → ℤ)) :
    Decidable (bu_tkBdry m σ) :=
  Classical.dec _

/-- Up-neighbors: one-vertex extensions whose new sign set is covered by old labels. -/
private noncomputable def bu_upFin {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (σ : Finset (Fin n → ℤ)) : Finset (Finset (Fin n → ℤ)) :=
  ((bu_tkBox n m).filter fun v =>
    v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ σ.image L).image
    fun v => insert v σ

/-- Down-neighbors: one-vertex deletions still covering the sign set. -/
private def bu_downFin {n : ℕ} (L : (Fin n → ℤ) → Bool × Fin n)
    (σ : Finset (Fin n → ℤ)) : Finset (Finset (Fin n → ℤ)) :=
  (σ.filter fun w =>
    (σ.erase w).Nonempty ∧ bu_tkS σ ⊆ (σ.erase w).image L).image
    fun w => σ.erase w

/-- Antipodal neighbor: the negation image when on the boundary. -/
private noncomputable def bu_antiFin {n : ℕ} (m : ℕ) (σ : Finset (Fin n → ℤ)) :
    Finset (Finset (Fin n → ℤ)) :=
  if bu_tkBdry m σ then {σ.image Neg.neg} else ∅

private theorem bu_mem_antiFin {n : ℕ} {m : ℕ} {σ τ' : Finset (Fin n → ℤ)} :
    τ' ∈ bu_antiFin m σ ↔ bu_tkBdry m σ ∧ τ' = σ.image Neg.neg := by
  by_cases hb : bu_tkBdry m σ <;> simp [bu_antiFin, hb, Finset.mem_singleton]

/-- Neighbors of a happy vertex are exactly the up/down/antipodal finsets. -/
private theorem bu_neighbor_image {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    (hm : 1 ≤ m)
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val) :
    Finset.image Subtype.val ((bu_tkG n m L hm).neighborFinset σ) =
      bu_upFin m L σ.val ∪ bu_downFin L σ.val ∪ bu_antiFin m σ.val := by
  have hsub : σ.val ⊆ bu_tkBox n m := Finset.mem_powerset.mp σ.property
  ext τ'
  simp only [Finset.mem_union]
  constructor
  · intro h
    obtain ⟨τ, hτmem, rfl⟩ := Finset.mem_image.mp h
    have hτadj := (SimpleGraph.mem_neighborFinset (bu_tkG n m L hm) σ τ).mp hτmem
    obtain ⟨hs, ht, hdoor⟩ := hτadj
    rcases hdoor with ⟨v, hvnot, heq, hcover⟩ | ⟨w, hwnot, heq, hcover⟩ | ⟨hb, heq⟩
    · have hvbox : v ∈ bu_tkBox n m := by
        have hmem : v ∈ τ.val := heq ▸ Finset.mem_insert_self v σ.val
        have hτsub : τ.val ⊆ bu_tkBox n m := Finset.mem_powerset.mp τ.property
        exact hτsub hmem
      have hchain : bu_tkChain (insert v σ.val) := heq ▸ ht.2.1
      have hcover' : bu_tkS (insert v σ.val) ⊆ σ.val.image L := heq ▸ hcover
      have hvmem : v ∈ (bu_tkBox n m).filter
          (fun v => v ∉ σ.val ∧ bu_tkChain (insert v σ.val) ∧
            bu_tkS (insert v σ.val) ⊆ σ.val.image L) := by
        rw [Finset.mem_filter]
        exact ⟨hvbox, hvnot, hchain, hcover'⟩
      have hUmem : insert v σ.val ∈ bu_upFin m L σ.val :=
        Finset.mem_image.mpr ⟨v, hvmem, rfl⟩
      rw [heq]
      exact Or.inl (Or.inl hUmem)
    · have hτe : τ.val = σ.val.erase w := by
        rw [heq, Finset.erase_insert hwnot]
      have hwσ : w ∈ σ.val := heq ▸ Finset.mem_insert_self w τ.val
      have hne : (σ.val.erase w).Nonempty := hτe ▸ ht.2.1.1
      have hcover' : bu_tkS σ.val ⊆ (σ.val.erase w).image L := hτe ▸ hcover
      have hwmem : w ∈ σ.val.filter
          (fun w => (σ.val.erase w).Nonempty ∧ bu_tkS σ.val ⊆ (σ.val.erase w).image L) := by
        rw [Finset.mem_filter]
        exact ⟨hwσ, hne, hcover'⟩
      have hDmem : σ.val.erase w ∈ bu_downFin L σ.val :=
        Finset.mem_image.mpr ⟨w, hwmem, rfl⟩
      rw [hτe]
      exact Or.inl (Or.inr hDmem)
    · have hAmem : σ.val.image Neg.neg ∈ bu_antiFin m σ.val :=
        bu_mem_antiFin.mpr ⟨hb, rfl⟩
      rw [heq]
      exact Or.inr hAmem
  · intro h
    rcases h with (hU | hD) | hA
    · obtain ⟨v, hvF, rfl⟩ := Finset.mem_image.mp hU
      rw [Finset.mem_filter] at hvF
      obtain ⟨hvbox, hvnot, hchain, hcover⟩ := hvF
      have hmem : insert v σ.val ∈ (bu_tkBox n m).powerset := by
        rw [Finset.mem_powerset]
        exact Finset.insert_subset hvbox hsub
      have hadj : bu_tkAdj m L σ.val (insert v σ.val) :=
        ⟨hσ, bu_happy_insert hvbox hσ rfl hchain hcover, Or.inl ⟨v, hvnot, rfl, hcover⟩⟩
      exact Finset.mem_image.mpr ⟨⟨insert v σ.val, hmem⟩,
        (SimpleGraph.mem_neighborFinset (bu_tkG n m L hm) _ _).mpr hadj, rfl⟩
    · obtain ⟨w, hwF, rfl⟩ := Finset.mem_image.mp hD
      rw [Finset.mem_filter] at hwF
      obtain ⟨hwσ, hne, hcover⟩ := hwF
      have hmem : σ.val.erase w ∈ (bu_tkBox n m).powerset := by
        rw [Finset.mem_powerset]
        exact Finset.Subset.trans (Finset.erase_subset w σ.val) hsub
      have hadj : bu_tkAdj m L σ.val (σ.val.erase w) :=
        ⟨hσ, bu_happy_erase hsub hσ.2.1 rfl hne hcover,
          Or.inr (Or.inl ⟨w, Finset.notMem_erase w σ.val,
            (Finset.insert_erase hwσ).symm, hcover⟩)⟩
      exact Finset.mem_image.mpr ⟨⟨σ.val.erase w, hmem⟩,
        (SimpleGraph.mem_neighborFinset (bu_tkG n m L hm) _ _).mpr hadj, rfl⟩
    · rw [bu_mem_antiFin] at hA
      obtain ⟨hb, rfl⟩ := hA
      have hmem : σ.val.image Neg.neg ∈ (bu_tkBox n m).powerset := by
        rw [Finset.mem_powerset]
        intro y hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        exact bu_neg_mem_tkBox (hsub hz)
      have hadj : bu_tkAdj m L σ.val (σ.val.image Neg.neg) :=
        ⟨hσ, bu_tkNeg_happy hanti hσ hb, Or.inr (Or.inr ⟨hb, rfl⟩)⟩
      exact Finset.mem_image.mpr ⟨⟨σ.val.image Neg.neg, hmem⟩,
        (SimpleGraph.mem_neighborFinset (bu_tkG n m L hm) _ _).mpr hadj, rfl⟩

/-- Members of the three neighbor finsets have cards `σ+1`, `σ-1`, `σ`. -/
private theorem bu_neighbor_cards {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} {x : Finset (Fin n → ℤ)}
    (hxU : x ∈ bu_upFin m L σ) : x.card = σ.card + 1 := by
  obtain ⟨v, hvF, hvv⟩ := Finset.mem_image.mp hxU
  rw [Finset.mem_filter] at hvF
  obtain ⟨_, hvnot, _, _⟩ := hvF
  rw [← hvv, Finset.card_insert_of_notMem hvnot]

private theorem bu_neighbor_cards_down {n : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} {x : Finset (Fin n → ℤ)}
    (hxD : x ∈ bu_downFin L σ) : x.card = σ.card - 1 := by
  obtain ⟨w, hwF, hww⟩ := Finset.mem_image.mp hxD
  rw [Finset.mem_filter] at hwF
  obtain ⟨hwσ, _, _⟩ := hwF
  rw [← hww, Finset.card_erase_of_mem hwσ]

private theorem bu_neighbor_cards_anti {n m : ℕ}
    {σ : Finset (Fin n → ℤ)} {x : Finset (Fin n → ℤ)}
    (hxA : x ∈ bu_antiFin m σ) : x.card = σ.card := by
  rw [bu_mem_antiFin] at hxA
  obtain ⟨_, rfl⟩ := hxA
  exact Finset.card_image_of_injective _ neg_injective

/-- The three neighbor finsets are pairwise disjoint. -/
private theorem bu_neighbor_disjoint {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (hcard : 1 ≤ σ.card) :
    Disjoint (bu_upFin m L σ) (bu_downFin L σ) ∧
    Disjoint (bu_upFin m L σ) (bu_antiFin m σ) ∧
    Disjoint (bu_downFin L σ) (bu_antiFin m σ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxU hxD
    have h1 := bu_neighbor_cards hxU
    have h2 := bu_neighbor_cards_down hxD
    omega
  · rw [Finset.disjoint_left]
    intro x hxU hxA
    have h1 := bu_neighbor_cards hxU
    have h2 := bu_neighbor_cards_anti hxA
    omega
  · rw [Finset.disjoint_left]
    intro x hxD hxA
    have h1 := bu_neighbor_cards_down hxD
    have h2 := bu_neighbor_cards_anti hxA
    omega

/-- Degree is the sum of the three neighbor counts. -/
private theorem bu_degree_eq {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val) :
    (bu_tkG n m L hm).degree σ =
      (bu_upFin m L σ.val).card + (bu_downFin L σ.val).card +
        (bu_antiFin m σ.val).card := by
  have himg := bu_neighbor_image hm hanti hσ
  have hcard : ((bu_tkG n m L hm).neighborFinset σ).card =
      (bu_upFin m L σ.val ∪ bu_downFin L σ.val ∪ bu_antiFin m σ.val).card := by
    rw [← himg]
    have hinj : Function.Injective
        (Subtype.val : bu_tkV n m → Finset (Fin n → ℤ)) := Subtype.val_injective
    exact (Finset.card_image_of_injective _ hinj).symm
  have h1pos : 1 ≤ σ.val.card := Finset.card_pos.mpr hσ.2.1.1
  have hd := bu_neighbor_disjoint (n := n) (m := m) (L := L) (σ := σ.val) h1pos
  have hUDA : ((bu_upFin m L σ.val ∪ bu_downFin L σ.val) ∪ bu_antiFin m σ.val).card =
      (bu_upFin m L σ.val).card + (bu_downFin L σ.val).card +
        (bu_antiFin m σ.val).card := by
    rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hd.2.1, hd.2.2⟩),
      Finset.card_union_of_disjoint hd.1]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hcard, hUDA]

private theorem bu_anti_card {n m : ℕ} {σ : Finset (Fin n → ℤ)} :
    (bu_antiFin m σ).card = if bu_tkBdry m σ then 1 else 0 := by
  by_cases hb : bu_tkBdry m σ <;> simp [bu_antiFin, hb]

/-- Tight chains have no down-neighbors (deletions lose a label). -/
private theorem bu_down_tight {n : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (hchain : bu_tkChain σ)
    (hc : σ.card = (bu_tkS σ).card) :
    bu_downFin L σ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨w, hwF, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_filter] at hwF
  obtain ⟨hwσ, _, hcover⟩ := hwF
  have hpos : 1 ≤ σ.card := Finset.card_pos.mpr hchain.1
  have h1 : (bu_tkS σ).card ≤ ((σ.erase w).image L).card :=
    Finset.card_le_card hcover
  have h2 : ((σ.erase w).image L).card ≤ σ.card - 1 :=
    le_trans Finset.card_image_le (by rw [Finset.card_erase_of_mem hwσ])
  omega

/-- Loose chains covered by `S` have no up-neighbors (signs would grow). -/
private theorem bu_up_loose_eq {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (hσ : bu_tkHappy m L σ)
    (hc : σ.card = (bu_tkS σ).card + 1) (himg : σ.image L = bu_tkS σ) :
    bu_upFin m L σ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨v, hvF, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_filter] at hvF
  obtain ⟨hvbox, hvnot, hchainv, hcover⟩ := hvF
  have hlt : (bu_tkS σ).card < (bu_tkS (insert v σ)).card :=
    Finset.card_lt_card
      (bu_loose_strict_growth hσ.2.1 hc hvbox hvnot hchainv)
  have hle : (bu_tkS (insert v σ)).card ≤ (bu_tkS σ).card := by
    rw [himg] at hcover
    exact Finset.card_le_card hcover
  omega

/-! ## Loose upward extensions gaining a new sign -/

private theorem bu_loose_upL_card {n m : ℕ} (hm : 1 ≤ m)
    {σ : Finset (Fin n → ℤ)} (hsub : σ ⊆ bu_tkBox n m) (hchainσ : bu_tkChain σ)
    (hc : σ.card = (bu_tkS σ).card + 1)
    {ℓ : Bool × Fin n} (hℓ : ℓ ∉ bu_tkS σ) (hℓn : bu_tkNeg ℓ ∉ bu_tkS σ) :
    (bu_tkUpL m σ ℓ).card = 1 := by
  obtain ⟨β, j⟩ := ℓ
  obtain ⟨b, hbσ, t, htσ, hbot, htop, hSeq, _hC, hsubX, _h1, _h2, hLoose,
    _hTight⟩ := bu_chain_card_bound hchainσ
  obtain ⟨hXT, hCX⟩ := hLoose hc
  have hbt : bu_tkLe b t := htop b hbσ
  have hzn : ∀ z ∈ σ, bu_tkMv b z ⊆ bu_tkMv b t ∧ z = bu_tkPt b t (bu_tkMv b z) :=
    fun z hz => bu_tkMv_normal_a hbt (hbot z hz) (htop z hz)
  have htj : t j = 0 := by
    by_contra hcon
    have hmem : (decide (0 < t j), j) ∈ bu_tkSgn t :=
      bu_mem_tkSgn.mpr ⟨hcon, rfl⟩
    rw [← hSeq] at hmem
    by_cases hβ : decide (0 < t j) = β
    · have he : (decide (0 < t j), j) = (β, j) := Prod.ext_iff.mpr ⟨hβ, rfl⟩
      rw [he] at hmem
      exact hℓ hmem
    · have hnegb : decide (0 < t j) = !β := by
        cases β <;> cases hd : decide (0 < t j)
        · exact (hβ hd).elim
        · rfl
        · rfl
        · exact (hβ hd).elim
      have he : (decide (0 < t j), j) = bu_tkNeg (β, j) := by
        rw [bu_tkNeg]
        exact Prod.ext_iff.mpr ⟨hnegb, rfl⟩
      rw [he] at hmem
      exact hℓn hmem
  have hjT : j ∉ Finset.univ.filter (fun i => t i ≠ 0) := by
    intro h
    rw [Finset.mem_filter] at h
    exact h.2 htj
  have hjX : j ∉ bu_tkMv b t := by
    rw [hXT]
    exact hjT
  have hjt : t j = b j := bu_tkMv_eq_off j hjX
  have hMvbb : bu_tkMv b b = ∅ := by
    rw [bu_tkMv]
    exact Finset.filter_false_of_mem (fun x _ h => h rfl)
  have hempty : (∅ : Finset (Fin n)) ∈ σ.image (bu_tkMv b) := by
    have hmem : bu_tkMv b b ∈ σ.image (bu_tkMv b) :=
      Finset.mem_image.mpr ⟨b, hbσ, rfl⟩
    rw [hMvbb] at hmem
    exact hmem
  have hXmem : bu_tkMv b t ∈ σ.image (bu_tkMv b) :=
    Finset.mem_image.mpr ⟨t, htσ, rfl⟩
  have hcompC : ∀ A ∈ σ.image (bu_tkMv b), ∀ B ∈ σ.image (bu_tkMv b),
      A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB
    rw [Finset.mem_image] at hA hB
    obtain ⟨z, hz, rfl⟩ := hA
    obtain ⟨w, hw, rfl⟩ := hB
    rcases hchainσ.2 z hz w hw with h | h
    · exact Or.inl ((bu_tkMv_le_iff hbt (hbot z hz) (htop z hz)
        (hbot w hw) (htop w hw)).mp h)
    · exact Or.inr ((bu_tkMv_le_iff hbt (hbot w hw) (htop w hw)
        (hbot z hz) (htop z hz)).mp h)
  have hgap := bu_gap_lemma hsubX hempty hXmem hcompC
  have hExtEmpty : bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t) = ∅ :=
    hgap.2.1 hCX
  set s0 : ℤ := (if β then 1 else -1) with hs0def
  have hs0 : s0 = 1 ∨ s0 = -1 := by
    rw [hs0def]
    by_cases hβ : β <;> simp [hβ]
  have hsign : (s0 = 1 → 0 ≤ t j) ∧ (s0 = -1 → t j ≤ 0) := by
    constructor <;> intro _ <;> omega
  have hs0dec : decide (0 < s0) = β := by
    rw [hs0def]
    cases β <;> simp
  have hPush_le : ∀ z ∈ σ, bu_tkLe z (bu_tkPush t j s0) :=
    fun z hz => bu_push_le_chain hs0 hsign htop hzn hjX hjt z hz
  have hPushchain : bu_tkChain (insert (bu_tkPush t j s0) σ) := by
    refine ⟨⟨t, Finset.mem_insert_of_mem htσ⟩, ?_⟩
    intro x hx y hy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
    · exact Or.inl (bu_tkLe_refl _)
    · exact Or.inr (hPush_le y hy')
    · have h := hPush_le x hx'
      exact Or.inl h
    · exact hchainσ.2 x hx' y hy'
  have hPushH := bu_push_height hs0 hsign
  have hPushnot := bu_push_notmem htop hPushH
  have hPushbox : bu_tkPush t j s0 ∈ bu_tkBox n m := by
    rw [bu_mem_tkBox]
    intro i
    by_cases hic : i = j
    · rw [hic]
      have e : (bu_tkPush t j s0) j = s0 := by simp [bu_tkPush, htj]
      rw [e]
      have habs : |s0| = 1 := by
        rw [hs0def]
        cases β <;> simp
      rw [habs]
      exact_mod_cast hm
    · have e : (bu_tkPush t j s0) i = t i := by simp [bu_tkPush, hic]
      rw [e]
      exact (bu_mem_tkBox.mp (hsub htσ)) i
  have hPushSgn : bu_tkSgn (bu_tkPush t j s0) = insert (β, j) (bu_tkSgn t) := by
    ext ⟨b', i⟩
    simp only [bu_mem_tkSgn]
    by_cases hic : i = j
    · rw [hic]
      have e : (bu_tkPush t j s0) j = s0 := by simp [bu_tkPush, htj]
      rw [e]
      constructor
      · rintro ⟨_, hβ'⟩
        rw [hs0dec] at hβ'
        rw [Finset.mem_insert]
        left
        exact Prod.ext_iff.mpr ⟨hβ', rfl⟩
      · intro h
        rw [Finset.mem_insert] at h
        rcases h with h | h
        · have h1 : b' = β := congrArg Prod.fst h
          have h2 : j = j := congrArg Prod.snd h
          refine ⟨by rw [hs0def]; cases β <;> simp, ?_⟩
          rw [h1, hs0dec]
        · rw [bu_mem_tkSgn] at h
          exact absurd h.1 (by rw [htj]; simp)
    · have e : (bu_tkPush t j s0) i = t i := by simp [bu_tkPush, hic]
      rw [e]
      constructor
      · rintro ⟨hne, hβ'⟩
        rw [Finset.mem_insert]
        right
        exact bu_mem_tkSgn.mpr ⟨hne, hβ'⟩
      · intro h
        rw [Finset.mem_insert] at h
        rcases h with h | h
        · have h2 : i = j := congrArg Prod.snd h
          exact absurd h2 hic
        · exact bu_mem_tkSgn.mp h
  have hPushS : bu_tkS (insert (bu_tkPush t j s0) σ) = insert (β, j) (bu_tkS σ) := by
    have hall : ∀ z ∈ insert (bu_tkPush t j s0) σ, bu_tkLe z (bu_tkPush t j s0) := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with hzv | hz
      · rw [hzv]
        exact bu_tkLe_refl _
      · exact hPush_le z hz
    have h := bu_tkS_of_top hPushchain (Finset.mem_insert_self _ _) hall
    rw [h, hPushSgn, hSeq]
  have hv0mem : bu_tkPush t j s0 ∈ bu_tkUpL m σ (β, j) := by
    rw [bu_mem_tkUpL]
    exact ⟨hPushbox, hPushnot, hPushchain, hPushS⟩
  have hUpEq : bu_tkUpL m σ (β, j) = {bu_tkPush t j s0} := by
    ext v
    rw [Finset.mem_singleton]
    constructor
    · intro hv
      rw [bu_mem_tkUpL] at hv
      obtain ⟨hvbox, hvnot, hvchain, hvS⟩ := hv
      have htri := bu_cofacet_pos hbσ htσ hvchain hvnot
      rcases htri with ⟨hbv, hvt⟩ | ⟨hvb, hne⟩ | ⟨htv, hne⟩
      · have hmem := bu_inside_mem_ext hbt hbot htop hvchain hbv hvt hvnot
        rw [hExtEmpty] at hmem
        exact (Finset.notMem_empty _ hmem).elim
      · have hcomp : bu_tkLe v t ∨ bu_tkLe t v :=
          hvchain.2 v (Finset.mem_insert_self v σ) t
            (Finset.mem_insert_of_mem htσ)
        have hvt' : bu_tkLe v t := bu_tkLe_trans_of_comparable hvb hbt hcomp
        have hall : ∀ z ∈ insert v σ, bu_tkLe z t := by
          intro z hz
          rw [Finset.mem_insert] at hz
          rcases hz with hzv | hz
          · rw [hzv]
            exact hvt'
          · exact htop z hz
        have hSame : bu_tkS (insert v σ) = bu_tkS σ := by
          have h := bu_tkS_of_top hvchain (Finset.mem_insert_of_mem htσ) hall
          rw [h, hSeq]
        have hcon : (β, j) ∈ bu_tkS σ := by
          rw [← hSame, hvS]
          exact Finset.mem_insert_self (β, j) _
        exact absurd hcon hℓ
      · have hE := bu_above_E hbt htop hbσ hvchain htv hne
        obtain ⟨hneE, hEX, hoff, hSv⟩ := hE
        have hSgv : bu_tkSgn v = insert (β, j) (bu_tkSgn t) := by
          rw [← hSv, hvS, hSeq]
        have hEsub : bu_tkMv t v ⊆ {j} := by
          intro i hiE
          have hiX : i ∉ bu_tkMv b t := hEX i hiE
          rw [hXT] at hiX
          have hti0 : t i = 0 := by
            by_contra hcon
            exact hiX (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcon⟩)
          have hvi : v i ≠ t i := by
            have hm := hiE
            rw [bu_tkMv, Finset.mem_filter] at hm
            exact hm.2
          have hvi0 : v i ≠ 0 := by
            rw [← hti0]
            exact hvi
          have hnew : (decide (0 < v i), i) ∈ bu_tkSgn v :=
            bu_mem_tkSgn.mpr ⟨hvi0, rfl⟩
          rw [hSgv] at hnew
          rw [Finset.mem_insert] at hnew
          rcases hnew with h | h
          · have hi : i = j := congrArg Prod.snd h
            exact Finset.mem_singleton.mpr hi
          · rw [bu_mem_tkSgn] at h
            exact absurd h.1 (by rw [hti0]; simp)
        have hE1 := bu_eq_singleton_of_sub hEsub hneE
        have hvj : v j = s0 := by
          have hjE : j ∈ bu_tkMv t v := by
            rw [hE1]
            exact Finset.mem_singleton_self j
          have hne_j : v j ≠ t j := by
            have hm := hjE
            rw [bu_tkMv, Finset.mem_filter] at hm
            exact hm.2
          have hdec : decide (0 < v j) = β := by
            have hmemj : (β, j) ∈ bu_tkSgn v := by
              rw [hSgv]
              exact Finset.mem_insert_self (β, j) _
            rw [bu_mem_tkSgn] at hmemj
            exact hmemj.2.symm
          have h1 := htv j
          rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
          · exact absurd c1 hne_j
          · have hpos : 0 < v j := by omega
            have hβt : β = true := by
              rw [← hdec]
              exact decide_eq_true hpos
            have hs : s0 = 1 := by simp [hs0def, hβt]
            rw [hs]
            omega
          · have hβf : β = false := by
              rw [← hdec]
              exact decide_eq_false (by omega : ¬ 0 < v j)
            have hs : s0 = -1 := by simp [hs0def, hβf]
            rw [hs]
            omega
        funext i
        by_cases hic : i = j
        · rw [hic, hvj]
          have e : bu_tkPush t j s0 j = s0 := by simp [bu_tkPush, htj]
          exact e.symm
        · have hvi : v i = t i := hoff i (by
            rw [hE1]
            simp [hic])
          have hpi : bu_tkPush t j s0 i = t i := by simp [bu_tkPush, hic]
          rw [hvi, hpi]
    · intro hv
      rw [hv]
      exact hv0mem
  rw [hUpEq, Finset.card_singleton]

/-! ## Label-removal count (pure finset combinatorics) -/

private theorem bu_label_image_cases {α β : Type*} [DecidableEq β]
    {σ : Finset α} {L : α → β} {S : Finset β}
    (hSsub : S ⊆ σ.image L) (hcard : σ.card = S.card + 1) :
    σ.image L = S ∨ ∃ ℓ, ℓ ∉ S ∧ σ.image L = insert ℓ S := by
  have himg_le : (σ.image L).card ≤ S.card + 1 :=
    le_trans Finset.card_image_le (le_of_eq hcard)
  have hDcard : (σ.image L \ S).card ≤ 1 := by
    have h := Finset.card_sdiff_of_subset hSsub
    omega
  by_cases hempty : σ.image L \ S = ∅
  · left
    exact Finset.Subset.antisymm
      (Finset.sdiff_eq_empty_iff_subset.mp hempty) hSsub
  · right
    have hne : (σ.image L \ S).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard1 : (σ.image L \ S).card = 1 := by
      have hpos : 0 < (σ.image L \ S).card := Finset.card_pos.mpr hne
      omega
    obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp hcard1
    have hℓmem : ℓ ∈ σ.image L \ S := by
      rw [hℓ]
      exact Finset.mem_singleton_self ℓ
    have hℓimg : ℓ ∈ σ.image L := (Finset.mem_sdiff.mp hℓmem).1
    have hℓnot : ℓ ∉ S := (Finset.mem_sdiff.mp hℓmem).2
    refine ⟨ℓ, hℓnot, ?_⟩
    ext y
    constructor
    · intro hy
      by_cases hyS : y ∈ S
      · exact Finset.mem_insert_of_mem hyS
      · have hmem : y ∈ σ.image L \ S := Finset.mem_sdiff.mpr ⟨hy, hyS⟩
        rw [hℓ] at hmem
        have hyℓ : y = ℓ := Finset.mem_singleton.mp hmem
        rw [hyℓ]
        exact Finset.mem_insert_self ℓ S
    · intro hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hyS
      · exact hℓimg
      · exact hSsub hyS

private theorem bu_label_removal_two {α β : Type*} [DecidableEq α] [DecidableEq β]
    {σ : Finset α} {L : α → β} {S : Finset β}
    (hcard : σ.card = S.card + 1) (himg : σ.image L = S) :
    (σ.filter (fun w => S ⊆ (σ.erase w).image L)).card = 2 := by
  have hlt : S.card < σ.card := by omega
  have hmaps : Set.MapsTo L (↑σ : Set α) (↑S : Set β) := by
    intro x hx
    have hx' : x ∈ σ := Finset.mem_coe.mp hx
    have hL : L x ∈ σ.image L := Finset.mem_image.mpr ⟨x, hx', rfl⟩
    rw [himg] at hL
    exact Finset.mem_coe.mpr hL
  obtain ⟨x, hxσ, y, hyσ, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hDn : ∀ w : α, w ∈ σ.filter (fun w => S ⊆ (σ.erase w).image L) ↔ w = x ∨ w = y := by
    intro w
    constructor
    · intro hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hwσ, hsubw⟩ := hw
      by_cases hwx : w = x
      · exact Or.inl hwx
      · by_cases hwy : w = y
        · exact Or.inr hwy
        · exfalso
          have hxE : x ∈ σ.erase w :=
            Finset.mem_erase.mpr ⟨fun h => hwx h.symm, hxσ⟩
          have hyE : y ∈ σ.erase w :=
            Finset.mem_erase.mpr ⟨fun h => hwy h.symm, hyσ⟩
          have hcardE : (σ.erase w).card = S.card := by
            rw [Finset.card_erase_of_mem hwσ]
            omega
          have heqS : (σ.erase w).image L = S := by
            have hle : ((σ.erase w).image L).card ≤ S.card := by
              calc ((σ.erase w).image L).card ≤ (σ.erase w).card :=
                    Finset.card_image_le
                _ = S.card := hcardE
            exact (Finset.eq_of_subset_of_card_le hsubw hle).symm
          have hinj : Set.InjOn L (↑(σ.erase w) : Set α) := by
            have hc : ((σ.erase w).image L).card = (σ.erase w).card := by
              rw [heqS, hcardE]
            exact Finset.card_image_iff.mp hc
          have hcon : x = y := hinj (Finset.mem_coe.mpr hxE)
            (Finset.mem_coe.mpr hyE) heq
          exact hne hcon
    · intro hw
      have hSsub : S ⊆ σ.image L := by rw [himg]
      rcases hw with hwx | hwy
      · rw [hwx, Finset.mem_filter]
        refine ⟨hxσ, ?_⟩
        intro s hs
        have hsimg : s ∈ σ.image L := hSsub hs
        obtain ⟨z, hzσ, hLz⟩ := Finset.mem_image.mp hsimg
        by_cases hzx : z = x
        · rw [hzx] at hLz
          have hLy : L y = s := heq.symm.trans hLz
          exact Finset.mem_image.mpr ⟨y,
            Finset.mem_erase.mpr ⟨Ne.symm hne, hyσ⟩, hLy⟩
        · exact Finset.mem_image.mpr ⟨z,
            Finset.mem_erase.mpr ⟨hzx, hzσ⟩, hLz⟩
      · rw [hwy, Finset.mem_filter]
        refine ⟨hyσ, ?_⟩
        intro s hs
        have hsimg : s ∈ σ.image L := hSsub hs
        obtain ⟨z, hzσ, hLz⟩ := Finset.mem_image.mp hsimg
        by_cases hzy : z = y
        · rw [hzy] at hLz
          have hLx : L x = s := heq.trans hLz
          exact Finset.mem_image.mpr ⟨x,
            Finset.mem_erase.mpr ⟨hne, hxσ⟩, hLx⟩
        · exact Finset.mem_image.mpr ⟨z,
            Finset.mem_erase.mpr ⟨hzy, hzσ⟩, hLz⟩
  have hEq : σ.filter (fun w => S ⊆ (σ.erase w).image L) = {x, y} := by
    ext w
    rw [hDn, Finset.mem_insert, Finset.mem_singleton]
  rw [hEq, Finset.card_pair_eq_two_iff.mpr hne]

private theorem bu_label_removal_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    {σ : Finset α} {L : α → β} {S : Finset β} {ℓ : β}
    (hcard : σ.card = S.card + 1) (hℓ : ℓ ∉ S) (himg : σ.image L = insert ℓ S) :
    σ.filter (fun w => S ⊆ (σ.erase w).image L) =
      σ.filter (fun w => L w = ℓ) ∧
    (σ.filter (fun w => S ⊆ (σ.erase w).image L)).card = 1 := by
  have hcardI : (insert ℓ S).card = S.card + 1 := Finset.card_insert_of_notMem hℓ
  have hinj : Set.InjOn L (↑σ : Set α) := by
    have hc : (σ.image L).card = σ.card := by rw [himg, hcardI, ← hcard]
    exact Finset.card_image_iff.mp hc
  have hEq : σ.filter (fun w => S ⊆ (σ.erase w).image L) =
      σ.filter (fun w => L w = ℓ) := by
    ext w
    by_cases hwσ : w ∈ σ
    · rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · intro h
        obtain ⟨_, hsubw⟩ := h
        by_contra hcon
        have hwimg : L w ∈ σ.image L :=
          Finset.mem_image.mpr ⟨w, hwσ, rfl⟩
        rw [himg] at hwimg
        rw [Finset.mem_insert] at hwimg
        rcases hwimg with hℓw | hSw
        · exact hcon ⟨hwσ, hℓw⟩
        · have hnot : L w ∉ (σ.erase w).image L := by
            intro hcon2
            obtain ⟨z, hzE, hLz⟩ := Finset.mem_image.mp hcon2
            have hzσ : z ∈ σ := Finset.mem_of_mem_erase hzE
            have hzw : z ≠ w := Finset.ne_of_mem_erase hzE
            have hzw' : z = w := hinj (Finset.mem_coe.mpr hzσ)
              (Finset.mem_coe.mpr hwσ) hLz
            exact hzw hzw'
          exact hnot (hsubw hSw)
      · intro h
        obtain ⟨hwσ', hLw⟩ := h
        refine ⟨hwσ', ?_⟩
        intro s hs
        have hSsub : S ⊆ σ.image L := by rw [himg]; exact Finset.subset_insert ℓ S
        have hsimg : s ∈ σ.image L := hSsub hs
        obtain ⟨z, hzσ, hLz⟩ := Finset.mem_image.mp hsimg
        have hzw : z ≠ w := by
          intro hcon
          rw [hcon] at hLz
          rw [← hLz] at hs
          rw [hLw] at hs
          exact hℓ hs
        exact Finset.mem_image.mpr ⟨z, Finset.mem_erase.mpr ⟨hzw, hzσ⟩, hLz⟩
    · rw [Finset.mem_filter, Finset.mem_filter]
      simp [hwσ]
  refine ⟨hEq, ?_⟩
  rw [hEq]
  obtain ⟨w0, hw0σ, hL0⟩ : ∃ w0 ∈ σ, L w0 = ℓ := by
    have hmem : ℓ ∈ σ.image L := by rw [himg]; exact Finset.mem_insert_self ℓ S
    obtain ⟨w0, hw0σ, hL0⟩ := Finset.mem_image.mp hmem
    exact ⟨w0, hw0σ, hL0⟩
  have hsingle : σ.filter (fun w => L w = ℓ) = {w0} := by
    ext w
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨hwσ, hLw⟩ := h
      have he : w = w0 := hinj (Finset.mem_coe.mpr hwσ)
        (Finset.mem_coe.mpr hw0σ) (by rw [hLw, hL0])
      exact he
    · intro h
      rw [h]
      exact ⟨hw0σ, hL0⟩
  rw [hsingle, Finset.card_singleton]

/-! ## Bridge lemmas between neighbor finsets and counters -/

/-- Insert map `v ↦ insert v σ` is injective on points outside `σ`. -/
private theorem bu_insert_inj_of_notMem {n : ℕ} {σ : Finset (Fin n → ℤ)}
    {v₁ v₂ : Fin n → ℤ} (h₁ : v₁ ∉ σ)
    (he : insert v₁ σ = insert v₂ σ) : v₁ = v₂ := by
  have hm : v₁ ∈ insert v₂ σ := he ▸ Finset.mem_insert_self v₁ σ
  rw [Finset.mem_insert] at hm
  rcases hm with h | h
  · exact h
  · exact absurd h h₁

/-- Erase map `w ↦ σ.erase w` is injective on members of `σ`. -/
private theorem bu_erase_inj {n : ℕ} {σ : Finset (Fin n → ℤ)}
    {w₁ w₂ : Fin n → ℤ} (h₁ : w₁ ∈ σ)
    (he : σ.erase w₁ = σ.erase w₂) : w₁ = w₂ := by
  by_contra hne
  have hm1 : w₁ ∈ σ.erase w₂ := Finset.mem_erase.mpr ⟨hne, h₁⟩
  have hm2 : w₁ ∈ σ.erase w₁ := he.symm ▸ hm1
  exact Finset.notMem_erase w₁ σ hm2

/-- For tight happy chains, the up-neighbor filter coincides with `bu_tkUp`. -/
private theorem bu_upFin_tight_card {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (himg : σ.image L = bu_tkS σ) :
    (bu_upFin m L σ).card = (bu_tkUp m σ).card := by
  have hfilter : ((bu_tkBox n m).filter fun v =>
      v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ σ.image L) =
      ((bu_tkBox n m).filter fun v =>
        v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ bu_tkS σ) := by
    rw [himg]
  have hinj : Set.InjOn (fun v => insert v σ)
      (↑((bu_tkBox n m).filter fun v =>
        v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ bu_tkS σ) :
        Set (Fin n → ℤ)) := by
    intro v₁ hv₁ v₂ hv₂ he
    have h₁ : v₁ ∉ σ := (Finset.mem_filter.mp (Finset.mem_coe.mp hv₁)).2.1
    exact bu_insert_inj_of_notMem h₁ he
  rw [bu_upFin, hfilter, bu_tkUp, Finset.card_image_of_injOn hinj]

/-- The singleton `{0}` is never on the boundary when `1 ≤ m`. -/
private theorem bu_singleton_not_bdry {n m : ℕ} (hm : 1 ≤ m) :
    ¬ bu_tkBdry m ({0} : Finset (Fin n → ℤ)) := by
  intro hbd
  obtain ⟨i, hi⟩ := hbd 0 (Finset.mem_singleton_self 0)
  simp at hi
  omega

/-- Down-neighbors of `{0}` are empty (erasing leaves nothing). -/
private theorem bu_down_singleton {n : ℕ} {L : (Fin n → ℤ) → Bool × Fin n} :
    bu_downFin L ({0} : Finset (Fin n → ℤ)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨w, hwF, _⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_filter] at hwF
  obtain ⟨hwσ, hne, _⟩ := hwF
  rw [Finset.mem_singleton] at hwσ
  subst hwσ
  simp at hne

/-- For loose chains with a new label, up-neighbors gain exactly `ℓ`. -/
private theorem bu_upFin_loose_new_card {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} {ℓ : Bool × Fin n}
    (hchainσ : bu_tkChain σ) (hc : σ.card = (bu_tkS σ).card + 1)
    (himg : σ.image L = insert ℓ (bu_tkS σ)) (hℓ : ℓ ∉ bu_tkS σ) :
    (bu_upFin m L σ).card = (bu_tkUpL m σ ℓ).card := by
  have hfilter : ((bu_tkBox n m).filter fun v =>
      v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ σ.image L) =
      ((bu_tkBox n m).filter fun v =>
        v ∉ σ ∧ bu_tkChain (insert v σ) ∧
          bu_tkS (insert v σ) = insert ℓ (bu_tkS σ)) := by
    ext v
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hvbox, hvnot, hchain, hcover⟩
      refine ⟨hvbox, hvnot, hchain, ?_⟩
      rw [himg] at hcover
      have hstrict := bu_loose_strict_growth hchainσ hc hvbox hvnot hchain
      have hsub1 : bu_tkS σ ⊆ bu_tkS (insert v σ) :=
        Finset.sup_mono (Finset.subset_insert v σ)
      have hlt : (bu_tkS σ).card < (bu_tkS (insert v σ)).card :=
        Finset.card_lt_card hstrict
      have hle : (bu_tkS (insert v σ)).card ≤ (insert ℓ (bu_tkS σ)).card :=
        Finset.card_le_card hcover
      have hinter : (insert ℓ (bu_tkS σ)).card = (bu_tkS σ).card + 1 :=
        Finset.card_insert_of_notMem hℓ
      have heq : (bu_tkS (insert v σ)).card = (insert ℓ (bu_tkS σ)).card := by
        omega
      exact Finset.eq_of_subset_of_card_le hcover (le_of_eq heq.symm)
    · rintro ⟨hvbox, hvnot, hchain, heq⟩
      refine ⟨hvbox, hvnot, hchain, ?_⟩
      rw [heq, himg]
  have hinj : Set.InjOn (fun v => insert v σ)
      (↑((bu_tkBox n m).filter fun v =>
        v ∉ σ ∧ bu_tkChain (insert v σ) ∧
          bu_tkS (insert v σ) = insert ℓ (bu_tkS σ)) :
        Set (Fin n → ℤ)) := by
    intro v₁ hv₁ v₂ hv₂ he
    have h₁ : v₁ ∉ σ := (Finset.mem_filter.mp (Finset.mem_coe.mp hv₁)).2.1
    exact bu_insert_inj_of_notMem h₁ he
  rw [bu_upFin, hfilter, bu_tkUpL, Finset.card_image_of_injOn hinj]

/-- When `2 ≤ σ.card`, the nonemptiness guard in `bu_downFin` is automatic. -/
private theorem bu_downFin_card_of_two_le {n : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (h2 : 2 ≤ σ.card) :
    (bu_downFin L σ).card =
      (σ.filter fun w => bu_tkS σ ⊆ (σ.erase w).image L).card := by
  have hfilter : (σ.filter fun w =>
      (σ.erase w).Nonempty ∧ bu_tkS σ ⊆ (σ.erase w).image L) =
      (σ.filter fun w => bu_tkS σ ⊆ (σ.erase w).image L) := by
    ext w
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hwσ, _, hcover⟩
      exact ⟨hwσ, hcover⟩
    · rintro ⟨hwσ, hcover⟩
      refine ⟨hwσ, ?_, hcover⟩
      rw [← Finset.card_pos]
      rw [Finset.card_erase_of_mem hwσ]
      omega
  have hinj : Set.InjOn (fun w => σ.erase w)
      (↑(σ.filter fun w => bu_tkS σ ⊆ (σ.erase w).image L) : Set (Fin n → ℤ)) := by
    intro w₁ hw₁ w₂ hw₂ he
    have h₁ : w₁ ∈ σ := (Finset.mem_filter.mp (Finset.mem_coe.mp hw₁)).1
    exact bu_erase_inj h₁ he
  rw [bu_downFin, hfilter, Finset.card_image_of_injOn hinj]

/-- Antipodal counter on the boundary. -/
private theorem bu_anti_card_pos {n m : ℕ} {σ : Finset (Fin n → ℤ)}
    (hb : bu_tkBdry m σ) : (bu_antiFin m σ).card = 1 := by
  simp [bu_anti_card, hb]

/-- Antipodal counter off the boundary. -/
private theorem bu_anti_card_neg {n m : ℕ} {σ : Finset (Fin n → ℤ)}
    (hb : ¬ bu_tkBdry m σ) : (bu_antiFin m σ).card = 0 := by
  simp [bu_anti_card, hb]

/-- Unhappy vertices are isolated. -/
private theorem bu_degree_not_happy {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m} {σ : bu_tkV n m} (hnh : ¬ bu_tkHappy m L σ.val) :
    (bu_tkG n m L hm).degree σ = 0 := by
  have hempty : (bu_tkG n m L hm).neighborFinset σ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro τ hτ
    rw [SimpleGraph.mem_neighborFinset] at hτ
    exact hnh hτ.1
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hempty, Finset.card_empty]

/-- The vertex `{0}` has degree one. -/
private theorem bu_degree_singleton {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    {σ : bu_tkV n m} (hval : σ.val = ({0} : Finset (Fin n → ℤ))) :
    (bu_tkG n m L hm).degree σ = 1 := by
  have hS : bu_tkS ({0} : Finset (Fin n → ℤ)) = ∅ := by
    rw [bu_tkS, Finset.sup_singleton, bu_tkSgn_zero]
  have hσ : bu_tkHappy m L σ.val := by
    rw [hval]
    exact bu_zero_happy.1
  have hdeg := bu_degree_eq (hm := hm) hanti hσ
  have hup : (bu_upFin m L σ.val).card = 1 := by
    have hc0 : ({0} : Finset (Fin n → ℤ)).card =
        (bu_tkS ({0} : Finset (Fin n → ℤ))).card + 1 :=
      (bu_zero_happy (n := n) (m := m) (L := L)).2
    have hchain0 : bu_tkChain ({0} : Finset (Fin n → ℤ)) :=
      (bu_zero_happy (n := n) (m := m) (L := L)).1.2.1
    have himg0 : (({0} : Finset (Fin n → ℤ)).image L) =
        insert (L 0) (bu_tkS ({0} : Finset (Fin n → ℤ))) := by
      rw [hS]
      ext y
      simp
    have hℓ0 : (L 0) ∉ bu_tkS ({0} : Finset (Fin n → ℤ)) := by
      rw [hS]
      exact Finset.notMem_empty _
    have hℓn0 : bu_tkNeg (L 0) ∉ bu_tkS ({0} : Finset (Fin n → ℤ)) := by
      rw [hS]
      exact Finset.notMem_empty _
    have hsub0 : ({0} : Finset (Fin n → ℤ)) ⊆ bu_tkBox n m := by
      intro z hz
      rw [Finset.mem_singleton] at hz
      rw [hz]
      exact bu_zero_mem_tkBox
    calc (bu_upFin m L σ.val).card = (bu_upFin m L {0}).card := by rw [hval]
      _ = (bu_tkUpL m {0} (L 0)).card := by
          exact bu_upFin_loose_new_card hchain0 hc0 himg0 hℓ0
      _ = 1 := bu_loose_upL_card hm hsub0 hchain0 hc0 hℓ0 hℓn0
  have hdown : (bu_downFin L σ.val).card = 0 := by
    rw [hval, bu_down_singleton, Finset.card_empty]
  have hanti0 : (bu_antiFin m σ.val).card = 0 := by
    rw [hval]
    exact bu_anti_card_neg (bu_singleton_not_bdry hm)
  rw [hdeg, hup, hdown, hanti0]

/-- Happy vertices other than `{0}` have degree two (tight case). -/
private theorem bu_degree_tight {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val)
    (hc : σ.val.card = (bu_tkS σ.val).card) :
    (bu_tkG n m L hm).degree σ = 2 := by
  have himg := bu_happy_tight_image hσ hc
  have hup : (bu_upFin m L σ.val).card = (bu_tkUp m σ.val).card :=
    bu_upFin_tight_card himg
  have hdown : (bu_downFin L σ.val).card = 0 := by
    rw [bu_down_tight hσ.2.1 hc, Finset.card_empty]
  have hcount := bu_tight_cofacet_count hm hσ.1 hσ.2.1 hc
  rw [bu_degree_eq (hm := hm) hanti hσ, hup, hdown]
  by_cases hb : bu_tkBdry m σ.val
  · rw [bu_anti_card_pos hb, hcount.1 hb]
  · rw [bu_anti_card_neg hb, hcount.2 hb]

/-- Happy loose vertices covered by `S` have degree two. -/
private theorem bu_degree_loose_eq {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val)
    (hc : σ.val.card = (bu_tkS σ.val).card + 1)
    (himg : σ.val.image L = bu_tkS σ.val) (hne : σ.val ≠ ({0} : Finset (Fin n → ℤ))) :
    (bu_tkG n m L hm).degree σ = 2 := by
  have hup0 : (bu_upFin m L σ.val).card = 0 := by
    rw [bu_up_loose_eq hσ hc himg, Finset.card_empty]
  have hSne : bu_tkS σ.val ≠ ∅ := by
    intro hcon
    exact hne ((bu_happy_empty_iff hσ.2.1).mp hcon)
  have hSpos : 1 ≤ (bu_tkS σ.val).card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hSne)
  have h2 : 2 ≤ σ.val.card := by omega
  have hdown2 : (bu_downFin L σ.val).card = 2 := by
    rw [bu_downFin_card_of_two_le h2, bu_label_removal_two hc himg]
  have hnb : ¬ bu_tkBdry m σ.val := bu_loose_not_bdry hm hσ.1 hσ.2.1 hc
  rw [bu_degree_eq (hm := hm) hanti hσ, hup0, hdown2, bu_anti_card_neg hnb]

/-- Happy loose vertices with a new label have degree two (unless `{0}`). -/
private theorem bu_degree_loose_new {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    (hN : bu_tkNoCompl m L)
    {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val)
    (hc : σ.val.card = (bu_tkS σ.val).card + 1)
    {ℓ : Bool × Fin n} (hℓnot : ℓ ∉ bu_tkS σ.val)
    (himg : σ.val.image L = insert ℓ (bu_tkS σ.val))
    (hne : σ.val ≠ ({0} : Finset (Fin n → ℤ))) :
    (bu_tkG n m L hm).degree σ = 2 := by
  obtain ⟨hℓn, _⟩ := bu_happy_loose_neg hσ hN hℓnot himg
  have hup1 : (bu_upFin m L σ.val).card = 1 := by
    rw [bu_upFin_loose_new_card hσ.2.1 hc himg hℓnot,
      bu_loose_upL_card hm hσ.1 hσ.2.1 hc hℓnot hℓn]
  have h1pos : 1 ≤ σ.val.card := Finset.card_pos.mpr hσ.2.1.1
  have h2 : 2 ≤ σ.val.card := by
    by_contra hcon
    have h1 : σ.val.card = 1 := by omega
    have hScard : (bu_tkS σ.val).card = 0 := by omega
    have hS : bu_tkS σ.val = ∅ := Finset.card_eq_zero.mp hScard
    exact hne ((bu_happy_empty_iff hσ.2.1).mp hS)
  have hdown1 : (bu_downFin L σ.val).card = 1 := by
    rw [bu_downFin_card_of_two_le h2, (bu_label_removal_one hc hℓnot himg).2]
  have hnb : ¬ bu_tkBdry m σ.val := bu_loose_not_bdry hm hσ.1 hσ.2.1 hc
  rw [bu_degree_eq (hm := hm) hanti hσ, hup1, hdown1, bu_anti_card_neg hnb]

/-- Full degree classification: happy non-singletons have degree two. -/
private theorem bu_degree_happy_two {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    (hN : bu_tkNoCompl m L)
    {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val)
    (hne : σ.val ≠ ({0} : Finset (Fin n → ℤ))) :
    (bu_tkG n m L hm).degree σ = 2 := by
  rcases bu_happy_card hσ with hc | hc
  · exact bu_degree_tight hanti hσ hc
  · rcases bu_label_image_cases hσ.2.2 hc with himg | ⟨ℓ, hℓnot, himg⟩
    · exact bu_degree_loose_eq hanti hσ hc himg hne
    · exact bu_degree_loose_new hanti hN hσ hc hℓnot himg hne

/-- Odd degrees mark exactly the `{0}` vertex. -/
private theorem bu_degree_odd_iff {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    (hN : bu_tkNoCompl m L) {σ : bu_tkV n m} :
    Odd ((bu_tkG n m L hm).degree σ) ↔ σ.val = ({0} : Finset (Fin n → ℤ)) := by
  constructor
  · intro hodd
    by_contra hne
    by_cases hσ : bu_tkHappy m L σ.val
    · have h2 := bu_degree_happy_two (hm := hm) hanti hN hσ hne
      rw [h2] at hodd
      exact (by simp : ¬ Odd 2) hodd
    · have h0 := bu_degree_not_happy (hm := hm) hσ
      rw [h0] at hodd
      exact (by simp : ¬ Odd 0) hodd
  · intro hval
    rw [bu_degree_singleton hanti hval]
    exact odd_one

/-! ## Lift from the cube to the upper hemisphere -/

/-- The unnormalized lift `x ↦ (1 - ‖x‖, x)` into `ℝ^(n+1)`. -/
private def buV (n : ℕ) (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cons (α := fun _ => ℝ) (1 - ‖x‖) x)

/-- The lift never hits the origin. -/
private theorem buV_ne_zero {n : ℕ} (x : Fin n → ℝ) : buV n x ≠ 0 := by
  rw [buV]
  intro hcon
  have hcon' : Fin.cons (α := fun _ => ℝ) (1 - ‖x‖) x = (0 : Fin (n + 1) → ℝ) := by
    have h2 := congrArg WithLp.ofLp hcon
    simpa [WithLp.ofLp_toLp] using h2
  have hhead : (1 : ℝ) - ‖x‖ = 0 := by
    have h0 := congrFun hcon' (0 : Fin (n + 1))
    rw [Fin.cons_zero, Pi.zero_apply] at h0
    exact h0
  have hnorm : ‖x‖ = 1 := by
    have h := sub_eq_zero.mp hhead
    exact h.symm
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
  have htail := congrFun hcon' i.succ
  rw [Fin.cons_succ, Pi.zero_apply] at htail
  exact hi htail

/-- The unnormalized lift is continuous. -/
private theorem buV_continuous {n : ℕ} : Continuous (buV n) := by
  have hcons : Continuous
      (fun x : Fin n → ℝ => (Fin.cons ((1 : ℝ) - ‖x‖) x : Fin (n + 1) → ℝ)) :=
    Continuous.finCons (A := fun _ => ℝ)
      (continuous_const.sub continuous_norm : Continuous fun x : Fin n → ℝ => (1 : ℝ) - ‖x‖)
      continuous_id
  have hto : Continuous
      (fun y : Fin (n + 1) → ℝ => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (n + 1)))) := by
    fun_prop
  unfold buV
  exact hto.comp hcons

/-- The lift to the sphere (normalized). -/
private noncomputable def buLift (n : ℕ) (x : Fin n → ℝ) :
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨‖buV n x‖⁻¹ • buV n x, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm (buV_ne_zero x)⟩

/-- The lift to the sphere is continuous. -/
private theorem buLift_continuous {n : ℕ} : Continuous (buLift n) := by
  have hsmul : Continuous (fun x : Fin n → ℝ => ‖buV n x‖⁻¹ • buV n x) :=
    Continuous.smul
      (Continuous.inv₀ buV_continuous.norm
        (fun x => norm_ne_zero_iff.mpr (buV_ne_zero x)))
      buV_continuous
  exact Continuous.subtype_mk hsmul _

/-- On the boundary sphere, the unnormalized lift is odd. -/
private theorem buV_neg_of_norm_one {n : ℕ} {x : Fin n → ℝ} (h : ‖x‖ = 1) :
    buV n (-x) = -buV n x := by
  have hhead : (1 : ℝ) - ‖-x‖ = -((1 : ℝ) - ‖x‖) := by
    rw [norm_neg, h]
    norm_num
  have hcons : (Fin.cons ((1 : ℝ) - ‖-x‖) (-x) : Fin (n + 1) → ℝ) =
      -(Fin.cons ((1 : ℝ) - ‖x‖) x : Fin (n + 1) → ℝ) := by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp only [Fin.cons_zero, Pi.neg_apply]
      exact hhead
    · intro i
      simp only [Fin.cons_succ, Pi.neg_apply]
  simp only [buV, hcons, WithLp.toLp_neg]

/-- On the boundary sphere, the lift is odd. -/
private theorem buLift_neg_of_norm_one {n : ℕ} {x : Fin n → ℝ} (h : ‖x‖ = 1) :
    buLift n (-x) = -buLift n x := by
  apply Subtype.ext
  rw [coe_neg_sphere]
  change ‖buV n (-x)‖⁻¹ • buV n (-x) = -(‖buV n x‖⁻¹ • buV n x)
  rw [buV_neg_of_norm_one h, norm_neg, smul_neg]

/-! ## The odd map from the lift -/

/-- The difference map `x ↦ F (lift x) - F (-lift x)`, read off in coordinates. -/
private noncomputable def buG (n : ℕ)
    (F : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n))
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (F (buLift n x) - F (-buLift n x)).ofLp i

/-- The difference map is continuous. -/
private theorem buG_continuous {n : ℕ}
    {F : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n)}
    (hF : Continuous F) : Continuous (buG n F) := by
  have h1 : Continuous (fun x : Fin n → ℝ => F (buLift n x)) :=
    hF.comp buLift_continuous
  have h2 : Continuous (fun x : Fin n → ℝ => F (-buLift n x)) :=
    hF.comp (continuous_neg.comp buLift_continuous)
  have hsub : Continuous
      (fun x : Fin n → ℝ => F (buLift n x) - F (-buLift n x)) := h1.sub h2
  unfold buG
  exact continuous_pi fun i => (PiLp.continuous_apply 2 _ i).comp hsub

/-- On the boundary sphere, the difference map is odd. -/
private theorem buG_neg_of_norm_one {n : ℕ}
    {F : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n)}
    {x : Fin n → ℝ} (h : ‖x‖ = 1) : buG n F (-x) = -buG n F x := by
  have hL : buLift n (-x) = -buLift n x := buLift_neg_of_norm_one h
  funext i
  change (F (buLift n (-x)) - F (-buLift n (-x))).ofLp i =
    -((F (buLift n x) - F (-buLift n x)).ofLp i)
  rw [hL, neg_neg, ← neg_sub, WithLp.ofLp_neg, Pi.neg_apply]

/-- A zero of the difference map gives an antipodal pair for `F`. -/
private theorem buG_zero {n : ℕ}
    {F : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n)}
    {x : Fin n → ℝ} (h : buG n F x = 0) :
    F (buLift n x) = F (-buLift n x) := by
  have hsub : F (buLift n x) - F (-buLift n x) = 0 := by
    apply PiLp.ext
    intro i
    exact congrFun h i
  exact sub_eq_zero.mp hsub

/-! ## Argmax labelling -/

/-- Argmax index of `a : Fin n → ℝ` (any maximizer). -/
private noncomputable def buIdx {n : ℕ} [Nonempty (Fin n)] (a : Fin n → ℝ) : Fin n :=
  Classical.choose (Finset.exists_max_image Finset.univ a Finset.univ_nonempty)

/-- Maximality of the argmax. -/
private theorem buIdx_max {n : ℕ} [Nonempty (Fin n)] (a : Fin n → ℝ) (j : Fin n) :
    a j ≤ a (buIdx a) :=
  (Classical.choose_spec
    (Finset.exists_max_image Finset.univ a Finset.univ_nonempty)).2 j
    (Finset.mem_univ j)

/-- Argmax of absolute values. -/
private noncomputable def buI {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) : Fin n :=
  buIdx (fun i => |v i|)

/-- Maximality of the absolute-value argmax. -/
private theorem buI_max {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) (j : Fin n) :
    |v j| ≤ |v (buI v)| :=
  buIdx_max (fun i => |v i|) j

/-- The sup norm is the maximal absolute coordinate. -/
private theorem buI_norm {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) :
    ‖v‖ = |v (buI v)| := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    exact buI_max v i
  · rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm v (buI v)

/-- The argmax is negation-invariant (same absolute values, no tie-breaking). -/
private theorem buI_neg {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) :
    buI (-v) = buI v := by
  have heq : (fun i => |(-v) i|) = (fun i => |v i|) := by
    funext i
    rw [Pi.neg_apply, abs_neg]
  unfold buI
  rw [heq]

/-- The label: sign and argmax index. -/
private noncomputable def buLab {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) : Bool × Fin n :=
  (decide (0 < v (buI v)), buI v)

/-- A nonzero vector has a nonzero maximal coordinate. -/
private theorem buI_ne_zero_of_ne {n : ℕ} [Nonempty (Fin n)] {v : Fin n → ℝ}
    (hv : v ≠ 0) : v (buI v) ≠ 0 := by
  intro hcon
  apply hv
  funext j
  have hle : |v j| ≤ 0 := by
    have h := buI_max v j
    rw [hcon, abs_zero] at h
    exact h
  have hj : |v j| = 0 := le_antisymm hle (abs_nonneg _)
  exact abs_eq_zero.mp hj

/-- Labels flip antipodally on nonzero vectors. -/
private theorem buLab_neg {n : ℕ} [Nonempty (Fin n)] {v : Fin n → ℝ}
    (hv : v ≠ 0) : buLab (-v) = bu_tkNeg (buLab v) := by
  have hI : buI (-v) = buI v := buI_neg v
  have hne : v (buI v) ≠ 0 := buI_ne_zero_of_ne hv
  simp only [buLab, hI, bu_tkNeg, Pi.neg_apply, Prod.mk.injEq]
  refine ⟨?_, trivial⟩
  by_cases hpos : 0 < v (buI v)
  · rw [decide_eq_true hpos]
    have hneg : ¬ (0 : ℝ) < -(v (buI v)) :=
      not_lt.mpr (neg_nonpos.mpr hpos.le)
    rw [decide_eq_false hneg]
    rfl
  · have hlt : v (buI v) < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
    rw [decide_eq_false hpos, decide_eq_true (neg_pos.mpr hlt)]
    rfl

/-! ## Epsilon-delta for a nowhere-zero map -/

/-- A continuous nowhere-zero map on the unit sup-ball is bounded below,
and uniformly continuous there. -/
private theorem bu_eps_delta {n : ℕ} {g : (Fin n → ℝ) → (Fin n → ℝ)}
    (hg : Continuous g)
    (hne : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, g x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, ε ≤ ‖g x‖) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1,
        ∀ y ∈ Metric.closedBall (0 : Fin n → ℝ) 1,
          dist x y < δ → dist (g x) (g y) < ε := by
  have hcompact : IsCompact (Metric.closedBall (0 : Fin n → ℝ) 1) :=
    isCompact_closedBall _ _
  have h0mem : (0 : Fin n → ℝ) ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  obtain ⟨x0, hx0, hmin⟩ :=
    hcompact.exists_isMinOn ⟨0, h0mem⟩ hg.norm.continuousOn
  have hpos : 0 < ‖g x0‖ := norm_pos_iff.mpr (hne x0 hx0)
  refine ⟨‖g x0‖, hpos, (fun x hx => hmin hx), ?_⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hg.continuousOn) _ hpos
  exact ⟨δ, hδpos, hδ⟩

/-! ## Tucker's lemma -/

/-- Tucker's lemma on the grid: an antipodal labeling has a complementary edge. -/
private theorem bu_tucker {n m : ℕ} (h0 : 0 < m)
    {L : (Fin n → ℤ) → Bool × Fin n}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z)) :
    ∃ z ∈ bu_tkBox n m, ∃ w ∈ bu_tkBox n m,
      bu_tkLe z w ∧ L w = bu_tkNeg (L z) := by
  have hm : 1 ≤ m := h0
  by_contra hcon
  have hN : bu_tkNoCompl m L := by
    intro z hz w hw hle heq
    exact hcon ⟨z, hz, w, hw, hle, heq⟩
  have hmem0 : ({0} : Finset (Fin n → ℤ)) ∈ (bu_tkBox n m).powerset := by
    rw [Finset.mem_powerset]
    intro z hz
    rw [Finset.mem_singleton] at hz
    rw [hz]
    exact bu_zero_mem_tkBox
  set v0 : bu_tkV n m := ⟨{0}, hmem0⟩ with hv0def
  have hfilter : Finset.univ.filter
      (fun v => Odd ((bu_tkG n m L hm).degree v)) = {v0} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [bu_degree_odd_iff (hm := hm) hanti hN]
    constructor
    · intro hval
      exact Subtype.ext hval
    · intro he
      rw [he]
  have heven := SimpleGraph.even_card_odd_degree_vertices (bu_tkG n m L hm)
  rw [hfilter, Finset.card_singleton] at heven
  exact (by decide : ¬ Even (1 : ℕ)) heven

/-! ## The no-zero contradiction -/

/-- Grid points scaled into the unit cube. -/
private noncomputable def buPt {n : ℕ} (m : ℕ) (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i => ((z i : ℤ) : ℝ) / (m : ℝ)

/-- Coordinate access unfolds. -/
private theorem buPt_apply {n : ℕ} {m : ℕ} {z : Fin n → ℤ} {i : Fin n} :
    (buPt m z) i = ((z i : ℤ) : ℝ) / (m : ℝ) := rfl

/-- Grid points land in the closed unit ball. -/
private theorem buPt_mem {n m : ℕ} (hmR : (0 : ℝ) < (m : ℝ)) {z : Fin n → ℤ}
    (hz : z ∈ bu_tkBox n m) : buPt m z ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have hi : |z i| ≤ (m : ℤ) := (bu_mem_tkBox.mp hz) i
  have hiR : ((((|z i| : ℤ))) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi
  rw [Real.norm_eq_abs, buPt_apply, abs_div, abs_of_pos hmR, ← Int.cast_abs,
    div_le_one hmR]
  exact hiR

/-- Boundary grid points land on the unit sphere. -/
private theorem buPt_norm_one {n m : ℕ} (hmR : (0 : ℝ) < (m : ℝ)) {z : Fin n → ℤ}
    (hz : z ∈ bu_tkBox n m) (hbd : ∃ i, |z i| = (m : ℤ)) : ‖buPt m z‖ = 1 := by
  obtain ⟨i, hi⟩ := hbd
  have hiR : ((((|z i| : ℤ))) : ℝ) = (m : ℝ) := by exact_mod_cast hi
  have hle : ‖buPt m z‖ ≤ 1 := mem_closedBall_zero_iff.mp (buPt_mem hmR hz)
  have hge : (1 : ℝ) ≤ ‖buPt m z‖ := by
    have h1 := norm_le_pi_norm (buPt m z) i
    rw [Real.norm_eq_abs, buPt_apply, abs_div, abs_of_pos hmR, ← Int.cast_abs, hiR,
      div_self hmR.ne'] at h1
    exact h1
  exact le_antisymm hle hge

/-- The grid map commutes with negation. -/
private theorem buPt_neg {n m : ℕ} (z : Fin n → ℤ) :
    buPt m (-z) = -buPt m z := by
  funext i
  simp only [buPt_apply, Pi.neg_apply, Int.cast_neg, neg_div]

/-- Comparable grid points map to close cube points. -/
private theorem buPt_dist {n m : ℕ} (hmR : (0 : ℝ) < (m : ℝ)) {z w : Fin n → ℤ}
    (hle : bu_tkLe z w) : dist (buPt m z) (buPt m w) ≤ 1 / (m : ℝ) := by
  have h1m : (0 : ℝ) ≤ 1 / (m : ℝ) := le_of_lt (one_div_pos.mpr hmR)
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg h1m]
  intro i
  have hzw : |z i - w i| ≤ 1 := by
    have h := hle i
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h, sub_self, abs_zero]; norm_num
    · rw [h2]; norm_num
    · rw [h2]; norm_num
  have h1 : (((((|z i - w i| : ℤ)))) : ℝ) ≤ 1 := by exact_mod_cast hzw
  have e : ((buPt m z - buPt m w) i) = (((((z i - w i : ℤ)))) : ℝ) / (m : ℝ) := by
    rw [Pi.sub_apply, buPt_apply, buPt_apply, ← sub_div, ← Int.cast_sub]
  rw [Real.norm_eq_abs, e, abs_div, abs_of_pos hmR, ← Int.cast_abs,
    div_le_div_iff_of_pos_right hmR]
  exact h1

/-- An odd map on the cube has a zero in the unit ball. -/
private theorem bu_no_zero {n : ℕ} [Nonempty (Fin n)]
    {g : (Fin n → ℝ) → (Fin n → ℝ)} (hg : Continuous g)
    (hodd : ∀ x : Fin n → ℝ, ‖x‖ = 1 → g (-x) = -g x) :
    ∃ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, g x = 0 := by
  by_contra hcon
  have hne : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, g x ≠ 0 := by
    intro x hx heq
    exact hcon ⟨x, hx, heq⟩
  obtain ⟨ε, hεpos, hε, δ, hδpos, hδε⟩ := bu_eps_delta hg hne
  obtain ⟨m, hmgt⟩ := exists_nat_gt (1 / δ)
  have hδnn : (0 : ℝ) < 1 / δ := one_div_pos.mpr hδpos
  have hm0 : 0 < m := by
    have hR : (0 : ℝ) < (m : ℝ) := lt_trans hδnn hmgt
    exact_mod_cast hR
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have h1m : (1 : ℝ) / (m : ℝ) < δ := by
    have h := one_div_lt_one_div_of_lt hδnn hmgt
    rwa [one_div_one_div] at h
  have hbox : ∀ z ∈ bu_tkBox n m, buPt m z ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
    fun z hz => buPt_mem hmR hz
  have hnorm1 : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → ‖buPt m z‖ = 1 :=
    fun z hz hbd => buPt_norm_one hmR hz hbd
  have hPtneg : ∀ z : Fin n → ℤ, buPt m (-z) = -buPt m z := fun z => buPt_neg z
  have hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) →
      (fun z => buLab (g (buPt m z))) (-z) =
        bu_tkNeg ((fun z => buLab (g (buPt m z))) z) := by
    intro z hz hbd
    change buLab (g (buPt m (-z))) = bu_tkNeg (buLab (g (buPt m z)))
    have h1 : g (buPt m (-z)) = -g (buPt m z) := by
      rw [hPtneg]
      exact hodd _ (hnorm1 z hz hbd)
    rw [h1]
    exact buLab_neg (hne _ (hbox z hz))
  obtain ⟨z, hz, w, hw, hle, heq⟩ :=
    bu_tucker (L := fun z => buLab (g (buPt m z))) hm0 hanti
  have heq_fst : decide (0 < (g (buPt m w)) (buI (g (buPt m w)))) =
      !(decide (0 < (g (buPt m z)) (buI (g (buPt m z))))) :=
    congrArg Prod.fst heq
  have heq_snd : buI (g (buPt m w)) = buI (g (buPt m z)) := congrArg Prod.snd heq
  rw [heq_snd] at heq_fst
  have haI : (g (buPt m z)) (buI (g (buPt m z))) ≠ 0 :=
    buI_ne_zero_of_ne (hne _ (hbox z hz))
  have hbI : (g (buPt m w)) (buI (g (buPt m z))) ≠ 0 := by
    rw [← heq_snd]
    exact buI_ne_zero_of_ne (hne _ (hbox w hw))
  have hsign : (0 < (g (buPt m z)) (buI (g (buPt m z))) ∧
        (g (buPt m w)) (buI (g (buPt m z))) < 0) ∨
      ((g (buPt m z)) (buI (g (buPt m z))) < 0 ∧
        0 < (g (buPt m w)) (buI (g (buPt m z)))) := by
    by_cases hda : 0 < (g (buPt m z)) (buI (g (buPt m z)))
    · left
      refine ⟨hda, ?_⟩
      have hdb : decide (0 < (g (buPt m w)) (buI (g (buPt m z)))) = false := by
        rw [heq_fst, decide_eq_true hda, Bool.not_true]
      have hn : ¬ 0 < (g (buPt m w)) (buI (g (buPt m z))) := of_decide_eq_false hdb
      exact lt_of_le_of_ne (not_lt.mp hn) (fun he => hbI he)
    · right
      have halt : (g (buPt m z)) (buI (g (buPt m z))) < 0 :=
        lt_of_le_of_ne (not_lt.mp hda) (fun he => haI he)
      have hdb : decide (0 < (g (buPt m w)) (buI (g (buPt m z)))) = true := by
        rw [heq_fst, decide_eq_false hda, Bool.not_false]
      exact ⟨halt, of_decide_eq_true hdb⟩
  have hgap : |(g (buPt m z)) (buI (g (buPt m z)))| ≤
      |(g (buPt m z)) (buI (g (buPt m z))) - (g (buPt m w)) (buI (g (buPt m z)))| := by
    rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hle1 : (g (buPt m z)) (buI (g (buPt m z))) ≤
          (g (buPt m z)) (buI (g (buPt m z))) - (g (buPt m w)) (buI (g (buPt m z))) := by
        linarith
      rw [abs_of_pos h1]
      exact le_trans hle1 (le_abs_self _)
    · have hle1 : (g (buPt m z)) (buI (g (buPt m z))) -
          (g (buPt m w)) (buI (g (buPt m z))) ≤
          (g (buPt m z)) (buI (g (buPt m z))) := by
        linarith
      have hneg : (g (buPt m z)) (buI (g (buPt m z))) -
          (g (buPt m w)) (buI (g (buPt m z))) < 0 :=
        lt_of_le_of_lt hle1 h1
      rw [abs_of_neg h1, abs_of_neg hneg]
      linarith
  have hclose : dist (g (buPt m z)) (g (buPt m w)) < ε :=
    hδε _ (hbox z hz) _ (hbox w hw) (buPt_dist hmR hle |>.trans_lt h1m)
  have hfar : ε ≤ dist (g (buPt m z)) (g (buPt m w)) := by
    rw [dist_eq_norm]
    have h1 : |(g (buPt m z)) (buI (g (buPt m z))) -
        (g (buPt m w)) (buI (g (buPt m z)))| ≤ ‖g (buPt m z) - g (buPt m w)‖ := by
      have h2 := norm_le_pi_norm (g (buPt m z) - g (buPt m w)) (buI (g (buPt m z)))
      rwa [Real.norm_eq_abs, Pi.sub_apply] at h2
    have h3 : ‖g (buPt m z)‖ ≤ ‖g (buPt m z) - g (buPt m w)‖ := by
      rw [buI_norm (g (buPt m z))]
      exact le_trans hgap h1
    exact le_trans (hε _ (hbox z hz)) h3
  linarith

/--
**Borsuk–Ulam theorem.** Let $n$ be a natural number and let $S^n$ be the unit sphere in the
Euclidean space $\mathbb{R}^{n+1}$. For every continuous map $f \colon S^n \to \mathbb{R}^n$ there
is a point $x \in S^n$ with $f(x) = f(-x)$.

Proves `Wanted` entry `borsukUlam`.

Source: K. Borsuk,
Fund. Math. 20 (1933) 177–190 antipodal theorem; S. Ulam; J. Matoušek, Using the Borsuk–Ulam
Theorem; Lean states `EuclideanSpace ℝ (Fin (n+1))` to `Fin n` specialization.
-/
public theorem borsukUlam
    {n : ℕ} (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) :
    ∃ x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, f x = f (-x) := by
  cases n with
  | zero =>
    refine ⟨buLift 0 0, ?_⟩
    apply PiLp.ext
    intro i
    exact Fin.elim0 i
  | succ k =>
    have hg : Continuous (buG (k + 1) f) := buG_continuous hf
    have hodd : ∀ x : Fin (k + 1) → ℝ, ‖x‖ = 1 → buG (k + 1) f (-x) = -buG (k + 1) f x :=
      fun x hx => buG_neg_of_norm_one hx
    obtain ⟨x, _, hx0⟩ := bu_no_zero hg hodd
    exact ⟨buLift (k + 1) x, buG_zero hx0⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
