/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import MathlibExt.Combinatorics.Enumerative.Stirling

/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem zagCard_fullCycles (n : ℕ) (hn : 0 < n) :
    Fintype.card {σ : Equiv.Perm (Fin n) //
      Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 1} =
      (n - 1).factorial := by
  rw [card_perm_cycleCount_eq_stirlingFirst]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using Nat.stirlingFirst_one_right m

private theorem zagMultiset_card_le_sum (m : Multiset ℕ)
    (hm : ∀ a ∈ m, 1 ≤ a) : m.card ≤ m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
      have ha : 1 ≤ a := hm a (by simp)
      have hm' : ∀ b ∈ m, 1 ≤ b := by
        intro b hb
        exact hm b (by simp [hb])
      simp only [Multiset.card_cons, Multiset.sum_cons]
      have := ih hm'
      omega

private theorem zagCycleCount_even_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Even (n - (Multiset.card σ.cycleType +
      Fintype.card (Function.fixedPoints σ))) ↔
      Even (σ.cycleType.sum + Multiset.card σ.cycleType) := by
  rw [Equiv.Perm.card_fixedPoints]
  simp only [Fintype.card_fin]
  have hsum : σ.cycleType.sum ≤ n := by
    simpa using σ.sum_cycleType_le
  have hcard : Multiset.card σ.cycleType ≤ σ.cycleType.sum :=
    zagMultiset_card_le_sum σ.cycleType fun a ha =>
      (Equiv.Perm.two_le_of_mem_cycleType ha).trans' (by omega)
  have hsub :
      n - (Multiset.card σ.cycleType + (n - σ.cycleType.sum)) =
        σ.cycleType.sum - Multiset.card σ.cycleType := by
    omega
  rw [hsub]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r + Multiset.card σ.cycleType, ?_⟩
    omega
  · rintro ⟨r, hr⟩
    have hcr : Multiset.card σ.cycleType ≤ r := by omega
    refine ⟨r - Multiset.card σ.cycleType, ?_⟩
    omega

private theorem zagSign_eq_neg_one_pow_cycleCount {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    σ.sign = (-1 : ℤˣ) ^
      (n - (Multiset.card σ.cycleType +
        Fintype.card (Function.fixedPoints σ))) := by
  rw [Equiv.Perm.sign_of_cycleType]
  exact neg_one_pow_congr (zagCycleCount_even_iff σ).symm

private noncomputable def zagCycleMinPos {n : ℕ} (e π : Equiv.Perm (Fin n))
    (x : Fin n) : Fin n :=
  let orbitPositions := Finset.univ.filter fun i => π.SameCycle (e i) x
  orbitPositions.min' ⟨e.symm x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    simpa using (Equiv.Perm.SameCycle.rfl : π.SameCycle x x)⟩⟩

private theorem zagCycleMinPos_mem {n : ℕ} (e π : Equiv.Perm (Fin n))
    (x : Fin n) : π.SameCycle (e (zagCycleMinPos e π x)) x := by
  classical
  rw [zagCycleMinPos]
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter fun i => π.SameCycle (e i) x) _)).2

private theorem zagCycleMinPos_le {n : ℕ} (e π : Equiv.Perm (Fin n))
    {x y : Fin n} (hxy : π.SameCycle y x) :
    zagCycleMinPos e π x ≤ e.symm y := by
  classical
  exact Finset.min'_le _ _ (by simp [hxy])

private theorem zagCycleMinPos_eq_of_sameCycle {n : ℕ}
    (e π : Equiv.Perm (Fin n)) {x y : Fin n} (hxy : π.SameCycle x y) :
    zagCycleMinPos e π x = zagCycleMinPos e π y := by
  apply le_antisymm
  · simpa using zagCycleMinPos_le e π
      ((zagCycleMinPos_mem e π y).trans hxy.symm)
  · simpa using zagCycleMinPos_le e π
      ((zagCycleMinPos_mem e π x).trans hxy)

private noncomputable def zagQuotientMinPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    Quotient (Equiv.Perm.SameCycle.setoid π) → Fin n :=
  Quotient.lift (zagCycleMinPos e π)
    (fun _x _y h => zagCycleMinPos_eq_of_sameCycle e π h)

private noncomputable def zagCycleMinima {n : ℕ}
    (e π : Equiv.Perm (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => zagCycleMinPos e π (e i) = i

private theorem zag_mem_cycleMinima_iff {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (i : Fin n) :
    i ∈ zagCycleMinima e π ↔ zagCycleMinPos e π (e i) = i := by
  classical
  simp [zagCycleMinima]

private noncomputable def zagCycleQuotientEquivMinima {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    Quotient (Equiv.Perm.SameCycle.setoid π) ≃
      {i : Fin n // i ∈ zagCycleMinima e π} where
  toFun q := ⟨zagQuotientMinPos e π q, by
    rw [zag_mem_cycleMinima_iff]
    refine Quotient.inductionOn q ?_
    intro x
    change zagCycleMinPos e π (e (zagCycleMinPos e π x)) =
      zagCycleMinPos e π x
    exact zagCycleMinPos_eq_of_sameCycle e π
      (zagCycleMinPos_mem e π x)⟩
  invFun i := Quotient.mk _ (e i.1)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    exact zagCycleMinPos_mem e π x
  right_inv i := by
    apply Subtype.ext
    exact (zag_mem_cycleMinima_iff e π i.1).mp i.2

private theorem zag_card_cycleMinima {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    (zagCycleMinima e π).card = cycleQuotientCount π := by
  rw [cycleQuotientCount,
    Nat.card_congr (zagCycleQuotientEquivMinima e π),
    Nat.card_eq_fintype_card, Fintype.card_coe]

private theorem zag_cycleMinPos_mem_cycleMinima {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (x : Fin n) :
    zagCycleMinPos e π x ∈ zagCycleMinima e π := by
  rw [zag_mem_cycleMinima_iff]
  exact zagCycleMinPos_eq_of_sameCycle e π (zagCycleMinPos_mem e π x)

private theorem zagCycleMinima_not_same_of_lt {n : ℕ}
    (e π : Equiv.Perm (Fin n)) {i j : Fin n}
    (hi : i ∈ zagCycleMinima e π) (hj : j ∈ zagCycleMinima e π)
    (hij : i < j) : ¬π.SameCycle (e i) (e j) := by
  intro hsame
  have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
  rw [(zag_mem_cycleMinima_iff e π i).mp hi,
    (zag_mem_cycleMinima_iff e π j).mp hj] at hmin
  exact hij.ne hmin

private structure ZagMarkedTriple {n : ℕ}
    (e π : Equiv.Perm (Fin n)) where
  first : Fin n
  middle : Fin n
  third : Fin n
  first_mem : first ∈ zagCycleMinima e π
  middle_mem : middle ∈ zagCycleMinima e π
  third_mem : third ∈ zagCycleMinima e π
  first_lt_middle : first < middle
  middle_lt_third : middle < third

private noncomputable def ZagMarkedTriple.toFinset {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) : Finset (Fin n) :=
  {m.first, m.middle, m.third}

private theorem ZagMarkedTriple.toFinset_subset {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) :
    m.toFinset ⊆ zagCycleMinima e π := by
  intro x hx
  simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact m.first_mem
  · exact m.middle_mem
  · exact m.third_mem

private theorem ZagMarkedTriple.toFinset_card {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) :
    m.toFinset.card = 3 := by
  have hfm : m.first ≠ m.middle := ne_of_lt m.first_lt_middle
  have hmt : m.middle ≠ m.third := ne_of_lt m.middle_lt_third
  have hft : m.first ≠ m.third :=
    ne_of_lt (m.first_lt_middle.trans m.middle_lt_third)
  simp [ZagMarkedTriple.toFinset, hfm, hmt, hft]

private theorem zagMarkedTriple_ext {n : ℕ} {e π : Equiv.Perm (Fin n)}
    {m m' : ZagMarkedTriple e π}
    (hfirst : m.first = m'.first) (hmiddle : m.middle = m'.middle)
    (hthird : m.third = m'.third) : m = m' := by
  cases m
  cases m'
  simp_all

private noncomputable def zagMarkedTripleEquivPowerset {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    ZagMarkedTriple e π ≃
      {s : Finset (Fin n) // s ∈ (zagCycleMinima e π).powersetCard 3} := by
  classical
  let toMarked : ZagMarkedTriple e π →
      {s : Finset (Fin n) // s ∈ (zagCycleMinima e π).powersetCard 3} := fun m =>
    ⟨m.toFinset, Finset.mem_powersetCard.mpr
      ⟨m.toFinset_subset, m.toFinset_card⟩⟩
  refine Equiv.ofBijective toMarked ?_
  constructor
  · intro m m' hmm'
    have hset : m.toFinset = m'.toFinset := congrArg Subtype.val hmm'
    have hfirst_le (x : Fin n) (hx : x ∈ m.toFinset) : m.first ≤ x := by
      simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact le_rfl
      · exact m.first_lt_middle.le
      · exact (m.first_lt_middle.trans m.middle_lt_third).le
    have hfirst_le' (x : Fin n) (hx : x ∈ m'.toFinset) : m'.first ≤ x := by
      simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact le_rfl
      · exact m'.first_lt_middle.le
      · exact (m'.first_lt_middle.trans m'.middle_lt_third).le
    have hfirst : m.first = m'.first := le_antisymm
      (hfirst_le m'.first (by rw [hset]; simp [ZagMarkedTriple.toFinset]))
      (hfirst_le' m.first (by rw [← hset]; simp [ZagMarkedTriple.toFinset]))
    have hmm_le : m.middle ≤ m'.middle := by
      have hm : m'.middle ∈ m.toFinset := by
        rw [hset]
        simp [ZagMarkedTriple.toFinset]
      simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hm
      rcases hm with hm | hm | hm
      · exfalso
        apply m'.first_lt_middle.ne
        exact (hfirst.symm.trans hm.symm)
      · exact hm.symm.le
      · rw [hm]
        exact m.middle_lt_third.le
    have hmm_ge : m'.middle ≤ m.middle := by
      have hm : m.middle ∈ m'.toFinset := by
        rw [← hset]
        simp [ZagMarkedTriple.toFinset]
      simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hm
      rcases hm with hm | hm | hm
      · exfalso
        apply m.first_lt_middle.ne
        exact hfirst.trans hm.symm
      · exact hm.symm.le
      · rw [hm]
        exact m'.middle_lt_third.le
    have hmiddle : m.middle = m'.middle := le_antisymm hmm_le hmm_ge
    have hthird : m.third = m'.third := by
      have hm : m.third ∈ m'.toFinset := by
        rw [← hset]
        simp [ZagMarkedTriple.toFinset]
      simp only [ZagMarkedTriple.toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hm
      rcases hm with hm | hm | hm
      · exfalso
        apply (m.first_lt_middle.trans m.middle_lt_third).ne
        exact hfirst.trans hm.symm
      · exfalso
        apply m.middle_lt_third.ne
        exact hmiddle.trans hm.symm
      · exact hm
    exact zagMarkedTriple_ext hfirst hmiddle hthird
  · intro s
    have hcard : s.1.card = 3 := (Finset.mem_powersetCard.mp s.2).2
    let o := s.1.orderIsoOfFin hcard
    let m : ZagMarkedTriple e π := {
      first := (o 0).1
      middle := (o 1).1
      third := (o 2).1
      first_mem := (Finset.mem_powersetCard.mp s.2).1 (o 0).2
      middle_mem := (Finset.mem_powersetCard.mp s.2).1 (o 1).2
      third_mem := (Finset.mem_powersetCard.mp s.2).1 (o 2).2
      first_lt_middle := by
        exact o.lt_iff_lt.mpr (by decide)
      middle_lt_third := by
        exact o.lt_iff_lt.mpr (by decide)
    }
    refine ⟨m, Subtype.ext ?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      change x ∈ {m.first, m.middle, m.third} at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · rw [hx]
        change ↑(o 0) ∈ s.1
        exact (o 0).2
      · rw [hx]
        change ↑(o 1) ∈ s.1
        exact (o 1).2
      · rw [hx]
        change ↑(o 2) ∈ s.1
        exact (o 2).2
    · rw [ZagMarkedTriple.toFinset_card, hcard]

private noncomputable instance zagMarkedTripleFintype {n : ℕ}
    (e π : Equiv.Perm (Fin n)) : Fintype (ZagMarkedTriple e π) :=
  Fintype.ofEquiv
    {s : Finset (Fin n) // s ∈ (zagCycleMinima e π).powersetCard 3}
    (zagMarkedTripleEquivPowerset e π).symm

private def zagExceedance {n : ℕ} (e π : Equiv.Perm (Fin n)) (x : Fin n) : Prop :=
  e.symm x < e.symm (π x)

private def zagTrivialAntiExceedance {n : ℕ} (e π : Equiv.Perm (Fin n))
    (x : Fin n) : Prop :=
  π x = e (zagCycleMinPos e π x)

private def zagNontrivialAntiExceedance {n : ℕ} (e π : Equiv.Perm (Fin n))
    (x : Fin n) : Prop :=
  ¬zagExceedance e π x ∧ ¬zagTrivialAntiExceedance e π x

private theorem zagTrivialAntiExceedance_not_exceedance {n : ℕ}
    (e π : Equiv.Perm (Fin n)) {x : Fin n}
    (hx : zagTrivialAntiExceedance e π x) : ¬zagExceedance e π x := by
  intro hexc
  have hmin := zagCycleMinPos_le e π (x := x) (y := x) Equiv.Perm.SameCycle.rfl
  simp only [zagExceedance] at hexc
  simp only [zagTrivialAntiExceedance] at hx
  rw [hx, e.symm_apply_apply] at hexc
  exact (not_lt_of_ge hmin) hexc

private noncomputable def zagCycleTrivialAntiExceedanceEquiv {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    Quotient (Equiv.Perm.SameCycle.setoid π) ≃
      {x : Fin n // zagTrivialAntiExceedance e π x} := by
  classical
  let pick : Fin n → {x : Fin n // zagTrivialAntiExceedance e π x} := fun x => by
    let m := e (zagCycleMinPos e π x)
    refine ⟨π.symm m, ?_⟩
    have hzx : π.SameCycle (π.symm m) x := by
      simpa [m] using zagCycleMinPos_mem e π x
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hzx
    simp only [zagTrivialAntiExceedance, Equiv.apply_symm_apply]
    rw [hmin]
  have pick_eq (x y : Fin n) (hxy : π.SameCycle x y) : pick x = pick y := by
    apply Subtype.ext
    simp only [pick]
    rw [zagCycleMinPos_eq_of_sameCycle e π hxy]
  refine Equiv.ofBijective (Quotient.lift pick pick_eq) ?_
  constructor
  · intro a b hab
    refine Quotient.inductionOn₂ a b ?_ hab
    intro x y hxy
    apply Quotient.sound
    have hpred :
        π.symm (e (zagCycleMinPos e π x)) =
          π.symm (e (zagCycleMinPos e π y)) :=
      congrArg Subtype.val hxy
    have hmin : e (zagCycleMinPos e π x) = e (zagCycleMinPos e π y) :=
      π.symm.injective hpred
    exact (zagCycleMinPos_mem e π x).symm.trans
      ((hmin.sameCycle π).trans (zagCycleMinPos_mem e π y))
  · rintro ⟨x, hx⟩
    refine ⟨Quotient.mk _ x, ?_⟩
    apply Subtype.ext
    change π.symm (e (zagCycleMinPos e π x)) = x
    rw [← hx]
    exact π.symm_apply_apply x

private theorem zagCard_trivialAntiExceedances {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    Nat.card {x : Fin n // zagTrivialAntiExceedance e π x} =
      cycleQuotientCount π := by
  rw [cycleQuotientCount]
  exact (Nat.card_congr (zagCycleTrivialAntiExceedanceEquiv e π)).symm

private def zagNontrivialAntiExceedanceEquiv {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    {x : Fin n // zagNontrivialAntiExceedance e π x} ≃
      {x : {x : Fin n // ¬zagExceedance e π x} //
        ¬zagTrivialAntiExceedance e π x.1} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def zagTrivialAntiExceedanceEquiv {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    {x : Fin n // zagTrivialAntiExceedance e π x} ≃
      {x : {x : Fin n // ¬zagExceedance e π x} //
        zagTrivialAntiExceedance e π x.1} where
  toFun x := ⟨⟨x.1, zagTrivialAntiExceedance_not_exceedance e π x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem zagCard_nontrivialAntiExceedances {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    Nat.card {x : Fin n // zagNontrivialAntiExceedance e π x} =
      n - Nat.card {x : Fin n // zagExceedance e π x} -
        cycleQuotientCount π := by
  classical
  have hsplit :
      Nat.card {x : {x : Fin n // ¬zagExceedance e π x} //
          ¬zagTrivialAntiExceedance e π x.1} =
        Nat.card {x : Fin n // ¬zagExceedance e π x} -
          Nat.card {x : {x : Fin n // ¬zagExceedance e π x} //
            zagTrivialAntiExceedance e π x.1} := by
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl _
  have hanti :
      Nat.card {x : Fin n // ¬zagExceedance e π x} =
        n - Nat.card {x : Fin n // zagExceedance e π x} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_fin]
  have htrivial :
      Nat.card {x : {x : Fin n // ¬zagExceedance e π x} //
          zagTrivialAntiExceedance e π x.1} = cycleQuotientCount π := by
    calc
      _ = Nat.card {x : Fin n // zagTrivialAntiExceedance e π x} :=
        (Nat.card_congr (zagTrivialAntiExceedanceEquiv e π)).symm
      _ = cycleQuotientCount π := zagCard_trivialAntiExceedances e π
  rw [Nat.card_congr (zagNontrivialAntiExceedanceEquiv e π), hsplit,
    hanti, htrivial]

private theorem zagProduct_cycleCount_even {n : ℕ}
    (σ τ : Equiv.Perm (Fin n))
    (hσ : Multiset.card σ.cycleType +
      Fintype.card (Function.fixedPoints σ) = 1)
    (hτ : Multiset.card τ.cycleType +
      Fintype.card (Function.fixedPoints τ) = 1) :
    Even (n - (Multiset.card (σ * τ).cycleType +
      Fintype.card (Function.fixedPoints (σ * τ)))) := by
  have hs : σ.sign = (-1 : ℤˣ) ^ (n - 1) := by
    rw [zagSign_eq_neg_one_pow_cycleCount, hσ]
  have ht : τ.sign = (-1 : ℤˣ) ^ (n - 1) := by
    rw [zagSign_eq_neg_one_pow_cycleCount, hτ]
  have hp : (σ * τ).sign = 1 := by
    rw [Equiv.Perm.sign_mul, hs, ht, ← pow_add]
    exact (Even.add_self (n - 1)).neg_one_pow
  rw [zagSign_eq_neg_one_pow_cycleCount] at hp
  exact (neg_one_pow_eq_one_iff_even (by decide)).mp hp

private theorem zagCard_cyclePairs_eq_zero_of_odd (n k : ℕ) (hodd : Odd (n - k)) :
    Fintype.card {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
      Multiset.card p.1.cycleType + Fintype.card (Function.fixedPoints p.1) = 1 ∧
      Multiset.card p.2.cycleType + Fintype.card (Function.fixedPoints p.2) = 1 ∧
      Multiset.card (p.1 * p.2).cycleType +
        Fintype.card (Function.fixedPoints (p.1 * p.2)) = k} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun p => ?_⟩
  have heven := zagProduct_cycleCount_even p.1.1 p.1.2 p.2.1 p.2.2.1
  rw [p.2.2.2] at heven
  exact (Nat.not_even_iff_odd.mpr hodd heven).elim

private def zagBlockSwapNat (a b c p : ℕ) : ℕ :=
  if p ≤ a then p
  else if p ≤ a + (c - b) then p + (b - a)
  else if p ≤ c then p - (c - b)
  else p

private def zagBlockUnswapNat (a b c p : ℕ) : ℕ :=
  if p ≤ a then p
  else if p ≤ b then p + (c - b)
  else if p ≤ c then p - (b - a)
  else p

private theorem zagBlockSwapNat_lt {a b c p n : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < n) (hp : p < n) :
    zagBlockSwapNat a b c p < n := by
  simp only [zagBlockSwapNat]
  split_ifs <;> omega

private theorem zagBlockUnswapNat_lt {a b c p n : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < n) (hp : p < n) :
    zagBlockUnswapNat a b c p < n := by
  simp only [zagBlockUnswapNat]
  split_ifs <;> omega

private theorem zagBlockUnswapNat_swap {a b c p : ℕ}
    (hab : a < b) (hbc : b < c) :
    zagBlockUnswapNat a b c (zagBlockSwapNat a b c p) = p := by
  simp only [zagBlockSwapNat, zagBlockUnswapNat]
  split_ifs <;> omega

private theorem zagBlockSwapNat_unswap {a b c p : ℕ}
    (hab : a < b) (hbc : b < c) :
    zagBlockSwapNat a b c (zagBlockUnswapNat a b c p) = p := by
  simp only [zagBlockSwapNat, zagBlockUnswapNat]
  split_ifs <;> omega

private def zagBlockSwap {n : ℕ} (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    Equiv.Perm (Fin n) where
  toFun p := ⟨zagBlockSwapNat a b c p,
    zagBlockSwapNat_lt hab hbc c.isLt p.isLt⟩
  invFun p := ⟨zagBlockUnswapNat a b c p,
    zagBlockUnswapNat_lt hab hbc c.isLt p.isLt⟩
  left_inv p := Fin.ext (zagBlockUnswapNat_swap (p := p) hab hbc)
  right_inv p := Fin.ext (zagBlockSwapNat_unswap (p := p) hab hbc)

private theorem zagBlockSwap_congr_right {n : ℕ} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hbd : b < d) (hcd : c = d) :
    zagBlockSwap a b c hab hbc = zagBlockSwap a b d hab hbd := by
  subst d
  rfl

@[simp]
private theorem zagBlockSwap_val {n : ℕ} (a b c p : Fin n)
    (hab : a < b) (hbc : b < c) :
    (zagBlockSwap a b c hab hbc p : ℕ) = zagBlockSwapNat a b c p :=
  rfl

@[simp]
private theorem zagBlockSwap_symm_val {n : ℕ} (a b c p : Fin n)
    (hab : a < b) (hbc : b < c) :
    ((zagBlockSwap a b c hab hbc).symm p : ℕ) =
      zagBlockUnswapNat a b c p :=
  rfl

private def zagBlockMiddle {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) : Fin n :=
  ⟨a + (c - b), by omega⟩

@[simp]
private theorem zagBlockMiddle_val {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    (zagBlockMiddle a b c hab hbc : ℕ) = a + (c - b) :=
  rfl

private theorem zagBlockMiddle_bounds {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    a < zagBlockMiddle a b c hab hbc ∧
      zagBlockMiddle a b c hab hbc < c := by
  constructor <;> rw [Fin.lt_def] <;>
    simp only [zagBlockMiddle_val] <;> omega

private theorem zagBlockMiddle_reverse {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockMiddle a (zagBlockMiddle a b c hab hbc) c
      (zagBlockMiddle_bounds a b c hab hbc).1
      (zagBlockMiddle_bounds a b c hab hbc).2 = b := by
  apply Fin.ext
  simp only [zagBlockMiddle_val]
  omega

private theorem zagBlockSwap_apply_left {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockSwap a b c hab hbc a = a := by
  apply Fin.ext
  simp [zagBlockSwapNat]

private theorem zagBlockSwap_apply_middle {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockSwap a b c hab hbc (zagBlockMiddle a b c hab hbc) = c := by
  apply Fin.ext
  change zagBlockSwapNat a b c (a + (c - b)) = c
  simp only [zagBlockSwapNat]
  split_ifs <;> omega

private theorem zagBlockSwap_apply_right {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockSwap a b c hab hbc c = b := by
  apply Fin.ext
  simp only [zagBlockSwap_val, zagBlockSwapNat]
  split_ifs <;> omega

private theorem zagBlockSwap_symm_apply_middle {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    (zagBlockSwap a b c hab hbc).symm b = c := by
  apply (zagBlockSwap a b c hab hbc).injective
  rw [Equiv.apply_symm_apply, zagBlockSwap_apply_right]

private theorem zagBlockSwap_symm_apply_left {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    (zagBlockSwap a b c hab hbc).symm a = a := by
  apply (zagBlockSwap a b c hab hbc).injective
  rw [Equiv.apply_symm_apply, zagBlockSwap_apply_left]

private theorem zagBlockSwap_symm_apply_right {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    (zagBlockSwap a b c hab hbc).symm c =
      zagBlockMiddle a b c hab hbc := by
  apply (zagBlockSwap a b c hab hbc).injective
  rw [Equiv.apply_symm_apply, zagBlockSwap_apply_middle]

private theorem zagBlockSwap_preserves_leftCut {n : ℕ}
    (a b c p : Fin n) (hab : a < b) (hbc : b < c) :
    a ≤ zagBlockSwap a b c hab hbc p ↔ a ≤ p := by
  rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val]
  simp only [zagBlockSwap_val, zagBlockSwapNat]
  split_ifs <;> omega

private theorem zagBlockSwap_symm_preserves_leftCut {n : ℕ}
    (a b c p : Fin n) (hab : a < b) (hbc : b < c) :
    a ≤ (zagBlockSwap a b c hab hbc).symm p ↔ a ≤ p := by
  have h := zagBlockSwap_preserves_leftCut a b c
    ((zagBlockSwap a b c hab hbc).symm p) hab hbc
  simpa using h.symm

private theorem zagBlockMiddle_le_unswap {n : ℕ}
    (a b c p : Fin n) (hab : a < b) (hbc : b < c)
    (hap : a < p) (hp : p ≤ b ∨ c ≤ p) :
    zagBlockMiddle a b c hab hbc ≤ (zagBlockSwap a b c hab hbc).symm p := by
  rw [Fin.le_iff_val_le_val]
  simp only [zagBlockMiddle_val, zagBlockSwap_symm_val,
    zagBlockUnswapNat]
  split_ifs <;> omega

private theorem zagBlockSwap_right_of_middle_le {n : ℕ}
    (a b c p : Fin n) (hab : a < b) (hbc : b < c)
    (hqp : zagBlockMiddle a b c hab hbc < p)
    (hbp : b ≤ zagBlockSwap a b c hab hbc p) :
    c ≤ p := by
  rw [Fin.le_iff_val_le_val] at hbp ⊢
  rw [Fin.lt_def] at hqp
  simp only [zagBlockMiddle_val, zagBlockSwap_val, zagBlockSwapNat] at hbp hqp
  split_ifs at hbp <;> omega

private theorem zagBlockSwap_symm_apply_of_right {n : ℕ}
    (a b c p : Fin n) (hab : a < b) (hbc : b < c) (hcp : c < p) :
    (zagBlockSwap a b c hab hbc).symm p = p := by
  apply Fin.ext
  simp only [zagBlockSwap_symm_val, zagBlockUnswapNat]
  split_ifs <;> omega

private theorem zagBlockSwapNat_reverse {a b c p : ℕ}
    (hab : a < b) (hbc : b < c) :
    zagBlockSwapNat a (a + (c - b)) c p =
      zagBlockUnswapNat a b c p := by
  simp only [zagBlockSwapNat, zagBlockUnswapNat]
  split_ifs <;> omega

private theorem zagBlockSwap_mul_reverse {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockSwap a b c hab hbc *
        zagBlockSwap a (zagBlockMiddle a b c hab hbc) c
          (zagBlockMiddle_bounds a b c hab hbc).1
          (zagBlockMiddle_bounds a b c hab hbc).2 = 1 := by
  have hreverse :
      zagBlockSwap a (zagBlockMiddle a b c hab hbc) c
          (zagBlockMiddle_bounds a b c hab hbc).1
          (zagBlockMiddle_bounds a b c hab hbc).2 =
        (zagBlockSwap a b c hab hbc)⁻¹ := by
    ext p
    change zagBlockSwapNat a (a + (c - b)) c p =
      zagBlockUnswapNat a b c p
    exact zagBlockSwapNat_reverse
      (show (a : ℕ) < b by simpa using hab)
      (show (b : ℕ) < c by simpa using hbc)
  rw [hreverse, mul_inv_cancel]

@[simp]
private theorem zagBlockSwap_inv_val {n : ℕ} (a b c p : Fin n)
    (hab : a < b) (hbc : b < c) :
    ((zagBlockSwap a b c hab hbc)⁻¹ p : ℕ) =
      zagBlockUnswapNat a b c p :=
  rfl

private def zagTriangle {α : Type*} [DecidableEq α] (a b c : α) :
    Equiv.Perm α :=
  Equiv.swap a c * Equiv.swap a b

private theorem zagTriangle_apply_left {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) :
    zagTriangle a b c a = b := by
  simp only [zagTriangle, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  rw [Equiv.swap_apply_of_ne_of_ne hab.symm hbc]

@[simp]
private theorem zagTriangle_apply_middle {α : Type*} [DecidableEq α]
    (a b c : α) : zagTriangle a b c b = c := by
  simp [zagTriangle, Equiv.Perm.mul_apply]

private theorem zagTriangle_apply_of_ne {α : Type*} [DecidableEq α]
    {a b c x : α} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    zagTriangle a b c x = x := by
  simp only [zagTriangle, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb,
    Equiv.swap_apply_of_ne_of_ne hxa hxc]

private theorem zagTriangle_mul_reverse {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    zagTriangle a b c * zagTriangle a c b = 1 := by
  ext x
  simp only [zagTriangle, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    Equiv.swap_apply_def]
  split_ifs <;> simp_all

private theorem zagTriangle_inv {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (zagTriangle a b c)⁻¹ = zagTriangle a c b := by
  have hrev := zagTriangle_mul_reverse hab hac hbc
  calc
    (zagTriangle a b c)⁻¹ = (zagTriangle a b c)⁻¹ * 1 := by rw [mul_one]
    _ = (zagTriangle a b c)⁻¹ *
        (zagTriangle a b c * zagTriangle a c b) := by rw [hrev]
    _ = zagTriangle a c b := by group

private def zagRotateNat (last p : ℕ) : ℕ :=
  if p = last then 0 else p + 1

private def zagTriangleNat (a b c p : ℕ) : ℕ :=
  if p = a then b else if p = b then c else if p = c then a else p

private theorem zagTriangle_val {n : ℕ} {a b c x : Fin n}
    (hab : a < b) (hbc : b < c) :
    (zagTriangle a b c x : ℕ) = zagTriangleNat a b c x := by
  simp only [zagTriangle, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    zagTriangleNat]
  split_ifs <;> simp_all <;> omega

private theorem zagBlockSwapNat_rotate_unswap {a b c p last : ℕ}
    (hab : a < b) (hbc : b < c) (hc : c < last + 1) (hp : p < last + 1) :
    zagBlockSwapNat a b c
        (zagRotateNat last (zagBlockUnswapNat a b c p)) =
      zagRotateNat last (zagTriangleNat a b c p) := by
  simp only [zagBlockSwapNat, zagBlockUnswapNat, zagRotateNat,
    zagTriangleNat]
  split_ifs <;> omega

private theorem zagBlockSwap_conj_finRotate {n : ℕ} (a b c : Fin n)
    (hab : a < b) (hbc : b < c) :
    zagBlockSwap a b c hab hbc * finRotate n *
        (zagBlockSwap a b c hab hbc)⁻¹ =
      finRotate n * zagTriangle a b c := by
  have hn : n ≠ 0 := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  ext x
  simp only [Equiv.Perm.mul_apply, zagBlockSwap_val, coe_finRotate,
    Fin.ext_iff, zagBlockSwap_inv_val, Fin.val_last, zagTriangle_val hab hbc]
  simpa only [zagRotateNat] using
    zagBlockSwapNat_rotate_unswap (p := x) (last := m) hab hbc c.isLt x.isLt

private def zagHorizontal {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  e * finRotate n * e⁻¹

private theorem zagConj_swap {α : Type*} [DecidableEq α]
    (e : Equiv.Perm α) (a b : α) :
    e * Equiv.swap a b * e⁻¹ = Equiv.swap (e a) (e b) := by
  ext x
  simpa using e.injective.map_swap a b (e.symm x)

private theorem zagConj_triangle {α : Type*} [DecidableEq α]
    (e : Equiv.Perm α) (a b c : α) :
    e * zagTriangle a b c * e⁻¹ = zagTriangle (e a) (e b) (e c) := by
  simp only [zagTriangle]
  rw [show e * (Equiv.swap a c * Equiv.swap a b) * e⁻¹ =
      (e * Equiv.swap a c * e⁻¹) * (e * Equiv.swap a b * e⁻¹) by group,
    zagConj_swap, zagConj_swap]

private theorem zagHorizontal_blockSwap {n : ℕ} (e : Equiv.Perm (Fin n))
    (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    zagHorizontal (e * zagBlockSwap a b c hab hbc) =
      zagHorizontal e * zagTriangle (e a) (e b) (e c) := by
  simp only [zagHorizontal, mul_inv_rev]
  rw [show (e * zagBlockSwap a b c hab hbc) * finRotate n *
        ((zagBlockSwap a b c hab hbc)⁻¹ * e⁻¹) =
      e * (zagBlockSwap a b c hab hbc * finRotate n *
        (zagBlockSwap a b c hab hbc)⁻¹) * e⁻¹ by group,
    zagBlockSwap_conj_finRotate]
  rw [show e * (finRotate n * zagTriangle a b c) * e⁻¹ =
      (e * finRotate n * e⁻¹) * (e * zagTriangle a b c * e⁻¹) by group,
    zagConj_triangle]

private def zagVertical {n : ℕ} (D e : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  D⁻¹ * zagHorizontal e

private theorem zagVertical_blockSwap {n : ℕ} (D e : Equiv.Perm (Fin n))
    (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    zagVertical D (e * zagBlockSwap a b c hab hbc) =
      zagVertical D e * zagTriangle (e a) (e b) (e c) := by
  simp only [zagVertical, zagHorizontal_blockSwap]
  group

private theorem zagSameCycle_of_step {α : Type*} [Finite α]
    (f g : Equiv.Perm α)
    (hstep : ∀ z, f.SameCycle z (g z)) {a b : α}
    (hab : g.SameCycle a b) : f.SameCycle a b := by
  obtain ⟨m, hm⟩ := hab.exists_nat_pow_eq
  have hpow : ∀ r : ℕ, f.SameCycle a ((g ^ r) a) := by
    intro r
    induction r with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ r ih =>
        exact ih.trans (by simpa [pow_succ'] using hstep ((g ^ r) a))
  simpa [hm] using hpow m

private theorem zagSameCycle_mul_swap_refines {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {x y a b : α}
    (hxy : f.SameCycle x y)
    (hab : (f * Equiv.swap x y).SameCycle a b) :
    f.SameCycle a b := by
  apply zagSameCycle_of_step f (f * Equiv.swap x y) _ hab
  intro z
  have hz : f.SameCycle z (Equiv.swap x y z) := by
    rw [Equiv.swap_apply_def]
    split_ifs with hzx hzy
    · simpa [hzx] using hxy
    · simpa [hzy] using hxy.symm
    · exact Equiv.Perm.SameCycle.rfl
  exact hz.trans (by
    simpa [Equiv.Perm.mul_apply] using
      (Equiv.Perm.SameCycle.refl f (Equiv.swap x y z)).apply_right)

private theorem zagSameCycle_mul_swap_of_not_affected {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {x y a b : α}
    (hxy : f.SameCycle x y) (hab : f.SameCycle a b)
    (hax : ¬f.SameCycle a x) :
    (f * Equiv.swap x y).SameCycle a b := by
  obtain ⟨m, hm⟩ := hab.exists_nat_pow_eq
  have hpow : ∀ r : ℕ, (f * Equiv.swap x y).SameCycle a ((f ^ r) a) := by
    intro r
    induction r with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ r ih =>
        let z := (f ^ r) a
        have haz : f.SameCycle a z := by
          exact ⟨(r : ℤ), by simp [z]⟩
        have hzx : z ≠ x := fun h => hax (by simpa [h] using haz)
        have hzy : z ≠ y := fun h => hax (haz.trans (by simpa [h] using hxy.symm))
        have hstep : (f * Equiv.swap x y) z = f z := by
          simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzx hzy]
        have hrel : (f * Equiv.swap x y).SameCycle z (f z) := by
          rw [← hstep]
          exact (Equiv.Perm.SameCycle.refl (f * Equiv.swap x y) z).apply_right
        exact ih.trans (by simpa [z, pow_succ', Equiv.Perm.mul_apply] using hrel)
  simpa [hm] using hpow m

private theorem zagSameCycle_mul_swap_iff_of_disjoint {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b x y : α}
    (hxa : ¬f.SameCycle x a) (hxb : ¬f.SameCycle x b) :
    (f * Equiv.swap a b).SameCycle x y ↔ f.SameCycle x y := by
  let g := f * Equiv.swap a b
  have hpow (r : ℕ) : (g ^ r) x = (f ^ r) x := by
    induction r with
    | zero => rfl
    | succ r ih =>
        have hcycle : f.SameCycle x ((f ^ r) x) :=
          ⟨(r : ℤ), by simp⟩
        have hne_a : (f ^ r) x ≠ a := fun h => hxa (by simpa [h] using hcycle)
        have hne_b : (f ^ r) x ≠ b := fun h => hxb (by simpa [h] using hcycle)
        rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
        simp only [Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hne_a hne_b]
  constructor
  · intro hxy
    obtain ⟨r, hr⟩ := hxy.exists_nat_pow_eq
    exact ⟨(r : ℤ), by rw [zpow_natCast, ← hpow]; exact hr⟩
  · intro hxy
    obtain ⟨r, hr⟩ := hxy.exists_nat_pow_eq
    exact ⟨(r : ℤ), by rw [zpow_natCast, hpow]; exact hr⟩

private theorem zagSameCycle_mul_triangle_iff_of_disjoint {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c x y : α}
    (hxa : ¬f.SameCycle x a) (hxb : ¬f.SameCycle x b)
    (hxc : ¬f.SameCycle x c) :
    (f * zagTriangle a b c).SameCycle x y ↔ f.SameCycle x y := by
  let g := f * Equiv.swap a c
  have hg : ∀ z, g.SameCycle x z ↔ f.SameCycle x z := fun z =>
    zagSameCycle_mul_swap_iff_of_disjoint f hxa hxc
  have hga : ¬g.SameCycle x a := fun h => hxa ((hg a).mp h)
  have hgb : ¬g.SameCycle x b := fun h => hxb ((hg b).mp h)
  calc
    (f * zagTriangle a b c).SameCycle x y ↔
        (g * Equiv.swap a b).SameCycle x y := by
      simp only [g, zagTriangle, mul_assoc]
    _ ↔ g.SameCycle x y :=
      zagSameCycle_mul_swap_iff_of_disjoint g hga hgb
    _ ↔ f.SameCycle x y := hg y

private theorem zagMulSwap_sameCycle_of_not_sameCycle {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {x y : α}
    (hxy : ¬f.SameCycle x y) :
    (f * Equiv.swap x y).SameCycle x y := by
  let returns (m : ℕ) : Prop := 0 < m ∧ (f ^ m) y = y
  have hex : ∃ m, returns m := by
    refine ⟨orderOf f, orderOf_pos f, ?_⟩
    rw [pow_orderOf_eq_one]
    rfl
  let m := Nat.find hex
  have hm : returns m := Nat.find_spec hex
  let g := f * Equiv.swap x y
  have hpow (r : ℕ) (hr : r < m) :
      (g ^ (r + 1)) x = (f ^ (r + 1)) y := by
    induction r with
    | zero => simp [g, Equiv.Perm.mul_apply]
    | succ r ih =>
        have hrm : r < m := by omega
        have hne_y : (f ^ (r + 1)) y ≠ y := by
          intro heq
          have hle := Nat.find_min' hex ⟨by omega, heq⟩
          omega
        have hne_x : (f ^ (r + 1)) y ≠ x := by
          intro heq
          apply hxy
          have hyx : f.SameCycle y x :=
            ⟨((r + 1 : ℕ) : ℤ), by rw [zpow_natCast]; exact heq⟩
          exact hyx.symm
        calc
          (g ^ (r + 1 + 1)) x = g ((g ^ (r + 1)) x) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          _ = g ((f ^ (r + 1)) y) := by rw [ih hrm]
          _ = f ((f ^ (r + 1)) y) := by
            simp only [g, Equiv.Perm.mul_apply]
            rw [Equiv.swap_apply_of_ne_of_ne hne_x hne_y]
          _ = (f ^ (r + 1 + 1)) y := by
            simp [pow_succ', Equiv.Perm.mul_apply]
  have hlt : m - 1 < m := by omega
  have hlast := hpow (m - 1) hlt
  have hsub : m - 1 + 1 = m := by omega
  rw [hsub, hm.2] at hlast
  exact ⟨(m : ℤ), by simpa using hlast⟩

private theorem zagSameCycle_mul_swap_union {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {x y z : α}
    (hz : f.SameCycle x z) :
    (f * Equiv.swap x y).SameCycle x z ∨
      (f * Equiv.swap x y).SameCycle y z := by
  obtain ⟨m, hm⟩ := hz.exists_nat_pow_eq
  have hpow : ∀ r : ℕ,
      (f * Equiv.swap x y).SameCycle x ((f ^ r) x) ∨
        (f * Equiv.swap x y).SameCycle y ((f ^ r) x) := by
    intro r
    induction r with
    | zero => exact Or.inl Equiv.Perm.SameCycle.rfl
    | succ r ih =>
        let w := (f ^ r) x
        by_cases hwx : w = x
        · right
          have hstep : (f * Equiv.swap x y) y = f x := by
            simp [Equiv.Perm.mul_apply]
          have hrel :=
            (Equiv.Perm.SameCycle.refl (f * Equiv.swap x y) y).apply_right
          simpa [pow_succ', w, Equiv.Perm.mul_apply, hstep, hwx] using hrel
        · by_cases hwy : w = y
          · left
            have hstep : (f * Equiv.swap x y) x = f y := by
              simp [Equiv.Perm.mul_apply]
            have hrel :=
              (Equiv.Perm.SameCycle.refl (f * Equiv.swap x y) x).apply_right
            simpa [pow_succ', w, Equiv.Perm.mul_apply, hstep, hwy] using hrel
          · have hstep : (f * Equiv.swap x y) w = f w := by
              simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwx hwy]
            rcases ih with hxw | hyw
            · left
              have hrel : (f * Equiv.swap x y).SameCycle w (f w) := by
                rw [← hstep]
                exact (Equiv.Perm.SameCycle.refl (f * Equiv.swap x y) w).apply_right
              exact hxw.trans (by
                simpa [w, pow_succ', Equiv.Perm.mul_apply] using hrel)
            · right
              have hrel : (f * Equiv.swap x y).SameCycle w (f w) := by
                rw [← hstep]
                exact (Equiv.Perm.SameCycle.refl (f * Equiv.swap x y) w).apply_right
              exact hyw.trans (by
                simpa [w, pow_succ', Equiv.Perm.mul_apply] using hrel)
  simpa [hm] using hpow m

private theorem zagTriangle_merge_sameCycles {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c : α}
    (hab : ¬f.SameCycle a b) (hac : ¬f.SameCycle a c)
    (hbc : ¬f.SameCycle b c) :
    let g := f * zagTriangle a b c
    g.SameCycle a b ∧ g.SameCycle a c := by
  let h := f * Equiv.swap a c
  have hac_h : h.SameCycle a c :=
    zagMulSwap_sameCycle_of_not_sameCycle f hac
  have hab_h : ¬h.SameCycle a b := by
    intro hab_h'
    have hu := zagSameCycle_mul_swap_union (f := h)
      (x := a) (y := c) (z := b) hab_h'
    have hundo : h * Equiv.swap a c = f := by
      simp [h, mul_assoc]
    rw [hundo] at hu
    rcases hu with hab' | hcb'
    · exact hab hab'
    · exact hbc hcb'.symm
  let g := h * Equiv.swap a b
  have hab_g : g.SameCycle a b :=
    zagMulSwap_sameCycle_of_not_sameCycle h hab_h
  have hac_or : g.SameCycle a c ∨ g.SameCycle b c :=
    zagSameCycle_mul_swap_union (f := h)
      (x := a) (y := b) (z := c) hac_h
  have hac_g : g.SameCycle a c := hac_or.elim id (fun hbc' => hab_g.trans hbc')
  simpa only [g, h, zagTriangle, mul_assoc] using ⟨hab_g, hac_g⟩

private theorem zagTriangle_merge_cases {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c x : α}
    (hab : ¬f.SameCycle a b) (hac : ¬f.SameCycle a c)
    (hbc : ¬f.SameCycle b c)
    (hx : (f * zagTriangle a b c).SameCycle a x) :
    f.SameCycle a x ∨ f.SameCycle b x ∨ f.SameCycle c x := by
  let h := f * Equiv.swap a c
  let g := h * Equiv.swap a b
  have hac_h : h.SameCycle a c :=
    zagMulSwap_sameCycle_of_not_sameCycle f hac
  have hab_h : ¬h.SameCycle a b := by
    intro hab_h'
    have hu := zagSameCycle_mul_swap_union (f := h)
      (x := a) (y := c) (z := b) hab_h'
    have hundo : h * Equiv.swap a c = f := by simp [h, mul_assoc]
    rw [hundo] at hu
    rcases hu with hab' | hcb'
    · exact hab hab'
    · exact hbc hcb'.symm
  have hxg : g.SameCycle a x := by
    simpa only [g, h, zagTriangle, mul_assoc] using hx
  have hsplit := zagSameCycle_mul_swap_union (f := g)
    (x := a) (y := b) (z := x) hxg
  have hgundo : g * Equiv.swap a b = h := by simp [g, mul_assoc]
  rw [hgundo] at hsplit
  rcases hsplit with hax | hbx
  · have hsplit' := zagSameCycle_mul_swap_union (f := h)
      (x := a) (y := c) (z := x) hax
    have hhundo : h * Equiv.swap a c = f := by simp [h, mul_assoc]
    rw [hhundo] at hsplit'
    exact hsplit'.elim Or.inl (fun hcx => Or.inr (Or.inr hcx))
  · right
    left
    have hnot : ¬h.SameCycle b a := fun hba => hab_h hba.symm
    have hpres := zagSameCycle_mul_swap_of_not_affected h hac_h hbx hnot
    have hhundo : h * Equiv.swap a c = f := by simp [h, mul_assoc]
    rwa [hhundo] at hpres

private theorem zagExists_positive_return {α : Type*} [Finite α]
    (f : Equiv.Perm α) (x : α) :
    ∃ m : ℕ, 0 < m ∧ (f ^ m) x = x := by
  refine ⟨orderOf f, orderOf_pos f, ?_⟩
  rw [pow_orderOf_eq_one]
  rfl

private noncomputable def zagReturnTime {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) (x : α) : ℕ :=
  Nat.find (zagExists_positive_return f x)

private theorem zagReturnTime_pos {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) (x : α) :
    0 < zagReturnTime f x :=
  (Nat.find_spec (zagExists_positive_return f x)).1

private theorem zagReturnTime_spec {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) (x : α) :
    (f ^ zagReturnTime f x) x = x :=
  (Nat.find_spec (zagExists_positive_return f x)).2

private theorem zagReturnTime_no_return {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) (x : α) {r : ℕ}
    (hr0 : 0 < r) (hr : r < zagReturnTime f x) :
    (f ^ r) x ≠ x := by
  intro hreturn
  have hle := Nat.find_min' (zagExists_positive_return f x) ⟨hr0, hreturn⟩
  exact (not_le_of_gt hr) hle

private theorem zagTriangle_merge_pow_left {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c : α}
    (hab : ¬f.SameCycle a b) (_hac : ¬f.SameCycle a c)
    (hbc : ¬f.SameCycle b c) {r : ℕ}
    (hr0 : 0 < r) (hr : r ≤ zagReturnTime f b) :
    ((f * zagTriangle a b c) ^ r) a = (f ^ r) b := by
  let g := f * zagTriangle a b c
  let L := zagReturnTime f b
  induction r using Nat.case_strong_induction_on with
  | hz => omega
  | hi r ih =>
      by_cases hrz : r = 0
      · subst r
        have hab_ne : a ≠ b := fun h => hab (h.sameCycle f)
        have hbc_ne : b ≠ c := fun h => hbc (h.sameCycle f)
        simp [Equiv.Perm.mul_apply,
          zagTriangle_apply_left hab_ne hbc_ne]
      · have hr0' : 0 < r := Nat.pos_of_ne_zero hrz
        have hrlt : r < L := by omega
        have ihr := ih r le_rfl hr0' (by omega)
        have hbr : f.SameCycle b ((f ^ r) b) :=
          ⟨(r : ℤ), by simp⟩
        have hne_b : (f ^ r) b ≠ b :=
          zagReturnTime_no_return f b hr0' hrlt
        have hne_a : (f ^ r) b ≠ a := fun hra =>
          hab (by simpa [hra] using hbr.symm)
        have hne_c : (f ^ r) b ≠ c := fun hrc =>
          hbc (by simpa [hrc] using hbr)
        calc
          (g ^ (r + 1)) a = g ((g ^ r) a) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          _ = g ((f ^ r) b) := by rw [ihr]
          _ = f ((f ^ r) b) := by
            rw [show g = f * zagTriangle a b c by rfl,
              Equiv.Perm.mul_apply,
              zagTriangle_apply_of_ne hne_a hne_b hne_c]
          _ = (f ^ (r + 1)) b := by
            rw [pow_succ', Equiv.Perm.mul_apply]

private theorem zagTriangle_merge_pow_middle {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c : α}
    (_hab : ¬f.SameCycle a b) (hac : ¬f.SameCycle a c)
    (hbc : ¬f.SameCycle b c) {r : ℕ}
    (hr0 : 0 < r) (hr : r ≤ zagReturnTime f c) :
    ((f * zagTriangle a b c) ^ r) b = (f ^ r) c := by
  let g := f * zagTriangle a b c
  let L := zagReturnTime f c
  induction r using Nat.case_strong_induction_on with
  | hz => omega
  | hi r ih =>
      by_cases hrz : r = 0
      · subst r
        simp [Equiv.Perm.mul_apply]
      · have hr0' : 0 < r := Nat.pos_of_ne_zero hrz
        have hrlt : r < L := by omega
        have ihr := ih r le_rfl hr0' (by omega)
        have hcr : f.SameCycle c ((f ^ r) c) :=
          ⟨(r : ℤ), by simp⟩
        have hne_c : (f ^ r) c ≠ c :=
          zagReturnTime_no_return f c hr0' hrlt
        have hne_a : (f ^ r) c ≠ a := fun hra =>
          hac (by simpa [hra] using hcr.symm)
        have hne_b : (f ^ r) c ≠ b := fun hrb =>
          hbc (by simpa [hrb] using hcr.symm)
        calc
          (g ^ (r + 1)) b = g ((g ^ r) b) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          _ = g ((f ^ r) c) := by rw [ihr]
          _ = f ((f ^ r) c) := by
            rw [show g = f * zagTriangle a b c by rfl,
              Equiv.Perm.mul_apply,
              zagTriangle_apply_of_ne hne_a hne_b hne_c]
          _ = (f ^ (r + 1)) c := by
            rw [pow_succ', Equiv.Perm.mul_apply]

private theorem zagTriangle_merge_pow_after_left {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c : α}
    (hab : ¬f.SameCycle a b) (hac : ¬f.SameCycle a c)
    (hbc : ¬f.SameCycle b c) {r : ℕ}
    (hr0 : 0 < r) (hr : r ≤ zagReturnTime f c) :
    ((f * zagTriangle a b c) ^ (zagReturnTime f b + r)) a =
      (f ^ r) c := by
  let g := f * zagTriangle a b c
  have hleft := zagTriangle_merge_pow_left f hab hac hbc
    (zagReturnTime_pos f b) (le_refl (zagReturnTime f b))
  have hmiddle := zagTriangle_merge_pow_middle f hab hac hbc hr0 hr
  calc
    (g ^ (zagReturnTime f b + r)) a =
        (g ^ r) ((g ^ zagReturnTime f b) a) := by
      rw [add_comm, pow_add, Equiv.Perm.mul_apply]
    _ = (g ^ r) b := by rw [hleft, zagReturnTime_spec]
    _ = (f ^ r) c := hmiddle

private theorem zagCycleQuotientCount_mul_swap {n : ℕ}
    (f : Equiv.Perm (Fin n)) {x y : Fin n} (hxy_ne : x ≠ y)
    (hxy : f.SameCycle x y) :
    cycleQuotientCount (f * Equiv.swap x y) =
      cycleQuotientCount f + 1 := by
  classical
  let Qf := Quotient (Equiv.Perm.SameCycle.setoid f)
  let Qg := Quotient (Equiv.Perm.SameCycle.setoid (f * Equiv.swap x y))
  let forget : Qg → Qf := Quotient.map id fun {_ _} h =>
    zagSameCycle_mul_swap_refines f hxy h
  have hforget : Function.Surjective forget := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    exact ⟨Quotient.mk _ z, rfl⟩
  have hlower : cycleQuotientCount f ≤
      cycleQuotientCount (f * Equiv.swap x y) := by
    exact Nat.card_le_card_of_surjective forget hforget
  let qx : Qf := Quotient.mk _ x
  let cover : Qf ⊕ Unit → Qg
    | Sum.inl q => if q = qx then Quotient.mk _ x else Quotient.mk _ q.out
    | Sum.inr _ => Quotient.mk _ y
  have hcover : Function.Surjective cover := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    by_cases hzx : f.SameCycle z x
    · rcases zagSameCycle_mul_swap_union f hzx.symm with hxz | hyz
      · refine ⟨Sum.inl qx, ?_⟩
        simp only [cover, ite_eq_left rfl]
        exact Quotient.sound hxz
      · refine ⟨Sum.inr (), ?_⟩
        exact Quotient.sound hyz
    · let qz : Qf := Quotient.mk _ z
      have hqz : qz ≠ qx := fun h => hzx (Quotient.exact h)
      refine ⟨Sum.inl qz, ?_⟩
      simp only [cover, ite_eq_right hqz]
      apply Quotient.sound
      have houtz : f.SameCycle qz.out z := by
        change (Equiv.Perm.SameCycle.setoid f).r qz.out z
        apply Quotient.exact
        change (Quotient.mk _ qz.out : Qf) = qz
        exact Quotient.out_eq qz
      have houtx : ¬f.SameCycle qz.out x := fun h =>
        hzx (houtz.symm.trans h)
      exact zagSameCycle_mul_swap_of_not_affected f hxy houtz houtx
  have hupper : cycleQuotientCount (f * Equiv.swap x y) ≤
      cycleQuotientCount f + 1 := by
    have h := Nat.card_le_card_of_surjective cover hcover
    change Nat.card Qg ≤ Nat.card Qf + 1
    simpa only [Nat.card_sum, Nat.card_unique] using h
  have hsign_ne : (f * Equiv.swap x y).sign ≠ f.sign := by
    have hsign : (f * Equiv.swap x y).sign = (-1 : ℤˣ) * f.sign := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy_ne]
      ac_rfl
    intro heq
    have hcancel : (-1 : ℤˣ) * f.sign = 1 * f.sign := by
      rw [← hsign, heq, one_mul]
    exact (by decide : (-1 : ℤˣ) ≠ 1) (mul_right_cancel hcancel)
  have hcount_ne : cycleQuotientCount (f * Equiv.swap x y) ≠
      cycleQuotientCount f := by
    intro hcount
    apply hsign_ne
    rw [zagSign_eq_neg_one_pow_cycleCount,
      ← cycleQuotientCount_eq,
      zagSign_eq_neg_one_pow_cycleCount,
      ← cycleQuotientCount_eq, hcount]
  omega

private theorem zagMulSwap_not_sameCycle {n : ℕ}
    (f : Equiv.Perm (Fin n)) {x y : Fin n} (hxy_ne : x ≠ y)
    (hxy : f.SameCycle x y) :
    ¬(f * Equiv.swap x y).SameCycle x y := by
  intro hsame
  have hforward := zagCycleQuotientCount_mul_swap f hxy_ne hxy
  have hbackward := zagCycleQuotientCount_mul_swap
    (f * Equiv.swap x y) hxy_ne hsame
  have hundo : (f * Equiv.swap x y) * Equiv.swap x y = f := by
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  rw [hundo, hforward] at hbackward
  omega

private theorem zagCycleQuotientCount_mul_triangle {n : ℕ}
    (f : Equiv.Perm (Fin n)) {a b c : Fin n}
    (hac_ne : a ≠ c) (hac : f.SameCycle a c)
    (hab_ne : a ≠ b)
    (hab : (f * Equiv.swap a c).SameCycle a b) :
    cycleQuotientCount (f * zagTriangle a b c) =
      cycleQuotientCount f + 2 := by
  have hfirst := zagCycleQuotientCount_mul_swap f hac_ne hac
  have hsecond := zagCycleQuotientCount_mul_swap
    (f * Equiv.swap a c) hab_ne hab
  simp only [zagTriangle, mul_assoc] at hsecond ⊢
  omega

private theorem zagSameCycle_mul_triangle_refines {n : ℕ}
    (f : Equiv.Perm (Fin n)) {a b c x y : Fin n}
    (hac : f.SameCycle a c)
    (hab : (f * Equiv.swap a c).SameCycle a b)
    (hxy : (f * zagTriangle a b c).SameCycle x y) :
    f.SameCycle x y := by
  have hh : (f * Equiv.swap a c).SameCycle x y := by
    simpa only [zagTriangle, mul_assoc] using
      zagSameCycle_mul_swap_refines (f * Equiv.swap a c) hab hxy
  exact zagSameCycle_mul_swap_refines f hac hh

private theorem zagTriangle_split_pairwise {n : ℕ}
    (f : Equiv.Perm (Fin n)) {a b c : Fin n}
    (hac_ne : a ≠ c) (hac : f.SameCycle a c)
    (hab_ne : a ≠ b)
    (hab : (f * Equiv.swap a c).SameCycle a b) :
    let g := f * zagTriangle a b c
    ¬g.SameCycle a b ∧ ¬g.SameCycle a c ∧ ¬g.SameCycle b c := by
  let h := f * Equiv.swap a c
  let g := h * Equiv.swap a b
  have hac_h : ¬h.SameCycle a c := by
    exact zagMulSwap_not_sameCycle f hac_ne hac
  have hab_g : ¬g.SameCycle a b := by
    exact zagMulSwap_not_sameCycle h hab_ne hab
  have hrefine (x y : Fin n) (hxy : g.SameCycle x y) : h.SameCycle x y := by
    exact zagSameCycle_mul_swap_refines h hab hxy
  have hac_g : ¬g.SameCycle a c := fun hcycle =>
    hac_h (hrefine a c hcycle)
  have hbc_g : ¬g.SameCycle b c := fun hcycle =>
    hac_h (hab.trans (hrefine b c hcycle))
  simpa only [g, h, zagTriangle, mul_assoc] using
    ⟨hab_g, hac_g, hbc_g⟩

private theorem zagNTAE_min_lt_image {n : ℕ} (e π : Equiv.Perm (Fin n))
    {ε : Fin n} (hε : zagNontrivialAntiExceedance e π ε) :
    zagCycleMinPos e π ε < e.symm (π ε) := by
  have hsame : π.SameCycle (π ε) ε :=
    (Equiv.Perm.SameCycle.refl π ε).apply_left
  have hle := zagCycleMinPos_le e π hsame
  apply lt_of_le_of_ne hle
  intro heq
  apply hε.2
  simp only [zagTrivialAntiExceedance]
  exact e.symm.injective (by simpa using heq.symm)

private theorem zagNTAE_image_lt {n : ℕ} (e π : Equiv.Perm (Fin n))
    {ε : Fin n} (hε : zagNontrivialAntiExceedance e π ε) :
    e.symm (π ε) < e.symm ε := by
  have hle : e.symm (π ε) ≤ e.symm ε := by
    exact not_lt.mp hε.1
  apply lt_of_le_of_ne hle
  intro heq
  have hfix : π ε = ε := e.symm.injective heq
  apply hε.2
  simp only [zagTrivialAntiExceedance]
  have hmin := zagCycleMinPos_mem e π ε
  have hlabel : e (zagCycleMinPos e π ε) = ε :=
    hmin.eq_of_right hfix
  exact hfix.trans hlabel.symm

private noncomputable def zagCycleHit {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b : Fin n) (hab : π.SameCycle a b) : ℕ :=
  Nat.find hab.exists_nat_pow_eq

private theorem zagCycleHit_spec {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b : Fin n) (hab : π.SameCycle a b) :
    (π ^ zagCycleHit π a b hab) a = b :=
  Nat.find_spec hab.exists_nat_pow_eq

private theorem zagCycleHit_pos {n : ℕ} (π : Equiv.Perm (Fin n))
    {a b : Fin n} (hab_ne : a ≠ b) (hab : π.SameCycle a b) :
    0 < zagCycleHit π a b hab := by
  by_contra h
  have hz : zagCycleHit π a b hab = 0 := Nat.eq_zero_of_not_pos h
  have heq : a = b := by
    simpa only [hz, pow_zero, Equiv.Perm.one_apply] using
      zagCycleHit_spec π a b hab
  exact hab_ne heq

private theorem zagCycleHit_minimal {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b : Fin n) (hab : π.SameCycle a b) {r : ℕ}
    (hr : (π ^ r) a = b) : zagCycleHit π a b hab ≤ r :=
  Nat.find_min' hab.exists_nat_pow_eq hr

private theorem zagCycleHit_no_return {n : ℕ} (π : Equiv.Perm (Fin n))
    {a b : Fin n} (hab : π.SameCycle a b)
    {r : ℕ} (hr0 : 0 < r) (hrH : r < zagCycleHit π a b hab) :
    (π ^ r) a ≠ a := by
  let H := zagCycleHit π a b hab
  intro hreturn
  have hearly : (π ^ (H - r)) a = b := by
    calc
      (π ^ (H - r)) a = (π ^ (H - r)) ((π ^ r) a) := by rw [hreturn]
      _ = (π ^ ((H - r) + r)) a := by
        rw [pow_add, Equiv.Perm.mul_apply]
      _ = (π ^ H) a := by congr 2; omega
      _ = b := by simpa [H] using zagCycleHit_spec π a b hab
  have hmin : H ≤ H - r := zagCycleHit_minimal π a b hab hearly
  omega

private theorem zagMulSwap_sameCycle_right_arc {n : ℕ}
    (π : Equiv.Perm (Fin n)) {a c x : Fin n}
    (hac_ne : a ≠ c) (hac : π.SameCycle a c)
    (hx : (π * Equiv.swap a c).SameCycle c x) :
    ∃ r : ℕ, 0 < r ∧ r ≤ zagCycleHit π a c hac ∧
      (π ^ r) a = x := by
  let H := zagCycleHit π a c hac
  let g := π * Equiv.swap a c
  have hHpos : 0 < H := zagCycleHit_pos π hac_ne hac
  obtain ⟨m, hm⟩ := hx.exists_nat_pow_eq
  have hstate : ∀ q : ℕ, ∃ r : ℕ, 0 < r ∧ r ≤ H ∧
      (g ^ q) c = (π ^ r) a := by
    intro q
    induction q with
    | zero =>
        exact ⟨H, hHpos, le_rfl, by
          simpa [H] using (zagCycleHit_spec π a c hac).symm⟩
    | succ q ih =>
        obtain ⟨r, hr0, hrH, hqr⟩ := ih
        by_cases hre : r = H
        · refine ⟨1, by omega, hHpos, ?_⟩
          calc
            (g ^ (q + 1)) c = g ((g ^ q) c) := by
              simpa only [Equiv.Perm.mul_apply] using
                congrArg (fun p : Equiv.Perm (Fin n) => p c) (pow_succ' g q)
            _ = g ((π ^ r) a) := by rw [hqr]
            _ = g c := by
              rw [hre]
              simpa [H] using zagCycleHit_spec π a c hac
            _ = π a := by simp [g, Equiv.Perm.mul_apply]
            _ = (π ^ 1) a := by simp
        · have hrlt : r < H := lt_of_le_of_ne hrH hre
          have hra : (π ^ r) a ≠ a :=
            zagCycleHit_no_return π hac hr0 hrlt
          have hrc : (π ^ r) a ≠ c := fun hrc =>
            (not_lt_of_ge (zagCycleHit_minimal π a c hac hrc)) hrlt
          refine ⟨r + 1, by omega, by omega, ?_⟩
          calc
            (g ^ (q + 1)) c = g ((g ^ q) c) := by
              simpa only [Equiv.Perm.mul_apply] using
                congrArg (fun p : Equiv.Perm (Fin n) => p c) (pow_succ' g q)
            _ = g ((π ^ r) a) := by rw [hqr]
            _ = π ((π ^ r) a) := by
              simp [g, Equiv.Perm.mul_apply,
                Equiv.swap_apply_of_ne_of_ne hra hrc]
            _ = (π ^ (r + 1)) a := by
              simpa only [Equiv.Perm.mul_apply] using
                (congrArg (fun p : Equiv.Perm (Fin n) => p a)
                  (pow_succ' π r)).symm
  obtain ⟨r, hr0, hrH, hr⟩ := hstate m
  exact ⟨r, hr0, hrH, hr.symm.trans hm⟩

private theorem zagFirstSwap_pow_between {n : ℕ}
    (π : Equiv.Perm (Fin n)) {a b c : Fin n}
    (hab : π.SameCycle a b) (hac : π.SameCycle a c)
    (hbefore : zagCycleHit π a c hac < zagCycleHit π a b hab)
    {r : ℕ} (hr0 : 0 < r)
    (hrle : r ≤ zagCycleHit π a b hab - zagCycleHit π a c hac) :
    ((π * Equiv.swap a c) ^ r) a =
      (π ^ (zagCycleHit π a c hac + r)) a := by
  let T := zagCycleHit π a c hac
  let H := zagCycleHit π a b hab
  let h := π * Equiv.swap a c
  induction r using Nat.case_strong_induction_on with
  | hz => omega
  | hi r ih =>
      by_cases hrz : r = 0
      · subst r
        calc
          (h ^ (0 + 1)) a = h a := by simp
          _ = π c := by simp [h, Equiv.Perm.mul_apply]
          _ = π ((π ^ T) a) := by
            rw [zagCycleHit_spec π a c hac]
          _ = (π ^ (T + (0 + 1))) a := by
            simpa only [Nat.zero_add, Equiv.Perm.mul_apply] using
              (congrArg (fun p : Equiv.Perm (Fin n) => p a)
                (pow_succ' π T)).symm
      · have hr0' : 0 < r := Nat.pos_of_ne_zero hrz
        have hrle' : r ≤ H - T := by omega
        have ihr := ih r le_rfl hr0' hrle'
        have hur : T + r < H := by omega
        have hne_a : (π ^ (T + r)) a ≠ a :=
          zagCycleHit_no_return π hab (by omega) hur
        have hne_c : (π ^ (T + r)) a ≠ c := by
          intro heq
          have hreturn : (π ^ r) a = a := by
            apply (π ^ T).injective
            calc
              (π ^ T) ((π ^ r) a) = (π ^ (T + r)) a := by
                rw [pow_add, Equiv.Perm.mul_apply]
              _ = c := heq
              _ = (π ^ T) a := (zagCycleHit_spec π a c hac).symm
          exact zagCycleHit_no_return π hab hr0' (by omega) hreturn
        calc
          (h ^ (r + 1)) a = h ((h ^ r) a) := by
            simpa only [Equiv.Perm.mul_apply] using
              congrArg (fun p : Equiv.Perm (Fin n) => p a) (pow_succ' h r)
          _ = h ((π ^ (T + r)) a) := by rw [ihr]
          _ = π ((π ^ (T + r)) a) := by
            simp [h, Equiv.Perm.mul_apply,
              Equiv.swap_apply_of_ne_of_ne hne_a hne_c]
          _ = (π ^ (T + (r + 1))) a := by
            rw [show T + (r + 1) = (T + r) + 1 by omega]
            simpa only [Equiv.Perm.mul_apply] using
              (congrArg (fun p : Equiv.Perm (Fin n) => p a)
                (pow_succ' π (T + r))).symm

private noncomputable def zagCutHit {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) : ℕ :=
  zagCycleHit π (e (zagCycleMinPos e π ε)) (π ε)
    (zagCycleMinPos_mem e π ε).apply_right

private theorem zagCutHit_spec {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) :
    (π ^ zagCutHit e π ε) (e (zagCycleMinPos e π ε)) = π ε :=
  zagCycleHit_spec π _ _ _

private theorem zagCutHit_two_le {n : ℕ} (e π : Equiv.Perm (Fin n))
    {ε : Fin n} (hε : zagNontrivialAntiExceedance e π ε) :
    2 ≤ zagCutHit e π ε := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  have habpos := zagNTAE_min_lt_image e π hε
  have hbeps := zagNTAE_image_lt e π hε
  have hab_ne : a ≠ b := fun h => by
    apply (ne_of_lt habpos)
    exact e.injective (by simpa [a, b] using h)
  have hpos : 0 < zagCutHit e π ε :=
    zagCycleHit_pos π hab_ne _
  by_contra htwo
  have hone : zagCutHit e π ε = 1 := by omega
  have hp : π a = π ε := by
    simpa only [hone, pow_one, a] using zagCutHit_spec e π ε
  have haeps : a = ε := π.injective hp
  have : zagCycleMinPos e π ε = e.symm ε := by
    apply e.injective
    simpa [a] using haeps
  omega

private theorem zagCutHit_pred {n : ℕ} (e π : Equiv.Perm (Fin n))
    {ε : Fin n} (hε : zagNontrivialAntiExceedance e π ε) :
    (π ^ (zagCutHit e π ε - 1)) (e (zagCycleMinPos e π ε)) = ε := by
  have htwo := zagCutHit_two_le e π hε
  have hs := zagCutHit_spec e π ε
  rw [show zagCutHit e π ε = zagCutHit e π ε - 1 + 1 by omega,
    pow_succ', Equiv.Perm.mul_apply] at hs
  exact π.injective hs

private noncomputable def zagCutCandidates {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i =>
    e.symm (π ε) < i ∧ ∃ t : ℕ,
      0 < t ∧ t < zagCutHit e π ε ∧
        (π ^ t) (e (zagCycleMinPos e π ε)) = e i

private theorem zagCutCandidates_nonempty {n : ℕ}
    (e π : Equiv.Perm (Fin n)) {ε : Fin n}
    (hε : zagNontrivialAntiExceedance e π ε) :
    (zagCutCandidates e π ε).Nonempty := by
  classical
  refine ⟨e.symm ε, ?_⟩
  rw [zagCutCandidates, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, zagNTAE_image_lt e π hε,
    zagCutHit e π ε - 1, ?_⟩
  refine ⟨by have := zagCutHit_two_le e π hε; omega,
    by have := zagCutHit_two_le e π hε; omega, ?_⟩
  simpa using zagCutHit_pred e π hε

private noncomputable def zagCutPos {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) (hε : zagNontrivialAntiExceedance e π ε) : Fin n :=
  (zagCutCandidates e π ε).min' (zagCutCandidates_nonempty e π hε)

private theorem zagCutPos_mem {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) (hε : zagNontrivialAntiExceedance e π ε) :
    zagCutPos e π ε hε ∈ zagCutCandidates e π ε :=
  Finset.min'_mem _ _

private theorem zagImage_lt_cutPos {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) (hε : zagNontrivialAntiExceedance e π ε) :
    e.symm (π ε) < zagCutPos e π ε hε := by
  classical
  have hm := zagCutPos_mem e π ε hε
  rw [zagCutCandidates] at hm
  exact (Finset.mem_filter.mp hm).2.1

private theorem zagCutPos_path {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) (hε : zagNontrivialAntiExceedance e π ε) :
    ∃ t : ℕ, 0 < t ∧ t < zagCutHit e π ε ∧
      (π ^ t) (e (zagCycleMinPos e π ε)) = e (zagCutPos e π ε hε) := by
  classical
  have hm := zagCutPos_mem e π ε hε
  rw [zagCutCandidates] at hm
  exact (Finset.mem_filter.mp hm).2.2

private theorem zagCutPos_min {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) (hε : zagNontrivialAntiExceedance e π ε)
    {i : Fin n} (hi : i ∈ zagCutCandidates e π ε) :
    zagCutPos e π ε hε ≤ i :=
  Finset.min'_le _ _ hi

private theorem zagCutHit_no_return {n : ℕ} (e π : Equiv.Perm (Fin n))
    (ε : Fin n) {r : ℕ} (hr0 : 0 < r) (hrh : r < zagCutHit e π ε) :
    (π ^ r) (e (zagCycleMinPos e π ε)) ≠
      e (zagCycleMinPos e π ε) := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let H := zagCutHit e π ε
  let hab : π.SameCycle a b := (zagCycleMinPos_mem e π ε).apply_right
  intro hreturn
  have hearly : (π ^ (H - r)) a = b := by
    calc
      (π ^ (H - r)) a = (π ^ (H - r)) ((π ^ r) a) := by rw [hreturn]
      _ = (π ^ ((H - r) + r)) a := by
        rw [pow_add, Equiv.Perm.mul_apply]
      _ = (π ^ H) a := by congr 2; omega
      _ = b := by simpa [a, b, H] using zagCutHit_spec e π ε
  have hmin : H ≤ H - r := by
    exact zagCycleHit_minimal π a b hab hearly
  omega

private theorem zagCutAfterSwap_same_image {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    (π * Equiv.swap (e (zagCycleMinPos e π ε))
      (e (zagCutPos e π ε hε))).SameCycle
        (e (zagCycleMinPos e π ε)) (π ε) := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  let H := zagCutHit e π ε
  obtain ⟨t, ht0, htH, htc⟩ := zagCutPos_path e π ε hε
  have hac : (π ^ t) a = c := by simpa [a, c] using htc
  have hH : (π ^ H) a = b := by
    simpa [a, b, H] using zagCutHit_spec e π ε
  have htadd : t + (H - t) = H := by omega
  have hpath : ∀ r : ℕ, 0 < r → r ≤ H - t →
      ((π * Equiv.swap a c) ^ r) a = (π ^ (t + r)) a := by
    intro r hr0 hrd
    induction r using Nat.case_strong_induction_on with
    | hz => omega
    | hi r ih =>
        by_cases hrz : r = 0
        · subst r
          calc
            ((π * Equiv.swap a c) ^ (0 + 1)) a =
                (π * Equiv.swap a c) a := by simp
            _ = π c := by simp [Equiv.Perm.mul_apply]
            _ = π ((π ^ t) a) := by rw [hac]
            _ = (π ^ (t + (0 + 1))) a := by
              simpa only [Nat.zero_add, Equiv.Perm.mul_apply] using
                (congrArg (fun q : Equiv.Perm (Fin n) => q a)
                  (pow_succ' π t)).symm
        · have hr0' : 0 < r := Nat.pos_of_ne_zero hrz
          have hrd' : r ≤ H - t := by omega
          have ih' := ih r le_rfl hr0' hrd'
          have hjH : t + r < H := by omega
          have hja : (π ^ (t + r)) a ≠ a := by
            apply zagCutHit_no_return e π ε
            · omega
            · simpa [H] using hjH
          have hjc : (π ^ (t + r)) a ≠ c := by
            intro hjc
            have hperiod : (π ^ r) a = a := by
              apply (π ^ t).injective
              simpa [pow_add, Equiv.Perm.mul_apply, hac] using hjc
            exact zagCutHit_no_return e π ε hr0' (by omega) hperiod
          calc
            ((π * Equiv.swap a c) ^ (r + 1)) a =
                (π * Equiv.swap a c) (((π * Equiv.swap a c) ^ r) a) := by
              simpa only [Equiv.Perm.mul_apply] using
                congrArg (fun q : Equiv.Perm (Fin n) => q a)
                  (pow_succ' (π * Equiv.swap a c) r)
            _ = (π * Equiv.swap a c) ((π ^ (t + r)) a) := by rw [ih']
            _ = π ((π ^ (t + r)) a) := by
              rw [Equiv.Perm.mul_apply,
                Equiv.swap_apply_of_ne_of_ne hja hjc]
            _ = (π ^ (t + (r + 1))) a := by
              rw [show t + (r + 1) = (t + r) + 1 by omega]
              simpa only [Equiv.Perm.mul_apply] using
                (congrArg (fun q : Equiv.Perm (Fin n) => q a)
                  (pow_succ' π (t + r))).symm
  have hdpos : 0 < H - t := by omega
  refine ⟨((H - t : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, hpath (H - t) hdpos le_rfl, htadd, hH]

private theorem zagNTAE_triangle_count {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    cycleQuotientCount
        (π * zagTriangle (e (zagCycleMinPos e π ε)) (π ε)
          (e (zagCutPos e π ε hε))) =
      cycleQuotientCount π + 2 := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  have habpos : e.symm a < e.symm b := by
    simpa [a, b] using zagNTAE_min_lt_image e π hε
  have hbcpos : e.symm b < e.symm c := by
    simpa [b, c] using zagImage_lt_cutPos e π ε hε
  have hac_ne : a ≠ c := fun h => by
    have := congrArg e.symm h
    omega
  have hab_ne : a ≠ b := fun h => by
    have := congrArg e.symm h
    omega
  have hac : π.SameCycle a c := by
    obtain ⟨t, _, _, ht⟩ := zagCutPos_path e π ε hε
    exact ⟨(t : ℤ), by simpa [a, c] using ht⟩
  exact zagCycleQuotientCount_mul_triangle π hac_ne hac hab_ne
    (by simpa [a, b, c] using zagCutAfterSwap_same_image e π ε hε)

private noncomputable def zagSliceOrder {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    Equiv.Perm (Fin n) :=
  e * zagBlockSwap (zagCycleMinPos e π ε) (e.symm (π ε))
    (zagCutPos e π ε hε)
    (zagNTAE_min_lt_image e π hε)
    (zagImage_lt_cutPos e π ε hε)

private noncomputable def zagSliceVertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    Equiv.Perm (Fin n) :=
  π * zagTriangle (e (zagCycleMinPos e π ε)) (π ε)
    (e (zagCutPos e π ε hε))

private theorem zagSliceVertical_eq {n : ℕ}
    (D e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hπ : π = zagVertical D e) :
    zagSliceVertical e π ε hε = zagVertical D (zagSliceOrder e π ε hε) := by
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  calc
    zagSliceVertical e π ε hε =
        π * zagTriangle (e i) (e j) (e l) := by
      simp only [zagSliceVertical, i, j, l, e.apply_symm_apply]
    _ = zagVertical D e * zagTriangle (e i) (e j) (e l) := by rw [hπ]
    _ = zagVertical D (e * zagBlockSwap i j l hij hjl) := by
      rw [zagVertical_blockSwap]
    _ = zagVertical D (zagSliceOrder e π ε hε) := by
      rfl

private theorem zagSliceOrder_apply_zero {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let z : Fin n := ⟨0, lt_of_le_of_lt (Nat.zero_le _) ε.isLt⟩
    zagSliceOrder e π ε hε z = e z := by
  dsimp only
  have hz : (⟨0, lt_of_le_of_lt (Nat.zero_le _) ε.isLt⟩ : Fin n) ≤
      zagCycleMinPos e π ε := by
    rw [Fin.le_iff_val_le_val]
    exact Nat.zero_le _
  simp [zagSliceOrder, Equiv.Perm.mul_apply, zagBlockSwap,
    zagBlockSwapNat, hz]

private theorem zagSliceOrder_apply_left {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    zagSliceOrder e π ε hε (zagCycleMinPos e π ε) =
      e (zagCycleMinPos e π ε) := by
  exact congrArg e (zagBlockSwap_apply_left _ _ _ _ _)

private theorem zagSliceOrder_apply_middle {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    zagSliceOrder e π ε hε (zagBlockMiddle i j l hij hjl) = e l := by
  dsimp only
  exact congrArg e (zagBlockSwap_apply_middle _ _ _ _ _)

private theorem zagSliceOrder_apply_right {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    zagSliceOrder e π ε hε (zagCutPos e π ε hε) = π ε := by
  calc
    zagSliceOrder e π ε hε (zagCutPos e π ε hε) =
        e (e.symm (π ε)) :=
      congrArg e (zagBlockSwap_apply_right _ _ _ _ _)
    _ = π ε := e.apply_symm_apply _

private theorem zagSliceVertical_count {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    cycleQuotientCount (zagSliceVertical e π ε hε) =
      cycleQuotientCount π + 2 :=
  zagNTAE_triangle_count e π ε hε

private theorem zagSliceVertical_pairwise {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let π' := zagSliceVertical e π ε hε
    let a := e (zagCycleMinPos e π ε)
    let b := π ε
    let c := e (zagCutPos e π ε hε)
    ¬π'.SameCycle a b ∧ ¬π'.SameCycle a c ∧
      ¬π'.SameCycle b c := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  have habpos : e.symm a < e.symm b := by
    simpa [a, b] using zagNTAE_min_lt_image e π hε
  have hbcpos : e.symm b < e.symm c := by
    simpa [b, c] using zagImage_lt_cutPos e π ε hε
  have hac_ne : a ≠ c := fun h => by
    have := congrArg e.symm h
    omega
  have hab_ne : a ≠ b := fun h => by
    have := congrArg e.symm h
    omega
  have hac : π.SameCycle a c := by
    obtain ⟨t, _, _, ht⟩ := zagCutPos_path e π ε hε
    exact ⟨(t : ℤ), by simpa [a, c] using ht⟩
  simpa only [zagSliceVertical, a, b, c] using
    zagTriangle_split_pairwise π hac_ne hac hab_ne
      (by simpa [a, b, c] using zagCutAfterSwap_same_image e π ε hε)

private theorem zagSliceVertical_sameCycle_refines {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) {x y : Fin n}
    (hxy : (zagSliceVertical e π ε hε).SameCycle x y) :
    π.SameCycle x y := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  have hac : π.SameCycle a c := by
    obtain ⟨t, _, _, ht⟩ := zagCutPos_path e π ε hε
    exact ⟨(t : ℤ), by simpa [a, c] using ht⟩
  have hab : (π * Equiv.swap a c).SameCycle a b := by
    simpa [a, b, c] using zagCutAfterSwap_same_image e π ε hε
  exact zagSameCycle_mul_triangle_refines π hac hab (by
    simpa only [zagSliceVertical, a, b, c] using hxy)

private theorem zagSlice_cycleMinPos_left {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    zagCycleMinPos (zagSliceOrder e π ε hε)
        (zagSliceVertical e π ε hε)
        (e (zagCycleMinPos e π ε)) =
      zagCycleMinPos e π ε := by
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let B := zagBlockSwap i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let a := e i
  let m := zagCycleMinPos e' π' a
  have heim : e.symm (e' m) = B m := by
    simp only [e', zagSliceOrder, B, i, j, l,
      Equiv.Perm.mul_apply, e.symm_apply_apply]
  have hma : π'.SameCycle (e' m) a := zagCycleMinPos_mem e' π' a
  have hma_old : π.SameCycle (e' m) a :=
    zagSliceVertical_sameCycle_refines e π ε hε hma
  have hmina : zagCycleMinPos e π a = i := by
    exact (zagCycleMinPos_eq_of_sameCycle e π
      (zagCycleMinPos_mem e π ε)).trans rfl
  have himage : i ≤ e.symm (e' m) := by
    simpa only [hmina] using zagCycleMinPos_le e π hma_old
  have him : i ≤ m := by
    apply (zagBlockSwap_preserves_leftCut i j l m hij hjl).mp
    simpa [B, heim] using himage
  have hei : e' i = a := by
    simpa [e', a, i] using zagSliceOrder_apply_left e π ε hε
  have hmi : m ≤ i := by
    have hle := zagCycleMinPos_le e' π'
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle a a)
    have hinv : e'.symm a = i := by
      apply e'.injective
      simp [hei]
    simpa [m, hinv] using hle
  exact le_antisymm hmi him

private theorem zagSlice_cycleMinPos_before {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε r : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hr : r ∈ zagCycleMinima e π)
    (hri : r < zagCycleMinPos e π ε) :
    r ∈ zagCycleMinima (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε) := by
  classical
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  have her : e' r = e r := by
    simp only [e', zagSliceOrder, Equiv.Perm.mul_apply]
    congr 1
    apply Fin.ext
    simp [zagBlockSwap_val, zagBlockSwapNat,
      show (r : ℕ) ≤ (zagCycleMinPos e π ε : ℕ) from hri.le]
  rw [zag_mem_cycleMinima_iff] at hr ⊢
  let m := zagCycleMinPos e' π' (e' r)
  have hmcycle : π.SameCycle (e' m) (e r) := by
    apply zagSliceVertical_sameCycle_refines e π ε hε
    rw [← her]
    exact zagCycleMinPos_mem e' π' (e' r)
  have hpos : r ≤ e.symm (e' m) := by
    have hle := zagCycleMinPos_le e π hmcycle
    rwa [hr] at hle
  have hrm : r ≤ m := by
    by_cases hmi : m < i
    · have hem : e' m = e m := by
        simp only [e', zagSliceOrder, Equiv.Perm.mul_apply]
        congr 1
        apply Fin.ext
        simp [zagBlockSwap_val, zagBlockSwapNat,
          show (m : ℕ) ≤ (zagCycleMinPos e π ε : ℕ) from hmi.le]
      rwa [hem, e.symm_apply_apply] at hpos
    · exact hri.le.trans (le_of_not_gt hmi)
  have hmr : m ≤ r := by
    have hle := zagCycleMinPos_le e' π'
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle (e' r) (e' r))
    simpa only [e'.symm_apply_apply] using hle
  exact le_antisymm hmr hrm

private theorem zagSlice_cycleMinPos_middle {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    zagCycleMinPos (zagSliceOrder e π ε hε)
        (zagSliceVertical e π ε hε) (e l) =
      zagBlockMiddle i j l hij hjl := by
  classical
  dsimp only
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let B := zagBlockSwap i j l hij hjl
  let q := zagBlockMiddle i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let a := e i
  let b := π ε
  let c := e l
  let h := π * Equiv.swap a c
  let m := zagCycleMinPos e' π' c
  have hac_ne : a ≠ c := fun hac => by
    have := congrArg e.symm hac
    simp only [a, c, e.symm_apply_apply] at this
    omega
  obtain ⟨t, ht0, htH, htc⟩ := zagCutPos_path e π ε hε
  have hac : π.SameCycle a c :=
    ⟨(t : ℤ), by simpa [a, c, i, l] using htc⟩
  have hab : h.SameCycle a b := by
    simpa [h, a, b, c, i, l] using zagCutAfterSwap_same_image e π ε hε
  have hma : π'.SameCycle (e' m) c := zagCycleMinPos_mem e' π' c
  have hmc : h.SameCycle (e' m) c := by
    apply zagSameCycle_mul_swap_refines h hab
    simpa only [π', zagSliceVertical, h, a, b, c, i, l,
      zagTriangle, mul_assoc] using hma
  obtain ⟨r, hr0, hrT, hrx⟩ :=
    zagMulSwap_sameCycle_right_arc π hac_ne hac hmc.symm
  have hTlt : zagCycleHit π a c hac < zagCutHit e π ε := by
    have hTle := zagCycleHit_minimal π a c hac (by
      simpa [a, c, i, l] using htc)
    omega
  have hrH : r < zagCutHit e π ε := lt_of_le_of_lt hrT hTlt
  let p := e.symm (e' m)
  have hpB : p = B m := by
    simp only [p, e', zagSliceOrder, B, i, j, l,
      Equiv.Perm.mul_apply, e.symm_apply_apply]
  have hnot_ac : ¬h.SameCycle a c := by
    exact zagMulSwap_not_sameCycle π hac_ne hac
  have hp_ne : p ≠ i := by
    intro hpi
    have hem : e' m = a := by
      apply e.symm.injective
      simp [p, a, hpi]
    exact hnot_ac (by simpa [hem] using hmc)
  have hmina : zagCycleMinPos e π a = i := by
    exact (zagCycleMinPos_eq_of_sameCycle e π
      (zagCycleMinPos_mem e π ε)).trans rfl
  have hminc : zagCycleMinPos e π c = i := by
    exact (zagCycleMinPos_eq_of_sameCycle e π hac).symm.trans hmina
  have hip_le : i ≤ p := by
    have hold : π.SameCycle (e' m) c :=
      zagSliceVertical_sameCycle_refines e π ε hε hma
    simpa only [hminc, p] using zagCycleMinPos_le e π hold
  have hip : i < p := lt_of_le_of_ne hip_le (Ne.symm hp_ne)
  have hp_side : p ≤ j ∨ l ≤ p := by
    by_cases hpj : p ≤ j
    · exact Or.inl hpj
    · right
      apply zagCutPos_min e π ε hε
      rw [zagCutCandidates, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, lt_of_not_ge hpj, r, hr0, hrH, ?_⟩
      calc
        (π ^ r) (e (zagCycleMinPos e π ε)) = (π ^ r) a := by
          simp only [a, i]
        _ = e' m := hrx
        _ = e p := by simp only [p, e.apply_symm_apply]
  have hqm : q ≤ m := by
    have hq := zagBlockMiddle_le_unswap i j l p hij hjl hip hp_side
    have hm : B.symm p = m := by
      apply B.injective
      simp [hpB]
    simpa [q, B, hm] using hq
  have heq : e' q = c := by
    simpa [e', q, c, i, j, l] using
      zagSliceOrder_apply_middle e π ε hε
  have hmq : m ≤ q := by
    have hle := zagCycleMinPos_le e' π'
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle c c)
    have hinv : e'.symm c = q := by
      apply e'.injective
      simp [heq]
    simpa [m, hinv] using hle
  exact le_antisymm hmq hqm

private theorem zagSlice_residual_ne_cut {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    e (zagCutPos e π ε hε) ≠ ε := by
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let q := zagBlockMiddle i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let c := e l
  intro hcε
  have heq : e' q = ε := by
    rw [← hcε]
    simpa [e', q, c, i, j, l] using
      zagSliceOrder_apply_middle e π ε hε
  have hmin : zagCycleMinPos e' π' ε = q := by
    rw [← hcε]
    simpa [e', π', q, c, i, j, l] using
      zagSlice_cycleMinPos_middle e π ε hε
  by_cases hfix : π' ε = ε
  · apply hres.2
    change π' ε = e' (zagCycleMinPos e' π' ε)
    rw [hfix, hmin, heq]
  · apply hres.1
    simp only [zagExceedance]
    have hsame : π'.SameCycle (π' ε) ε :=
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle ε ε).apply_left
    have hle : q ≤ e'.symm (π' ε) := by
      simpa only [hmin] using zagCycleMinPos_le e' π' hsame
    have hne : e'.symm (π' ε) ≠ q := fun he => by
      apply hfix
      calc
        π' ε = e' (e'.symm (π' ε)) := (e'.apply_symm_apply _).symm
        _ = e' q := by rw [he]
        _ = ε := heq
    have heps : e'.symm ε = q := by
      apply e'.injective
      simp [heq]
    rw [heps]
    exact lt_of_le_of_ne hle hne.symm

private theorem zagSlice_residual_apply {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagSliceVertical e π ε hε ε = π ε := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  have hae : a ≠ ε := fun hae => by
    have hp := congrArg e.symm hae
    have h1 := zagNTAE_min_lt_image e π hε
    have h2 := zagNTAE_image_lt e π hε
    simp only [a, e.symm_apply_apply] at hp
    omega
  have hbe : b ≠ ε := fun hbe => by
    have hp := congrArg e.symm hbe
    have h2 := zagNTAE_image_lt e π hε
    simp only [b] at hp
    omega
  have hce : c ≠ ε := zagSlice_residual_ne_cut e π ε hε hres
  change π (zagTriangle a b c ε) = π ε
  simp only [zagTriangle, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hae.symm hbe.symm,
    Equiv.swap_apply_of_ne_of_ne hae.symm hce.symm]

private theorem zagSlice_residual_min_gt_middle {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    zagBlockMiddle i j l hij hjl <
      zagCycleMinPos (zagSliceOrder e π ε hε)
        (zagSliceVertical e π ε hε) ε := by
  classical
  dsimp only
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let B := zagBlockSwap i j l hij hjl
  let q := zagBlockMiddle i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let g := zagSliceVertical e π ε hε
  let a := e i
  let b := π ε
  let c := e l
  let hab : π.SameCycle a b := (zagCycleMinPos_mem e π ε).apply_right
  obtain ⟨t, ht0, htCut, htc⟩ := zagCutPos_path e π ε hε
  let hac : π.SameCycle a c := ⟨(t : ℤ), by simpa [a, c, i, l] using htc⟩
  let T := zagCycleHit π a c hac
  let H := zagCycleHit π a b hab
  let h := π * Equiv.swap a c
  let habh : h.SameCycle a b := by
    simpa [h, a, b, c, i, l] using zagCutAfterSwap_same_image e π ε hε
  let d := zagCycleMinPos e' g ε
  let x := e' d
  have hH : H = zagCutHit e π ε := by
    rfl
  have hTlt : T < H := by
    have hTle := zagCycleHit_minimal π a c hac (by
      simpa [a, c, i, l] using htc)
    rw [hH]
    omega
  have hg_apply : g ε = b := by
    simpa [g, b] using zagSlice_residual_apply e π ε hε hres
  have hxd : g.SameCycle x ε := zagCycleMinPos_mem e' g ε
  have hbx : g.SameCycle b x := by
    have hbε : g.SameCycle b ε := by
      have hs := (Equiv.Perm.SameCycle.rfl : g.SameCycle ε ε).apply_right
      simpa [hg_apply] using hs.symm
    exact hbε.trans hxd.symm
  have hg_form : g = h * Equiv.swap a b := by
    simp only [g, zagSliceVertical, h, a, b, c, i, l,
      zagTriangle, mul_assoc]
  have hbx' : (h * Equiv.swap a b).SameCycle b x := by
    simpa only [← hg_form] using hbx
  have hab_ne : a ≠ b := fun hab_eq => by
    have hp := congrArg e.symm hab_eq
    simp only [a, b, i, e.symm_apply_apply] at hp
    omega
  obtain ⟨s, hs0, hsU, hsx⟩ :=
    zagMulSwap_sameCycle_right_arc h hab_ne habh hbx'
  have hHTpos : 0 < H - T := by omega
  have hhpow : (h ^ (H - T)) a = b := by
    rw [zagFirstSwap_pow_between π hab hac hTlt hHTpos le_rfl]
    have hadd : T + (H - T) = H := by omega
    rw [hadd, zagCycleHit_spec π a b hab]
  have hUle : zagCycleHit h a b habh ≤ H - T :=
    zagCycleHit_minimal h a b habh hhpow
  have hsle : s ≤ H - T := hsU.trans hUle
  have hsx_old : (π ^ (T + s)) a = x := by
    have hp := zagFirstSwap_pow_between π hab hac hTlt hs0 hsle
    exact hp.symm.trans hsx
  let p := e.symm x
  have hpB : p = B d := by
    simp only [p, x, e', zagSliceOrder, B, i, j, l,
      Equiv.Perm.mul_apply, e.symm_apply_apply]
  obtain ⟨hgab, hgac, hgbc⟩ := zagSliceVertical_pairwise e π ε hε
  have hxa : x ≠ a := fun hxa => hgab (by simpa [hxa] using hbx.symm)
  have hxc : x ≠ c := fun hxc => hgbc (by simpa [hxc] using hbx)
  have hxeps_old : π.SameCycle x ε :=
    zagSliceVertical_sameCycle_refines e π ε hε hxd
  have hminx : zagCycleMinPos e π x = i := by
    exact (zagCycleMinPos_eq_of_sameCycle e π hxeps_old).trans rfl
  have hip_le : i ≤ p := by
    simpa only [hminx, p] using zagCycleMinPos_le e π hxeps_old
  have hip : i < p := by
    apply lt_of_le_of_ne hip_le
    intro hip
    apply hxa
    apply e.symm.injective
    simp [p, a, hip]
  have hp_side : p ≤ j ∨ l ≤ p := by
    by_cases hpj : p ≤ j
    · exact Or.inl hpj
    · right
      have hrs_le : T + s ≤ H := by omega
      have hrs_ne : T + s ≠ H := by
        intro hrs
        have hxb : x = b := by
          rw [← hsx_old, hrs, zagCycleHit_spec π a b hab]
        have hpj_eq : p = j := by
          simp [p, j, b, hxb]
        exact hpj hpj_eq.le
      apply zagCutPos_min e π ε hε
      rw [zagCutCandidates, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, lt_of_not_ge hpj, T + s, by omega, ?_, ?_⟩
      · rw [← hH]
        exact lt_of_le_of_ne hrs_le hrs_ne
      · calc
          (π ^ (T + s)) (e (zagCycleMinPos e π ε)) =
              (π ^ (T + s)) a := by simp only [a, i]
          _ = x := hsx_old
          _ = e p := by simp only [p, e.apply_symm_apply]
  have hqd : q ≤ d := by
    have hq := zagBlockMiddle_le_unswap i j l p hij hjl hip hp_side
    have hd : B.symm p = d := by
      apply B.injective
      simp [hpB]
    simpa [q, B, hd] using hq
  have hqd_ne : q ≠ d := fun hqd_eq => by
    apply hxc
    have heq : e' q = c := by
      simpa [e', q, c, i, j, l] using
        zagSliceOrder_apply_middle e π ε hε
    simpa [x, hqd_eq] using heq
  exact lt_of_le_of_ne hqd hqd_ne

private theorem zagSlice_terminal_cycleMinPos_right {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagCycleMinPos (zagSliceOrder e π ε hε)
        (zagSliceVertical e π ε hε) (π ε) =
      zagCutPos e π ε hε := by
  classical
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let B := zagBlockSwap i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let g := zagSliceVertical e π ε hε
  let a := e i
  let b := π ε
  let c := e l
  let d := zagCycleMinPos e' g b
  have heb : e' l = b := by
    simpa [e', l, b] using zagSliceOrder_apply_right e π ε hε
  have hbinv : e'.symm b = l := by
    apply e'.injective
    simp [heb]
  have hdl : d ≤ l := by
    have hle := zagCycleMinPos_le e' g
      (Equiv.Perm.SameCycle.rfl : g.SameCycle b b)
    simpa [d, hbinv] using hle
  apply le_antisymm hdl
  by_contra hnle
  have hdl' : d < l := lt_of_not_ge hnle
  by_cases hcε : c = ε
  · have hab_ne : a ≠ b := fun hab => by
      have hp := congrArg e.symm hab
      simp only [a, b, i, e.symm_apply_apply] at hp
      omega
    have hac_ne : a ≠ c := fun hac => by
      have hp := congrArg e.symm hac
      simp only [a, c, i, l, e.symm_apply_apply] at hp
      omega
    have hbc_ne : b ≠ c := fun hbc => by
      have hp := congrArg e.symm hbc
      simp only [b, c, l, e.symm_apply_apply] at hp
      omega
    have hgb : g b = b := by
      change π (zagTriangle a b c b) = b
      have htri : zagTriangle a b c b = c := by
        simp [zagTriangle, Equiv.Perm.mul_apply]
      rw [htri, hcε]
    have hdb : e' d = b :=
      (zagCycleMinPos_mem e' g b).eq_of_right hgb
    have : d = l := by
      apply e'.injective
      simpa [heb] using hdb
    omega
  · have hae : a ≠ ε := fun hae => by
      have hp := congrArg e.symm hae
      have h1 := zagNTAE_min_lt_image e π hε
      have h2 := zagNTAE_image_lt e π hε
      simp only [a, i, e.symm_apply_apply] at hp
      omega
    have hbe : b ≠ ε := fun hbe => by
      have hp := congrArg e.symm hbe
      have h2 := zagNTAE_image_lt e π hε
      simp only [b] at hp
      omega
    have hge : g ε = b := by
      change π (zagTriangle a b c ε) = π ε
      simp only [zagTriangle, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hae.symm hbe.symm,
        Equiv.swap_apply_of_ne_of_ne hae.symm (Ne.symm hcε)]
    have hl_eps_le : l ≤ e.symm ε := by
      apply zagCutPos_min e π ε hε
      rw [zagCutCandidates, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, zagNTAE_image_lt e π hε,
        zagCutHit e π ε - 1, ?_, ?_, ?_⟩
      · have := zagCutHit_two_le e π hε
        omega
      · have := zagCutHit_two_le e π hε
        omega
      · simpa using zagCutHit_pred e π hε
    have hl_eps : l < e.symm ε := by
      apply lt_of_le_of_ne hl_eps_le
      intro heq
      apply hcε
      apply e.symm.injective
      simpa [c, l] using heq
    have heps : e'.symm ε = e.symm ε := by
      have hB := zagBlockSwap_symm_apply_of_right i j l (e.symm ε)
        hij hjl hl_eps
      change (e * B)⁻¹ ε = e.symm ε
      rw [mul_inv_rev, Equiv.Perm.mul_apply]
      exact hB
    have hanti : ¬zagExceedance e' g ε := by
      simp only [zagExceedance, hge, hbinv, heps]
      omega
    have hnontriv : ¬zagTrivialAntiExceedance e' g ε := by
      have hεb : g.SameCycle ε b := by
        have hs := (Equiv.Perm.SameCycle.rfl : g.SameCycle ε ε).apply_right
        simpa [hge] using hs
      have hmineps : zagCycleMinPos e' g ε = d :=
        zagCycleMinPos_eq_of_sameCycle e' g hεb
      simp only [zagTrivialAntiExceedance, hge]
      intro hbd
      have : l = d := by
        apply e'.injective
        calc
          e' l = b := heb
          _ = e' (zagCycleMinPos e' g ε) := hbd
          _ = e' d := by rw [hmineps]
      omega
    exact hterm ⟨hanti, hnontriv⟩

private noncomputable def zagSliceMarked {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) : Finset (Fin n) :=
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  {zagCycleMinPos e' π' (e (zagCycleMinPos e π ε)),
    zagCycleMinPos e' π' (π ε),
    zagCycleMinPos e' π' (e (zagCutPos e π ε hε))}

private theorem zagSliceMarked_eq_terminal {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    zagSliceMarked e π ε hε =
      {i, zagBlockMiddle i j l hij hjl, l} := by
  dsimp only
  rw [zagSliceMarked]
  simp only [zagSlice_cycleMinPos_left,
    zagSlice_terminal_cycleMinPos_right e π ε hε hterm,
    zagSlice_cycleMinPos_middle]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem zagSliceMarked_eq_residual {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    let e' := zagSliceOrder e π ε hε
    let π' := zagSliceVertical e π ε hε
    zagSliceMarked e π ε hε =
      {i, zagBlockMiddle i j l hij hjl, zagCycleMinPos e' π' ε} := by
  dsimp only
  rw [zagSliceMarked]
  have happ := zagSlice_residual_apply e π ε hε hres
  have hsame : (zagSliceVertical e π ε hε).SameCycle
      (π ε) ε := by
    have hs := (Equiv.Perm.SameCycle.rfl :
      (zagSliceVertical e π ε hε).SameCycle ε ε).apply_right
    simpa [happ] using hs.symm
  rw [zagSlice_cycleMinPos_left, zagSlice_cycleMinPos_middle,
    zagCycleMinPos_eq_of_sameCycle _ _ hsame]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem zagSlice_merge_order {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    let q := zagBlockMiddle i j l hij hjl
    zagSliceOrder e π ε hε * zagBlockSwap i q l
        (zagBlockMiddle_bounds i j l hij hjl).1
        (zagBlockMiddle_bounds i j l hij hjl).2 = e := by
  dsimp only
  rw [zagSliceOrder, mul_assoc, zagBlockSwap_mul_reverse, mul_one]

private theorem zagSlice_merge_vertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    let q := zagBlockMiddle i j l hij hjl
    let e' := zagSliceOrder e π ε hε
    zagSliceVertical e π ε hε * zagTriangle (e' i) (e' q) (e' l) = π := by
  dsimp only
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  have hab : a ≠ b := fun h => by
    have hp := congrArg e.symm h
    have hlt := zagNTAE_min_lt_image e π hε
    exact (ne_of_lt hlt) (by simpa [a, b] using hp)
  have hac : a ≠ c := fun h => by
    have hp := congrArg e.symm h
    have h1 := zagNTAE_min_lt_image e π hε
    have h2 := zagImage_lt_cutPos e π ε hε
    simp only [a, c, e.symm_apply_apply] at hp
    omega
  have hbc : b ≠ c := fun h => by
    have hp := congrArg e.symm h
    have h2 := zagImage_lt_cutPos e π ε hε
    simp only [b, c, e.symm_apply_apply] at hp
    omega
  rw [zagSliceOrder_apply_left, zagSliceOrder_apply_middle,
    zagSliceOrder_apply_right]
  change (π * zagTriangle a b c) * zagTriangle a c b = π
  rw [mul_assoc, zagTriangle_mul_reverse hab hac hbc, mul_one]

private theorem zagMarkedTriple_pairwise {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) :
    ¬π.SameCycle (e m.first) (e m.middle) ∧
      ¬π.SameCycle (e m.first) (e m.third) ∧
      ¬π.SameCycle (e m.middle) (e m.third) := by
  have hfirst := (zag_mem_cycleMinima_iff e π m.first).mp m.first_mem
  have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
  have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
  constructor
  · intro hsame
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    rw [hfirst, hmiddle] at hmin
    exact m.first_lt_middle.ne hmin
  constructor
  · intro hsame
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    rw [hfirst, hthird] at hmin
    exact (m.first_lt_middle.trans m.middle_lt_third).ne hmin
  · intro hsame
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    rw [hmiddle, hthird] at hmin
    exact m.middle_lt_third.ne hmin

private noncomputable def zagMergeOrder {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    Equiv.Perm (Fin n) :=
  e * zagBlockSwap m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third

private noncomputable def zagMergeVertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    Equiv.Perm (Fin n) :=
  π * zagTriangle (e m.first) (e m.middle) (e m.third)

private noncomputable def zagMergePoint {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) : Fin n :=
  (zagMergeVertical e π m).symm (e m.third)

private theorem zagMergeOrder_symm_apply {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (x : Fin n) :
    (zagMergeOrder e π m).symm (e x) =
      (zagBlockSwap m.first m.middle m.third
        m.first_lt_middle m.middle_lt_third).symm x := by
  let B := zagBlockSwap m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third
  change ((e * B)⁻¹) (e x) = B⁻¹ x
  rw [mul_inv_rev, Equiv.Perm.mul_apply]
  change B.symm (e.symm (e x)) = B.symm x
  rw [e.symm_apply_apply]

private theorem zagMergeVertical_sameCycles {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let π' := zagMergeVertical e π m
    π'.SameCycle (e m.first) (e m.middle) ∧
      π'.SameCycle (e m.first) (e m.third) := by
  obtain ⟨hfm, hft, hmt⟩ := zagMarkedTriple_pairwise m
  exact zagTriangle_merge_sameCycles π hfm hft hmt

private theorem zagMergeVertical_apply_point {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    zagMergeVertical e π m (zagMergePoint e π m) = e m.third := by
  exact Equiv.apply_symm_apply _ _

private theorem zagMergePoint_eq_middle_of_fixed {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π)
    (hfix : π.symm (e m.third) = e m.third) :
    zagMergePoint e π m = e m.middle := by
  have hfm : e m.first ≠ e m.middle :=
    e.injective.ne (ne_of_lt m.first_lt_middle)
  have hft : e m.first ≠ e m.third :=
    e.injective.ne (ne_of_lt (m.first_lt_middle.trans m.middle_lt_third))
  have hmt : e m.middle ≠ e m.third :=
    e.injective.ne (ne_of_lt m.middle_lt_third)
  rw [zagMergePoint, zagMergeVertical]
  change (zagTriangle (e m.first) (e m.middle) (e m.third))⁻¹
      (π.symm (e m.third)) = e m.middle
  rw [zagTriangle_inv hfm hft hmt, hfix,
    zagTriangle_apply_middle]

private theorem zagMergePoint_eq_preimage_of_not_fixed {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π)
    (hfix : π.symm (e m.third) ≠ e m.third) :
    zagMergePoint e π m = π.symm (e m.third) := by
  let y := π.symm (e m.third)
  have hyc : π.SameCycle y (e m.third) := by
    have h := (Equiv.Perm.SameCycle.rfl : π.SameCycle y y).apply_left
    simpa [y] using h.symm
  obtain ⟨hfm_cycle, hft_cycle, hmt_cycle⟩ := zagMarkedTriple_pairwise m
  have hyf : y ≠ e m.first := fun hy => hft_cycle (by simpa [hy] using hyc)
  have hym : y ≠ e m.middle := fun hy => hmt_cycle (by simpa [hy] using hyc)
  have hyt : y ≠ e m.third := hfix
  have hfm : e m.first ≠ e m.middle :=
    e.injective.ne (ne_of_lt m.first_lt_middle)
  have hft : e m.first ≠ e m.third :=
    e.injective.ne (ne_of_lt (m.first_lt_middle.trans m.middle_lt_third))
  have hmt : e m.middle ≠ e m.third :=
    e.injective.ne (ne_of_lt m.middle_lt_third)
  rw [zagMergePoint, zagMergeVertical]
  change (zagTriangle (e m.first) (e m.middle) (e m.third))⁻¹ y = y
  rw [zagTriangle_inv hfm hft hmt,
    zagTriangle_apply_of_ne hyf hyt hym]

private theorem zagMergePoint_nontrivialAntiExceedance {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    zagNontrivialAntiExceedance (zagMergeOrder e π m)
      (zagMergeVertical e π m) (zagMergePoint e π m) := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let q := zagBlockMiddle m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third
  have hq := zagBlockMiddle_bounds m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third
  have hpos_first : e'.symm (e m.first) = m.first := by
    change (zagMergeOrder e π m).symm (e m.first) = m.first
    rw [zagMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_left]
  have hpos_middle : e'.symm (e m.middle) = m.third := by
    change (zagMergeOrder e π m).symm (e m.middle) = m.third
    rw [zagMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_middle]
  have hpos_third : e'.symm (e m.third) = q := by
    change (zagMergeOrder e π m).symm (e m.third) = q
    rw [zagMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  have happ : π' ε = e m.third := by
    exact zagMergeVertical_apply_point e π m
  constructor
  · intro hexc
    simp only [zagExceedance] at hexc
    change e'.symm ε < e'.symm (π' ε) at hexc
    rw [happ, hpos_third] at hexc
    by_cases hfix : π.symm (e m.third) = e m.third
    · have hε := zagMergePoint_eq_middle_of_fixed e π m hfix
      change ε = e m.middle at hε
      rw [hε, hpos_middle] at hexc
      exact (not_lt_of_ge hq.2.le) hexc
    · let y := π.symm (e m.third)
      have hyc : π.SameCycle y (e m.third) := by
        have h := (Equiv.Perm.SameCycle.rfl : π.SameCycle y y).apply_left
        simpa [y] using h.symm
      have hmin := zagCycleMinPos_le e π hyc
      have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
      rw [hthird] at hmin
      have hpos_ne : e.symm y ≠ m.third := by
        intro heq
        apply hfix
        apply e.symm.injective
        simpa [y] using heq
      have hlt : m.third < e.symm y := lt_of_le_of_ne hmin hpos_ne.symm
      have hpos_y : e'.symm y = e.symm y := by
        change (zagMergeOrder e π m).symm y = e.symm y
        have hs := zagMergeOrder_symm_apply e π m (e.symm y)
        simp only [e.apply_symm_apply] at hs
        rw [hs, zagBlockSwap_symm_apply_of_right _ _ _ _
          m.first_lt_middle m.middle_lt_third hlt]
      have hε := zagMergePoint_eq_preimage_of_not_fixed e π m hfix
      change ε = y at hε
      rw [hε, hpos_y] at hexc
      omega
  · intro htriv
    simp only [zagTrivialAntiExceedance] at htriv
    have hmin_eq : zagCycleMinPos e' π' ε = q := by
      calc
        zagCycleMinPos e' π' ε = e'.symm (e' (zagCycleMinPos e' π' ε)) := by
          rw [e'.symm_apply_apply]
        _ = e'.symm (π' ε) := by rw [htriv]
        _ = e'.symm (e m.third) := by rw [happ]
        _ = q := hpos_third
    obtain ⟨hfm, hft⟩ := zagMergeVertical_sameCycles e π m
    change π'.SameCycle (e m.first) (e m.middle) at hfm
    change π'.SameCycle (e m.first) (e m.third) at hft
    have htε : π'.SameCycle (e m.third) ε := by
      have h := (Equiv.Perm.SameCycle.rfl : π'.SameCycle ε ε).apply_left
      simpa [happ] using h
    have hfε : π'.SameCycle (e m.first) ε := hft.trans htε
    have hle := zagCycleMinPos_le e' π' hfε
    rw [hmin_eq, hpos_first] at hle
    exact (not_le_of_gt hq.1) hle

private theorem zagMerge_cycleMinPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    zagCycleMinPos (zagMergeOrder e π m) (zagMergeVertical e π m)
      (zagMergePoint e π m) = m.first := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  have hpos_first : e'.symm (e m.first) = m.first := by
    change (zagMergeOrder e π m).symm (e m.first) = m.first
    rw [zagMergeOrder_symm_apply, zagBlockSwap_symm_apply_left]
  obtain ⟨hfm, hft, hmt⟩ := zagMarkedTriple_pairwise m
  obtain ⟨hmerge_middle, hmerge_third⟩ :=
    zagMergeVertical_sameCycles e π m
  change π'.SameCycle (e m.first) (e m.middle) at hmerge_middle
  change π'.SameCycle (e m.first) (e m.third) at hmerge_third
  have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
  have htε : π'.SameCycle (e m.third) ε := by
    have h := (Equiv.Perm.SameCycle.rfl : π'.SameCycle ε ε).apply_left
    simpa [happ] using h
  have hfε : π'.SameCycle (e m.first) ε := hmerge_third.trans htε
  apply le_antisymm
  · have hle := zagCycleMinPos_le e' π' hfε
    rwa [hpos_first] at hle
  · let d := zagCycleMinPos e' π' ε
    let z := e' d
    have hzε : π'.SameCycle z ε := by
      exact zagCycleMinPos_mem e' π' ε
    have hfz : π'.SameCycle (e m.first) z := hfε.trans hzε.symm
    have hcases : π.SameCycle (e m.first) z ∨
        π.SameCycle (e m.middle) z ∨ π.SameCycle (e m.third) z := by
      apply zagTriangle_merge_cases π hfm hft hmt
      simpa only [π', zagMergeVertical] using hfz
    have hfirst := (zag_mem_cycleMinima_iff e π m.first).mp m.first_mem
    have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
    have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
    have htarget : m.first ≤ e.symm z := by
      rcases hcases with hfz' | hmz' | htz'
      · have hle := zagCycleMinPos_le e π hfz'.symm
        rwa [hfirst] at hle
      · have hle := zagCycleMinPos_le e π hmz'.symm
        rw [hmiddle] at hle
        exact m.first_lt_middle.le.trans hle
      · have hle := zagCycleMinPos_le e π htz'.symm
        rw [hthird] at hle
        exact (m.first_lt_middle.trans m.middle_lt_third).le.trans hle
    have hswap : m.first ≤
        (zagBlockSwap m.first m.middle m.third
          m.first_lt_middle m.middle_lt_third).symm (e.symm z) :=
      (zagBlockSwap_symm_preserves_leftCut _ _ _ _
        m.first_lt_middle m.middle_lt_third).mpr htarget
    have horder := zagMergeOrder_symm_apply e π m (e.symm z)
    simp only [e.apply_symm_apply] at horder
    calc
      m.first ≤ e'.symm z := by
        change m.first ≤ (zagMergeOrder e π m).symm z
        rwa [horder]
      _ = d := by simp [z]

private theorem zagMerge_cycleMinPos_before {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (r : Fin n)
    (hr : r ∈ zagCycleMinima e π) (hrf : r < m.first) :
    r ∈ zagCycleMinima (zagMergeOrder e π m)
      (zagMergeVertical e π m) := by
  classical
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  have her : e' r = e r := by
    simp only [e', zagMergeOrder, Equiv.Perm.mul_apply]
    congr 1
    apply Fin.ext
    simp [zagBlockSwap_val, zagBlockSwapNat,
      show (r : ℕ) ≤ (m.first : ℕ) from hrf.le]
  have hrf_cycle : ¬π.SameCycle (e r) (e m.first) :=
    zagCycleMinima_not_same_of_lt e π hr m.first_mem hrf
  have hrm_cycle : ¬π.SameCycle (e r) (e m.middle) :=
    zagCycleMinima_not_same_of_lt e π hr m.middle_mem
      (hrf.trans m.first_lt_middle)
  have hrt_cycle : ¬π.SameCycle (e r) (e m.third) :=
    zagCycleMinima_not_same_of_lt e π hr m.third_mem
      (hrf.trans (m.first_lt_middle.trans m.middle_lt_third))
  rw [zag_mem_cycleMinima_iff] at hr ⊢
  let d := zagCycleMinPos e' π' (e' r)
  have hdcycle : π.SameCycle (e r) (e' d) := by
    apply (zagSameCycle_mul_triangle_iff_of_disjoint π
      hrf_cycle hrm_cycle hrt_cycle).mp
    have hnew : π'.SameCycle (e r) (e' d) := by
      rw [← her]
      exact (zagCycleMinPos_mem e' π' (e' r)).symm
    simpa only [π', zagMergeVertical] using hnew
  have hpos : r ≤ e.symm (e' d) := by
    have hle := zagCycleMinPos_le e π hdcycle.symm
    rwa [hr] at hle
  have hrd : r ≤ d := by
    by_cases hdf : d < m.first
    · have hed : e' d = e d := by
        simp only [e', zagMergeOrder, Equiv.Perm.mul_apply]
        congr 1
        apply Fin.ext
        simp [zagBlockSwap_val, zagBlockSwapNat,
          show (d : ℕ) ≤ (m.first : ℕ) from hdf.le]
      rwa [hed, e.symm_apply_apply] at hpos
    · exact hrf.le.trans (le_of_not_gt hdf)
  have hdr : d ≤ r := by
    have hle := zagCycleMinPos_le e' π'
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle (e' r) (e' r))
    simpa only [e'.symm_apply_apply] using hle
  exact le_antisymm hdr hrd

private theorem zagMerge_cutHit {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let e' := zagMergeOrder e π m
    let π' := zagMergeVertical e π m
    let ε := zagMergePoint e π m
    zagCutHit e' π' ε =
      zagReturnTime π (e m.middle) + zagReturnTime π (e m.third) := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let a := e m.first
  let b := e m.middle
  let c := e m.third
  let Lb := zagReturnTime π b
  let Lc := zagReturnTime π c
  obtain ⟨hab, hac, hbc⟩ := zagMarkedTriple_pairwise m
  have hac' : π'.SameCycle a c := by
    exact (zagMergeVertical_sameCycles e π m).2
  have hac_ne : a ≠ c := fun h => hac (h.sameCycle π)
  have hsum : (π' ^ (Lb + Lc)) a = c := by
    have hp := zagTriangle_merge_pow_after_left π hab hac hbc
      (zagReturnTime_pos π c) (le_refl (zagReturnTime π c))
    simpa only [π', zagMergeVertical, a, b, c, Lb, Lc] using
      hp.trans (zagReturnTime_spec π c)
  have hno (r : ℕ) (hr0 : 0 < r) (hr : r < Lb + Lc) :
      (π' ^ r) a ≠ c := by
    by_cases hrb : r ≤ Lb
    · have hp := zagTriangle_merge_pow_left π hab hac hbc hr0 hrb
      intro hrc
      apply hbc
      refine ⟨(r : ℤ), ?_⟩
      rw [zpow_natCast]
      have hp' : (π' ^ r) a = (π ^ r) b := by
        simpa only [π', zagMergeVertical, a, b, c] using hp
      exact hp'.symm.trans hrc
    · let s := r - Lb
      have hs0 : 0 < s := by omega
      have hslt : s < Lc := by omega
      have hp := zagTriangle_merge_pow_after_left π hab hac hbc hs0 hslt.le
      have hpr : (π' ^ r) a = (π ^ s) c := by
        simpa only [π', zagMergeVertical, a, b, c, Lb, Lc, s,
          show Lb + (r - Lb) = r by omega] using hp
      intro hrc
      exact zagReturnTime_no_return π c hs0 hslt (hpr.symm.trans hrc)
  let H := zagCycleHit π' a c hac'
  have hHle : H ≤ Lb + Lc :=
    zagCycleHit_minimal π' a c hac' hsum
  have hleH : Lb + Lc ≤ H := by
    by_contra h
    have hHlt : H < Lb + Lc := by omega
    have hHpos := zagCycleHit_pos π' hac_ne hac'
    exact hno H hHpos hHlt (zagCycleHit_spec π' a c hac')
  have hH : H = Lb + Lc := le_antisymm hHle hleH
  change zagCutHit e' π' ε = Lb + Lc
  rw [zagCutHit]
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have hfirst : e' m.first = a := by
    change zagMergeOrder e π m m.first = e m.first
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_left]
  have happ : π' ε = c := zagMergeVertical_apply_point e π m
  have hstart : e' (zagCycleMinPos e' π' ε) = a := by
    rw [hmin, hfirst]
  calc
    zagCycleHit π' (e' (zagCycleMinPos e' π' ε)) (π' ε) _ = H := by
      congr 1
    _ = Lb + Lc := hH

private theorem zagMerge_third_mem_cutCandidates {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let e' := zagMergeOrder e π m
    let π' := zagMergeVertical e π m
    let ε := zagMergePoint e π m
    m.third ∈ zagCutCandidates e' π' ε := by
  classical
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let q := zagBlockMiddle m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third
  obtain ⟨hab, hac, hbc⟩ := zagMarkedTriple_pairwise m
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
  have hpos_image : e'.symm (π' ε) = q := by
    rw [happ]
    change (zagMergeOrder e π m).symm (e m.third) = q
    rw [zagMergeOrder_symm_apply, zagBlockSwap_symm_apply_right]
  have hfirst : e' m.first = e m.first := by
    change zagMergeOrder e π m m.first = e m.first
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_left]
  have hthird : e' m.third = e m.middle := by
    change zagMergeOrder e π m m.third = e m.middle
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_right]
  have hpow :
      (π' ^ zagReturnTime π (e m.middle)) (e m.first) = e m.middle := by
    have hp := zagTriangle_merge_pow_left π hab hac hbc
      (zagReturnTime_pos π (e m.middle))
      (le_refl (zagReturnTime π (e m.middle)))
    have hp' : (π' ^ zagReturnTime π (e m.middle)) (e m.first) =
        (π ^ zagReturnTime π (e m.middle)) (e m.middle) := by
      simpa only [π', zagMergeVertical] using hp
    exact hp'.trans
      (zagReturnTime_spec π (e m.middle))
  change m.third ∈ Finset.univ.filter fun i =>
    e'.symm (π' ε) < i ∧ ∃ t : ℕ,
      0 < t ∧ t < zagCutHit e' π' ε ∧
        (π' ^ t) (e' (zagCycleMinPos e' π' ε)) = e' i
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, zagReturnTime π (e m.middle),
    zagReturnTime_pos π (e m.middle), ?_, ?_⟩
  · rw [hpos_image]
    exact (zagBlockMiddle_bounds m.first m.middle m.third
      m.first_lt_middle m.middle_lt_third).2
  · rw [zagMerge_cutHit]
    have hcpos := zagReturnTime_pos π (e m.third)
    omega
  · rw [hmin, hfirst, hthird]
    exact hpow

private theorem zagMerge_cutCandidate_ge_third {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) {x : Fin n}
    (hx : x ∈ zagCutCandidates (zagMergeOrder e π m)
      (zagMergeVertical e π m) (zagMergePoint e π m)) :
    m.third ≤ x := by
  classical
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let q := zagBlockMiddle m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third
  let Lb := zagReturnTime π (e m.middle)
  let Lc := zagReturnTime π (e m.third)
  obtain ⟨hab, hac, hbc⟩ := zagMarkedTriple_pairwise m
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have hfirst : e' m.first = e m.first := by
    change zagMergeOrder e π m m.first = e m.first
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_left]
  have hpos_image : e'.symm (π' ε) = q := by
    have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
    rw [happ]
    change (zagMergeOrder e π m).symm (e m.third) = q
    rw [zagMergeOrder_symm_apply, zagBlockSwap_symm_apply_right]
  change x ∈ Finset.univ.filter (fun i =>
    e'.symm (π' ε) < i ∧ ∃ t : ℕ,
      0 < t ∧ t < zagCutHit e' π' ε ∧
        (π' ^ t) (e' (zagCycleMinPos e' π' ε)) = e' i) at hx
  obtain ⟨hqx, t, ht0, htcut, hpath⟩ := (Finset.mem_filter.mp hx).2
  rw [hpos_image] at hqx
  have ht : t < Lb + Lc := by
    rw [zagMerge_cutHit] at htcut
    exact htcut
  rw [hmin, hfirst] at hpath
  have horder : e' x = e ((zagBlockSwap m.first m.middle m.third
      m.first_lt_middle m.middle_lt_third) x) := by
    simp [e', zagMergeOrder, Equiv.Perm.mul_apply]
  by_cases htb : t ≤ Lb
  · have hp := zagTriangle_merge_pow_left π hab hac hbc ht0 htb
    have hp' : (π' ^ t) (e m.first) = (π ^ t) (e m.middle) := by
      simpa only [π', zagMergeVertical] using hp
    have heq : (π ^ t) (e m.middle) = e' x := hp'.symm.trans hpath
    have hcycle : π.SameCycle (e m.middle) ((π ^ t) (e m.middle)) :=
      ⟨(t : ℤ), by rw [zpow_natCast]⟩
    have hle := zagCycleMinPos_le e π hcycle.symm
    have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
    rw [hmiddle, heq, horder, e.symm_apply_apply] at hle
    exact zagBlockSwap_right_of_middle_le _ _ _ _
      m.first_lt_middle m.middle_lt_third hqx hle
  · let s := t - Lb
    have hs0 : 0 < s := by omega
    have hslt : s < Lc := by omega
    have hp := zagTriangle_merge_pow_after_left π hab hac hbc hs0 hslt.le
    have hp' : (π' ^ t) (e m.first) = (π ^ s) (e m.third) := by
      simpa only [π', zagMergeVertical, Lb, Lc, s,
        show Lb + (t - Lb) = t by omega] using hp
    have heq : (π ^ s) (e m.third) = e' x := hp'.symm.trans hpath
    have hcycle : π.SameCycle (e m.third) ((π ^ s) (e m.third)) :=
      ⟨(s : ℤ), by rw [zpow_natCast]⟩
    have hle := zagCycleMinPos_le e π hcycle.symm
    have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
    rw [hthird, heq, horder, e.symm_apply_apply] at hle
    have hmiddle_le := m.middle_lt_third.le.trans hle
    exact zagBlockSwap_right_of_middle_le _ _ _ _
      m.first_lt_middle m.middle_lt_third hqx hmiddle_le

private theorem zagMerge_cutPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let hε := zagMergePoint_nontrivialAntiExceedance e π m
    zagCutPos (zagMergeOrder e π m) (zagMergeVertical e π m)
      (zagMergePoint e π m) hε = m.third := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let hε := zagMergePoint_nontrivialAntiExceedance e π m
  apply le_antisymm
  · apply zagCutPos_min e' π' ε hε
    exact zagMerge_third_mem_cutCandidates e π m
  · apply zagMerge_cutCandidate_ge_third e π m
    exact zagCutPos_mem e' π' ε hε

private theorem zagSlice_merge_order_from_marked {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let e' := zagMergeOrder e π m
    let π' := zagMergeVertical e π m
    let ε := zagMergePoint e π m
    let hε := zagMergePoint_nontrivialAntiExceedance e π m
    zagSliceOrder e' π' ε hε = e := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let hε := zagMergePoint_nontrivialAntiExceedance e π m
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
  have himage : e'.symm (π' ε) =
      zagBlockMiddle m.first m.middle m.third
        m.first_lt_middle m.middle_lt_third := by
    rw [happ]
    change (zagMergeOrder e π m).symm (e m.third) = _
    rw [zagMergeOrder_symm_apply, zagBlockSwap_symm_apply_right]
  have hcut : zagCutPos e' π' ε hε = m.third := zagMerge_cutPos e π m
  change e' * zagBlockSwap (zagCycleMinPos e' π' ε) (e'.symm (π' ε))
      (zagCutPos e' π' ε hε) _ _ = e
  simp only [hmin, himage, hcut]
  change (e * zagBlockSwap m.first m.middle m.third
      m.first_lt_middle m.middle_lt_third) *
    zagBlockSwap m.first
      (zagBlockMiddle m.first m.middle m.third
        m.first_lt_middle m.middle_lt_third) m.third _ _ = e
  rw [mul_assoc, zagBlockSwap_mul_reverse, mul_one]

private theorem zagSlice_merge_vertical_from_marked {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let e' := zagMergeOrder e π m
    let π' := zagMergeVertical e π m
    let ε := zagMergePoint e π m
    let hε := zagMergePoint_nontrivialAntiExceedance e π m
    zagSliceVertical e' π' ε hε = π := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let hε := zagMergePoint_nontrivialAntiExceedance e π m
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
  have hcut : zagCutPos e' π' ε hε = m.third := zagMerge_cutPos e π m
  have hfirst : e' m.first = e m.first := by
    change zagMergeOrder e π m m.first = e m.first
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_left]
  have hthird : e' m.third = e m.middle := by
    change zagMergeOrder e π m m.third = e m.middle
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_right]
  have hfm : e m.first ≠ e m.middle :=
    e.injective.ne (ne_of_lt m.first_lt_middle)
  have hft : e m.first ≠ e m.third :=
    e.injective.ne (ne_of_lt (m.first_lt_middle.trans m.middle_lt_third))
  have hmt : e m.middle ≠ e m.third :=
    e.injective.ne (ne_of_lt m.middle_lt_third)
  change π' * zagTriangle (e' (zagCycleMinPos e' π' ε)) (π' ε)
      (e' (zagCutPos e' π' ε hε)) = π
  simp only [hmin, happ, hcut, hfirst, hthird]
  change (π * zagTriangle (e m.first) (e m.middle) (e m.third)) *
      zagTriangle (e m.first) (e m.third) (e m.middle) = π
  rw [mul_assoc, zagTriangle_mul_reverse hfm hft hmt, mul_one]

private theorem zagMerge_residual_cycleMinPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π)
    (hres : zagNontrivialAntiExceedance e π (zagMergePoint e π m)) :
    zagCycleMinPos e π (zagMergePoint e π m) = m.third := by
  have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
  have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
  have hnotfixed : π.symm (e m.third) ≠ e m.third := by
    intro hfix
    have hε := zagMergePoint_eq_middle_of_fixed e π m hfix
    rw [hε] at hres
    by_cases hb : π (e m.middle) = e m.middle
    · apply hres.2
      simp only [zagTrivialAntiExceedance, hmiddle, hb]
    · apply hres.1
      simp only [zagExceedance, e.symm_apply_apply]
      have hsame : π.SameCycle (π (e m.middle)) (e m.middle) :=
        (Equiv.Perm.SameCycle.rfl :
          π.SameCycle (e m.middle) (e m.middle)).apply_left
      have hle := zagCycleMinPos_le e π hsame
      rw [hmiddle] at hle
      exact lt_of_le_of_ne hle fun heq => hb (e.symm.injective (by simpa using heq.symm))
  have hε := zagMergePoint_eq_preimage_of_not_fixed e π m hnotfixed
  have hsame : π.SameCycle (zagMergePoint e π m) (e m.third) := by
    rw [hε]
    exact (Equiv.Perm.SameCycle.rfl :
      π.SameCycle (e m.third) (e m.third)).symm_apply_left
  rw [zagCycleMinPos_eq_of_sameCycle e π hsame, hthird]

private theorem zagSlice_merge_marked_from_marked {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let e' := zagMergeOrder e π m
    let π' := zagMergeVertical e π m
    let ε := zagMergePoint e π m
    let hε := zagMergePoint_nontrivialAntiExceedance e π m
    zagSliceMarked e' π' ε hε = m.toFinset := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let hε := zagMergePoint_nontrivialAntiExceedance e π m
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
  have himage : e'.symm (π' ε) =
      zagBlockMiddle m.first m.middle m.third
        m.first_lt_middle m.middle_lt_third := by
    rw [happ]
    change (zagMergeOrder e π m).symm (e m.third) = _
    rw [zagMergeOrder_symm_apply, zagBlockSwap_symm_apply_right]
  have hcut : zagCutPos e' π' ε hε = m.third := zagMerge_cutPos e π m
  have hmiddle_reverse :
      zagBlockMiddle m.first
        (zagBlockMiddle m.first m.middle m.third
          m.first_lt_middle m.middle_lt_third) m.third _ _ = m.middle :=
    zagBlockMiddle_reverse m.first m.middle m.third
      m.first_lt_middle m.middle_lt_third
  have horder : zagSliceOrder e' π' ε hε = e :=
    zagSlice_merge_order_from_marked e π m
  have hvertical : zagSliceVertical e' π' ε hε = π :=
    zagSlice_merge_vertical_from_marked e π m
  by_cases hres : zagNontrivialAntiExceedance
      (zagSliceOrder e' π' ε hε) (zagSliceVertical e' π' ε hε) ε
  · have hres' : zagNontrivialAntiExceedance e π ε := by
      simpa only [horder, hvertical] using hres
    have hresmin : zagCycleMinPos e π ε = m.third :=
      zagMerge_residual_cycleMinPos e π m hres'
    have hs := zagSliceMarked_eq_residual e' π' ε hε hres
    dsimp only at hs
    simpa only [hmin, himage, hcut, hmiddle_reverse, horder, hvertical,
      hresmin, ZagMarkedTriple.toFinset] using hs
  · have hs := zagSliceMarked_eq_terminal e' π' ε hε hres
    dsimp only at hs
    simpa only [hmin, himage, hcut, hmiddle_reverse,
      ZagMarkedTriple.toFinset] using hs

private theorem zagResidual_middle_lt_image {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    m.middle < e.symm (π ε) := by
  have h := zagNTAE_min_lt_image e π hε
  rw [hthird] at h
  exact m.middle_lt_third.trans h

private noncomputable def zagResidualMergeOrder {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) : Equiv.Perm (Fin n) :=
  e * zagBlockSwap m.first m.middle (e.symm (π ε))
    m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)

private noncomputable def zagResidualMergeVertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n) :
    Equiv.Perm (Fin n) :=
  π * zagTriangle (e m.first) (e m.middle) (π ε)

private theorem zagResidual_critical_pairwise {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) (ε : Fin n)
    (hthird : zagCycleMinPos e π ε = m.third) :
    ¬π.SameCycle (e m.first) (e m.middle) ∧
      ¬π.SameCycle (e m.first) (π ε) ∧
      ¬π.SameCycle (e m.middle) (π ε) := by
  have hfirst := (zag_mem_cycleMinima_iff e π m.first).mp m.first_mem
  have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
  have himage : zagCycleMinPos e π (π ε) = m.third := by
    rw [zagCycleMinPos_eq_of_sameCycle e π
      ((Equiv.Perm.SameCycle.rfl : π.SameCycle ε ε).apply_left), hthird]
  constructor
  · exact (zagMarkedTriple_pairwise m).1
  constructor
  · intro hsame
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    rw [hfirst, himage] at hmin
    exact (m.first_lt_middle.trans m.middle_lt_third).ne hmin
  · intro hsame
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    rw [hmiddle, himage] at hmin
    exact m.middle_lt_third.ne hmin

private theorem zagResidualMergeOrder_symm_apply {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε x : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    (zagResidualMergeOrder e π m ε hε hthird).symm (e x) =
      (zagBlockSwap m.first m.middle (e.symm (π ε))
        m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)).symm x := by
  let B := zagBlockSwap m.first m.middle (e.symm (π ε))
    m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)
  change ((e * B)⁻¹) (e x) = B⁻¹ x
  rw [mul_inv_rev, Equiv.Perm.mul_apply]
  change B.symm (e.symm (e x)) = B.symm x
  rw [e.symm_apply_apply]

private theorem zagResidualMergeVertical_apply_point {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    zagResidualMergeVertical e π m ε ε = π ε := by
  have hfirst := (zag_mem_cycleMinima_iff e π m.first).mp m.first_mem
  have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
  have hεf : ε ≠ e m.first := by
    intro heq
    have hm : zagCycleMinPos e π ε = m.first := by simpa [heq] using hfirst
    rw [hm] at hthird
    exact (m.first_lt_middle.trans m.middle_lt_third).ne hthird
  have hεm : ε ≠ e m.middle := by
    intro heq
    have hm : zagCycleMinPos e π ε = m.middle := by simpa [heq] using hmiddle
    rw [hm] at hthird
    exact m.middle_lt_third.ne hthird
  have hεb : ε ≠ π ε := by
    intro heq
    have hlt := zagNTAE_image_lt e π hε
    rw [← heq] at hlt
    exact (lt_irrefl _ hlt).elim
  simp only [zagResidualMergeVertical, Equiv.Perm.mul_apply]
  rw [zagTriangle_apply_of_ne hεf hεm hεb]

private theorem zagResidualMergePoint_nontrivialAntiExceedance {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    zagNontrivialAntiExceedance
      (zagResidualMergeOrder e π m ε hε hthird)
      (zagResidualMergeVertical e π m ε) ε := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let q := zagBlockMiddle m.first m.middle l m.first_lt_middle
    (zagResidual_middle_lt_image m ε hε hthird)
  have hbounds := zagBlockMiddle_bounds m.first m.middle l
    m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have hpos_image : e'.symm (π ε) = q := by
    rw [← e.apply_symm_apply (π ε)]
    change (zagResidualMergeOrder e π m ε hε hthird).symm (e l) = q
    rw [zagResidualMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  have hpos_eps : e'.symm ε = e.symm ε := by
    have hs := zagResidualMergeOrder_symm_apply e π m ε (e.symm ε) hε hthird
    simp only [e.apply_symm_apply] at hs
    have hlast : l < e.symm ε := zagNTAE_image_lt e π hε
    rw [hs, zagBlockSwap_symm_apply_of_right _ _ _ _
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird) hlast]
  constructor
  · intro hexc
    simp only [zagExceedance] at hexc
    change e'.symm ε < e'.symm (π' ε) at hexc
    rw [happ, hpos_image, hpos_eps] at hexc
    have hlast : l < e.symm ε := zagNTAE_image_lt e π hε
    exact (not_lt_of_ge (hbounds.2.le.trans hlast.le)) hexc
  · intro htriv
    simp only [zagTrivialAntiExceedance] at htriv
    obtain ⟨hfm, hfb, hmb⟩ := zagResidual_critical_pairwise m ε hthird
    have hmerge := zagTriangle_merge_sameCycles π hfm hfb hmb
    have hAimage : π'.SameCycle (e m.first) (π ε) := by
      exact hmerge.2
    have himageε : π'.SameCycle (π ε) ε := by
      have h := (Equiv.Perm.SameCycle.rfl : π'.SameCycle ε ε).apply_left
      simpa [happ] using h
    have hAε := hAimage.trans himageε
    have hle := zagCycleMinPos_le e' π' hAε
    have hpos_first : e'.symm (e m.first) = m.first := by
      change (zagResidualMergeOrder e π m ε hε hthird).symm
        (e m.first) = m.first
      rw [zagResidualMergeOrder_symm_apply,
        zagBlockSwap_symm_apply_left]
    have hmin_eq : zagCycleMinPos e' π' ε = q := by
      calc
        zagCycleMinPos e' π' ε = e'.symm (e' (zagCycleMinPos e' π' ε)) := by
          rw [e'.symm_apply_apply]
        _ = e'.symm (π' ε) := by rw [htriv]
        _ = e'.symm (π ε) := by rw [happ]
        _ = q := hpos_image
    rw [hmin_eq, hpos_first] at hle
    exact (not_le_of_gt hbounds.1) hle

private theorem zagResidualMerge_cycleMinPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    zagCycleMinPos (zagResidualMergeOrder e π m ε hε hthird)
      (zagResidualMergeVertical e π m ε) ε = m.first := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  have hpos_first : e'.symm (e m.first) = m.first := by
    change (zagResidualMergeOrder e π m ε hε hthird).symm
      (e m.first) = m.first
    rw [zagResidualMergeOrder_symm_apply, zagBlockSwap_symm_apply_left]
  obtain ⟨hfm, hfb, hmb⟩ := zagResidual_critical_pairwise m ε hthird
  obtain ⟨hmerge_middle, hmerge_image⟩ :=
    zagTriangle_merge_sameCycles π hfm hfb hmb
  change π'.SameCycle (e m.first) (e m.middle) at hmerge_middle
  change π'.SameCycle (e m.first) (π ε) at hmerge_image
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have himageε : π'.SameCycle (π ε) ε := by
    have h := (Equiv.Perm.SameCycle.rfl : π'.SameCycle ε ε).apply_left
    simpa [happ] using h
  have hfε : π'.SameCycle (e m.first) ε := hmerge_image.trans himageε
  apply le_antisymm
  · have hle := zagCycleMinPos_le e' π' hfε
    rwa [hpos_first] at hle
  · let d := zagCycleMinPos e' π' ε
    let z := e' d
    have hzε : π'.SameCycle z ε := zagCycleMinPos_mem e' π' ε
    have hfz : π'.SameCycle (e m.first) z := hfε.trans hzε.symm
    have hcases : π.SameCycle (e m.first) z ∨
        π.SameCycle (e m.middle) z ∨ π.SameCycle (π ε) z := by
      apply zagTriangle_merge_cases π hfm hfb hmb
      simpa only [π', zagResidualMergeVertical] using hfz
    have hfirst := (zag_mem_cycleMinima_iff e π m.first).mp m.first_mem
    have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
    have himage : zagCycleMinPos e π (π ε) = m.third := by
      rw [zagCycleMinPos_eq_of_sameCycle e π
        ((Equiv.Perm.SameCycle.rfl : π.SameCycle ε ε).apply_left), hthird]
    have htarget : m.first ≤ e.symm z := by
      rcases hcases with hfz' | hmz' | hbz'
      · have hle := zagCycleMinPos_le e π hfz'.symm
        rwa [hfirst] at hle
      · have hle := zagCycleMinPos_le e π hmz'.symm
        rw [hmiddle] at hle
        exact m.first_lt_middle.le.trans hle
      · have hle := zagCycleMinPos_le e π hbz'.symm
        rw [himage] at hle
        exact (m.first_lt_middle.trans m.middle_lt_third).le.trans hle
    have hswap : m.first ≤
        (zagBlockSwap m.first m.middle (e.symm (π ε))
          m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)).symm
          (e.symm z) :=
      (zagBlockSwap_symm_preserves_leftCut _ _ _ _
        m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)).mpr htarget
    have horder := zagResidualMergeOrder_symm_apply e π m ε (e.symm z) hε hthird
    simp only [e.apply_symm_apply] at horder
    calc
      m.first ≤ e'.symm z := by
        change m.first ≤
          (zagResidualMergeOrder e π m ε hε hthird).symm z
        rwa [horder]
      _ = d := by simp [z]

private theorem zagResidualMerge_cycleMinPos_before {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε r : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third)
    (hr : r ∈ zagCycleMinima e π) (hrf : r < m.first) :
    r ∈ zagCycleMinima (zagResidualMergeOrder e π m ε hε hthird)
      (zagResidualMergeVertical e π m ε) := by
  classical
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  have her : e' r = e r := by
    simp only [e', zagResidualMergeOrder, Equiv.Perm.mul_apply]
    congr 1
    apply Fin.ext
    simp [zagBlockSwap_val, zagBlockSwapNat,
      show (r : ℕ) ≤ (m.first : ℕ) from hrf.le]
  have hrf_cycle : ¬π.SameCycle (e r) (e m.first) :=
    zagCycleMinima_not_same_of_lt e π hr m.first_mem hrf
  have hrm_cycle : ¬π.SameCycle (e r) (e m.middle) :=
    zagCycleMinima_not_same_of_lt e π hr m.middle_mem
      (hrf.trans m.first_lt_middle)
  have hrt_cycle : ¬π.SameCycle (e r) (e m.third) :=
    zagCycleMinima_not_same_of_lt e π hr m.third_mem
      (hrf.trans (m.first_lt_middle.trans m.middle_lt_third))
  have hrimage_cycle : ¬π.SameCycle (e r) (π ε) := by
    intro hsame
    apply hrt_cycle
    exact hsame.trans ((Equiv.Perm.SameCycle.rfl : π.SameCycle ε ε).apply_left |>.trans
      (by
        have hmem := zagCycleMinPos_mem e π ε
        rw [hthird] at hmem
        exact hmem.symm))
  rw [zag_mem_cycleMinima_iff] at hr ⊢
  let d := zagCycleMinPos e' π' (e' r)
  have hdcycle : π.SameCycle (e r) (e' d) := by
    apply (zagSameCycle_mul_triangle_iff_of_disjoint π
      hrf_cycle hrm_cycle hrimage_cycle).mp
    have hnew : π'.SameCycle (e r) (e' d) := by
      rw [← her]
      exact (zagCycleMinPos_mem e' π' (e' r)).symm
    simpa only [π', zagResidualMergeVertical] using hnew
  have hpos : r ≤ e.symm (e' d) := by
    have hle := zagCycleMinPos_le e π hdcycle.symm
    rwa [hr] at hle
  have hrd : r ≤ d := by
    by_cases hdf : d < m.first
    · have hed : e' d = e d := by
        simp only [e', zagResidualMergeOrder, Equiv.Perm.mul_apply]
        congr 1
        apply Fin.ext
        simp [zagBlockSwap_val, zagBlockSwapNat,
          show (d : ℕ) ≤ (m.first : ℕ) from hdf.le]
      rwa [hed, e.symm_apply_apply] at hpos
    · exact hrf.le.trans (le_of_not_gt hdf)
  have hdr : d ≤ r := by
    have hle := zagCycleMinPos_le e' π'
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle (e' r) (e' r))
    simpa only [e'.symm_apply_apply] using hle
  exact le_antisymm hdr hrd

private theorem zagResidualMerge_cutHit {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    zagCutHit e' π' ε =
      zagReturnTime π (e m.middle) + zagReturnTime π (π ε) := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let a := e m.first
  let b := e m.middle
  let c := π ε
  let Lb := zagReturnTime π b
  let Lc := zagReturnTime π c
  obtain ⟨hab, hac, hbc⟩ := zagResidual_critical_pairwise m ε hthird
  have hac' : π'.SameCycle a c := by
    exact (zagTriangle_merge_sameCycles π hab hac hbc).2
  have hac_ne : a ≠ c := fun h => hac (h.sameCycle π)
  have hsum : (π' ^ (Lb + Lc)) a = c := by
    have hp := zagTriangle_merge_pow_after_left π hab hac hbc
      (zagReturnTime_pos π c) (le_refl (zagReturnTime π c))
    simpa only [π', zagResidualMergeVertical, a, b, c, Lb, Lc] using
      hp.trans (zagReturnTime_spec π c)
  have hno (r : ℕ) (hr0 : 0 < r) (hr : r < Lb + Lc) :
      (π' ^ r) a ≠ c := by
    by_cases hrb : r ≤ Lb
    · have hp := zagTriangle_merge_pow_left π hab hac hbc hr0 hrb
      intro hrc
      apply hbc
      refine ⟨(r : ℤ), ?_⟩
      rw [zpow_natCast]
      have hp' : (π' ^ r) a = (π ^ r) b := by
        simpa only [π', zagResidualMergeVertical, a, b, c] using hp
      exact hp'.symm.trans hrc
    · let s := r - Lb
      have hs0 : 0 < s := by omega
      have hslt : s < Lc := by omega
      have hp := zagTriangle_merge_pow_after_left π hab hac hbc hs0 hslt.le
      have hpr : (π' ^ r) a = (π ^ s) c := by
        simpa only [π', zagResidualMergeVertical, a, b, c, Lb, Lc, s,
          show Lb + (r - Lb) = r by omega] using hp
      intro hrc
      exact zagReturnTime_no_return π c hs0 hslt (hpr.symm.trans hrc)
  let H := zagCycleHit π' a c hac'
  have hHle : H ≤ Lb + Lc := zagCycleHit_minimal π' a c hac' hsum
  have hleH : Lb + Lc ≤ H := by
    by_contra h
    have hHlt : H < Lb + Lc := by omega
    have hHpos := zagCycleHit_pos π' hac_ne hac'
    exact hno H hHpos hHlt (zagCycleHit_spec π' a c hac')
  have hH : H = Lb + Lc := le_antisymm hHle hleH
  change zagCutHit e' π' ε = Lb + Lc
  rw [zagCutHit]
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have hfirst : e' m.first = a := by
    change zagResidualMergeOrder e π m ε hε hthird m.first = e m.first
    simp [zagResidualMergeOrder, Equiv.Perm.mul_apply,
      zagBlockSwap_apply_left]
  have happ : π' ε = c :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have hstart : e' (zagCycleMinPos e' π' ε) = a := by rw [hmin, hfirst]
  calc
    zagCycleHit π' (e' (zagCycleMinPos e' π' ε)) (π' ε) _ = H := by
      congr 1
    _ = Lb + Lc := hH

private theorem zagResidualMerge_last_mem_cutCandidates {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    e.symm (π ε) ∈ zagCutCandidates e' π' ε := by
  classical
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let q := zagBlockMiddle m.first m.middle l m.first_lt_middle
    (zagResidual_middle_lt_image m ε hε hthird)
  obtain ⟨hab, hac, hbc⟩ := zagResidual_critical_pairwise m ε hthird
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have hpos_image : e'.symm (π' ε) = q := by
    rw [happ, ← e.apply_symm_apply (π ε)]
    change (zagResidualMergeOrder e π m ε hε hthird).symm (e l) = q
    rw [zagResidualMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  have hfirst : e' m.first = e m.first := by
    change zagResidualMergeOrder e π m ε hε hthird m.first = e m.first
    simp [zagResidualMergeOrder, Equiv.Perm.mul_apply,
      zagBlockSwap_apply_left]
  have hlast : e' l = e m.middle := by
    change e ((zagBlockSwap m.first m.middle (e.symm (π ε))
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird))
        (e.symm (π ε))) = e m.middle
    rw [zagBlockSwap_apply_right]
  have hpow :
      (π' ^ zagReturnTime π (e m.middle)) (e m.first) = e m.middle := by
    have hp := zagTriangle_merge_pow_left π hab hac hbc
      (zagReturnTime_pos π (e m.middle))
      (le_refl (zagReturnTime π (e m.middle)))
    have hp' : (π' ^ zagReturnTime π (e m.middle)) (e m.first) =
        (π ^ zagReturnTime π (e m.middle)) (e m.middle) := by
      simpa only [π', zagResidualMergeVertical] using hp
    exact hp'.trans (zagReturnTime_spec π (e m.middle))
  change l ∈ Finset.univ.filter fun i =>
    e'.symm (π' ε) < i ∧ ∃ t : ℕ,
      0 < t ∧ t < zagCutHit e' π' ε ∧
        (π' ^ t) (e' (zagCycleMinPos e' π' ε)) = e' i
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, zagReturnTime π (e m.middle),
    zagReturnTime_pos π (e m.middle), ?_, ?_⟩
  · rw [hpos_image]
    exact (zagBlockMiddle_bounds m.first m.middle l m.first_lt_middle
      (zagResidual_middle_lt_image m ε hε hthird)).2
  · rw [zagResidualMerge_cutHit]
    have hcpos := zagReturnTime_pos π (π ε)
    omega
  · rw [hmin, hfirst, hlast]
    exact hpow

private theorem zagResidualMerge_cutCandidate_ge_last {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) {x : Fin n}
    (hx : x ∈ zagCutCandidates
      (zagResidualMergeOrder e π m ε hε hthird)
      (zagResidualMergeVertical e π m ε) ε) :
    e.symm (π ε) ≤ x := by
  classical
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let q := zagBlockMiddle m.first m.middle l m.first_lt_middle
    (zagResidual_middle_lt_image m ε hε hthird)
  let Lb := zagReturnTime π (e m.middle)
  let Lc := zagReturnTime π (π ε)
  obtain ⟨hab, hac, hbc⟩ := zagResidual_critical_pairwise m ε hthird
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have hfirst : e' m.first = e m.first := by
    change zagResidualMergeOrder e π m ε hε hthird m.first = e m.first
    simp [zagResidualMergeOrder, Equiv.Perm.mul_apply,
      zagBlockSwap_apply_left]
  have hpos_image : e'.symm (π' ε) = q := by
    have happ : π' ε = π ε :=
      zagResidualMergeVertical_apply_point e π m ε hε hthird
    rw [happ, ← e.apply_symm_apply (π ε)]
    change (zagResidualMergeOrder e π m ε hε hthird).symm (e l) = q
    rw [zagResidualMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  change x ∈ Finset.univ.filter (fun i =>
    e'.symm (π' ε) < i ∧ ∃ t : ℕ,
      0 < t ∧ t < zagCutHit e' π' ε ∧
        (π' ^ t) (e' (zagCycleMinPos e' π' ε)) = e' i) at hx
  obtain ⟨hqx, t, ht0, htcut, hpath⟩ := (Finset.mem_filter.mp hx).2
  rw [hpos_image] at hqx
  have ht : t < Lb + Lc := by
    rw [zagResidualMerge_cutHit] at htcut
    exact htcut
  rw [hmin, hfirst] at hpath
  have horder : e' x = e ((zagBlockSwap m.first m.middle l
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)) x) := by
    change e ((zagBlockSwap m.first m.middle (e.symm (π ε))
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)) x) =
        e ((zagBlockSwap m.first m.middle l m.first_lt_middle
          (zagResidual_middle_lt_image m ε hε hthird)) x)
    rfl
  by_cases htb : t ≤ Lb
  · have hp := zagTriangle_merge_pow_left π hab hac hbc ht0 htb
    have hp' : (π' ^ t) (e m.first) = (π ^ t) (e m.middle) := by
      simpa only [π', zagResidualMergeVertical] using hp
    have heq : (π ^ t) (e m.middle) = e' x := hp'.symm.trans hpath
    have hcycle : π.SameCycle (e m.middle) ((π ^ t) (e m.middle)) :=
      ⟨(t : ℤ), by rw [zpow_natCast]⟩
    have hle := zagCycleMinPos_le e π hcycle.symm
    have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
    rw [hmiddle, heq, horder, e.symm_apply_apply] at hle
    exact zagBlockSwap_right_of_middle_le _ _ _ _
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird) hqx hle
  · let s := t - Lb
    have hs0 : 0 < s := by omega
    have hslt : s < Lc := by omega
    have hp := zagTriangle_merge_pow_after_left π hab hac hbc hs0 hslt.le
    have hp' : (π' ^ t) (e m.first) = (π ^ s) (π ε) := by
      simpa only [π', zagResidualMergeVertical, Lb, Lc, s,
        show Lb + (t - Lb) = t by omega] using hp
    have heq : (π ^ s) (π ε) = e' x := hp'.symm.trans hpath
    have hcycle : π.SameCycle (π ε) ((π ^ s) (π ε)) :=
      ⟨(s : ℤ), by rw [zpow_natCast]⟩
    have hle := zagCycleMinPos_le e π hcycle.symm
    have himage : zagCycleMinPos e π (π ε) = m.third := by
      rw [zagCycleMinPos_eq_of_sameCycle e π
        ((Equiv.Perm.SameCycle.rfl : π.SameCycle ε ε).apply_left), hthird]
    rw [himage, heq, horder, e.symm_apply_apply] at hle
    have hmiddle_le := m.middle_lt_third.le.trans hle
    exact zagBlockSwap_right_of_middle_le _ _ _ _
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)
      hqx hmiddle_le

private theorem zagResidualMerge_cutPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    let hε' := zagResidualMergePoint_nontrivialAntiExceedance
      e π m ε hε hthird
    zagCutPos e' π' ε hε' = e.symm (π ε) := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let hε' := zagResidualMergePoint_nontrivialAntiExceedance
    e π m ε hε hthird
  apply le_antisymm
  · apply zagCutPos_min e' π' ε hε'
    exact zagResidualMerge_last_mem_cutCandidates e π m ε hε hthird
  · apply zagResidualMerge_cutCandidate_ge_last e π m ε hε hthird
    exact zagCutPos_mem e' π' ε hε'

private theorem zagResidualSlice_merge_order {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    let hε' := zagResidualMergePoint_nontrivialAntiExceedance
      e π m ε hε hthird
    zagSliceOrder e' π' ε hε' = e := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let q := zagBlockMiddle m.first m.middle l m.first_lt_middle
    (zagResidual_middle_lt_image m ε hε hthird)
  let hε' := zagResidualMergePoint_nontrivialAntiExceedance
    e π m ε hε hthird
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have himage : e'.symm (π' ε) = q := by
    rw [happ, ← e.apply_symm_apply (π ε)]
    change (zagResidualMergeOrder e π m ε hε hthird).symm (e l) = q
    rw [zagResidualMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  have hcut : zagCutPos e' π' ε hε' = l :=
    zagResidualMerge_cutPos e π m ε hε hthird
  change e' * zagBlockSwap (zagCycleMinPos e' π' ε) (e'.symm (π' ε))
      (zagCutPos e' π' ε hε') _ _ = e
  simp only [hmin, himage, hcut]
  change (e * zagBlockSwap m.first m.middle (e.symm (π ε))
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)) *
    zagBlockSwap m.first
      (zagBlockMiddle m.first m.middle (e.symm (π ε))
        m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird))
      (e.symm (π ε)) _ _ = e
  rw [mul_assoc, zagBlockSwap_mul_reverse, mul_one]

private theorem zagResidualSlice_merge_vertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    let hε' := zagResidualMergePoint_nontrivialAntiExceedance
      e π m ε hε hthird
    zagSliceVertical e' π' ε hε' = π := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let hε' := zagResidualMergePoint_nontrivialAntiExceedance
    e π m ε hε hthird
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have hcut : zagCutPos e' π' ε hε' = l :=
    zagResidualMerge_cutPos e π m ε hε hthird
  have hfirst : e' m.first = e m.first := by
    change zagResidualMergeOrder e π m ε hε hthird m.first = e m.first
    simp [zagResidualMergeOrder, Equiv.Perm.mul_apply,
      zagBlockSwap_apply_left]
  have hlast : e' l = e m.middle := by
    change e ((zagBlockSwap m.first m.middle (e.symm (π ε))
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird))
        (e.symm (π ε))) = e m.middle
    rw [zagBlockSwap_apply_right]
  obtain ⟨hfm, hfb, hmb⟩ := zagResidual_critical_pairwise m ε hthird
  have hfm_ne : e m.first ≠ e m.middle := fun h => hfm (h.sameCycle π)
  have hfb_ne : e m.first ≠ π ε := fun h => hfb (h.sameCycle π)
  have hmb_ne : e m.middle ≠ π ε := fun h => hmb (h.sameCycle π)
  change π' * zagTriangle (e' (zagCycleMinPos e' π' ε)) (π' ε)
      (e' (zagCutPos e' π' ε hε')) = π
  simp only [hmin, happ, hcut, hfirst, hlast]
  change (π * zagTriangle (e m.first) (e m.middle) (π ε)) *
      zagTriangle (e m.first) (π ε) (e m.middle) = π
  rw [mul_assoc, zagTriangle_mul_reverse hfm_ne hfb_ne hmb_ne, mul_one]

private theorem zagResidualSlice_merge_marked {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    let hε' := zagResidualMergePoint_nontrivialAntiExceedance
      e π m ε hε hthird
    zagSliceMarked e' π' ε hε' = m.toFinset := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let q := zagBlockMiddle m.first m.middle l m.first_lt_middle
    (zagResidual_middle_lt_image m ε hε hthird)
  let hε' := zagResidualMergePoint_nontrivialAntiExceedance
    e π m ε hε hthird
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have himage : e'.symm (π' ε) = q := by
    rw [happ, ← e.apply_symm_apply (π ε)]
    change (zagResidualMergeOrder e π m ε hε hthird).symm (e l) = q
    rw [zagResidualMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  have hcut : zagCutPos e' π' ε hε' = l :=
    zagResidualMerge_cutPos e π m ε hε hthird
  have hmiddle_reverse :
      zagBlockMiddle m.first
        (zagBlockMiddle m.first m.middle l m.first_lt_middle
          (zagResidual_middle_lt_image m ε hε hthird)) l _ _ = m.middle :=
    zagBlockMiddle_reverse m.first m.middle l m.first_lt_middle
      (zagResidual_middle_lt_image m ε hε hthird)
  have horder : zagSliceOrder e' π' ε hε' = e :=
    zagResidualSlice_merge_order e π m ε hε hthird
  have hvertical : zagSliceVertical e' π' ε hε' = π :=
    zagResidualSlice_merge_vertical e π m ε hε hthird
  have hres : zagNontrivialAntiExceedance
      (zagSliceOrder e' π' ε hε') (zagSliceVertical e' π' ε hε') ε := by
    simpa only [horder, hvertical] using hε
  have hs := zagSliceMarked_eq_residual e' π' ε hε' hres
  dsimp only at hs
  simpa only [hmin, himage, hcut, q, l, hmiddle_reverse, horder, hvertical,
    hthird, ZagMarkedTriple.toFinset] using hs

private theorem zagCycleMinimum_not_nontrivialAntiExceedance {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (i : Fin n)
    (hi : i ∈ zagCycleMinima e π) :
    ¬zagNontrivialAntiExceedance e π (e i) := by
  intro hε
  have hmin := (zag_mem_cycleMinima_iff e π i).mp hi
  by_cases hfix : π (e i) = e i
  · apply hε.2
    simp only [zagTrivialAntiExceedance, hmin, hfix]
  · apply hε.1
    simp only [zagExceedance, e.symm_apply_apply]
    have hsame : π.SameCycle (π (e i)) (e i) :=
      (Equiv.Perm.SameCycle.rfl : π.SameCycle (e i) (e i)).apply_left
    have hle := zagCycleMinPos_le e π hsame
    rw [hmin] at hle
    exact lt_of_le_of_ne hle fun heq =>
      hfix (e.symm.injective (by simpa using heq.symm))

private theorem zagMergePoint_not_nontrivialAntiExceedance {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    ¬zagNontrivialAntiExceedance e π (zagMergePoint e π m) := by
  by_cases hfix : π.symm (e m.third) = e m.third
  · have hpoint := zagMergePoint_eq_middle_of_fixed e π m hfix
    rw [hpoint]
    exact zagCycleMinimum_not_nontrivialAntiExceedance e π m.middle m.middle_mem
  · intro hε
    have hpoint := zagMergePoint_eq_preimage_of_not_fixed e π m hfix
    apply hε.2
    simp only [zagTrivialAntiExceedance]
    have hsame : π.SameCycle (zagMergePoint e π m) (e m.third) := by
      rw [hpoint]
      exact (Equiv.Perm.SameCycle.rfl :
        π.SameCycle (e m.third) (e m.third)).symm_apply_left
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
    rw [hmin, hthird, hpoint, π.apply_symm_apply]

private noncomputable def zagSliceTerminalTriple {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    ZagMarkedTriple (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε) := by
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij := zagNTAE_min_lt_image e π hε
  let hjl := zagImage_lt_cutPos e π ε hε
  let q := zagBlockMiddle i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  exact {
    first := i
    middle := q
    third := l
    first_mem := by
      rw [zag_mem_cycleMinima_iff]
      change zagCycleMinPos e' π' (e' i) = i
      rw [show e' i = e i by exact zagSliceOrder_apply_left e π ε hε]
      exact zagSlice_cycleMinPos_left e π ε hε
    middle_mem := by
      rw [zag_mem_cycleMinima_iff]
      change zagCycleMinPos e' π' (e' q) = q
      rw [show e' q = e l by exact zagSliceOrder_apply_middle e π ε hε]
      exact zagSlice_cycleMinPos_middle e π ε hε
    third_mem := by
      rw [zag_mem_cycleMinima_iff]
      change zagCycleMinPos e' π' (e' l) = l
      rw [show e' l = π ε by exact zagSliceOrder_apply_right e π ε hε]
      exact zagSlice_terminal_cycleMinPos_right e π ε hε hterm
    first_lt_middle := (zagBlockMiddle_bounds i j l hij hjl).1
    middle_lt_third := (zagBlockMiddle_bounds i j l hij hjl).2
  }

private noncomputable def zagSliceResidualTriple {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    ZagMarkedTriple (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε) := by
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij := zagNTAE_min_lt_image e π hε
  let hjl := zagImage_lt_cutPos e π ε hε
  let q := zagBlockMiddle i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let d := zagCycleMinPos e' π' ε
  exact {
    first := i
    middle := q
    third := d
    first_mem := by
      rw [zag_mem_cycleMinima_iff]
      change zagCycleMinPos e' π' (e' i) = i
      rw [show e' i = e i by exact zagSliceOrder_apply_left e π ε hε]
      exact zagSlice_cycleMinPos_left e π ε hε
    middle_mem := by
      rw [zag_mem_cycleMinima_iff]
      change zagCycleMinPos e' π' (e' q) = q
      rw [show e' q = e l by exact zagSliceOrder_apply_middle e π ε hε]
      exact zagSlice_cycleMinPos_middle e π ε hε
    third_mem := zag_cycleMinPos_mem_cycleMinima e' π' ε
    first_lt_middle := (zagBlockMiddle_bounds i j l hij hjl).1
    middle_lt_third := zagSlice_residual_min_gt_middle e π ε hε hres
  }

private theorem zagSliceResidualTriple_third {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagCycleMinPos (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε) ε =
        (zagSliceResidualTriple e π ε hε hres).third :=
  rfl

private theorem zagSliceTerminalTriple_toFinset {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    (zagSliceTerminalTriple e π ε hε hterm).toFinset =
      zagSliceMarked e π ε hε := by
  have hs := zagSliceMarked_eq_terminal e π ε hε hterm
  dsimp only at hs
  simpa only [zagSliceTerminalTriple, ZagMarkedTriple.toFinset] using hs.symm

private theorem zagSliceResidualTriple_toFinset {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    (zagSliceResidualTriple e π ε hε hres).toFinset =
      zagSliceMarked e π ε hε := by
  have hs := zagSliceMarked_eq_residual e π ε hε hres
  dsimp only at hs
  simpa only [zagSliceResidualTriple, ZagMarkedTriple.toFinset] using hs.symm

private structure ZagPointedPlane (n : ℕ) where
  order : Equiv.Perm (Fin n)
  vertical : Equiv.Perm (Fin n)
  point : Fin n
  point_property : zagNontrivialAntiExceedance order vertical point

private theorem zagPointedPlane_ext {n : ℕ} {p q : ZagPointedPlane n}
    (horder : p.order = q.order) (hvertical : p.vertical = q.vertical)
    (hpoint : p.point = q.point) : p = q := by
  cases p
  cases q
  simp_all

private structure ZagMarkedPlane (n : ℕ) where
  order : Equiv.Perm (Fin n)
  vertical : Equiv.Perm (Fin n)
  marked : ZagMarkedTriple order vertical

private theorem zagMarkedTriple_heq_of_toFinset {n : ℕ}
    {e π e' π' : Equiv.Perm (Fin n)} {m : ZagMarkedTriple e π}
    {m' : ZagMarkedTriple e' π'} (he : e = e') (hπ : π = π')
    (hset : m.toFinset = m'.toFinset) : HEq m m' := by
  subst e'
  subst π'
  apply heq_of_eq
  apply (zagMarkedTripleEquivPowerset e π).injective
  apply Subtype.ext
  exact hset

private theorem zagMarkedTriple_heq_of_fields {n : ℕ}
    {e π e' π' : Equiv.Perm (Fin n)} {m : ZagMarkedTriple e π}
    {m' : ZagMarkedTriple e' π'} (he : e = e') (hπ : π = π')
    (hfirst : m.first = m'.first) (hmiddle : m.middle = m'.middle)
    (hthird : m.third = m'.third) : HEq m m' := by
  subst e'
  subst π'
  apply heq_of_eq
  exact zagMarkedTriple_ext hfirst hmiddle hthird

private theorem zagMarkedPlane_ext {n : ℕ} {p q : ZagMarkedPlane n}
    (horder : p.order = q.order) (hvertical : p.vertical = q.vertical)
    (hmarked : HEq p.marked q.marked) : p = q := by
  cases p
  cases q
  simp_all

private structure ZagResidualMarkedPlane (n : ℕ) where
  order : Equiv.Perm (Fin n)
  vertical : Equiv.Perm (Fin n)
  marked : ZagMarkedTriple order vertical
  point : Fin n
  point_property : zagNontrivialAntiExceedance order vertical point
  point_cycle_min : zagCycleMinPos order vertical point = marked.third

private theorem zagResidualMarkedPlane_ext {n : ℕ}
    {p q : ZagResidualMarkedPlane n}
    (horder : p.order = q.order) (hvertical : p.vertical = q.vertical)
    (hmarked : HEq p.marked q.marked) (hpoint : p.point = q.point) : p = q := by
  cases p
  cases q
  simp_all

private noncomputable def zagSliceStep {n : ℕ} (p : ZagPointedPlane n) :
    ZagMarkedPlane n ⊕ ZagResidualMarkedPlane n := by
  classical
  let e' := zagSliceOrder p.order p.vertical p.point p.point_property
  let π' := zagSliceVertical p.order p.vertical p.point p.point_property
  exact if hres : zagNontrivialAntiExceedance e' π' p.point then
    Sum.inr {
      order := e'
      vertical := π'
      marked := zagSliceResidualTriple p.order p.vertical p.point
        p.point_property hres
      point := p.point
      point_property := hres
      point_cycle_min := zagSliceResidualTriple_third p.order p.vertical p.point
        p.point_property hres
    }
  else
    Sum.inl {
      order := e'
      vertical := π'
      marked := zagSliceTerminalTriple p.order p.vertical p.point
        p.point_property hres
    }

private noncomputable def zagMergeStep {n : ℕ} :
    ZagMarkedPlane n ⊕ ZagResidualMarkedPlane n → ZagPointedPlane n
  | Sum.inl p => {
      order := zagMergeOrder p.order p.vertical p.marked
      vertical := zagMergeVertical p.order p.vertical p.marked
      point := zagMergePoint p.order p.vertical p.marked
      point_property := zagMergePoint_nontrivialAntiExceedance
        p.order p.vertical p.marked
    }
  | Sum.inr p => {
      order := zagResidualMergeOrder p.order p.vertical p.marked p.point
        p.point_property p.point_cycle_min
      vertical := zagResidualMergeVertical p.order p.vertical p.marked p.point
      point := p.point
      point_property := zagResidualMergePoint_nontrivialAntiExceedance
        p.order p.vertical p.marked p.point p.point_property p.point_cycle_min
    }

private theorem zagMerge_slice_terminal_order {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagMergeOrder (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε)
      (zagSliceTerminalTriple e π ε hε hterm) = e := by
  simpa only [zagMergeOrder, zagSliceTerminalTriple] using
    zagSlice_merge_order e π ε hε

private theorem zagMerge_slice_terminal_vertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagMergeVertical (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε)
      (zagSliceTerminalTriple e π ε hε hterm) = π := by
  simpa only [zagMergeVertical, zagSliceTerminalTriple] using
    zagSlice_merge_vertical e π ε hε

private theorem zagMerge_slice_terminal_point {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagMergePoint (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε)
      (zagSliceTerminalTriple e π ε hε hterm) = ε := by
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let m := zagSliceTerminalTriple e π ε hε hterm
  have hv : zagMergeVertical e' π' m = π :=
    zagMerge_slice_terminal_vertical e π ε hε hterm
  have hl : e' m.third = π ε := by
    change zagSliceOrder e π ε hε (zagCutPos e π ε hε) = π ε
    exact zagSliceOrder_apply_right e π ε hε
  change (zagMergeVertical e' π' m).symm (e' m.third) = ε
  rw [hv, hl, π.symm_apply_apply]

private theorem zagResidualMerge_slice_order {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagResidualMergeOrder (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε)
      (zagSliceResidualTriple e π ε hε hres) ε hres
      (zagSliceResidualTriple_third e π ε hε hres) = e := by
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let l := zagCutPos e π ε hε
  have hlast : e'.symm (π' ε) = l := by
    apply e'.injective
    rw [e'.apply_symm_apply]
    exact (zagSlice_residual_apply e π ε hε hres).trans
      (zagSliceOrder_apply_right e π ε hε).symm
  simp only [zagResidualMergeOrder, zagSliceResidualTriple]
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let hij := zagNTAE_min_lt_image e π hε
  let hjl := zagImage_lt_cutPos e π ε hε
  let q := zagBlockMiddle i j l hij hjl
  have hiq : i < q := (zagBlockMiddle_bounds i j l hij hjl).1
  have hql : q < l := (zagBlockMiddle_bounds i j l hij hjl).2
  have hqactual : q < e'.symm (π' ε) := by rw [hlast]; exact hql
  have hB : zagBlockSwap i q (e'.symm (π' ε)) hiq hqactual =
      zagBlockSwap i q l hiq hql :=
    zagBlockSwap_congr_right i q (e'.symm (π' ε)) l
      hiq hqactual hql hlast
  rw [hB]
  exact zagSlice_merge_order e π ε hε

private theorem zagResidualMerge_slice_vertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagResidualMergeVertical (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε)
      (zagSliceResidualTriple e π ε hε hres) ε = π := by
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let i := zagCycleMinPos e π ε
  let l := zagCutPos e π ε hε
  let j := e.symm (π ε)
  let q := zagBlockMiddle i j l (zagNTAE_min_lt_image e π hε)
    (zagImage_lt_cutPos e π ε hε)
  have hpoint : π' ε = π ε := zagSlice_residual_apply e π ε hε hres
  have hright : e' l = π ε := zagSliceOrder_apply_right e π ε hε
  change π' * zagTriangle (e' i) (e' q) (π' ε) = π
  rw [hpoint, ← hright]
  exact zagSlice_merge_vertical e π ε hε

private theorem zagSliceStep_mergeStep_terminal {n : ℕ} (p : ZagMarkedPlane n) :
    zagSliceStep (zagMergeStep (Sum.inl p)) = Sum.inl p := by
  rcases p with ⟨e, π, m⟩
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let hε := zagMergePoint_nontrivialAntiExceedance e π m
  have he : zagSliceOrder e' π' ε hε = e :=
    zagSlice_merge_order_from_marked e π m
  have hπ : zagSliceVertical e' π' ε hε = π :=
    zagSlice_merge_vertical_from_marked e π m
  have hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e' π' ε hε) (zagSliceVertical e' π' ε hε) ε := by
    intro hres
    apply zagMergePoint_not_nontrivialAntiExceedance e π m
    simpa only [he, hπ] using hres
  have hset :
      (zagSliceTerminalTriple e' π' ε hε hterm).toFinset = m.toFinset :=
    (zagSliceTerminalTriple_toFinset e' π' ε hε hterm).trans
      (zagSlice_merge_marked_from_marked e π m)
  have hm : HEq (zagSliceTerminalTriple e' π' ε hε hterm) m :=
    zagMarkedTriple_heq_of_toFinset he hπ hset
  have hp : ZagMarkedPlane.mk (zagSliceOrder e' π' ε hε)
      (zagSliceVertical e' π' ε hε)
      (zagSliceTerminalTriple e' π' ε hε hterm) =
      ZagMarkedPlane.mk e π m :=
    zagMarkedPlane_ext he hπ hm
  change zagSliceStep ⟨e', π', ε, hε⟩ = Sum.inl ⟨e, π, m⟩
  simp only [zagSliceStep, hterm]
  exact congrArg Sum.inl hp

private theorem zagSliceStep_mergeStep_residual {n : ℕ}
    (p : ZagResidualMarkedPlane n) :
    zagSliceStep (zagMergeStep (Sum.inr p)) = Sum.inr p := by
  rcases p with ⟨e, π, m, ε, hε, hthird⟩
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let hε' := zagResidualMergePoint_nontrivialAntiExceedance
    e π m ε hε hthird
  have he : zagSliceOrder e' π' ε hε' = e :=
    zagResidualSlice_merge_order e π m ε hε hthird
  have hπ : zagSliceVertical e' π' ε hε' = π :=
    zagResidualSlice_merge_vertical e π m ε hε hthird
  have hres : zagNontrivialAntiExceedance
      (zagSliceOrder e' π' ε hε') (zagSliceVertical e' π' ε hε') ε := by
    simpa only [he, hπ] using hε
  have hset :
      (zagSliceResidualTriple e' π' ε hε' hres).toFinset = m.toFinset :=
    (zagSliceResidualTriple_toFinset e' π' ε hε' hres).trans
      (zagResidualSlice_merge_marked e π m ε hε hthird)
  have hm : HEq (zagSliceResidualTriple e' π' ε hε' hres) m :=
    zagMarkedTriple_heq_of_toFinset he hπ hset
  have hp : ZagResidualMarkedPlane.mk (zagSliceOrder e' π' ε hε')
      (zagSliceVertical e' π' ε hε')
      (zagSliceResidualTriple e' π' ε hε' hres) ε hres
      (zagSliceResidualTriple_third e' π' ε hε' hres) =
      ZagResidualMarkedPlane.mk e π m ε hε hthird :=
    zagResidualMarkedPlane_ext he hπ hm rfl
  change zagSliceStep ⟨e', π', ε, hε'⟩ =
    Sum.inr ⟨e, π, m, ε, hε, hthird⟩
  simp only [zagSliceStep, hres]
  exact congrArg Sum.inr hp

private inductive ZagOddMarks {n : ℕ}
    (e π : Equiv.Perm (Fin n)) : Fin n → Type
  | terminal (m : ZagMarkedTriple e π) : ZagOddMarks e π m.first
  | prepend (first middle third : Fin n)
      (first_mem : first ∈ zagCycleMinima e π)
      (middle_mem : middle ∈ zagCycleMinima e π)
      (first_lt_middle : first < middle)
      (middle_lt_third : middle < third)
      (tail : ZagOddMarks e π third) : ZagOddMarks e π first

private def ZagOddMarks.depth {n : ℕ} {e π : Equiv.Perm (Fin n)}
    {root : Fin n} : ZagOddMarks e π root → ℕ
  | .terminal _ => 0
  | .prepend _ _ _ _ _ _ _ tail => tail.depth + 1

private def ZagOddMarks.toList {n : ℕ} {e π : Equiv.Perm (Fin n)}
    {root : Fin n} : ZagOddMarks e π root → List (Fin n)
  | .terminal m => [m.first, m.middle, m.third]
  | .prepend first middle _ _ _ _ _ tail =>
      first :: middle :: tail.toList

private theorem ZagOddMarks.length_toList {n : ℕ}
    {e π : Equiv.Perm (Fin n)} {root : Fin n}
    (m : ZagOddMarks e π root) :
    m.toList.length = 2 * m.depth + 3 := by
  induction m with
  | terminal => rfl
  | prepend first middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail ih =>
      simp only [toList, List.length_cons, depth, ih]
      omega

private theorem ZagOddMarks.root_le_of_mem {n : ℕ}
    {e π : Equiv.Perm (Fin n)} {root x : Fin n}
    (m : ZagOddMarks e π root) (hx : x ∈ m.toList) : root ≤ x := by
  induction m with
  | terminal m =>
      simp only [toList, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact le_rfl
      · exact m.first_lt_middle.le
      · exact (m.first_lt_middle.trans m.middle_lt_third).le
  | prepend first middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail ih =>
      simp only [toList, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact le_rfl
      · exact first_lt_middle.le
      · exact first_lt_middle.le.trans
          (middle_lt_third.le.trans (ih hx))

private theorem ZagOddMarks.mem_cycleMinima {n : ℕ}
    {e π : Equiv.Perm (Fin n)} {root x : Fin n}
    (m : ZagOddMarks e π root) (hx : x ∈ m.toList) :
    x ∈ zagCycleMinima e π := by
  induction m with
  | terminal m =>
      simp only [toList, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact m.first_mem
      · exact m.middle_mem
      · exact m.third_mem
  | prepend first middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail ih =>
      simp only [toList, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact first_mem
      · exact middle_mem
      · exact ih hx

private theorem ZagOddMarks.sortedLT_toList {n : ℕ}
    {e π : Equiv.Perm (Fin n)} {root : Fin n}
    (m : ZagOddMarks e π root) : m.toList.SortedLT := by
  induction m with
  | terminal m =>
      simp [toList, List.sortedLT_cons, List.sortedLT_nil,
        m.first_lt_middle, m.middle_lt_third,
        m.first_lt_middle.trans m.middle_lt_third]
  | prepend first middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail ih =>
      rw [List.sortedLT_iff_pairwise] at ih ⊢
      simp only [toList, List.pairwise_cons]
      refine ⟨?_, ?_, ih⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact first_lt_middle
        · exact first_lt_middle.trans
            (middle_lt_third.trans_le (tail.root_le_of_mem hx))
      · intro x hx
        exact middle_lt_third.trans_le (tail.root_le_of_mem hx)

private theorem ZagOddMarks.nodup_toList {n : ℕ}
    {e π : Equiv.Perm (Fin n)} {root : Fin n}
    (m : ZagOddMarks e π root) : m.toList.Nodup :=
  m.sortedLT_toList.nodup

private theorem ZagOddMarks.head?_toList {n : ℕ}
    {e π : Equiv.Perm (Fin n)} {root : Fin n}
    (m : ZagOddMarks e π root) : m.toList.head? = some root := by
  cases m <;> rfl

private theorem ZagOddMarks.heq_of_toList {n : ℕ}
    {e π : Equiv.Perm (Fin n)} {root root' : Fin n}
    (m : ZagOddMarks e π root) (m' : ZagOddMarks e π root')
    (h : m.toList = m'.toList) : HEq m m' := by
  induction m generalizing root' with
  | terminal a =>
      cases m' with
      | terminal b =>
          simp only [toList, List.cons.injEq] at h
          obtain ⟨hfirst, hmiddle, hthird, _⟩ := h
          have hab : a = b := zagMarkedTriple_ext hfirst hmiddle hthird
          subst b
          rfl
      | prepend _ middle third first_mem middle_mem first_lt_middle
          middle_lt_third tail =>
          have hlen := congrArg List.length h
          rw [length_toList, length_toList] at hlen
          simp only [depth] at hlen
          omega
  | prepend first middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail ih =>
      cases m' with
      | terminal b =>
          have hlen := congrArg List.length h
          rw [length_toList, length_toList] at hlen
          simp only [depth] at hlen
          omega
      | prepend _ middle' third' first_mem' middle_mem' first_lt_middle'
          middle_lt_third' tail' =>
          simp only [toList, List.cons.injEq] at h
          obtain ⟨hfirst, hmiddle, htail⟩ := h
          have hthird : third = third' := by
            have hhead := congrArg List.head? htail
            rw [tail.head?_toList, tail'.head?_toList] at hhead
            exact Option.some.inj hhead
          subst root'
          subst middle'
          subst third'
          have htail_eq : HEq tail tail' := ih tail' htail
          cases htail_eq
          rfl

private theorem zagOddMarks_exists_of_list {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (l : List (Fin n))
    (hsorted : l.SortedLT)
    (hmem : ∀ x ∈ l, x ∈ zagCycleMinima e π)
    (hodd : Odd l.length) (hthree : 3 ≤ l.length) :
    ∃ root, ∃ m : ZagOddMarks e π root, m.toList = l := by
  induction l using List.twoStepInduction with
  | nil => simp at hthree
  | singleton a => simp at hthree
  | cons_cons a b l ih _ =>
      rw [List.sortedLT_iff_pairwise] at hsorted
      simp only [List.pairwise_cons] at hsorted
      have hab : a < b := hsorted.1 b (by simp)
      have hsorted_l : l.SortedLT := by
        rw [List.sortedLT_iff_pairwise]
        exact hsorted.2.2
      have hmem_l : ∀ x ∈ l, x ∈ zagCycleMinima e π := by
        intro x hx
        exact hmem x (by simp [hx])
      have hodd_l : Odd l.length := by
        obtain ⟨d, hd⟩ := hodd
        refine ⟨d - 1, ?_⟩
        simp only [List.length_cons] at hd
        omega
      cases l with
      | nil => simp at hodd_l
      | cons c rest =>
          have hbc : b < c := hsorted.2.1 c (by simp)
          cases rest with
          | nil =>
              let m : ZagMarkedTriple e π := {
                first := a
                middle := b
                third := c
                first_mem := hmem a (by simp)
                middle_mem := hmem b (by simp)
                third_mem := hmem c (by simp)
                first_lt_middle := hab
                middle_lt_third := hbc
              }
              exact ⟨a, .terminal m, rfl⟩
          | cons d rest =>
              have hthree_l : 3 ≤ (c :: d :: rest).length := by
                obtain ⟨t, ht⟩ := hodd_l
                simp only [List.length_cons] at ht ⊢
                omega
              obtain ⟨root, tail, htail⟩ :=
                ih hsorted_l hmem_l hodd_l hthree_l
              have hroot : root = c := by
                have hhead := tail.head?_toList
                rw [htail] at hhead
                exact Option.some.inj hhead.symm
              subst root
              refine ⟨a, .prepend a b c (hmem a (by simp))
                (hmem b (by simp)) hab hbc tail, ?_⟩
              simp only [ZagOddMarks.toList, htail]

private theorem zagOddMarksSigma_ext {n : ℕ}
    {e π : Equiv.Perm (Fin n)}
    {q q' : Σ root, ZagOddMarks e π root}
    (h : q.2.toList = q'.2.toList) : q = q' := by
  have hroot : q.1 = q'.1 := by
    have hhead := congrArg List.head? h
    rw [q.2.head?_toList, q'.2.head?_toList] at hhead
    exact Option.some.inj hhead
  rcases q with ⟨root, m⟩
  rcases q' with ⟨root', m'⟩
  dsimp only at hroot h ⊢
  subst root'
  have hm : HEq m m' := ZagOddMarks.heq_of_toList m m' h
  cases hm
  rfl

private noncomputable def zagOddMarksDepthEquivPowerset {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (d : ℕ) :
    {q : Σ root, ZagOddMarks e π root // q.2.depth = d} ≃
      {s : Finset (Fin n) //
        s ∈ (zagCycleMinima e π).powersetCard (2 * d + 3)} := by
  classical
  let toSubset :
      {q : Σ root, ZagOddMarks e π root // q.2.depth = d} →
        {s : Finset (Fin n) //
          s ∈ (zagCycleMinima e π).powersetCard (2 * d + 3)} := fun q =>
    ⟨q.1.2.toList.toFinset, Finset.mem_powersetCard.mpr ⟨by
      intro x hx
      exact q.1.2.mem_cycleMinima (by simpa using hx), by
      rw [List.toFinset_card_of_nodup q.1.2.nodup_toList,
        q.1.2.length_toList, q.2]⟩⟩
  refine Equiv.ofBijective toSubset ?_
  constructor
  · intro q q' hqq'
    apply Subtype.ext
    apply zagOddMarksSigma_ext
    apply q.1.2.sortedLT_toList.eq_of_mem_iff q'.1.2.sortedLT_toList
    intro x
    have hset := congrArg Subtype.val hqq'
    simpa only [toSubset, List.mem_toFinset] using Finset.ext_iff.mp hset x
  · intro s
    let l := s.1.sort
    have hsorted : l.SortedLT := s.1.sortedLT_sort
    have hmem : ∀ x ∈ l, x ∈ zagCycleMinima e π := by
      intro x hx
      exact (Finset.mem_powersetCard.mp s.2).1 (by simpa [l] using hx)
    have hlen : l.length = 2 * d + 3 := by
      change (s.1.sort).length = 2 * d + 3
      rw [Finset.length_sort]
      exact (Finset.mem_powersetCard.mp s.2).2
    have hodd : Odd l.length := by
      refine ⟨d + 1, ?_⟩
      omega
    have hthree : 3 ≤ l.length := by omega
    obtain ⟨root, m, hm⟩ :=
      zagOddMarks_exists_of_list e π l hsorted hmem hodd hthree
    have hdepth : m.depth = d := by
      have hmLength := m.length_toList
      rw [hm, hlen] at hmLength
      omega
    refine ⟨⟨⟨root, m⟩, hdepth⟩, Subtype.ext ?_⟩
    change m.toList.toFinset = s.1
    rw [hm]
    exact Finset.sort_toFinset s.1 (fun a b => a ≤ b)

private noncomputable instance zagOddMarksDepthFintype {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (d : ℕ) :
    Fintype {q : Σ root, ZagOddMarks e π root // q.2.depth = d} :=
  Fintype.ofEquiv
    {s : Finset (Fin n) //
      s ∈ (zagCycleMinima e π).powersetCard (2 * d + 3)}
    (zagOddMarksDepthEquivPowerset e π d).symm

private theorem zagCard_oddMarks_depth {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (d : ℕ) :
    Nat.card {q : Σ root, ZagOddMarks e π root // q.2.depth = d} =
      (cycleQuotientCount π).choose (2 * d + 3) := by
  rw [Nat.card_congr (zagOddMarksDepthEquivPowerset e π d),
    Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, zag_card_cycleMinima]

private structure ZagOddMarkedPlane (n : ℕ) where
  order : Equiv.Perm (Fin n)
  vertical : Equiv.Perm (Fin n)
  root : Fin n
  marks : ZagOddMarks order vertical root

private theorem zagOddMarkedPlane_ext {n : ℕ}
    {p q : ZagOddMarkedPlane n}
    (horder : p.order = q.order) (hvertical : p.vertical = q.vertical)
    (hroot : p.root = q.root) (hmarks : HEq p.marks q.marks) : p = q := by
  cases p
  cases q
  simp_all

private theorem zagOddMarkedPlane_ext_toList {n : ℕ}
    {p q : ZagOddMarkedPlane n}
    (horder : p.order = q.order) (hvertical : p.vertical = q.vertical)
    (hroot : p.root = q.root) (hmarks : p.marks.toList = q.marks.toList) :
    p = q := by
  rcases p with ⟨e, π, r, m⟩
  rcases q with ⟨e', π', r', m'⟩
  dsimp only at horder hvertical hroot hmarks ⊢
  subst e'
  subst π'
  subst r'
  exact zagOddMarkedPlane_ext rfl rfl rfl
    (ZagOddMarks.heq_of_toList m m' hmarks)

private structure ZagFullSliceResult {n : ℕ} (p : ZagPointedPlane n) where
  out : ZagOddMarkedPlane n
  root_eq : out.root = zagCycleMinPos p.order p.vertical p.point
  preserves_before : ∀ r : Fin n,
    r < zagCycleMinPos p.order p.vertical p.point →
    r ∈ zagCycleMinima p.order p.vertical →
    r ∈ zagCycleMinima out.order out.vertical

private noncomputable def zagFullSlice {n : ℕ} (p : ZagPointedPlane n) :
    ZagFullSliceResult p := by
  classical
  let e' := zagSliceOrder p.order p.vertical p.point p.point_property
  let π' := zagSliceVertical p.order p.vertical p.point p.point_property
  if hres : zagNontrivialAntiExceedance e' π' p.point then
    let m := zagSliceResidualTriple p.order p.vertical p.point
      p.point_property hres
    let p' : ZagPointedPlane n := ⟨e', π', p.point, hres⟩
    let next := zagFullSlice p'
    have hmfirst : m.first ∈ zagCycleMinima next.out.order next.out.vertical := by
      apply next.preserves_before m.first
      · exact m.first_lt_middle.trans m.middle_lt_third
      · exact m.first_mem
    have hmmiddle : m.middle ∈ zagCycleMinima next.out.order next.out.vertical := by
      apply next.preserves_before m.middle m.middle_lt_third m.middle_mem
    have hmiddle_root : m.middle < next.out.root := by
      rw [next.root_eq]
      exact m.middle_lt_third
    exact {
      out := {
        order := next.out.order
        vertical := next.out.vertical
        root := m.first
        marks := .prepend m.first m.middle next.out.root hmfirst hmmiddle
          m.first_lt_middle hmiddle_root next.out.marks
      }
      root_eq := rfl
      preserves_before := by
        intro r hr hmem
        apply next.preserves_before r
        · exact hr.trans (m.first_lt_middle.trans m.middle_lt_third)
        · exact zagSlice_cycleMinPos_before p.order p.vertical p.point r
            p.point_property hmem hr
    }
  else
    let m := zagSliceTerminalTriple p.order p.vertical p.point
      p.point_property hres
    exact {
      out := ⟨e', π', m.first, .terminal m⟩
      root_eq := rfl
      preserves_before := fun r hr hmem =>
        zagSlice_cycleMinPos_before p.order p.vertical p.point r
          p.point_property hmem hr
    }
termination_by n - (zagCycleMinPos p.order p.vertical p.point).val
decreasing_by
  have hlt : zagCycleMinPos p.order p.vertical p.point <
      zagCycleMinPos e' π' p.point := by
    exact m.first_lt_middle.trans m.middle_lt_third
  change n - (zagCycleMinPos e' π' p.point).val <
    n - (zagCycleMinPos p.order p.vertical p.point).val
  omega

private theorem zagFullSlice_of_terminal {n : ℕ} (p : ZagPointedPlane n)
    (q : ZagMarkedPlane n) (h : zagSliceStep p = Sum.inl q) :
    (zagFullSlice p).out =
      ⟨q.order, q.vertical, q.marked.first, .terminal q.marked⟩ := by
  classical
  rw [zagFullSlice.eq_1]
  by_cases hres : zagNontrivialAntiExceedance
      (zagSliceOrder p.order p.vertical p.point p.point_property)
      (zagSliceVertical p.order p.vertical p.point p.point_property) p.point
  · have h' := h
    simp only [zagSliceStep, hres, ↓reduceDIte, reduceCtorEq] at h'
  · simp only [hres, ↓reduceDIte, ZagOddMarkedPlane.mk.injEq]
    have h' := h
    simp only [zagSliceStep, hres, ↓reduceDIte, Sum.inl.injEq] at h'
    have hq := h'
    cases hq
    exact ⟨rfl, rfl, rfl, HEq.rfl⟩

private theorem zagFullSlice_of_residual {n : ℕ} (p : ZagPointedPlane n)
    (q : ZagResidualMarkedPlane n) (h : zagSliceStep p = Sum.inr q) :
    let p' : ZagPointedPlane n :=
      ⟨q.order, q.vertical, q.point, q.point_property⟩
    let next := zagFullSlice p'
    (zagFullSlice p).out = {
      order := next.out.order
      vertical := next.out.vertical
      root := q.marked.first
      marks := .prepend q.marked.first q.marked.middle next.out.root
        (next.preserves_before q.marked.first
          (by
            rw [q.point_cycle_min]
            exact q.marked.first_lt_middle.trans q.marked.middle_lt_third)
          q.marked.first_mem)
        (next.preserves_before q.marked.middle
          (by rw [q.point_cycle_min]; exact q.marked.middle_lt_third)
          q.marked.middle_mem)
        q.marked.first_lt_middle
        (by rw [next.root_eq, q.point_cycle_min]; exact q.marked.middle_lt_third)
        next.out.marks
    } := by
  classical
  rw [zagFullSlice.eq_1]
  by_cases hres : zagNontrivialAntiExceedance
      (zagSliceOrder p.order p.vertical p.point p.point_property)
      (zagSliceVertical p.order p.vertical p.point p.point_property) p.point
  · simp only [hres, ↓reduceDIte, ZagOddMarkedPlane.mk.injEq]
    have h' := h
    simp only [zagSliceStep, hres, ↓reduceDIte, Sum.inr.injEq] at h'
    have hq := h'
    cases hq
    exact ⟨rfl, rfl, rfl, HEq.rfl⟩
  · have h' := h
    simp only [zagSliceStep, hres, ↓reduceDIte, reduceCtorEq] at h'

private structure ZagFullMergeResult {n : ℕ} (q : ZagOddMarkedPlane n) where
  out : ZagPointedPlane n
  root_eq : zagCycleMinPos out.order out.vertical out.point = q.root
  preserves_before : ∀ r : Fin n,
    r < q.root →
    r ∈ zagCycleMinima q.order q.vertical →
    r ∈ zagCycleMinima out.order out.vertical

private noncomputable def zagFullMergeCore {n : ℕ}
    (e π : Equiv.Perm (Fin n)) {root : Fin n}
    (marks : ZagOddMarks e π root) :
    ZagFullMergeResult ⟨e, π, root, marks⟩ := by
  classical
  cases marks with
  | terminal m =>
      let e' := zagMergeOrder e π m
      let π' := zagMergeVertical e π m
      let ε := zagMergePoint e π m
      let hε := zagMergePoint_nontrivialAntiExceedance e π m
      exact {
        out := ⟨e', π', ε, hε⟩
        root_eq := zagMerge_cycleMinPos e π m
        preserves_before := fun r hr hmem =>
          zagMerge_cycleMinPos_before e π m r hmem hr
      }
  | prepend _ middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail =>
      let next := zagFullMergeCore e π tail
      have hfirst : root ∈
          zagCycleMinima next.out.order next.out.vertical := by
        apply next.preserves_before root
        · exact first_lt_middle.trans middle_lt_third
        · exact first_mem
      have hmiddle : middle ∈
          zagCycleMinima next.out.order next.out.vertical := by
        apply next.preserves_before middle middle_lt_third middle_mem
      have hthird : third ∈
          zagCycleMinima next.out.order next.out.vertical := by
        have hmem := zag_cycleMinPos_mem_cycleMinima next.out.order
          next.out.vertical next.out.point
        rwa [next.root_eq] at hmem
      let m : ZagMarkedTriple next.out.order next.out.vertical := {
        first := root
        middle := middle
        third := third
        first_mem := hfirst
        middle_mem := hmiddle
        third_mem := hthird
        first_lt_middle := first_lt_middle
        middle_lt_third := middle_lt_third
      }
      let e' := zagResidualMergeOrder next.out.order next.out.vertical m
        next.out.point next.out.point_property next.root_eq
      let π' := zagResidualMergeVertical next.out.order next.out.vertical m
        next.out.point
      let hε := zagResidualMergePoint_nontrivialAntiExceedance next.out.order
        next.out.vertical m next.out.point next.out.point_property next.root_eq
      exact {
        out := ⟨e', π', next.out.point, hε⟩
        root_eq := by
          simpa only [m] using
            zagResidualMerge_cycleMinPos next.out.order next.out.vertical
              m next.out.point next.out.point_property next.root_eq
        preserves_before := by
          intro r hr hmem
          apply zagResidualMerge_cycleMinPos_before next.out.order
            next.out.vertical m next.out.point r next.out.point_property
            next.root_eq
          · apply next.preserves_before r
            · exact hr.trans (first_lt_middle.trans middle_lt_third)
            · exact hmem
          · simpa only [m] using hr
      }
termination_by sizeOf marks

private noncomputable def zagFullMerge {n : ℕ} (q : ZagOddMarkedPlane n) :
    ZagFullMergeResult q := by
  rcases q with ⟨e, π, root, marks⟩
  exact zagFullMergeCore e π marks

private theorem zagFullMerge_terminal_out {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    (zagFullMerge ⟨e, π, m.first, .terminal m⟩).out =
      ⟨zagMergeOrder e π m, zagMergeVertical e π m,
        zagMergePoint e π m, zagMergePoint_nontrivialAntiExceedance e π m⟩ := by
  change (zagFullMergeCore e π (.terminal m)).out = _
  rw [zagFullMergeCore.eq_1]

private theorem zagFullMerge_prepend_out {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (first middle third : Fin n)
    (first_mem : first ∈ zagCycleMinima e π)
    (middle_mem : middle ∈ zagCycleMinima e π)
    (first_lt_middle : first < middle) (middle_lt_third : middle < third)
    (tail : ZagOddMarks e π third) :
    let next := zagFullMerge ⟨e, π, third, tail⟩
    let m : ZagMarkedTriple next.out.order next.out.vertical := {
      first := first
      middle := middle
      third := third
      first_mem := next.preserves_before first
        (first_lt_middle.trans middle_lt_third) first_mem
      middle_mem := next.preserves_before middle middle_lt_third middle_mem
      third_mem := by
        have hmem := zag_cycleMinPos_mem_cycleMinima next.out.order
          next.out.vertical next.out.point
        rwa [next.root_eq] at hmem
      first_lt_middle := first_lt_middle
      middle_lt_third := middle_lt_third
    }
    (zagFullMerge ⟨e, π, first, .prepend first middle third first_mem middle_mem
      first_lt_middle middle_lt_third tail⟩).out =
      ⟨zagResidualMergeOrder next.out.order next.out.vertical m next.out.point
          next.out.point_property next.root_eq,
        zagResidualMergeVertical next.out.order next.out.vertical m next.out.point,
        next.out.point,
        zagResidualMergePoint_nontrivialAntiExceedance next.out.order
          next.out.vertical m next.out.point next.out.point_property next.root_eq⟩ := by
  dsimp only [zagFullMerge]
  rw [zagFullMergeCore.eq_1]

private theorem zagFullMerge_fullSlice {n : ℕ} (p : ZagPointedPlane n) :
    (zagFullMerge (zagFullSlice p).out).out = p := by
  classical
  fun_induction zagFullSlice p with
  | case1 p e' π' hres m p' next hmfirst hmmiddle hmiddle_root ih2 ih1 =>
      rw [zagFullMerge_prepend_out]
      let innerResult := zagFullMerge ⟨next.out.order, next.out.vertical,
        next.out.root, next.out.marks⟩
      let inner := innerResult.out
      let m₂ : ZagMarkedTriple inner.order inner.vertical := {
        first := m.first
        middle := m.middle
        third := next.out.root
        first_mem := innerResult.preserves_before m.first
          (m.first_lt_middle.trans hmiddle_root) hmfirst
        middle_mem := innerResult.preserves_before m.middle hmiddle_root hmmiddle
        third_mem := by
          have hmem := zag_cycleMinPos_mem_cycleMinima inner.order inner.vertical
            inner.point
          rwa [innerResult.root_eq] at hmem
        first_lt_middle := m.first_lt_middle
        middle_lt_third := hmiddle_root
      }
      let r₂ : ZagResidualMarkedPlane n :=
        ⟨inner.order, inner.vertical, m₂, inner.point, inner.point_property,
          innerResult.root_eq⟩
      let r₁ : ZagResidualMarkedPlane n :=
        ⟨p'.order, p'.vertical, m, p'.point, p'.point_property,
          zagSliceResidualTriple_third p.order p.vertical p.point
            p.point_property hres⟩
      have hinner : inner = p' := by
        exact ih2
      have he := congrArg ZagPointedPlane.order hinner
      have hπ := congrArg ZagPointedPlane.vertical hinner
      have hpoint := congrArg ZagPointedPlane.point hinner
      have hm : HEq m₂ m := by
        apply zagMarkedTriple_heq_of_fields he hπ
        · rfl
        · rfl
        · exact next.root_eq.trans
            (zagSliceResidualTriple_third p.order p.vertical p.point
              p.point_property hres).symm
      have hr : r₂ = r₁ := by
        exact zagResidualMarkedPlane_ext he hπ hm hpoint
      change zagMergeStep (Sum.inr r₂) = p
      rw [hr]
      apply zagPointedPlane_ext
      · exact
          zagResidualMerge_slice_order p.order p.vertical p.point
            p.point_property hres
      · exact
          zagResidualMerge_slice_vertical p.order p.vertical p.point
            p.point_property hres
      · rfl
  | case2 p e' π' hterm m =>
      rw [zagFullMerge_terminal_out]
      apply zagPointedPlane_ext
      · exact zagMerge_slice_terminal_order p.order p.vertical p.point
          p.point_property hterm
      · exact zagMerge_slice_terminal_vertical p.order p.vertical p.point
          p.point_property hterm
      · exact zagMerge_slice_terminal_point p.order p.vertical p.point
          p.point_property hterm

private theorem zagFullSlice_fullMerge {n : ℕ} (q : ZagOddMarkedPlane n) :
    (zagFullSlice (zagFullMerge q).out).out = q := by
  classical
  rcases q with ⟨e, π, root, marks⟩
  induction marks with
  | terminal m =>
      let marked : ZagMarkedPlane n := ⟨e, π, m⟩
      have hs : zagSliceStep (zagMergeStep (Sum.inl marked)) =
          Sum.inl marked := zagSliceStep_mergeStep_terminal marked
      have hf := zagFullSlice_of_terminal
        (zagMergeStep (Sum.inl marked)) marked hs
      rw [zagFullMerge_terminal_out]
      change (zagFullSlice (zagMergeStep (Sum.inl marked))).out = _
      simpa only [marked] using hf
  | prepend first middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail ih =>
      let next := zagFullMerge ⟨e, π, third, tail⟩
      let m : ZagMarkedTriple next.out.order next.out.vertical := {
        first := first
        middle := middle
        third := third
        first_mem := next.preserves_before first
          (first_lt_middle.trans middle_lt_third) first_mem
        middle_mem := next.preserves_before middle middle_lt_third middle_mem
        third_mem := by
          have hmem := zag_cycleMinPos_mem_cycleMinima next.out.order
            next.out.vertical next.out.point
          rwa [next.root_eq] at hmem
        first_lt_middle := first_lt_middle
        middle_lt_third := middle_lt_third
      }
      let residual : ZagResidualMarkedPlane n :=
        ⟨next.out.order, next.out.vertical, m, next.out.point,
          next.out.point_property, next.root_eq⟩
      have hs : zagSliceStep (zagMergeStep (Sum.inr residual)) =
          Sum.inr residual := zagSliceStep_mergeStep_residual residual
      have hf := zagFullSlice_of_residual
        (zagMergeStep (Sum.inr residual)) residual hs
      rw [zagFullMerge_prepend_out]
      change (zagFullSlice (zagMergeStep (Sum.inr residual))).out = _
      rw [hf]
      have horder : (zagFullSlice next.out).out.order = e :=
        congrArg (fun q : ZagOddMarkedPlane n => q.order) ih
      have hvertical : (zagFullSlice next.out).out.vertical = π :=
        congrArg (fun q : ZagOddMarkedPlane n => q.vertical) ih
      have htail : (zagFullSlice next.out).out.marks.toList = tail.toList :=
        congrArg (fun q : ZagOddMarkedPlane n => q.marks.toList) ih
      apply zagOddMarkedPlane_ext_toList
      · change (zagFullSlice next.out).out.order = e
        exact horder
      · change (zagFullSlice next.out).out.vertical = π
        exact hvertical
      · rfl
      · simp only [ZagOddMarks.toList]
        change first :: middle :: (zagFullSlice next.out).out.marks.toList =
          first :: middle :: tail.toList
        exact congrArg (fun xs => first :: middle :: xs) htail

private def zagDiagonal {n : ℕ}
    (e π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  zagHorizontal e * π⁻¹

private theorem zagVertical_diagonal {n : ℕ}
    (e π : Equiv.Perm (Fin n)) :
    zagVertical (zagDiagonal e π) e = π := by
  simp only [zagVertical, zagDiagonal, mul_inv_rev, inv_inv]
  group

private theorem zagDiagonal_of_vertical {n : ℕ}
    (D e π : Equiv.Perm (Fin n)) (hπ : π = zagVertical D e) :
    zagDiagonal e π = D := by
  subst π
  simp only [zagDiagonal, zagVertical, mul_inv_rev, inv_inv]
  group

private theorem zagSlice_diagonal {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (x : Fin n)
    (hx : zagNontrivialAntiExceedance e π x) :
    zagDiagonal (zagSliceOrder e π x hx)
        (zagSliceVertical e π x hx) =
      zagDiagonal e π := by
  let D := zagDiagonal e π
  have hπ : π = zagVertical D e := (zagVertical_diagonal e π).symm
  exact zagDiagonal_of_vertical D _ _
    (zagSliceVertical_eq D e π x hx hπ)

private def zagBasePoint {n : ℕ} (x : Fin n) : Fin n :=
  ⟨0, lt_of_le_of_lt (Nat.zero_le _) x.isLt⟩

private theorem zagSliceOrder_basePoint {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (x : Fin n)
    (hx : zagNontrivialAntiExceedance e π x) :
    zagSliceOrder e π x hx (zagBasePoint x) = e (zagBasePoint x) := by
  simpa only [zagBasePoint] using zagSliceOrder_apply_zero e π x hx

private theorem zagFullSlice_diagonal {n : ℕ} (p : ZagPointedPlane n) :
    zagDiagonal (zagFullSlice p).out.order (zagFullSlice p).out.vertical =
      zagDiagonal p.order p.vertical := by
  fun_induction zagFullSlice p with
  | case1 p e' π' hres m p' next hmfirst hmmiddle hmiddle_root ih _ =>
      exact ih.trans (zagSlice_diagonal p.order p.vertical p.point
        p.point_property)
  | case2 p e' π' hterm m =>
      exact zagSlice_diagonal p.order p.vertical p.point p.point_property

private theorem zagFullSlice_basePoint {n : ℕ} (p : ZagPointedPlane n) :
    (zagFullSlice p).out.order (zagBasePoint p.point) =
      p.order (zagBasePoint p.point) := by
  fun_induction zagFullSlice p with
  | case1 p e' π' hres m p' next hmfirst hmmiddle hmiddle_root ih _ =>
      exact ih.trans (zagSliceOrder_basePoint p.order p.vertical p.point
        p.point_property)
  | case2 p e' π' hterm m =>
      exact zagSliceOrder_basePoint p.order p.vertical p.point p.point_property

private theorem zagFullSlice_cycleCount {n : ℕ} (p : ZagPointedPlane n) :
    cycleQuotientCount (zagFullSlice p).out.vertical =
      cycleQuotientCount p.vertical +
        2 * ((zagFullSlice p).out.marks.depth + 1) := by
  fun_induction zagFullSlice p with
  | case1 p e' π' hres m p' next hmfirst hmmiddle hmiddle_root ih _ =>
      change cycleQuotientCount next.out.vertical =
        cycleQuotientCount p.vertical +
          2 * (next.out.marks.depth + 1 + 1)
      calc
        cycleQuotientCount next.out.vertical =
            cycleQuotientCount p'.vertical +
              2 * (next.out.marks.depth + 1) := ih
        _ = (cycleQuotientCount p.vertical + 2) +
              2 * (next.out.marks.depth + 1) := by
            rw [zagSliceVertical_count]
        _ = cycleQuotientCount p.vertical +
              2 * (next.out.marks.depth + 1 + 1) := by omega
  | case2 p e' π' hterm m =>
      change cycleQuotientCount
          (zagSliceVertical p.order p.vertical p.point p.point_property) =
        cycleQuotientCount p.vertical + 2 * (0 + 1)
      rw [zagSliceVertical_count]

private theorem zagFinRotate_cycleCount (n : ℕ) (hn : 0 < n) :
    cycleQuotientCount (finRotate n) = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  cases m with
  | zero =>
      rw [Subsingleton.elim (finRotate 1) 1]
      simp [cycleQuotientCount_eq]
  | succ m =>
      rw [cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints,
        cycleType_finRotate]
      simp

private theorem zagHorizontal_cycleCount {n : ℕ}
    (e : Equiv.Perm (Fin n)) (hn : 0 < n) :
    cycleQuotientCount (zagHorizontal e) = 1 := by
  rw [cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints,
    zagHorizontal, Equiv.Perm.cycleType_conj]
  simpa only [cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints] using
    zagFinRotate_cycleCount n hn

private theorem zagCycleType_eq_finRotate_of_cycleCount_one {n : ℕ}
    (hn : 0 < n) (s : Equiv.Perm (Fin n))
    (hs : cycleQuotientCount s = 1) :
    s.cycleType = (finRotate n).cycleType := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  cases m with
  | zero =>
      congr 1
      exact Subsingleton.elim s (finRotate 1)
  | succ m =>
      have hs' : Multiset.card s.cycleType +
          ((m + 2) - s.cycleType.sum) = 1 := by
        simpa only [cycleQuotientCount_eq,
          Equiv.Perm.card_fixedPoints, Fintype.card_fin] using hs
      have hcard_le : Multiset.card s.cycleType ≤ 1 := by omega
      have hcard_ne : Multiset.card s.cycleType ≠ 0 := by
        intro hzero
        have htype : s.cycleType = 0 := Multiset.card_eq_zero.mp hzero
        rw [htype] at hs'
        simp only [Multiset.card_zero, Multiset.sum_zero, Nat.zero_add] at hs'
        omega
      have hcard : Multiset.card s.cycleType = 1 := by omega
      obtain ⟨r, hr⟩ := Multiset.card_eq_one.mp hcard
      have hrsum : r ≤ m + 2 := by
        simpa only [hr, Multiset.sum_singleton, Fintype.card_fin] using
          s.sum_cycleType_le
      have hrn : r = m + 2 := by
        rw [hr] at hs'
        simp only [Multiset.card_singleton, Multiset.sum_singleton] at hs'
        omega
      rw [hr, hrn, cycleType_finRotate]

private theorem zagFinRotate_pow_base {n : ℕ} (i : Fin n) :
    ((finRotate n) ^ i.val) (zagBasePoint i) = i := by
  change ((finRotate n)^[i.val]) (zagBasePoint i) = i
  rw [← finCycle_eq_finRotate_iterate]
  change zagBasePoint i + i = i
  apply Fin.ext
  simp [Fin.add_def, zagBasePoint, Nat.mod_eq_of_lt i.isLt]

private theorem zagConj_pow {n m : ℕ}
    (e r : Equiv.Perm (Fin n)) :
    (e * r * e⁻¹) ^ m = e * r ^ m * e⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', pow_succ', ih]
      group

private theorem zagHorizontal_pow_base {n : ℕ}
    (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (zagHorizontal e ^ i.val) (e (zagBasePoint i)) = e i := by
  rw [zagHorizontal, zagConj_pow]
  simp only [Equiv.Perm.mul_apply]
  change e (((finRotate n) ^ i.val) (e.symm (e (zagBasePoint i)))) = e i
  rw [e.symm_apply_apply, zagFinRotate_pow_base]

private noncomputable def zagAnchoredOrderEquivFullCycle (n : ℕ)
    (hn : 0 < n) :
    {e : Equiv.Perm (Fin n) // e (zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩} ≃
      {s : Equiv.Perm (Fin n) // cycleQuotientCount s = 1} := by
  classical
  let z : Fin n := ⟨0, hn⟩
  let toCycle :
      {e : Equiv.Perm (Fin n) // e (zagBasePoint z) = zagBasePoint z} →
        {s : Equiv.Perm (Fin n) // cycleQuotientCount s = 1} := fun e =>
    ⟨zagHorizontal e.1, zagHorizontal_cycleCount e.1 hn⟩
  refine Equiv.ofBijective toCycle ?_
  constructor
  · intro e f hef
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have hhorizontal : zagHorizontal e.1 = zagHorizontal f.1 :=
      congrArg Subtype.val hef
    have hbase : zagBasePoint i = zagBasePoint z := Fin.ext rfl
    have hebase : e.1 (zagBasePoint i) = zagBasePoint i := by
      simpa only [hbase] using e.2
    have hfbase : f.1 (zagBasePoint i) = zagBasePoint i := by
      simpa only [hbase] using f.2
    calc
      e.1 i = (zagHorizontal e.1 ^ i.val) (e.1 (zagBasePoint i)) :=
        (zagHorizontal_pow_base e.1 i).symm
      _ = (zagHorizontal e.1 ^ i.val) (zagBasePoint i) := by rw [hebase]
      _ = (zagHorizontal f.1 ^ i.val) (zagBasePoint i) := by rw [hhorizontal]
      _ = (zagHorizontal f.1 ^ i.val) (f.1 (zagBasePoint i)) := by rw [hfbase]
      _ = f.1 i := zagHorizontal_pow_base f.1 i
  · intro s
    have htype : (finRotate n).cycleType = s.1.cycleType :=
      (zagCycleType_eq_finRotate_of_cycleCount_one hn s.1 s.2).symm
    have hconj := Equiv.Perm.isConj_of_cycleType_eq htype
    obtain ⟨e, he⟩ := isConj_iff.mp hconj
    let y : Fin n := e.symm z
    let e' : Equiv.Perm (Fin n) := e * (finRotate n) ^ y.val
    have he'base : e' (zagBasePoint z) = zagBasePoint z := by
      change e (((finRotate n) ^ y.val) z) = z
      have hpow : ((finRotate n) ^ y.val) z = y := by
        simpa only [z, zagBasePoint] using zagFinRotate_pow_base y
      rw [hpow]
      exact e.apply_symm_apply z
    refine ⟨⟨e', he'base⟩, Subtype.ext ?_⟩
    change zagHorizontal e' = s.1
    calc
      zagHorizontal e' = zagHorizontal e := by
        simp only [zagHorizontal, e', mul_inv_rev]
        group
      _ = s.1 := he

private abbrev ZagFullPerm (n : ℕ) :=
  {s : Equiv.Perm (Fin n) // cycleQuotientCount s = 1}

private abbrev ZagPlanePairs (n k : ℕ) :=
  {p : ZagFullPerm n × Equiv.Perm (Fin n) //
    cycleQuotientCount p.2 = k ∧
      cycleQuotientCount (p.1.1 * p.2⁻¹) = 1}

private abbrev ZagPlaneConfigBy (n : ℕ) (hn : 0 < n) (k l : ℕ) :=
  {p : {e : Equiv.Perm (Fin n) //
      e (zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩} ×
      Equiv.Perm (Fin n) //
    cycleQuotientCount p.2 = k ∧
      cycleQuotientCount (zagDiagonal p.1.1 p.2) = l}

private abbrev ZagPlaneConfig (n : ℕ) (hn : 0 < n) (k : ℕ) :=
  ZagPlaneConfigBy n hn k 1

private noncomputable def zagPlaneConfigEquivPairs (n k : ℕ) (hn : 0 < n) :
    ZagPlaneConfig n hn k ≃ ZagPlanePairs n k := by
  let E := zagAnchoredOrderEquivFullCycle n hn
  refine {
    toFun := fun p =>
      ⟨(E p.1.1, p.1.2), by
        have he : (E p.1.1).1 = zagHorizontal p.1.1.1 := rfl
        exact ⟨p.2.1, by simpa only [zagDiagonal, he] using p.2.2⟩⟩
    invFun := fun p =>
      ⟨(E.symm p.1.1, p.1.2), by
        have he : zagHorizontal (E.symm p.1.1).1 = p.1.1.1 := by
          exact congrArg Subtype.val (E.apply_symm_apply p.1.1)
        exact ⟨p.2.1, by simpa only [zagDiagonal, he] using p.2.2⟩⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · exact E.symm_apply_apply p.1.1
    · rfl
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · exact E.apply_symm_apply p.1.1
    · rfl

private noncomputable def zagReverseIndex (n : ℕ) (hn : 0 < n) :
    Equiv.Perm (Fin n) := by
  let hNeZero : NeZero n := ⟨hn.ne'⟩
  exact Equiv.neg (Fin n)

private theorem zagReverseIndex_apply {n : ℕ} (hn : 0 < n) (i : Fin n) :
    zagReverseIndex n hn i = -i := by
  let hNeZero : NeZero n := ⟨hn.ne'⟩
  rfl

private theorem zagReverseIndex_inv {n : ℕ} (hn : 0 < n) :
    (zagReverseIndex n hn)⁻¹ = zagReverseIndex n hn := by
  let hNeZero : NeZero n := ⟨hn.ne'⟩
  rfl

private theorem zagReverseIndex_conj_finRotate {n : ℕ} (hn : 0 < n) :
    zagReverseIndex n hn * finRotate n * (zagReverseIndex n hn)⁻¹ =
      (finRotate n)⁻¹ := by
  let hNeZero : NeZero n := ⟨hn.ne'⟩
  apply Equiv.ext
  intro i
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, zagReverseIndex_inv,
    zagReverseIndex_apply, zagReverseIndex_apply,
    finRotate_apply]
  change -(-i + 1) = (finRotate n).symm i
  rw [finRotate_symm_apply]
  simp only [neg_add_rev, neg_neg]
  exact (add_comm (-1 : Fin n) i).trans (sub_eq_add_neg i 1).symm

private noncomputable def zagReverseOrder {n : ℕ} (hn : 0 < n)
    (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  e * zagReverseIndex n hn

private theorem zagHorizontal_reverseOrder {n : ℕ} (hn : 0 < n)
    (e : Equiv.Perm (Fin n)) :
    zagHorizontal (zagReverseOrder hn e) = (zagHorizontal e)⁻¹ := by
  let R := zagReverseIndex n hn
  calc
    zagHorizontal (zagReverseOrder hn e) =
        e * (R * finRotate n * R⁻¹) * e⁻¹ := by
      simp only [zagHorizontal, zagReverseOrder, R, mul_inv_rev]
      group
    _ = e * (finRotate n)⁻¹ * e⁻¹ := by
      rw [zagReverseIndex_conj_finRotate]
    _ = (zagHorizontal e)⁻¹ := by
      simp only [zagHorizontal, mul_inv_rev]
      group

private theorem zagReverseOrder_basePoint {n : ℕ} (hn : 0 < n)
    (e : Equiv.Perm (Fin n))
    (he : e (zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩) :
    zagReverseOrder hn e (zagBasePoint ⟨0, hn⟩) =
      zagBasePoint ⟨0, hn⟩ := by
  rw [zagReverseOrder, Equiv.Perm.mul_apply, zagReverseIndex_apply]
  have hneg : -(zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩ := by
    let hNeZero : NeZero n := ⟨hn.ne'⟩
    apply Fin.ext
    simp [zagBasePoint]
  rw [hneg, he]

private theorem zagReverseIndex_lt {n : ℕ} (hn : 0 < n)
    (a b : Fin n) :
    -(finRotate n a) < -b ↔ ¬a < b ∧ b.val ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  cases m with
  | zero =>
      have ha : a = ⟨0, by omega⟩ := Subsingleton.elim _ _
      have hb : b = ⟨0, by omega⟩ := Subsingleton.elim _ _
      subst a
      subst b
      simp
  | succ m =>
      let hNeZero : NeZero (m + 2) := ⟨by omega⟩
      simp only [Fin.lt_def, Fin.val_neg', finRotate_apply,
        Fin.val_add, Fin.val_one]
      change ((m + 2) - (a.val + 1) % (m + 2)) % (m + 2) <
          ((m + 2) - b.val) % (m + 2) ↔
        ¬a.val < b.val ∧ b.val ≠ 0
      by_cases ha : a.val + 1 = m + 2
      · have hmoda : (a.val + 1) % (m + 2) = 0 := by
          rw [ha, Nat.mod_self]
        rw [hmoda]
        simp only [Nat.sub_zero, Nat.mod_self, zero_lt_iff]
        by_cases hb : b.val = 0
        · simp [hb]
        · have hbpos : 0 < b.val := Nat.pos_of_ne_zero hb
          have hsubpos : 0 < (m + 2) - b.val := by omega
          have hsublt : (m + 2) - b.val < m + 2 := by omega
          rw [Nat.mod_eq_of_lt hsublt]
          constructor
          · intro _hleft
            exact ⟨by omega, hb⟩
          · intro _hright
            exact hsubpos.ne'
      · have halt : a.val + 1 < m + 2 := by omega
        rw [Nat.mod_eq_of_lt halt]
        have hleftlt : (m + 2) - (a.val + 1) < m + 2 := by omega
        rw [Nat.mod_eq_of_lt hleftlt]
        by_cases hb : b.val = 0
        · simp [hb, Nat.mod_self]
        · have hsublt : (m + 2) - b.val < m + 2 := by omega
          rw [Nat.mod_eq_of_lt hsublt]
          constructor
          · intro h
            exact ⟨by omega, hb⟩
          · rintro ⟨hab, -⟩
            omega

private theorem zagReverseOrder_symm_apply {n : ℕ} (hn : 0 < n)
    (e : Equiv.Perm (Fin n)) (x : Fin n) :
    (zagReverseOrder hn e).symm x = -(e.symm x) := by
  apply (zagReverseOrder hn e).injective
  rw [Equiv.apply_symm_apply, zagReverseOrder, Equiv.Perm.mul_apply,
    zagReverseIndex_apply, neg_neg, e.apply_symm_apply]

private theorem zagHorizontal_apply_order {n : ℕ}
    (e : Equiv.Perm (Fin n)) (x : Fin n) :
    e.symm (zagHorizontal e x) = finRotate n (e.symm x) := by
  simp [zagHorizontal, Equiv.Perm.mul_apply]

private theorem zagReflectedVertical_apply_horizontal {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (x : Fin n) :
    (zagDiagonal e π)⁻¹ (zagHorizontal e x) = π x := by
  have h : (zagDiagonal e π)⁻¹ * zagHorizontal e = π := by
    simp only [zagDiagonal, mul_inv_rev, inv_inv]
    group
  exact congrArg (fun f : Equiv.Perm (Fin n) => f x) h

private theorem zagReflected_exceedance_iff {n : ℕ} (hn : 0 < n)
    (e π : Equiv.Perm (Fin n)) (x : Fin n) :
    zagExceedance (zagReverseOrder hn e) (zagDiagonal e π)⁻¹
        (zagHorizontal e x) ↔
      ¬zagExceedance e π x ∧
        π x ≠ e (zagBasePoint x) := by
  rw [zagExceedance, zagReverseOrder_symm_apply,
    zagReflectedVertical_apply_horizontal,
    zagReverseOrder_symm_apply, zagHorizontal_apply_order,
    zagReverseIndex_lt hn]
  constructor
  · rintro ⟨hexc, hzero⟩
    exact ⟨hexc, fun h => hzero (by
      rw [h, e.symm_apply_apply]
      rfl)⟩
  · rintro ⟨hexc, hbase⟩
    refine ⟨hexc, fun hzero => hbase ?_⟩
    apply e.symm.injective
    rw [e.symm_apply_apply]
    exact Fin.ext hzero

private theorem zagCard_reflected_exceedances {n : ℕ} (hn : 0 < n)
    (e π : Equiv.Perm (Fin n)) :
    Nat.card {x : Fin n //
        zagExceedance (zagReverseOrder hn e) (zagDiagonal e π)⁻¹ x} =
      n - Nat.card {x : Fin n // zagExceedance e π x} - 1 := by
  classical
  let s := zagHorizontal e
  let base := e (zagBasePoint ⟨0, hn⟩)
  let reflected :
      {x : Fin n // ¬zagExceedance e π x ∧ π x ≠ base} ≃
        {x : Fin n //
          zagExceedance (zagReverseOrder hn e) (zagDiagonal e π)⁻¹ x} :=
    Equiv.subtypeEquiv s (fun x => by
      simpa only [s, base, show zagBasePoint x = zagBasePoint ⟨0, hn⟩ from
        Fin.ext rfl] using (zagReflected_exceedance_iff hn e π x).symm)
  let split :
      {x : Fin n // ¬zagExceedance e π x ∧ π x ≠ base} ≃
        {x : {x : Fin n // ¬zagExceedance e π x} // π x.1 ≠ base} := {
    toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl
  }
  have hspecial : Fintype.card
      {x : {x : Fin n // ¬zagExceedance e π x} // π x.1 = base} = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    let x₀ : Fin n := π.symm base
    have hx₀ : ¬zagExceedance e π x₀ := by
      intro hx
      have hright : e.symm (π x₀) = zagBasePoint ⟨0, hn⟩ := by
        change e.symm (π (π.symm base)) = zagBasePoint ⟨0, hn⟩
        rw [π.apply_symm_apply]
        change e.symm (e (zagBasePoint ⟨0, hn⟩)) = zagBasePoint ⟨0, hn⟩
        rw [e.symm_apply_apply]
      rw [zagExceedance, hright, Fin.lt_def] at hx
      exact Nat.not_lt_zero _ hx
    let q₀ : {x : {x : Fin n // ¬zagExceedance e π x} // π x.1 = base} :=
      ⟨⟨x₀, hx₀⟩, π.apply_symm_apply base⟩
    refine ⟨q₀, fun q => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply π.injective
    exact q.2.trans q₀.2.symm
  have hanti : Fintype.card {x : Fin n // ¬zagExceedance e π x} =
      n - Fintype.card {x : Fin n // zagExceedance e π x} := by
    simpa only [Fintype.card_fin] using
      Fintype.card_subtype_compl (fun x : Fin n => zagExceedance e π x)
  rw [Nat.card_congr reflected.symm, Nat.card_congr split,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    hspecial, hanti, Nat.card_eq_fintype_card]

private theorem zagCycleQuotientCount_inv {n : ℕ}
    (f : Equiv.Perm (Fin n)) :
    cycleQuotientCount f⁻¹ = cycleQuotientCount f := by
  rw [cycleQuotientCount_eq, cycleQuotientCount_eq,
    Equiv.Perm.card_fixedPoints, Equiv.Perm.card_fixedPoints,
    Equiv.Perm.cycleType_inv]

private abbrev ZagOriginalPoints {n : ℕ} {hn : 0 < n} {k l : ℕ}
    (q : ZagPlaneConfigBy n hn k l) :=
  {x : Fin n // zagNontrivialAntiExceedance q.1.1.1 q.1.2 x}

private abbrev ZagReflectedPoints {n : ℕ} {hn : 0 < n} {k l : ℕ}
    (q : ZagPlaneConfigBy n hn k l) :=
  {x : Fin n // zagNontrivialAntiExceedance
    (zagReverseOrder hn q.1.1.1) (zagDiagonal q.1.1.1 q.1.2)⁻¹ x}

private theorem zagCard_original_add_reflected {n k : ℕ} (hn : 0 < n)
    (q : ZagPlaneConfig n hn k) :
    Nat.card (ZagOriginalPoints q) + Nat.card (ZagReflectedPoints q) = n - k := by
  classical
  let e := q.1.1.1
  let π := q.1.2
  let D := zagDiagonal e π
  let exc := Nat.card {x : Fin n // zagExceedance e π x}
  have hπ : cycleQuotientCount π = k := q.2.1
  have hD : cycleQuotientCount D = 1 := q.2.2
  have hDinv : cycleQuotientCount D⁻¹ = 1 := by
    rw [zagCycleQuotientCount_inv, hD]
  have horig : Nat.card (ZagOriginalPoints q) = n - exc - k := by
    simpa only [e, π, exc, hπ] using zagCard_nontrivialAntiExceedances e π
  have hrefExc : Nat.card {x : Fin n //
      zagExceedance (zagReverseOrder hn e) D⁻¹ x} = n - exc - 1 := by
    simpa only [e, π, D, exc] using zagCard_reflected_exceedances hn e π
  have href : Nat.card (ZagReflectedPoints q) = n - (n - exc - 1) - 1 := by
    simpa only [e, π, D, hDinv, hrefExc] using
      zagCard_nontrivialAntiExceedances (zagReverseOrder hn e) D⁻¹
  let base := e (zagBasePoint ⟨0, hn⟩)
  let x₀ := π.symm base
  have hx₀ : ¬zagExceedance e π x₀ := by
    intro hx
    have hright : e.symm (π x₀) = zagBasePoint ⟨0, hn⟩ := by
      change e.symm (π (π.symm base)) = zagBasePoint ⟨0, hn⟩
      rw [π.apply_symm_apply]
      change e.symm (e (zagBasePoint ⟨0, hn⟩)) = zagBasePoint ⟨0, hn⟩
      rw [e.symm_apply_apply]
    rw [zagExceedance, hright, Fin.lt_def] at hx
    exact Nat.not_lt_zero _ hx
  have hexc_lt_raw : Nat.card {x : Fin n // zagExceedance e π x} < n := by
    rw [Nat.card_eq_fintype_card]
    simpa only [Fintype.card_fin] using
      (Fintype.card_subtype_lt (p := zagExceedance e π) hx₀)
  have hexc_lt : exc < n := by
    simpa only [exc] using hexc_lt_raw
  have hanti_card :
      Nat.card {x : Fin n // ¬zagExceedance e π x} = n - exc := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_fin, exc]
  have hcycle_le_anti :
      cycleQuotientCount π ≤
        Nat.card {x : Fin n // ¬zagExceedance e π x} := by
    calc
      cycleQuotientCount π =
          Nat.card {x : Fin n // zagTrivialAntiExceedance e π x} :=
        (zagCard_trivialAntiExceedances e π).symm
      _ = Nat.card {x : {x : Fin n // ¬zagExceedance e π x} //
          zagTrivialAntiExceedance e π x.1} :=
        Nat.card_congr (zagTrivialAntiExceedanceEquiv e π)
      _ ≤ Nat.card {x : Fin n // ¬zagExceedance e π x} := by
        simp only [Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_le _
  have hsum : exc + k ≤ n := by
    rw [hanti_card, hπ] at hcycle_le_anti
    omega
  rw [horig, href]
  omega

private abbrev ZagOriginalTotal (n : ℕ) (hn : 0 < n) (k l : ℕ) :=
  Σ q : ZagPlaneConfigBy n hn k l, ZagOriginalPoints q

private abbrev ZagReflectedTotal (n : ℕ) (hn : 0 < n) (k : ℕ) :=
  Σ q : ZagPlaneConfig n hn k, ZagReflectedPoints q

private theorem zagCard_originalTotal_add_reflectedTotal
    (n k : ℕ) (hn : 0 < n) :
    Nat.card (ZagOriginalTotal n hn k 1) +
        Nat.card (ZagReflectedTotal n hn k) =
      (n - k) * Nat.card (ZagPlaneConfig n hn k) := by
  rw [Nat.card_sigma, Nat.card_sigma, ← Finset.sum_add_distrib]
  simp_rw [zagCard_original_add_reflected hn]
  rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card, Nat.mul_comm]

private abbrev ZagPointedConfigBy (n : ℕ) (hn : 0 < n) (k l : ℕ) :=
  {p : ZagPointedPlane n //
    p.order (zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩ ∧
      cycleQuotientCount p.vertical = k ∧
      cycleQuotientCount (zagDiagonal p.order p.vertical) = l}

private def zagOriginalTotalEquivPointedConfigBy
    (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    ZagOriginalTotal n hn k l ≃ ZagPointedConfigBy n hn k l where
  toFun q :=
    ⟨⟨q.1.1.1.1, q.1.1.2, q.2.1, q.2.2⟩,
      q.1.1.1.2, q.1.2.1, q.1.2.2⟩
  invFun p :=
    ⟨⟨(⟨p.1.order, p.2.1⟩, p.1.vertical), ⟨p.2.2.1, p.2.2.2⟩⟩,
      ⟨p.1.point, p.1.point_property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev ZagOddMarkedConfigBy (n : ℕ) (hn : 0 < n) (k l : ℕ) :=
  {q : ZagOddMarkedPlane n //
    q.order (zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩ ∧
      cycleQuotientCount q.vertical =
        k + 2 * (q.marks.depth + 1) ∧
      cycleQuotientCount (zagDiagonal q.order q.vertical) = l}

private noncomputable def zagPointedConfigByEquivOddMarkedConfigBy
    (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    ZagPointedConfigBy n hn k l ≃ ZagOddMarkedConfigBy n hn k l where
  toFun p := by
    let q := (zagFullSlice p.1).out
    refine ⟨q, ?_, ?_, ?_⟩
    · have hbase := zagFullSlice_basePoint p.1
      have hpoint : zagBasePoint p.1.point = zagBasePoint ⟨0, hn⟩ := Fin.ext rfl
      rw [hpoint] at hbase
      exact hbase.trans p.2.1
    · simpa only [q, p.2.2.1] using zagFullSlice_cycleCount p.1
    · exact (congrArg cycleQuotientCount
        (zagFullSlice_diagonal p.1)).trans p.2.2.2
  invFun q := by
    let p := (zagFullMerge q.1).out
    have hs : (zagFullSlice p).out = q.1 := zagFullSlice_fullMerge q.1
    refine ⟨p, ?_, ?_, ?_⟩
    · have hbase := zagFullSlice_basePoint p
      have hpoint : zagBasePoint p.point = zagBasePoint ⟨0, hn⟩ := Fin.ext rfl
      rw [hpoint, hs] at hbase
      exact hbase.symm.trans q.2.1
    · have hcount := zagFullSlice_cycleCount p
      rw [hs] at hcount
      omega
    · have hdiag := zagFullSlice_diagonal p
      rw [hs] at hdiag
      exact (congrArg cycleQuotientCount hdiag.symm).trans q.2.2.2
  left_inv p := by
    apply Subtype.ext
    exact zagFullMerge_fullSlice p.1
  right_inv q := by
    apply Subtype.ext
    exact zagFullSlice_fullMerge q.1

private theorem ZagOddMarks.depth_lt {n : ℕ}
    {e π : Equiv.Perm (Fin n)} {root : Fin n}
    (m : ZagOddMarks e π root) : m.depth < n := by
  have hlen := m.nodup_toList.length_le_card
  rw [m.length_toList, Fintype.card_fin] at hlen
  omega

private abbrev ZagMarkedDepthDecomposition
    (n : ℕ) (hn : 0 < n) (k l : ℕ) :=
  Σ d : Fin n,
    Σ q : ZagPlaneConfigBy n hn (k + 2 * (d.val + 1)) l,
      {m : Σ root, ZagOddMarks q.1.1.1 q.1.2 root //
        m.2.depth = d.val}

private noncomputable def zagOddMarkedDepthFiberEquiv
    (n : ℕ) (hn : 0 < n) (k l : ℕ) (d : Fin n) :
    {q : ZagOddMarkedConfigBy n hn k l //
        (⟨q.1.marks.depth, q.1.marks.depth_lt⟩ : Fin n) = d} ≃
      Σ c : ZagPlaneConfigBy n hn (k + 2 * (d.val + 1)) l,
        {m : Σ root, ZagOddMarks c.1.1.1 c.1.2 root //
          m.2.depth = d.val} where
  toFun q := by
    have hdepth : q.1.1.marks.depth = d.val := congrArg Fin.val q.2
    let c : ZagPlaneConfigBy n hn (k + 2 * (d.val + 1)) l :=
      ⟨(⟨q.1.1.order, q.1.2.1⟩, q.1.1.vertical), by
        exact ⟨by simpa only [hdepth] using q.1.2.2.1, q.1.2.2.2⟩⟩
    exact ⟨c, ⟨⟨q.1.1.root, q.1.1.marks⟩, hdepth⟩⟩
  invFun r := by
    let c := r.1
    let m := r.2.1
    let q : ZagOddMarkedConfigBy n hn k l := by
      refine ⟨⟨c.1.1.1, c.1.2, m.1, m.2⟩, c.1.1.2, ?_, c.2.2⟩
      rw [c.2.1, r.2.2]
    refine ⟨q, ?_⟩
    apply Fin.ext
    exact r.2.2
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    apply zagOddMarkedPlane_ext <;> rfl
  right_inv r := by
    rcases r with ⟨c, ⟨⟨root, marks⟩, hdepth⟩⟩
    apply Sigma.ext
    · rfl
    · exact HEq.rfl

private noncomputable def zagOddMarkedConfigByEquivDepthDecomposition
    (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    ZagOddMarkedConfigBy n hn k l ≃
      ZagMarkedDepthDecomposition n hn k l := by
  let depthIndex : ZagOddMarkedConfigBy n hn k l → Fin n := fun q =>
    ⟨q.1.marks.depth, q.1.marks.depth_lt⟩
  exact (Equiv.sigmaFiberEquiv depthIndex).symm.trans
    (Equiv.sigmaCongrRight fun d => zagOddMarkedDepthFiberEquiv n hn k l d)

private theorem zagCard_originalTotal_eq_sum_depth
    (n k l : ℕ) (hn : 0 < n) :
    Nat.card (ZagOriginalTotal n hn k l) =
      ∑ d : Fin n,
        (k + 2 * (d.val + 1)).choose (2 * d.val + 3) *
          Nat.card (ZagPlaneConfigBy n hn (k + 2 * (d.val + 1)) l) := by
  classical
  let E := (zagOriginalTotalEquivPointedConfigBy n hn k l).trans
    ((zagPointedConfigByEquivOddMarkedConfigBy n hn k l).trans
      (zagOddMarkedConfigByEquivDepthDecomposition n hn k l))
  rw [Nat.card_congr E, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.card_sigma]
  have hmarks (q : ZagPlaneConfigBy n hn (k + 2 * (d.val + 1)) l) :
      Nat.card {m : Σ root, ZagOddMarks q.1.1.1 q.1.2 root //
          m.2.depth = d.val} =
        (k + 2 * (d.val + 1)).choose (2 * d.val + 3) := by
    rw [zagCard_oddMarks_depth, q.2.1]
  simp_rw [hmarks]
  rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.mul_comm]

private theorem zagCycleQuotientCount_le {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : cycleQuotientCount σ ≤ n := by
  rw [cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints]
  simp only [Fintype.card_fin]
  have hsum : σ.cycleType.sum ≤ n := by
    simpa using σ.sum_cycleType_le
  have hcard : Multiset.card σ.cycleType ≤ σ.cycleType.sum :=
    zagMultiset_card_le_sum σ.cycleType fun a ha =>
      (Equiv.Perm.two_le_of_mem_cycleType ha).trans' (by omega)
  omega

private theorem zagVertical_cycleCount_odd {n k j : ℕ} (hn : 0 < n)
    (hparity : Even (n - k)) (e π : Equiv.Perm (Fin n))
    (hj : cycleQuotientCount π = j)
    (hdiag : cycleQuotientCount (zagDiagonal e π) = k) : Odd j := by
  let D := zagDiagonal e π
  let s := zagHorizontal e
  have hsignCount (σ : Equiv.Perm (Fin n)) :
      σ.sign = (-1 : ℤˣ) ^ (n - cycleQuotientCount σ) := by
    simpa only [cycleQuotientCount_eq] using zagSign_eq_neg_one_pow_cycleCount σ
  have hDsign : D.sign = 1 := by
    rw [hsignCount, show cycleQuotientCount D = k by exact hdiag]
    exact hparity.neg_one_pow
  have hfactor : D * π = s := by
    simp only [D, s, zagDiagonal]
    group
  have hsign : π.sign = s.sign := by
    have h := congrArg Equiv.Perm.sign hfactor
    rw [Equiv.Perm.sign_mul, hDsign, one_mul] at h
    exact h
  rw [hsignCount, hj] at hsign
  rw [hsignCount, show cycleQuotientCount s = 1 by
    exact zagHorizontal_cycleCount e hn] at hsign
  have hpowParity : Even (n - j) ↔ Even (n - 1) := by
    constructor
    · intro hjEven
      by_contra hsEven
      have hsOdd : Odd (n - 1) := Nat.not_even_iff_odd.mp hsEven
      have hone : (1 : ℤˣ) = -1 := by
        simpa only [hjEven.neg_one_pow, hsOdd.neg_one_pow] using hsign
      exact (by decide : (1 : ℤˣ) ≠ -1) hone
    · intro hsEven
      by_contra hjEven
      have hjOdd : Odd (n - j) := Nat.not_even_iff_odd.mp hjEven
      have hone : (-1 : ℤˣ) = 1 := by
        simpa only [hjOdd.neg_one_pow, hsEven.neg_one_pow] using hsign
      exact (by decide : (-1 : ℤˣ) ≠ 1) hone
  have hjle : j ≤ n := by
    rw [← hj]
    exact zagCycleQuotientCount_le π
  rw [Nat.even_sub' hjle, Nat.even_sub' (by omega : 1 ≤ n)] at hpowParity
  simp only [odd_one, iff_true] at hpowParity
  by_cases hnOdd : Odd n
  · exact (hpowParity.mpr hnOdd).mp hnOdd
  · by_contra hjOdd
    exact hnOdd (hpowParity.mp ⟨fun h => (hnOdd h).elim, fun h => (hjOdd h).elim⟩)

private abbrev ZagAnchoredOrder (n : ℕ) (hn : 0 < n) :=
  {e : Equiv.Perm (Fin n) //
    e (zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩}

private abbrev ZagPlaneConfigDiagonal (n : ℕ) (hn : 0 < n) (k : ℕ) :=
  {p : ZagAnchoredOrder n hn × Equiv.Perm (Fin n) //
    cycleQuotientCount (zagDiagonal p.1.1 p.2) = k}

private noncomputable def zagPlaneConfigDiagonalEquivProduct
    (n k : ℕ) (hn : 0 < n) :
    ZagPlaneConfigDiagonal n hn k ≃
      ZagAnchoredOrder n hn ×
        {D : Equiv.Perm (Fin n) // cycleQuotientCount D = k} where
  toFun q := (q.1.1, ⟨zagDiagonal q.1.1.1 q.1.2, q.2⟩)
  invFun q := by
    refine ⟨(q.1, q.2.1⁻¹ * zagHorizontal q.1.1), ?_⟩
    have hdiag :
        zagDiagonal q.1.1 (q.2.1⁻¹ * zagHorizontal q.1.1) = q.2.1 := by
      simp only [zagDiagonal, mul_inv_rev, inv_inv]
      group
    rw [hdiag]
    exact q.2.2
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (zagDiagonal q.1.1.1 q.1.2)⁻¹ * zagHorizontal q.1.1.1 = q.1.2
      simp only [zagDiagonal, mul_inv_rev, inv_inv]
      group
  right_inv q := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change zagDiagonal q.1.1 (q.2.1⁻¹ * zagHorizontal q.1.1) = q.2.1
      simp only [zagDiagonal, mul_inv_rev, inv_inv]
      group

private theorem zagCard_planeConfigDiagonal
    (n k : ℕ) (hn : 0 < n) :
    Nat.card (ZagPlaneConfigDiagonal n hn k) =
      (n - 1).factorial * Nat.stirlingFirst n k := by
  rw [Nat.card_congr (zagPlaneConfigDiagonalEquivProduct n k hn), Nat.card_prod]
  have horder : Nat.card (ZagAnchoredOrder n hn) = (n - 1).factorial := by
    rw [Nat.card_congr (zagAnchoredOrderEquivFullCycle n hn),
      Nat.card_eq_fintype_card]
    simpa only [cycleQuotientCount_eq] using zagCard_fullCycles n hn
  have hcycles :
      Fintype.card {D : Equiv.Perm (Fin n) // cycleQuotientCount D = k} =
        Nat.stirlingFirst n k := by
    simpa only [cycleQuotientCount_eq] using card_perm_cycleCount_eq_stirlingFirst n k
  rw [horder, Nat.card_eq_fintype_card, hcycles]

private abbrev ZagVerticalFiber
    (n : ℕ) (hn : 0 < n) (k j : ℕ) :=
  {q : ZagPlaneConfigDiagonal n hn k //
    cycleQuotientCount q.1.2 = j}

private def zagPlaneConfigByEquivVerticalFiber
    (n : ℕ) (hn : 0 < n) (j k : ℕ) :
    ZagPlaneConfigBy n hn j k ≃ ZagVerticalFiber n hn k j where
  toFun q := ⟨⟨q.1, q.2.2⟩, q.2.1⟩
  invFun q := ⟨q.1.1, q.2, q.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev ZagOddVerticalDecomposition
    (n : ℕ) (hn : 0 < n) (k : ℕ) :=
  ZagVerticalFiber n hn k 1 ⊕
    Σ d : Fin n, ZagVerticalFiber n hn k (2 * d.val + 3)

private noncomputable def zagOddVerticalDecompositionEquiv
    (n k : ℕ) (hn : 0 < n) (hparity : Even (n - k)) :
    ZagOddVerticalDecomposition n hn k ≃ ZagPlaneConfigDiagonal n hn k := by
  let toRaw : ZagOddVerticalDecomposition n hn k →
      ZagPlaneConfigDiagonal n hn k
    | Sum.inl q => q.1
    | Sum.inr q => q.2.1
  refine Equiv.ofBijective toRaw ?_
  constructor
  · intro a b hab
    rcases a with a | ⟨d, a⟩
    · rcases b with b | ⟨d, b⟩
      · apply congrArg Sum.inl
        apply Subtype.ext
        exact hab
      · have hcount := congrArg
          (fun q : ZagPlaneConfigDiagonal n hn k =>
            cycleQuotientCount q.1.2) hab
        rw [a.2, b.2] at hcount
        omega
    · rcases b with b | ⟨d', b⟩
      · have hcount := congrArg
          (fun q : ZagPlaneConfigDiagonal n hn k =>
            cycleQuotientCount q.1.2) hab
        rw [a.2, b.2] at hcount
        omega
      · have hcount := congrArg
          (fun q : ZagPlaneConfigDiagonal n hn k =>
            cycleQuotientCount q.1.2) hab
        rw [a.2, b.2] at hcount
        have hdd : d = d' := by
          apply Fin.ext
          omega
        subst d'
        apply congrArg Sum.inr
        apply Sigma.ext
        · rfl
        · exact heq_of_eq (Subtype.ext hab)
  · intro q
    let j := cycleQuotientCount q.1.2
    have hjOdd : Odd j :=
      zagVertical_cycleCount_odd hn hparity q.1.1.1 q.1.2 rfl q.2
    by_cases hjOne : j = 1
    · exact ⟨Sum.inl ⟨q, hjOne⟩, rfl⟩
    · obtain ⟨r, hr⟩ := hjOdd
      have hrpos : 0 < r := by
        by_contra hrzero
        have : r = 0 := by omega
        subst r
        simp only [mul_zero, zero_add] at hr
        exact hjOne hr
      have hjle : j ≤ n := by
        exact (show cycleQuotientCount q.1.2 ≤ n from
          zagCycleQuotientCount_le q.1.2)
      let d : Fin n := ⟨r - 1, by omega⟩
      have hjDepth : j = 2 * d.val + 3 := by
        dsimp only [d]
        omega
      exact ⟨Sum.inr ⟨d, ⟨q, hjDepth⟩⟩, rfl⟩

private theorem zagCard_planeConfigDiagonal_decompose
    (n k : ℕ) (hn : 0 < n) (hparity : Even (n - k)) :
    Nat.card (ZagPlaneConfigDiagonal n hn k) =
      Nat.card (ZagPlaneConfigBy n hn 1 k) +
        ∑ d : Fin n, Nat.card (ZagPlaneConfigBy n hn (2 * d.val + 3) k) := by
  let E := zagOddVerticalDecompositionEquiv n k hn hparity
  rw [← Nat.card_congr E, Nat.card_sum, Nat.card_sigma]
  have hcard (j : ℕ) :
      Nat.card (ZagVerticalFiber n hn k j) =
        Nat.card (ZagPlaneConfigBy n hn j k) :=
    (Nat.card_congr (zagPlaneConfigByEquivVerticalFiber n hn j k)).symm
  rw [hcard]
  simp_rw [hcard]

private theorem zagReverseOrder_reverseOrder {n : ℕ} (hn : 0 < n)
    (e : Equiv.Perm (Fin n)) :
    zagReverseOrder hn (zagReverseOrder hn e) = e := by
  let R := zagReverseIndex n hn
  have hR : R * R = 1 := by
    have hRinv : R⁻¹ = R := zagReverseIndex_inv hn
    calc
      R * R = R * R⁻¹ := congrArg (fun x => R * x) hRinv.symm
      _ = 1 := mul_inv_cancel R
  change (e * R) * R = e
  rw [mul_assoc, hR, mul_one]

private theorem zagDiagonal_reflected {n : ℕ} (hn : 0 < n)
    (e π : Equiv.Perm (Fin n)) :
    zagDiagonal (zagReverseOrder hn e) (zagDiagonal e π)⁻¹ = π⁻¹ := by
  rw [zagDiagonal, zagHorizontal_reverseOrder, inv_inv, zagDiagonal]
  group

private noncomputable def zagReflectConfig
    (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    ZagPlaneConfigBy n hn k l → ZagPlaneConfigBy n hn l k := fun q =>
  ⟨(⟨zagReverseOrder hn q.1.1.1,
      zagReverseOrder_basePoint hn q.1.1.1 q.1.1.2⟩,
      (zagDiagonal q.1.1.1 q.1.2)⁻¹),
    ⟨by rw [zagCycleQuotientCount_inv, q.2.2], by
      rw [zagDiagonal_reflected, zagCycleQuotientCount_inv, q.2.1]⟩⟩

private theorem zagReflectConfig_involutive
    (n : ℕ) (hn : 0 < n) (k l : ℕ)
    (q : ZagPlaneConfigBy n hn k l) :
    zagReflectConfig n hn l k (zagReflectConfig n hn k l q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact zagReverseOrder_reverseOrder hn q.1.1.1
  · exact congrArg Inv.inv (zagDiagonal_reflected hn q.1.1.1 q.1.2)

private noncomputable def zagReflectConfigEquiv
    (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    ZagPlaneConfigBy n hn k l ≃ ZagPlaneConfigBy n hn l k where
  toFun := zagReflectConfig n hn k l
  invFun := zagReflectConfig n hn l k
  left_inv := zagReflectConfig_involutive n hn k l
  right_inv := zagReflectConfig_involutive n hn l k

private noncomputable def zagReflectedTotalEquivOriginalTotal
    (n k : ℕ) (hn : 0 < n) :
    ZagReflectedTotal n hn k ≃ ZagOriginalTotal n hn 1 k :=
  Equiv.sigmaCongr (zagReflectConfigEquiv n hn k 1) fun _q => Equiv.refl _

private theorem zagCard_reflectedTotal_eq_sum_depth
    (n k : ℕ) (hn : 0 < n) :
    Nat.card (ZagReflectedTotal n hn k) =
      ∑ d : Fin n,
        Nat.card (ZagPlaneConfigBy n hn (2 * d.val + 3) k) := by
  rw [Nat.card_congr (zagReflectedTotalEquivOriginalTotal n k hn),
    zagCard_originalTotal_eq_sum_depth]
  apply Finset.sum_congr rfl
  intro d hd
  have hindex : 1 + 2 * (d.val + 1) = 2 * d.val + 3 := by omega
  rw [hindex, Nat.choose_self, one_mul]

private theorem zagPlaneConfig_recurrence
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (hparity : Even (n - k)) :
    (n + 1 - k) * Nat.card (ZagPlaneConfig n hn k) =
      (∑ d : Fin n,
        (k + 2 * (d.val + 1)).choose (k - 1) *
          Nat.card (ZagPlaneConfig n hn (k + 2 * (d.val + 1)))) +
        (n - 1).factorial * Nat.stirlingFirst n k := by
  have hpair := zagCard_originalTotal_add_reflectedTotal n k hn
  have horiginal := zagCard_originalTotal_eq_sum_depth n k 1 hn
  have hreflected := zagCard_reflectedTotal_eq_sum_depth n k hn
  have hdecompose := zagCard_planeConfigDiagonal_decompose n k hn hparity
  have htotal := zagCard_planeConfigDiagonal n k hn
  have hswap : Nat.card (ZagPlaneConfig n hn k) =
      Nat.card (ZagPlaneConfigBy n hn 1 k) :=
    Nat.card_congr (zagReflectConfigEquiv n hn k 1)
  have hreflected_add :
      Nat.card (ZagReflectedTotal n hn k) +
          Nat.card (ZagPlaneConfig n hn k) =
        (n - 1).factorial * Nat.stirlingFirst n k := by
    calc
      _ = (∑ d : Fin n,
            Nat.card (ZagPlaneConfigBy n hn (2 * d.val + 3) k)) +
          Nat.card (ZagPlaneConfig n hn k) := by rw [hreflected]
      _ = Nat.card (ZagPlaneConfigBy n hn 1 k) +
          ∑ d : Fin n,
            Nat.card (ZagPlaneConfigBy n hn (2 * d.val + 3) k) := by
        rw [← hswap]
        exact Nat.add_comm _ _
      _ = Nat.card (ZagPlaneConfigDiagonal n hn k) := hdecompose.symm
      _ = (n - 1).factorial * Nat.stirlingFirst n k := htotal
  have hchoose (d : Fin n) :
      (k + 2 * (d.val + 1)).choose (2 * d.val + 3) =
        (k + 2 * (d.val + 1)).choose (k - 1) := by
    have hsum : k + 2 * (d.val + 1) =
        (2 * d.val + 3) + (k - 1) := by omega
    calc
      _ = ((2 * d.val + 3) + (k - 1)).choose (2 * d.val + 3) := by rw [hsum]
      _ = ((2 * d.val + 3) + (k - 1)).choose (k - 1) := Nat.choose_symm_add
      _ = (k + 2 * (d.val + 1)).choose (k - 1) := by rw [hsum]
  simp_rw [hchoose] at horiginal
  have hcoefficient : n + 1 - k = (n - k) + 1 := by omega
  calc
    (n + 1 - k) * Nat.card (ZagPlaneConfig n hn k) =
        (n - k) * Nat.card (ZagPlaneConfig n hn k) +
          Nat.card (ZagPlaneConfig n hn k) := by
      rw [hcoefficient, add_mul, one_mul]
    _ = (Nat.card (ZagOriginalTotal n hn k 1) +
          Nat.card (ZagReflectedTotal n hn k)) +
        Nat.card (ZagPlaneConfig n hn k) := by rw [hpair]
    _ = Nat.card (ZagOriginalTotal n hn k 1) +
        (Nat.card (ZagReflectedTotal n hn k) +
          Nat.card (ZagPlaneConfig n hn k)) := Nat.add_assoc _ _ _
    _ = Nat.card (ZagOriginalTotal n hn k 1) +
        (n - 1).factorial * Nat.stirlingFirst n k := by rw [hreflected_add]
    _ = (∑ d : Fin n,
          (k + 2 * (d.val + 1)).choose (k - 1) *
            Nat.card (ZagPlaneConfig n hn (k + 2 * (d.val + 1)))) +
        (n - 1).factorial * Nat.stirlingFirst n k := by rw [horiginal]

private abbrev ZagCyclePairs (n k : ℕ) :=
  {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
    cycleQuotientCount p.1 = 1 ∧
      cycleQuotientCount p.2 = 1 ∧
      cycleQuotientCount (p.1 * p.2) = k}

private noncomputable def zagPlanePairsEquivCyclePairs (n k : ℕ) :
    ZagPlanePairs n k ≃ ZagCyclePairs n k where
  toFun q := by
    refine ⟨(q.1.2 * q.1.1.1⁻¹, q.1.1.1), ?_, q.1.1.2, ?_⟩
    · have hfirst : q.1.2 * q.1.1.1⁻¹ =
          (q.1.1.1 * q.1.2⁻¹)⁻¹ := by
        simp only [mul_inv_rev, inv_inv]
      rw [hfirst, zagCycleQuotientCount_inv, q.2.2]
    · have hproduct : (q.1.2 * q.1.1.1⁻¹) * q.1.1.1 = q.1.2 := by group
      rw [hproduct, q.2.1]
  invFun p := by
    refine ⟨(⟨p.1.2, p.2.2.1⟩, p.1.1 * p.1.2), p.2.2.2, ?_⟩
    have hdiag : p.1.2 * (p.1.1 * p.1.2)⁻¹ = p.1.1⁻¹ := by
      simp only [mul_inv_rev]
      group
    rw [hdiag, zagCycleQuotientCount_inv, p.2.1]
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · group
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · group
    · rfl

private noncomputable def zagPlaneConfigEquivCyclePairs
    (n k : ℕ) (hn : 0 < n) :
    ZagPlaneConfig n hn k ≃ ZagCyclePairs n k :=
  (zagPlaneConfigEquivPairs n k hn).trans (zagPlanePairsEquivCyclePairs n k)

private theorem zagCyclePairs_recurrence
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (hparity : Even (n - k)) :
    (n + 1 - k) * Nat.card (ZagCyclePairs n k) =
      (∑ d : Fin n,
        (k + 2 * (d.val + 1)).choose (k - 1) *
          Nat.card (ZagCyclePairs n (k + 2 * (d.val + 1)))) +
        (n - 1).factorial * Nat.stirlingFirst n k := by
  have h := zagPlaneConfig_recurrence n k hn hk hkn hparity
  have hcard (j : ℕ) :
      Nat.card (ZagPlaneConfig n hn j) = Nat.card (ZagCyclePairs n j) :=
    Nat.card_congr (zagPlaneConfigEquivCyclePairs n j hn)
  simp_rw [hcard] at h
  exact h

private noncomputable def zagStirlingPolynomial (n : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.range n, (Polynomial.X + Polynomial.C (i : ℤ))

private theorem zagStirlingPolynomial_coeff (n k : ℕ) :
    (zagStirlingPolynomial n).coeff k = (Nat.stirlingFirst n k : ℤ) := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => simp [zagStirlingPolynomial]
      | succ k => simp [zagStirlingPolynomial, Polynomial.coeff_one]
  | succ n ih =>
      cases k with
      | zero =>
          rw [zagStirlingPolynomial, Finset.prod_range_succ]
          change ((zagStirlingPolynomial n) *
            (Polynomial.X + Polynomial.C (n : ℤ))).coeff 0 = _
          rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul,
            ← Polynomial.coeff_zero_eq_eval_zero, ih]
          cases n <;> simp
      | succ k =>
          rw [zagStirlingPolynomial, Finset.prod_range_succ]
          change ((zagStirlingPolynomial n) *
            (Polynomial.X + Polynomial.C (n : ℤ))).coeff (k + 1) = _
          rw [mul_add, Polynomial.coeff_add, Polynomial.coeff_mul_X,
            Polynomial.coeff_mul_C, ih, ih, Nat.stirlingFirst_succ_succ]
          push_cast
          ring

private theorem zagStirlingPolynomial_natDegree_le (n : ℕ) :
    (zagStirlingPolynomial n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [zagStirlingPolynomial_coeff, Nat.stirlingFirst_eq_zero_of_lt hk]
  exact Int.ofNat_zero

private theorem zagStirlingPolynomial_taylor_coeff (n k : ℕ) (a : ℤ) :
    (Polynomial.taylor a (zagStirlingPolynomial n)).coeff k =
      ∑ m ∈ Finset.range (n + 1),
        ((m + k).choose k : ℤ) * (Nat.stirlingFirst n (m + k) : ℤ) * a ^ m := by
  rw [Polynomial.taylor_coeff]
  have hdegree := Polynomial.natDegree_hasseDeriv_le (zagStirlingPolynomial n) k
  have hrange : (Polynomial.hasseDeriv k (zagStirlingPolynomial n)).natDegree < n + 1 := by
    have hp := zagStirlingPolynomial_natDegree_le n
    omega
  rw [Polynomial.eval_eq_sum_range' hrange]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.hasseDeriv_coeff, zagStirlingPolynomial_coeff]

private theorem zagOddDifferenceSum (n : ℕ) (A : ℕ → ℤ)
    (hzero : ∀ d < n + 1, n + 2 ≤ 2 * d + 1 → A (2 * d + 1) = 0) :
    (∑ m ∈ Finset.range (n + 2), A m * (1 - (-1 : ℤ) ^ m)) =
      2 * ∑ d : Fin (n + 1), A (2 * d.val + 1) := by
  classical
  let s := (Finset.range (n + 2)).filter Odd
  let t := (Finset.range (n + 1)).filter fun d => 2 * d + 1 < n + 2
  have heven :
      ∑ m ∈ (Finset.range (n + 2)).filter (fun m => ¬Odd m),
          A m * (1 - (-1 : ℤ) ^ m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hmEven : Even m := Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hm).2
    rw [hmEven.neg_one_pow, sub_self, mul_zero]
  have hodd :
      ∑ m ∈ s, A m = ∑ d ∈ t, A (2 * d + 1) := by
    apply Finset.sum_bij (fun m _ => m / 2)
    · intro m hm
      have hmRange := (Finset.mem_filter.mp hm).1
      have hmLt := Finset.mem_range.mp hmRange
      have hmOdd := (Finset.mem_filter.mp hm).2
      have hmEq := Nat.two_mul_div_two_add_one_of_odd hmOdd
      rw [two_mul] at hmEq
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · rw [two_mul, hmEq]
        exact hmLt
    · intro a ha b hb hab
      have haEq := Nat.two_mul_div_two_add_one_of_odd (Finset.mem_filter.mp ha).2
      have hbEq := Nat.two_mul_div_two_add_one_of_odd (Finset.mem_filter.mp hb).2
      omega
    · intro d hd
      have hdRange := (Finset.mem_filter.mp hd).1
      have hdBound := (Finset.mem_filter.mp hd).2
      refine ⟨2 * d + 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdBound, ?_⟩, ?_⟩
      · exact ⟨d, by omega⟩
      · omega
    · intro m hm
      have hmEq := Nat.two_mul_div_two_add_one_of_odd (Finset.mem_filter.mp hm).2
      rw [hmEq]
  have htail :
      ∑ d ∈ t, A (2 * d + 1) =
        ∑ d ∈ Finset.range (n + 1), A (2 * d + 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
      (fun d => 2 * d + 1 < n + 2) (fun d => A (2 * d + 1))]
    change ∑ d ∈ t, A (2 * d + 1) =
      ∑ d ∈ t, A (2 * d + 1) +
        ∑ d ∈ (Finset.range (n + 1)).filter (fun d => ¬2 * d + 1 < n + 2),
          A (2 * d + 1)
    have hz :
        ∑ d ∈ (Finset.range (n + 1)).filter (fun d => ¬2 * d + 1 < n + 2),
          A (2 * d + 1) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hdNot := (Finset.mem_filter.mp hd).2
      exact hzero d (Finset.mem_range.mp (Finset.mem_filter.mp hd).1)
        (by rw [two_mul] at hdNot ⊢; omega)
    rw [hz, add_zero]
  calc
    _ = (∑ m ∈ s, A m * (1 - (-1 : ℤ) ^ m)) + 0 := by
      rw [← heven, Finset.sum_filter_add_sum_filter_not]
    _ = ∑ m ∈ s, 2 * A m := by
      simp only [add_zero]
      apply Finset.sum_congr rfl
      intro m hm
      have hmOdd := (Finset.mem_filter.mp hm).2
      rw [hmOdd.neg_one_pow]
      ring
    _ = 2 * ∑ m ∈ s, A m := by rw [Finset.mul_sum]
    _ = 2 * ∑ d ∈ t, A (2 * d + 1) := by rw [hodd]
    _ = 2 * ∑ d ∈ Finset.range (n + 1), A (2 * d + 1) := by rw [htail]
    _ = 2 * ∑ d : Fin (n + 1), A (2 * d.val + 1) := by
      rw [Finset.sum_range]

private theorem zagStirlingPolynomial_succ (n : ℕ) :
    zagStirlingPolynomial (n + 1) =
      zagStirlingPolynomial n * (Polynomial.X + Polynomial.C (n : ℤ)) := by
  rw [zagStirlingPolynomial, Finset.prod_range_succ]
  rfl

private theorem zagStirlingPolynomial_taylor_one_two_step (m : ℕ) :
    Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial (m + 2)) =
      Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m) *
        (Polynomial.X + Polynomial.C (m + 1 : ℤ)) *
        (Polynomial.X + Polynomial.C (m + 2 : ℤ)) := by
  rw [show m + 2 = (m + 1) + 1 by omega, zagStirlingPolynomial_succ,
    zagStirlingPolynomial_succ]
  simp only [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  push_cast
  simp only [Polynomial.C_add, Polynomial.C_1, Polynomial.C_ofNat]
  ring_nf

private theorem zagStirlingPolynomial_taylor_neg_one_two_step (m : ℕ) :
    Polynomial.taylor (-1 : ℤ) (zagStirlingPolynomial (m + 2)) =
      (Polynomial.X - Polynomial.C 1) * Polynomial.X *
        Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m) := by
  induction m with
  | zero =>
      norm_num [zagStirlingPolynomial, Finset.prod_range_succ, Polynomial.taylor_apply]
      ring_nf
  | succ m ih =>
      conv_lhs =>
        rw [show m + 1 + 2 = (m + 2) + 1 by omega, zagStirlingPolynomial_succ]
      conv_rhs =>
        rw [zagStirlingPolynomial_succ]
      simp only [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.add_comp,
        Polynomial.X_comp, Polynomial.C_comp] at ih ⊢
      rw [ih]
      push_cast
      simp only [Polynomial.C_add, Polynomial.C_neg, Polynomial.C_1,
        Polynomial.C_ofNat]
      ring_nf

private theorem zagStirlingPolynomial_taylor_sub (m : ℕ) :
    Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial (m + 2)) -
        Polynomial.taylor (-1 : ℤ) (zagStirlingPolynomial (m + 2)) =
      Polynomial.C (m + 2 : ℤ) *
        (Polynomial.C 2 * Polynomial.X + Polynomial.C (m + 1 : ℤ)) *
        Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m) := by
  rw [zagStirlingPolynomial_taylor_one_two_step,
    zagStirlingPolynomial_taylor_neg_one_two_step]
  simp only [Polynomial.C_add, Polynomial.C_1, Polynomial.C_ofNat]
  ring_nf

private theorem zagX_mul_stirlingPolynomial_taylor_one (m : ℕ) :
    Polynomial.X * Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m) =
      zagStirlingPolynomial (m + 1) := by
  induction m with
  | zero => simp [zagStirlingPolynomial, Polynomial.taylor_apply]
  | succ m ih =>
    rw [zagStirlingPolynomial_succ]
    simp only [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.add_comp,
      Polynomial.X_comp, Polynomial.C_comp] at ih ⊢
    rw [← mul_assoc, ih]
    conv_rhs =>
      rw [show m + 1 + 1 = (m + 1) + 1 by rfl, zagStirlingPolynomial_succ]
    push_cast
    simp only [Polynomial.C_add, Polynomial.C_1]
    ring

private theorem zagStirlingPolynomial_taylor_one_coeff (m k : ℕ) :
    (Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m)).coeff k =
      (Nat.stirlingFirst (m + 1) (k + 1) : ℤ) := by
  calc
    _ = (Polynomial.X *
        Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m)).coeff (k + 1) :=
      (Polynomial.coeff_X_mul _ k).symm
    _ = (zagStirlingPolynomial (m + 1)).coeff (k + 1) := by
      rw [zagX_mul_stirlingPolynomial_taylor_one]
    _ = _ := zagStirlingPolynomial_coeff _ _

private theorem zagStirlingPolynomial_taylor_sub_coeff_rhs (m k : ℕ) :
    (Polynomial.C (m + 2 : ℤ) *
        (Polynomial.C 2 * Polynomial.X + Polynomial.C (m + 1 : ℤ)) *
        Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m)).coeff k =
      (m + 2 : ℤ) *
        (2 * (Nat.stirlingFirst (m + 1) k : ℤ) +
          (m + 1 : ℤ) * (Nat.stirlingFirst (m + 1) (k + 1) : ℤ)) := by
  have hpoly :
      Polynomial.C (m + 2 : ℤ) *
          (Polynomial.C 2 * Polynomial.X + Polynomial.C (m + 1 : ℤ)) *
          Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m) =
        Polynomial.C (m + 2 : ℤ) *
          (Polynomial.C 2 * zagStirlingPolynomial (m + 1) +
            Polynomial.C (m + 1 : ℤ) *
              Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial m)) := by
    rw [← zagX_mul_stirlingPolynomial_taylor_one m]
    ring
  rw [hpoly, Polynomial.coeff_C_mul, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, zagStirlingPolynomial_coeff,
    zagStirlingPolynomial_taylor_one_coeff]

private theorem zagStirlingPolynomial_taylor_sub_coeff_lhs
    (m k : ℕ) (hk : 0 < k) :
    (Polynomial.taylor (1 : ℤ) (zagStirlingPolynomial (m + 2)) -
        Polynomial.taylor (-1 : ℤ) (zagStirlingPolynomial (m + 2))).coeff (k - 1) =
      2 * ((k : ℤ) * (Nat.stirlingFirst (m + 2) k : ℤ) +
        ∑ d : Fin (m + 1),
          ((k + 2 * (d.val + 1)).choose (k - 1) : ℤ) *
            (Nat.stirlingFirst (m + 2) (k + 2 * (d.val + 1)) : ℤ)) := by
  let A : ℕ → ℤ := fun r =>
    ((r + (k - 1)).choose (k - 1) : ℤ) *
      (Nat.stirlingFirst (m + 2) (r + (k - 1)) : ℤ)
  have hzero : ∀ d < m + 1 + 1, m + 1 + 2 ≤ 2 * d + 1 → A (2 * d + 1) = 0 := by
    intro d hd hdLarge
    have hlt : m + 2 < 2 * d + 1 + (k - 1) := by omega
    simp only [A, Nat.stirlingFirst_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
  have hdiff := zagOddDifferenceSum (m + 1) A hzero
  rw [Polynomial.coeff_sub, zagStirlingPolynomial_taylor_coeff,
    zagStirlingPolynomial_taylor_coeff, ← Finset.sum_sub_distrib]
  have hsum :
      (∑ x ∈ Finset.range (m + 2 + 1),
          (((x + (k - 1)).choose (k - 1) : ℤ) *
                (Nat.stirlingFirst (m + 2) (x + (k - 1)) : ℤ) * 1 ^ x -
            ((x + (k - 1)).choose (k - 1) : ℤ) *
                (Nat.stirlingFirst (m + 2) (x + (k - 1)) : ℤ) * (-1) ^ x)) =
        ∑ x ∈ Finset.range (m + 1 + 2), A x * (1 - (-1) ^ x) := by
    apply Finset.sum_congr
    · congr
    · intro x hx
      dsimp only [A]
      simp only [one_pow]
      ring
  rw [hsum, hdiff]
  rw [Fin.sum_univ_succ]
  have hhead : A 1 = (k : ℤ) * (Nat.stirlingFirst (m + 2) k : ℤ) := by
    have hkEq : 1 + (k - 1) = k := by omega
    have hkSucc : (k - 1) + 1 = k := by omega
    have hchoose : k.choose (k - 1) = k := by
      calc
        _ = ((k - 1) + 1).choose (k - 1) := by rw [hkSucc]
        _ = (k - 1) + 1 := Nat.choose_succ_self_right (k - 1)
        _ = k := hkSucc
    dsimp only [A]
    rw [hkEq, hchoose]
  simp only [Fin.val_zero, mul_zero, zero_add, Fin.val_succ]
  rw [hhead]
  apply congrArg (fun z : ℤ => 2 * z)
  apply congrArg (fun z : ℤ =>
    (k : ℤ) * (Nat.stirlingFirst (m + 2) k : ℤ) + z)
  apply Finset.sum_congr rfl
  intro d hd
  dsimp only [A]
  have hindex : 2 * (d.val + 1) + 1 + (k - 1) =
      k + 2 * (d.val + 1) := by omega
  rw [hindex]

private theorem zagTwo_mul_choose_two (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      cases n with
      | zero => simp
      | succ m =>
          rw [Nat.succ_sub_one] at ih
          simp only [Nat.succ_sub_one]
          nlinarith

private theorem zagStirlingFirst_recurrence
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) :
    (n + 1 - k) * Nat.stirlingFirst (n + 1) k =
      (∑ d : Fin n,
        (k + 2 * (d.val + 1)).choose (k - 1) *
          Nat.stirlingFirst (n + 1) (k + 2 * (d.val + 1))) +
        (n + 1).choose 2 * Nat.stirlingFirst n k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hpoly := congrArg (fun p : Polynomial ℤ => p.coeff (k - 1))
    (zagStirlingPolynomial_taylor_sub m)
  rw [zagStirlingPolynomial_taylor_sub_coeff_lhs m k hk,
    zagStirlingPolynomial_taylor_sub_coeff_rhs] at hpoly
  norm_cast at hpoly
  have hkSucc : (k - 1) + 1 = k := by omega
  rw [hkSucc] at hpoly
  have hstirling : Nat.stirlingFirst (m + 1 + 1) k =
      (m + 1) * Nat.stirlingFirst (m + 1) k +
        Nat.stirlingFirst (m + 1) (k - 1) := by
    calc
      _ = Nat.stirlingFirst (m + 1 + 1) ((k - 1) + 1) := by rw [hkSucc]
      _ = (m + 1) * Nat.stirlingFirst (m + 1) ((k - 1) + 1) +
          Nat.stirlingFirst (m + 1) (k - 1) :=
        Nat.stirlingFirst_succ_succ (m + 1) (k - 1)
      _ = _ := by rw [hkSucc]
  have hchoose := zagTwo_mul_choose_two (m + 1 + 1)
  rw [Nat.succ_sub_one] at hchoose
  have hsub : m + 1 + 1 - k + k = m + 1 + 1 := by omega
  nlinarith

private theorem zagCyclePairs_card_eq_zero_of_lt (n k : ℕ) (hnk : n < k) :
    Nat.card (ZagCyclePairs n k) = 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  constructor
  intro p
  have hle := zagCycleQuotientCount_le (p.1.1 * p.1.2)
  rw [p.2.2.2] at hle
  omega

private theorem zagCyclePairs_cross_mul_gap
    (n r : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (hgap : n - k = 2 * r) :
    (n + 1).choose 2 * Nat.card (ZagCyclePairs n k) =
      (n - 1).factorial * Nat.stirlingFirst (n + 1) k := by
  induction r using Nat.strong_induction_on generalizing k with
  | h r ih =>
      have hparity : Even (n - k) := ⟨r, by omega⟩
      have hpairs := zagCyclePairs_recurrence n k hn hk hkn hparity
      have hstirling := zagStirlingFirst_recurrence n k hn hk hkn
      let C := (n + 1).choose 2
      let F := (n - 1).factorial
      let pairSum := ∑ d : Fin n,
        (k + 2 * (d.val + 1)).choose (k - 1) *
          Nat.card (ZagCyclePairs n (k + 2 * (d.val + 1)))
      let stirlingSum := ∑ d : Fin n,
        (k + 2 * (d.val + 1)).choose (k - 1) *
          Nat.stirlingFirst (n + 1) (k + 2 * (d.val + 1))
      have hsum : C * pairSum = F * stirlingSum := by
        dsimp only [pairSum, stirlingSum]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        let j := k + 2 * (d.val + 1)
        by_cases hjn : j ≤ n
        · have hjk : k < j := by dsimp only [j]; omega
          have hjgap : n - j = 2 * (r - (d.val + 1)) := by
            dsimp only [j]
            omega
          have hjr : r - (d.val + 1) < r := by omega
          have hjformula := ih (r - (d.val + 1)) hjr j (by omega) hjn hjgap
          dsimp only [C, F]
          dsimp only [j] at hjformula
          nlinarith
        · have hnj : n + 1 < j := by
            dsimp only [j]
            omega
          rw [zagCyclePairs_card_eq_zero_of_lt n j (by omega),
            Nat.stirlingFirst_eq_zero_of_lt hnj]
          simp
      dsimp only [C, F, pairSum, stirlingSum] at hsum
      apply Nat.mul_left_cancel (by omega : 0 < n + 1 - k)
      nlinarith

private theorem zagCyclePairs_cross_mul
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (hparity : Even (n - k)) :
    (n + 1).choose 2 * Nat.card (ZagCyclePairs n k) =
      (n - 1).factorial * Nat.stirlingFirst (n + 1) k := by
  obtain ⟨r, hr⟩ := hparity
  apply zagCyclePairs_cross_mul_gap n r hn k hk hkn
  omega

/--
**Zagier's formula for products of two cyclic permutations.** Let $n$ and $k$ be integers
with $n \ge 1$ and $1 \le k \le n$. Call a permutation of an $n$-element set cyclic when it has
exactly one cycle, fixed points counted as cycles. Write $c(n+1, k)$ for the unsigned Stirling
number of the first kind, the number of permutations of $n + 1$ elements with exactly $k$
cycles. If $\sigma$ and $\tau$ are chosen independently and uniformly among the cyclic
permutations of an $n$-element set, then the probability that $\sigma\tau$ has exactly $k$
cycles, fixed points included, is

$$\frac{1 + (-1)^{n-k}}{(n+1)!} \, c(n+1, k).$$

Proof: We formalize the plane-permutation transposition and reflection bijections of
Chen and Reidys, arXiv:1502.07674, lines 786-1074, and their specialization to Zagier's
recurrence, lines 1167-1370. A generating-polynomial coefficient identity supplies the
matching Stirling recurrence; descending induction on the cycle count finishes.

Source: R. Cori and G. Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem [Zagier], lines 351-359,
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Hetyei/hetyei2.tex>, quoting D. Zagier.

Proves `Wanted` entry `zagier_probability_product_two_cyclic_permutations`.
-/
public theorem zagier_probability_product_two_cyclic_permutations
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) :
    ((Fintype.card {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
        Multiset.card p.1.cycleType + Fintype.card (Function.fixedPoints p.1) = 1 ∧
        Multiset.card p.2.cycleType + Fintype.card (Function.fixedPoints p.2) = 1 ∧
        Multiset.card (p.1 * p.2).cycleType +
            Fintype.card (Function.fixedPoints (p.1 * p.2)) = k}) : ℚ) /
      ((Fintype.card {σ : Equiv.Perm (Fin n) //
          Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 1}) : ℚ) ^ 2 =
      (1 + (-1 : ℚ) ^ (n - k)) / Nat.factorial (n + 1) *
        Nat.stirlingFirst (n + 1) k := by
  have hnum :
      Fintype.card {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
          Multiset.card p.1.cycleType +
              Fintype.card (Function.fixedPoints p.1) = 1 ∧
          Multiset.card p.2.cycleType +
              Fintype.card (Function.fixedPoints p.2) = 1 ∧
          Multiset.card (p.1 * p.2).cycleType +
              Fintype.card (Function.fixedPoints (p.1 * p.2)) = k} =
        Nat.card (ZagCyclePairs n k) := by
    let E :
        {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
          Multiset.card p.1.cycleType +
              Fintype.card (Function.fixedPoints p.1) = 1 ∧
          Multiset.card p.2.cycleType +
              Fintype.card (Function.fixedPoints p.2) = 1 ∧
          Multiset.card (p.1 * p.2).cycleType +
              Fintype.card (Function.fixedPoints (p.1 * p.2)) = k} ≃
          ZagCyclePairs n k :=
      Equiv.subtypeEquivProp (funext fun p => propext (by
        simp only [cycleQuotientCount_eq]))
    calc
      _ = Fintype.card (ZagCyclePairs n k) := Fintype.card_congr E
      _ = Nat.card (ZagCyclePairs n k) := Nat.card_eq_fintype_card.symm
  rw [zagCard_fullCycles n hn]
  by_cases hparity : Even (n - k)
  · rw [hnum, hparity.neg_one_pow]
    norm_num
    have hcross := zagCyclePairs_cross_mul n k hn hk hkn hparity
    have hchoose := zagTwo_mul_choose_two (n + 1)
    rw [Nat.succ_sub_one] at hchoose
    have hfactorial :
        (n + 1).factorial = (n + 1) * n * (n - 1).factorial := by
      have hnEq : n - 1 + 1 = n := by omega
      rw [Nat.factorial_succ]
      conv_lhs =>
        enter [2]
        rw [show n = (n - 1) + 1 by omega, Nat.factorial_succ]
      rw [hnEq]
      simp only [mul_assoc]
    have hchooseQ :
        (2 : ℚ) * (n + 1).choose 2 = (n + 1) * n := by
      exact_mod_cast hchoose
    have hfactorialQ :
        ((n + 1).factorial : ℚ) = (n + 1) * n * (n - 1).factorial := by
      exact_mod_cast hfactorial
    have hcrossQ :
        ((n + 1).choose 2 : ℚ) * Nat.card (ZagCyclePairs n k) =
          (n - 1).factorial * Nat.stirlingFirst (n + 1) k := by
      exact_mod_cast hcross
    rw [Nat.card_eq_fintype_card] at hcrossQ
    have hsmallFactorial : ((n - 1).factorial : ℚ) ≠ 0 := by positivity
    have hlargeFactorial : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    calc
      (Fintype.card (ZagCyclePairs n k) : ℚ) * (n + 1).factorial =
          Fintype.card (ZagCyclePairs n k) *
            (((n + 1) * n) * (n - 1).factorial) := by rw [hfactorialQ]
      _ = Fintype.card (ZagCyclePairs n k) *
            ((2 * (n + 1).choose 2) * (n - 1).factorial) := by rw [hchooseQ]
      _ = 2 * ((n + 1).choose 2 * Fintype.card (ZagCyclePairs n k)) *
            (n - 1).factorial := by ring
      _ = 2 * ((n - 1).factorial * Nat.stirlingFirst (n + 1) k) *
            (n - 1).factorial := by rw [hcrossQ]
      _ = ((n - 1).factorial : ℚ) ^ 2 * 2 *
            Nat.stirlingFirst (n + 1) k := by ring
  · have hodd : Odd (n - k) := Nat.not_even_iff_odd.mp hparity
    rw [zagCard_cyclePairs_eq_zero_of_odd n k hodd, hodd.neg_one_pow]
    norm_num

end MetaMathlibExt
