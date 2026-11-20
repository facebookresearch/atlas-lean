/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalCompactVariation










namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section



theorem fkIsingSquareRadialPatchPrimal_exists_orderedDual
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real) (p : FKIsingSquareRadialPatchPrimalNode m) :
    ∃ q : FKIsingSquareRadialPatchDualNode m,
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p ≤
        fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q := by
  by_cases hi : p.1.1.1 + 1 < m
  · let q : FKIsingSquareRadialPatchDualNode m :=
      ⟨(⟨p.1.1.1 + 1, hi⟩, p.1.2), by
        change ¬ Even ((p.1.1.1 + 1) + p.1.2.1)
        rw [Nat.not_even_iff]
        have hpmod := Nat.even_iff.mp p.2
        omega⟩
    refine ⟨q, ?_⟩
    have h := fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd
      n m hn hm (by omega) p.1.1.1 p.1.2.1 hi p.1.2.2 p.2
    change base + fkIsingSquareRadialPatchPrimitive
        n m hn hm (by omega) p.1.1.1 p.1.2.1 ≤
      base + fkIsingSquareRadialPatchPrimitive
        n m hn hm (by omega) (p.1.1.1 + 1) p.1.2.1
    linarith
  · have hi0 : 0 < p.1.1.1 := by
      have hip := p.1.1.2
      omega
    have hprev : p.1.1.1 - 1 + 1 < m := by
      have hip := p.1.1.2
      omega
    have hodd : ¬ Even (p.1.1.1 - 1 + p.1.2.1) := by
      rw [Nat.not_even_iff]
      have hpmod := Nat.even_iff.mp p.2
      omega
    let q : FKIsingSquareRadialPatchDualNode m :=
      ⟨(⟨p.1.1.1 - 1, by omega⟩, p.1.2), hodd⟩
    refine ⟨q, ?_⟩
    have h := fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd_of_odd
      n m hn hm (by omega) (p.1.1.1 - 1) p.1.2.1 hprev p.1.2.2 hodd
    have heq : p.1.1.1 - 1 + 1 = p.1.1.1 := by omega
    rw [heq] at h
    change base + fkIsingSquareRadialPatchPrimitive
        n m hn hm (by omega) p.1.1.1 p.1.2.1 ≤
      base + fkIsingSquareRadialPatchPrimitive
        n m hn hm (by omega) (p.1.1.1 - 1) p.1.2.1
    linarith



theorem fkIsingSquareRadialPatchDual_exists_orderedPrimal
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real) (q : FKIsingSquareRadialPatchDualNode m) :
    ∃ p : FKIsingSquareRadialPatchPrimalNode m,
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p ≤
        fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q := by
  by_cases hi : q.1.1.1 + 1 < m
  · have heven : Even (q.1.1.1 + 1 + q.1.2.1) := by
      rw [Nat.even_iff]
      have hqmod := Nat.not_even_iff.mp q.2
      omega
    let p : FKIsingSquareRadialPatchPrimalNode m :=
      ⟨(⟨q.1.1.1 + 1, hi⟩, q.1.2), heven⟩
    refine ⟨p, ?_⟩
    have h := fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd_of_odd
      n m hn hm (by omega) q.1.1.1 q.1.2.1 hi q.1.2.2 q.2
    change base + fkIsingSquareRadialPatchPrimitive
        n m hn hm (by omega) (q.1.1.1 + 1) q.1.2.1 ≤
      base + fkIsingSquareRadialPatchPrimitive
        n m hn hm (by omega) q.1.1.1 q.1.2.1
    linarith
  · have hi0 : 0 < q.1.1.1 := by
      have hiq := q.1.1.2
      omega
    have hprev : q.1.1.1 - 1 + 1 < m := by
      have hiq := q.1.1.2
      omega
    have heven : Even (q.1.1.1 - 1 + q.1.2.1) := by
      rw [Nat.even_iff]
      have hqmod := Nat.not_even_iff.mp q.2
      omega
    let p : FKIsingSquareRadialPatchPrimalNode m :=
      ⟨(⟨q.1.1.1 - 1, by omega⟩, q.1.2), heven⟩
    refine ⟨p, ?_⟩
    have h := fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd
      n m hn hm (by omega) (q.1.1.1 - 1) q.1.2.1
        hprev q.1.2.2 heven
    have heq : q.1.1.1 - 1 + 1 = q.1.1.1 := by omega
    rw [heq] at h
    change base + fkIsingSquareRadialPatchPrimitive
        n m hn hm (by omega) (q.1.1.1 - 1) q.1.2.1 ≤
      base + fkIsingSquareRadialPatchPrimitive
        n m hn hm (by omega) q.1.1.1 q.1.2.1
    linarith




theorem fkIsingSquareRadialPatch_unitRange_of_primalLower_dualUpper
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real)
    (hprimalLower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
    (hdualUpper : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
    (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue
        n m hn hm (by omega) base p ∧
      fkIsingSquareRadialPatchPrimalValue
        n m hn hm (by omega) base p ≤ 1) ∧
      (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base q ∧
        fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base q ≤ 1) := by
  constructor
  · intro p
    obtain ⟨q, hpq⟩ := fkIsingSquareRadialPatchPrimal_exists_orderedDual
      n m hn hm hm2 base p
    exact ⟨hprimalLower p, hpq.trans (hdualUpper q)⟩
  · intro q
    obtain ⟨p, hpq⟩ := fkIsingSquareRadialPatchDual_exists_orderedPrimal
      n m hn hm hm2 base q
    exact ⟨(hprimalLower p).trans hpq, hdualUpper q⟩

theorem fkIsingSquareRadialPatchPrimal_deepVariation_sq_le_of_unitRange
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (r : Nat) (hr : 0 < r) (base : Real)
    (hlower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p)
    (hupper : ∀ p,
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ≤ 1) :
    (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤
      16 * (#(fkIsingSquareRadialPatchPrimalDeepDarts
        n m hm hmpos r) : Real) * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  have h := isingFiniteGraph_compactVariation_sq_le_of_superharmonicOn
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r)
    (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base)
    0 1 1 (4 * (m : Real) ^ 2 / (r : Real) ^ 2)
    (fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r)
    (fkIsingSquareRadialPatchPrimalValue_superharmonicOn
      n m hn hm hmpos base)
    hlower hupper
    (fkIsingSquareRadialPatchPrimalTentCutoff_support n m hm hmpos r)
    (by norm_num)
    (fkIsingSquareRadialPatchPrimalTentCutoff_one n m hm hmpos r hr)
    (fkIsingSquareRadialPatchPrimalTentCutoff_energy_le
      n m hm hmpos r hr)
  norm_num at h
  ring_nf at h ⊢
  exact h

theorem fkIsingSquareRadialPatchDual_deepVariation_sq_le_of_unitRange
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base : Real)
    (hlower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p)
    (hupper : ∀ p,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p ≤ 1) :
    (∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤
      16 * (#(fkIsingSquareRadialPatchDualDeepDarts m hm2 r) : Real) *
        (m : Real) ^ 2 / (r : Real) ^ 2 := by
  have hmpos : 0 < m := by omega
  have h := isingFiniteGraph_compactVariation_sq_le_of_subharmonicOn
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualTentCutoff m hm2 r)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base)
    0 1 1 (4 * (m : Real) ^ 2 / (r : Real) ^ 2)
    (fkIsingSquareRadialPatchDualDeepDarts m hm2 r)
    (fkIsingSquareRadialPatchDualValue_subharmonicOn
      n m hn hm hmpos base)
    hlower hupper
    (fkIsingSquareRadialPatchDualTentCutoff_support m hm2 r)
    (by norm_num)
    (fkIsingSquareRadialPatchDualTentCutoff_one m hm2 r hr)
    (fkIsingSquareRadialPatchDualTentCutoff_energy_le m hm2 r hr)
  norm_num at h
  ring_nf at h ⊢
  exact h



theorem fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_unitRange
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (r : Nat) (hr : 0 < r) (base : Real)
    (hlower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p)
    (hupper : ∀ p,
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ≤ 1) :
    ((1 / (m : Real)) *
      ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤
      64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  let S := fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r
  let V : Real := ∑ d ∈ S,
    |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd -
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|
  have hraw : V ^ 2 ≤
      16 * (#S : Real) * (m : Real) ^ 2 / (r : Real) ^ 2 :=
    fkIsingSquareRadialPatchPrimal_deepVariation_sq_le_of_unitRange
      n m hn hm hmpos r hr base hlower hupper
  have hcardNat : S.card ≤ 4 * m ^ 2 :=
    fkIsingSquareRadialPatchPrimalDeepDarts_card_le n m hm hmpos r
  have hcard : (#S : Real) ≤ 4 * (m : Real) ^ 2 := by
    exact_mod_cast hcardNat
  have hraw' : V ^ 2 ≤ 64 * (m : Real) ^ 4 / (r : Real) ^ 2 := by
    calc
      _ ≤ 16 * (#S : Real) * (m : Real) ^ 2 / (r : Real) ^ 2 := hraw
      _ ≤ 16 * (4 * (m : Real) ^ 2) * (m : Real) ^ 2 /
          (r : Real) ^ 2 := by gcongr
      _ = 64 * (m : Real) ^ 4 / (r : Real) ^ 2 := by ring
  change ((1 / (m : Real)) * V) ^ 2 ≤ _
  calc
    _ = (1 / (m : Real) ^ 2) * V ^ 2 := by ring
    _ ≤ (1 / (m : Real) ^ 2) *
        (64 * (m : Real) ^ 4 / (r : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hraw' (by positivity)
    _ = 64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
      field_simp

theorem fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_unitRange
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base : Real)
    (hlower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p)
    (hupper : ∀ p,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p ≤ 1) :
    ((1 / (m : Real)) *
      ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤
      64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  let S := fkIsingSquareRadialPatchDualDeepDarts m hm2 r
  let V : Real := ∑ d ∈ S,
    |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|
  have hraw : V ^ 2 ≤
      16 * (#S : Real) * (m : Real) ^ 2 / (r : Real) ^ 2 :=
    fkIsingSquareRadialPatchDual_deepVariation_sq_le_of_unitRange
      n m hn hm hm2 r hr base hlower hupper
  have hcardNat : S.card ≤ 4 * m ^ 2 :=
    fkIsingSquareRadialPatchDualDeepDarts_card_le m hm2 r
  have hcard : (#S : Real) ≤ 4 * (m : Real) ^ 2 := by
    exact_mod_cast hcardNat
  have hraw' : V ^ 2 ≤ 64 * (m : Real) ^ 4 / (r : Real) ^ 2 := by
    calc
      _ ≤ 16 * (#S : Real) * (m : Real) ^ 2 / (r : Real) ^ 2 := hraw
      _ ≤ 16 * (4 * (m : Real) ^ 2) * (m : Real) ^ 2 /
          (r : Real) ^ 2 := by gcongr
      _ = 64 * (m : Real) ^ 4 / (r : Real) ^ 2 := by ring
  change ((1 / (m : Real)) * V) ^ 2 ≤ _
  calc
    _ = (1 / (m : Real) ^ 2) * V ^ 2 := by ring
    _ ≤ (1 / (m : Real) ^ 2) *
        (64 * (m : Real) ^ 4 / (r : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hraw' (by positivity)
    _ = 64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
      field_simp

theorem fkIsingSquareRadialPatchPrimal_physicalDeepVariation_fixedFraction
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (r : Nat) (hr : 0 < r) (base K : Real) (hK : 0 ≤ K)
    (hmr : (m : Real) ≤ K * (r : Real))
    (hlower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p)
    (hupper : ∀ p,
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ≤ 1) :
    ((1 / (m : Real)) *
      ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤
      64 * K ^ 2 := by
  have hmain :=
    fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_unitRange
      n m hn hm hmpos r hr base hlower hupper
  refine hmain.trans ?_
  have hsquare : (m : Real) ^ 2 ≤ (K * (r : Real)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg hK (by positivity))).2 hmr
  rw [div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast hr : (0 : Real) < r))]
  nlinarith

theorem fkIsingSquareRadialPatchDual_physicalDeepVariation_fixedFraction
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base K : Real) (hK : 0 ≤ K)
    (hmr : (m : Real) ≤ K * (r : Real))
    (hlower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p)
    (hupper : ∀ p,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p ≤ 1) :
    ((1 / (m : Real)) *
      ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤
      64 * K ^ 2 := by
  have hmain :=
    fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_unitRange
      n m hn hm hm2 r hr base hlower hupper
  refine hmain.trans ?_
  have hsquare : (m : Real) ^ 2 ≤ (K * (r : Real)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg hK (by positivity))).2 hmr
  rw [div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast hr : (0 : Real) < r))]
  nlinarith

end

end StatMech.Universality
