/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Card
public import MathlibExt.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.PowerSeries.Basic

namespace MetaMathlibExt

@[expose]
public section

/-- Excedance count of a permutation of `Fin n`: the number of `i` with `σ i > i`.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 130-132; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def excedanceCount (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => i < σ i)).card

/-- An `r`-minus-cycle permutation of `Fin n`: every cycle length is at most `r`.

Fixed one-cycles are omitted by `Equiv.Perm.cycleType`, so they are handled
explicitly: a fixed point requires `1 ≤ r`, and every nontrivial entry of
`σ.cycleType` requires `≤ r`. The point condition is vacuous for `Fin 0`.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 106-108 and Lines 257-259;
URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def IsRMinusAssociatedCyclePerm (r n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, σ i = i → 1 ≤ r) ∧ ∀ m ∈ σ.cycleType.toFinset, m ≤ r

/-- An `r`-associated-cycle permutation of `Fin n`: every cycle length exceeds `r`.

Fixed one-cycles are omitted by `Equiv.Perm.cycleType`, so they are handled
explicitly: a fixed point requires `r < 1`, and every nontrivial entry of
`σ.cycleType` requires `r <` its length. The point condition is vacuous for
`Fin 0`, including when `r = 0`.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 106-108 and Lines 653-657;
URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def IsRAssociatedCyclePerm (r n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, σ i = i → r < 1) ∧ ∀ m ∈ σ.cycleType.toFinset, r < m

instance (r n : ℕ) : DecidablePred (IsRMinusAssociatedCyclePerm r n) :=
  fun σ => by unfold IsRMinusAssociatedCyclePerm; infer_instance

instance (r n : ℕ) : DecidablePred (IsRAssociatedCyclePerm r n) :=
  fun σ => by unfold IsRAssociatedCyclePerm; infer_instance

/-- The `r`-minus-associated Stirling Eulerian number `A^(r-minus)_(n,m)`:
the cardinality of permutations of `n` objects with all cycle lengths at most
`r` and exactly `m` excedances.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 257-259; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def rMinusAssociatedStirlingEulerian (r n m : ℕ) : ℕ :=
  ((Finset.univ.filter (IsRMinusAssociatedCyclePerm r n)).filter
    (fun σ => excedanceCount n σ = m)).card

/-- The `r`-associated Stirling Eulerian number `A^r_(n,m)`: the cardinality of
permutations of `n` objects with all cycle lengths greater than `r` and exactly
`m` excedances.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 653-657; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def rAssociatedStirlingEulerian (r n m : ℕ) : ℕ :=
  ((Finset.univ.filter (IsRAssociatedCyclePerm r n)).filter
    (fun σ => excedanceCount n σ = m)).card

/-- The circular Eulerian number `C_{n,m}`: the number of circular permutations of
`n ≥ 1` objects (a single cycle through all points, so the identity of one point is
circular) with exactly `m` excedances. A permutation of `Fin n` is circular when
`n ≥ 1` and all points lie in one cycle (`Equiv.Perm.SameCycle`); for `n ≥ 2` this is
Mathlib's `n`-cycle `σ.IsCycle ∧ σ.support = Finset.univ`
(`sameCycle_all_iff_isCycle_support_eq_univ`). The empty permutation of `Fin 0` has no
cycle, so `C_{0,m} = 0`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorems 5 and 6 (excedance distribution `C_n(x)` over
circular permutations, `C_{1,0} = 1`). -/
def circularEulerian (n m : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (0 < n ∧ ∀ i j : Fin n, σ.SameCycle i j) ∧
      excedanceCount n σ = m)).card

/-- Characteristic values `C_{0,0} = 0`, `C_{1,0} = 1` and `C_{3,1} = C_{3,2} = 1`:
of the two 3-cycles, `1 ↦ 3 ↦ 2 ↦ 1` has one excedance and `1 ↦ 2 ↦ 3 ↦ 1` has two.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 5. -/
theorem circularEulerian_small :
    circularEulerian 0 0 = 0 ∧ circularEulerian 1 0 = 1 ∧ circularEulerian 3 1 = 1 ∧
      circularEulerian 3 2 = 1 := by
  decide

/-- For `n ≥ 2`, a permutation of `Fin n` has a single cycle through all points exactly
when it is an `n`-cycle in Mathlib's sense, `σ.IsCycle ∧ σ.support = Finset.univ`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorems 5 and 6 (circular permutations). -/
theorem sameCycle_all_iff_isCycle_support_eq_univ {n : ℕ} (hn : 2 ≤ n)
    (σ : Equiv.Perm (Fin n)) :
    (∀ i j : Fin n, σ.SameCycle i j) ↔ σ.IsCycle ∧ σ.support = Finset.univ := by
  constructor
  · intro hall
    obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra h
      push Not at h
      have h1 : σ = 1 := Equiv.ext h
      have h01 := hall ⟨0, by omega⟩ ⟨1, by omega⟩
      rw [h1, Equiv.Perm.sameCycle_one] at h01
      exact absurd (congrArg Fin.val h01) (by simp)
    refine ⟨⟨x, hx, fun y _ => hall x y⟩, ?_⟩
    ext y
    simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
    exact fun hy => hx (((hall x y).apply_eq_self_iff).mpr hy)
  · rintro ⟨hc, hs⟩ i j
    have hmov : ∀ z, σ z ≠ z := fun z => Equiv.Perm.mem_support.mp (hs ▸ Finset.mem_univ z)
    exact hc.sameCycle (hmov i) (hmov j)

/-- An `r`-cycle permutation of `Fin n` (the paper's `(r)`-cycle permutations, the set
`S_n^r` of Corollary 25): every cycle, fixed points included as one-cycles, has length
exactly `r`, i.e. every `σ`-orbit has `r` elements. The condition is vacuous for `Fin 0`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorems 20-23 and Corollaries 24-26. -/
def IsRCyclePerm (r n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, (Finset.univ.filter (σ.SameCycle i)).card = r

instance (r n : ℕ) : DecidablePred (IsRCyclePerm r n) :=
  fun σ => by unfold IsRCyclePerm; infer_instance

/-- Characterization of `r`-cycle permutations through the cycle type: `σ` is an `r`-cycle
permutation iff every fixed point forces `r = 1` and every nontrivial cycle length in
`σ.cycleType` equals `r`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorems 20-23 (cycle lengths of `(r)`-cycle permutations). -/
theorem isRCyclePerm_iff {r n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsRCyclePerm r n σ ↔ (∀ i, σ i = i → r = 1) ∧ ∀ k ∈ σ.cycleType, k = r := by
  have key : ∀ i, σ i ≠ i →
      Finset.univ.filter (σ.SameCycle i) = (σ.cycleOf i).support := by
    intro i hi
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨fun h => ⟨h, Equiv.Perm.mem_support.mpr hi⟩, fun h => h.1⟩
  have fixed : ∀ i, σ i = i → Finset.univ.filter (σ.SameCycle i) = {i} := by
    intro i hi
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact (h.eq_of_left hi).symm
    · rintro rfl
      exact Equiv.Perm.SameCycle.refl σ j
  constructor
  · intro h
    refine ⟨fun i hi => by rw [← h i, fixed i hi, Finset.card_singleton], fun k hk => ?_⟩
    rw [Equiv.Perm.cycleType_def, Multiset.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    have hc' : c ∈ σ.cycleFactorsFinset := Finset.mem_val.mp hc
    obtain ⟨a, ha⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc').1.nonempty_support
    have hca : c = σ.cycleOf a := Equiv.Perm.cycle_is_cycleOf ha hc'
    have hσa : σ a ≠ a :=
      Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le hc' ha)
    simp only [Function.comp_apply]
    rw [hca, ← key a hσa, h a]
  · rintro ⟨h1, h2⟩ i
    by_cases hi : σ i = i
    · rw [fixed i hi, Finset.card_singleton, h1 i hi]
    · rw [key i hi]
      apply h2
      rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
      exact ⟨σ.cycleOf i, Finset.mem_val.mpr
        (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hi)), rfl⟩

/-- The number `A^{(r)}_{n,m}` of `r`-cycle permutations of `n` objects (all cycle
lengths equal to `r`) with exactly `m` excedances.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorems 20 and 21. -/
def rCycleStirlingEulerian (r n m : ℕ) : ℕ :=
  ((Finset.univ.filter (IsRCyclePerm r n)).filter (fun σ => excedanceCount n σ = m)).card

/-- Characteristic values: `A^{(r)}_{0,0} = 1` (the empty permutation),
`A^{(2)}_{2,1} = 1` (the transposition), `A^{(2)}_{3,1} = 0`, and
`A^{(3)}_{3,1} = A^{(3)}_{3,2} = 1` (the two 3-cycles).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 20 and Corollary 25. -/
theorem rCycleStirlingEulerian_small :
    rCycleStirlingEulerian 2 0 0 = 1 ∧ rCycleStirlingEulerian 2 2 1 = 1 ∧
      rCycleStirlingEulerian 2 3 1 = 0 ∧ rCycleStirlingEulerian 3 3 1 = 1 ∧
      rCycleStirlingEulerian 3 3 2 = 1 := by
  decide

/-- The exponential generating function of the excedance and cycle distribution over a
family `P` of permutations, in the paper's convention
`∑_{n ≥ 0} ∑_{σ ∈ P_n} x^{e(σ)} q^{c(σ)} u^n / n!`, with `e` the excedance count and `c`
the number of cycles (fixed points included; the existing `cycleQuotientCount`), over a
commutative `ℚ`-algebra `R` (so `x` and `q` can be indeterminates). With `q = 1` it is the paper's `P(x, u)`, with general `q` its
`q`-analogue `P(q, x, u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 6 and Corollary 43 (the series `C(x,u)` and
`A_k(x,u)`), Corollary 24 (the weight `x^{e(π)} q^{c(π)}`). -/
noncomputable def permExcedanceCycleEGF {R : Type*} [CommRing R] [Algebra ℚ R]
    (P : ∀ n, Equiv.Perm (Fin n) → Prop) [∀ n, DecidablePred (P n)] (x q : R) :
    PowerSeries R :=
  PowerSeries.mk fun n => ((n.factorial : ℚ)⁻¹) •
    ∑ σ ∈ Finset.univ.filter (P n), x ^ excedanceCount n σ * q ^ cycleQuotientCount σ

/-- The coefficient of `u^n` in `permExcedanceCycleEGF P x q` is
`(1/n!) ∑_{σ ∈ P_n} x^{e(σ)} q^{c(σ)}`; for the family of all permutations the constant
coefficient is `1` (the empty permutation).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 6. -/
theorem coeff_permExcedanceCycleEGF {R : Type*} [CommRing R] [Algebra ℚ R]
    (P : ∀ n, Equiv.Perm (Fin n) → Prop) [∀ n, DecidablePred (P n)] (x q : R) (n : ℕ) :
    PowerSeries.coeff n (permExcedanceCycleEGF P x q) = ((n.factorial : ℚ)⁻¹) •
      ∑ σ ∈ Finset.univ.filter (P n), x ^ excedanceCount n σ * q ^ cycleQuotientCount σ := by
  simp [permExcedanceCycleEGF]

/-- The constant coefficient of the series of all permutations is `1`: the only
permutation of `Fin 0` has no excedance and no cycle.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 6. -/
theorem coeff_zero_permExcedanceCycleEGF_true {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) :
    PowerSeries.coeff 0 (permExcedanceCycleEGF (fun _ _ => True) x q) = 1 := by
  rw [coeff_permExcedanceCycleEGF]
  have he : excedanceCount 0 (1 : Equiv.Perm (Fin 0)) = 0 := by decide
  have hc : cycleQuotientCount (1 : Equiv.Perm (Fin 0)) = 0 := by
    rw [cycleQuotientCount_eq]; simp
  simp [Finset.univ_unique, he, hc]

end
end MetaMathlibExt
