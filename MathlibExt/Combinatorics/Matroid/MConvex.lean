/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.Finsupp.Order

/-!
# M-convex sets and matroids

A set `J ⊆ ℕ^ι` is *M-convex* (Murota, *Discrete Convex Analysis*, SIAM 2003, Chapter 4) if for
all `α, β ∈ J` and every index `i` with `α i > β i` there is an index `j` with `α j < β j` and
`α - e_i + e_j ∈ J`. Brändén and Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020),
Theorem 3.10, characterise M-convex sets as the supports of Lorentzian polynomials, and observe
(Theorem 3.10, (7) ⇔ (8)) that an M-convex set of zero-one vectors is exactly the set of
indicator vectors of the bases of a matroid. This file proves that last equivalence for
Mathlib's `Matroid`:

* `isMConvex_baseVectors`: the indicator vectors of the bases of a matroid form an M-convex set;
* `exists_matroid_baseVectors_eq`: conversely, a nonempty M-convex set of zero-one vectors on a
  finite type is the set of base indicator vectors of a matroid whose ground set is everything;
* `isMConvex_iff_exists_matroid`: the two together, for zero-one sets on a finite type.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Matroid.MConvex

open Finsupp

variable {ι : Type*}

/-- **M-convex set** (Murota, *Discrete Convex Analysis*, SIAM 2003, Section 4.1; Brändén and
Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), Section 1). A set `J` of vectors in
`ℕ^ι` is M-convex if for all `α, β ∈ J` and every index `i` with `α i > β i` there is an index
`j` with `α j < β j` and `α - e_i + e_j ∈ J`, where `e_i` is the `i`-th unit vector. -/
def IsMConvex (J : Set (ι →₀ ℕ)) : Prop :=
  ∀ α ∈ J, ∀ β ∈ J, ∀ i, α i > β i → ∃ j, α j < β j ∧ α - single i 1 + single j 1 ∈ J

/-- **Indicator vector of a finite set.** The zero-one vector `∑_{i ∈ B} e_i` in `ℕ^ι` of a
finite set `B ⊆ ι` (Brändén and Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020),
Section 2.1, where a subset `S` is identified with the zero-one vector `∑_{i ∈ S} e_i`). -/
noncomputable def indicatorVec (B : Finset ι) : ι →₀ ℕ :=
  Finsupp.indicator B (fun _ _ => 1)

theorem indicatorVec_apply [DecidableEq ι] (B : Finset ι) (i : ι) :
    indicatorVec B i = if i ∈ B then 1 else 0 := by
  classical
  unfold indicatorVec
  rw [Finsupp.indicator_apply]
  split_ifs <;> rfl

theorem indicatorVec_injective : Function.Injective (indicatorVec (ι := ι)) := by
  classical
  intro B C h
  ext i
  have := DFunLike.congr_fun h i
  simp only [indicatorVec_apply] at this
  by_cases hB : i ∈ B <;> by_cases hC : i ∈ C <;> simp_all

/-- **Base vectors of a matroid.** The set of indicator vectors `∑_{i ∈ B} e_i` of the finite
bases `B` of a matroid `M` on `ι`; for a matroid on `[n]` this is the support of its basis
generating polynomial (Brändén and Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020),
Section 3.2 and Theorem 3.10 (8)). -/
def baseVectors (M : _root_.Matroid ι) : Set (ι →₀ ℕ) :=
  {α | ∃ B : Finset ι, M.IsBase (B : Set ι) ∧ α = indicatorVec B}

/-- Removing `i ∈ B` and adding `j ∉ B` to the indicator vector of `B` gives the indicator vector
of `insert j (B.erase i)`. -/
theorem indicatorVec_exchange [DecidableEq ι] {B : Finset ι} {i j : ι} (hi : i ∈ B)
    (hj : j ∉ B) :
    indicatorVec B - single i 1 + single j 1 = indicatorVec (insert j (B.erase i)) := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  have hji : ¬j = i := fun h => hij h.symm
  ext k
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, indicatorVec_apply,
    Finset.mem_insert, Finset.mem_erase, single_apply]
  by_cases hki : i = k
  · subst hki
    simp [hi, hij, hji]
  · by_cases hkj : j = k
    · subst hkj
      simp [hj, hki]
    · have hk1 : k ≠ i := fun h => hki h.symm
      have hk2 : k ≠ j := fun h => hkj h.symm
      simp [hki, hkj, hk1, hk2]

/-- **Base vectors of a matroid are M-convex** (Brändén and Huh, *Lorentzian polynomials*,
Ann. of Math. 192 (2020), Theorem 3.10, (8) ⇒ (7)). For every matroid `M` on `ι`, the set of
indicator vectors of its finite bases is M-convex. The proof is the base exchange axiom. -/
theorem isMConvex_baseVectors (M : _root_.Matroid ι) : IsMConvex (baseVectors M) := by
  classical
  unfold IsMConvex
  rintro α ⟨B₁, hB₁, rfl⟩ β ⟨B₂, hB₂, rfl⟩ i hi
  simp only [indicatorVec_apply] at hi
  have hiB₁ : i ∈ B₁ := by by_contra h; simp [h] at hi
  have hiB₂ : i ∉ B₂ := by intro h; simp [h, hiB₁] at hi
  obtain ⟨j, ⟨hjB₂, hjB₁⟩, hbase⟩ :=
    hB₁.exchange hB₂ (e := i) ⟨by simpa using hiB₁, by simpa using hiB₂⟩
  have hjB₂' : j ∈ B₂ := by simpa using hjB₂
  have hjB₁' : j ∉ B₁ := by simpa using hjB₁
  refine ⟨j, by simp [indicatorVec_apply, hjB₁', hjB₂'], insert j (B₁.erase i), ?_, ?_⟩
  · simpa [Finset.coe_insert, Finset.coe_erase] using hbase
  · exact indicatorVec_exchange hiB₁ hjB₁'

/-- A zero-one vector is the indicator vector of its support. -/
theorem eq_indicatorVec_support {α : ι →₀ ℕ} (h : ∀ i, α i ≤ 1) :
    α = indicatorVec α.support := by
  classical
  ext i
  have := h i
  by_cases hi : α i = 0
  · simp [indicatorVec_apply, hi]
  · simp only [indicatorVec_apply, Finsupp.mem_support_iff, ne_eq, hi, not_false_eq_true,
      ite_true]
    omega

/-- **Zero-one M-convex sets are matroid base sets** (Brändén and Huh, *Lorentzian
polynomials*, Ann. of Math. 192 (2020), Theorem 3.10, (7) ⇒ (8)). If `ι` is finite and `J` is a
nonempty M-convex set of zero-one vectors in `ℕ^ι`, then `J` is the set of base indicator
vectors of a matroid on `ι` whose ground set is all of `ι`. -/
theorem exists_matroid_baseVectors_eq [Finite ι] {J : Set (ι →₀ ℕ)} (hne : J.Nonempty)
    (h01 : ∀ α ∈ J, ∀ i, α i ≤ 1) (hJ : IsMConvex J) :
    ∃ M : _root_.Matroid ι, M.E = Set.univ ∧ baseVectors M = J := by
  classical
  let P : Set ι → Prop := fun X => ∃ B : Finset ι, (B : Set ι) = X ∧ indicatorVec B ∈ J
  have hP : ∀ B : Finset ι, P B ↔ indicatorVec B ∈ J := by
    intro B
    constructor
    · rintro ⟨C, hC, hCJ⟩
      rwa [Finset.coe_inj.mp hC] at hCJ
    · exact fun h => ⟨B, rfl, h⟩
  have hex : ∃ B, P B := by
    obtain ⟨α, hα⟩ := hne
    exact ⟨α.support, α.support, rfl, eq_indicatorVec_support (h01 α hα) ▸ hα⟩
  have hexch : _root_.Matroid.ExchangeProperty P := by
    rintro X Y ⟨B₁, rfl, hB₁⟩ ⟨B₂, rfl, hB₂⟩ a ⟨haX, haY⟩
    have ha₁ : a ∈ B₁ := by simpa using haX
    have ha₂ : a ∉ B₂ := by simpa using haY
    obtain ⟨j, hj, hjJ⟩ := (show IsMConvex J from hJ) _ hB₁ _ hB₂ a
      (by simp [indicatorVec_apply, ha₁, ha₂])
    simp only [indicatorVec_apply] at hj
    have hj₁ : j ∉ B₁ := by intro h; simp [h] at hj; split_ifs at hj <;> omega
    have hj₂ : j ∈ B₂ := by by_contra h; simp [h] at hj
    refine ⟨j, ⟨by simpa using hj₂, by simpa using hj₁⟩, insert j (B₁.erase a), ?_, ?_⟩
    · simp [Finset.coe_insert, Finset.coe_erase]
    · rwa [← indicatorVec_exchange ha₁ hj₁]
  refine ⟨_root_.Matroid.ofIsBaseOfFinite Set.finite_univ P hex hexch
    (fun _ _ => Set.subset_univ _), rfl, ?_⟩
  ext α
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact (hP B).mp hB
  · intro hα
    exact ⟨α.support, (hP _).mpr (eq_indicatorVec_support (h01 α hα) ▸ hα),
      eq_indicatorVec_support (h01 α hα)⟩

/-- **Matroids are the zero-one M-convex sets** (Brändén and Huh, *Lorentzian polynomials*,
Ann. of Math. 192 (2020), Theorem 3.10, (7) ⇔ (8)). On a finite type `ι`, a nonempty set `J` of
zero-one vectors in `ℕ^ι` is M-convex if and only if it is the set of base indicator vectors of
a matroid on `ι` whose ground set is all of `ι`. -/
theorem isMConvex_iff_exists_matroid [Finite ι] {J : Set (ι →₀ ℕ)} (hne : J.Nonempty)
    (h01 : ∀ α ∈ J, ∀ i, α i ≤ 1) :
    IsMConvex J ↔ ∃ M : _root_.Matroid ι, M.E = Set.univ ∧ baseVectors M = J := by
  constructor
  · exact exists_matroid_baseVectors_eq hne h01
  · rintro ⟨M, -, rfl⟩
    exact isMConvex_baseVectors M

end MathlibExt.Combinatorics.Matroid.MConvex
