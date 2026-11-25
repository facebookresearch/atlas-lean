/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.QpGraph
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Sym.Card

/-!
# Linear identifiability of edge lengths for fixed topology and weights

For fixed lineage weights, the predicted f-statistic vector on a family of statistics is
`B ℓ` for the design matrix `B`. The edge lengths are therefore determined by the
statistics iff `B` has full column rank. With more edges than `n choose 2` (the dimension
of the f-statistic space) no family of f-statistics determines them, and positive lengths
then admit a different positive length vector with the same f-statistics.

## Main results

* `DriftModel.ofLen`: any weights and nonnegative lengths are realized by a drift model.
* `QpGraph.len_identifiable_iff_rank_eq_card`: identifiability iff full column rank.
* `QpGraph.not_injective_of_choose_two_lt`: more edges than `n choose 2` is never
  identifiable.
* `QpGraph.exists_driftModel_pos_len_ne`: the positive-orthant kernel construction.

## References

* N. Patterson et al., "Ancient admixture in human history", *Genetics* 192 (2012),
  1065–1093 (admixture graph fitting; the f-statistics span a space of dimension
  `n choose 2`).
-/

@[expose] public section

open MeasureTheory Matrix MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.QpGraph

namespace MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel

/-- Every weight matrix `w` and every nonnegative length vector `len` are realized by a drift
model: the counting measure on the edge set (not normalized), with root frequency `1 / 2` and
increment `√(len e)` on the atom `e` (so the increments have disjoint supports, hence are
orthogonal in L²: the integral of the product of two of them is `0`). -/
noncomputable def ofLen {P E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E]
    [DiscreteMeasurableSpace E] (w : P → E → ℝ) (len : E → ℝ) (hlen : ∀ e, 0 ≤ len e) :
    DriftModel (Measure.count : Measure E) E P where
  root _ := 1 / 2
  incr e ω := if ω = e then √(len e) else 0
  len := len
  weight := w
  memLp_root := memLp_const _
  memLp_incr _ := MemLp.of_discrete
  inner_incr e f hef := by
    rw [integral_count]
    refine Finset.sum_eq_zero fun ω _ => ?_
    by_cases h : ω = e
    · subst h; simp [hef]
    · simp [h]
  sq_incr e := by
    rw [integral_count, Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
    simp [Real.sq_sqrt (hlen e)]

end MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel

namespace MathlibExt.Biology.PopulationGenetics.QpGraph

variable {ι E P : Type*} [Fintype E]

/-- A real matrix has injective `mulVec` iff it has full column rank. -/
private theorem injective_mulVec_iff_rank_eq_card {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) : Function.Injective A.mulVec ↔ A.rank = Fintype.card n := by
  rw [Matrix.mulVec_injective_iff, Matrix.rank_eq_finrank_span_cols,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank]
  exact eq_comm

/-- Identifiability, direction `⇐`: if the design matrix has full column rank (injective
`mulVec`), two drift models with the same weights and the same basis statistics have the same
edge lengths. -/
theorem len_eq_of_f4_eq {Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'}
    {μ : Measure Ω} {μ' : Measure Ω'} {w : P → E → ℝ} {A B C D : ι → P}
    (hB : Function.Injective (designMatrix w A B C D).mulVec) (M : DriftModel μ E P)
    (M' : DriftModel μ' E P) (hw : M.weight = w) (hw' : M'.weight = w)
    (hf : ∀ i, f4 μ M.freq (A i) (B i) (C i) (D i) = f4 μ' M'.freq (A i) (B i) (C i) (D i)) :
    M.len = M'.len := by
  apply hB
  have h1 := f4_eq_designMatrix_mulVec M A B C D
  have h2 := f4_eq_designMatrix_mulVec M' A B C D
  rw [hw] at h1
  rw [hw'] at h2
  rw [← h1, ← h2]
  funext i
  exact hf i

/-- Identifiability, direction `⇒`: if the design matrix does not have full column rank, there
are two drift models with the given weights, different edge lengths, and the same basis
statistics. -/
theorem exists_len_ne_of_not_injective [MeasurableSpace E]
    [DiscreteMeasurableSpace E] {w : P → E → ℝ} {A B C D : ι → P}
    (hB : ¬ Function.Injective (designMatrix w A B C D).mulVec) :
    ∃ M M' : DriftModel (Measure.count : Measure E) E P, M.weight = w ∧ M'.weight = w ∧
      M.len ≠ M'.len ∧
      ∀ i, f4 Measure.count M.freq (A i) (B i) (C i) (D i) =
        f4 Measure.count M'.freq (A i) (B i) (C i) (D i) := by
  classical
  obtain ⟨x, y, hxy, hne⟩ : ∃ x y, (designMatrix w A B C D) *ᵥ x =
      (designMatrix w A B C D) *ᵥ y ∧ x ≠ y := by
    simp only [Function.Injective, not_forall] at hB
    obtain ⟨x, y, h, hne⟩ := hB
    exact ⟨x, y, h, hne⟩
  set v := x - y
  have hv : (designMatrix w A B C D) *ᵥ v = 0 := by simp [v, mulVec_sub, hxy]
  refine ⟨DriftModel.ofLen w (fun e => |v e|) (fun e => abs_nonneg _),
    DriftModel.ofLen w (fun e => |v e| - v e) (fun e => sub_nonneg.mpr (le_abs_self _)),
    rfl, rfl, fun h => hne ?_, fun i => ?_⟩
  · have h' := congrFun h
    funext e
    have := h' e
    simp only [DriftModel.ofLen] at this
    have : v e = 0 := by linarith
    simpa [v, sub_eq_zero] using this
  · have h1 := congrFun (f4_eq_designMatrix_mulVec
      (DriftModel.ofLen w (fun e => |v e|) (fun e => abs_nonneg _)) A B C D) i
    have h2 := congrFun (f4_eq_designMatrix_mulVec
      (DriftModel.ofLen w (fun e => |v e| - v e) (fun e => sub_nonneg.mpr (le_abs_self _)))
      A B C D) i
    have h3 : (designMatrix w A B C D *ᵥ fun e => |v e|) =
        designMatrix w A B C D *ᵥ fun e => |v e| - v e := by
      have : (fun e => |v e| - v e) = (fun e => |v e|) - v := rfl
      rw [this, mulVec_sub, hv, sub_zero]
    exact h1.trans ((congrFun h3 i).trans h2.symm)

/-- Identifiability criterion: the edge lengths are determined by the basis statistics (among
drift models on the counting measure of the edge set with the given weights) iff the design
matrix has full column rank. -/
theorem len_identifiable_iff_rank_eq_card [MeasurableSpace E]
    [DiscreteMeasurableSpace E] (w : P → E → ℝ) (A B C D : ι → P) :
    (∀ M M' : DriftModel (Measure.count : Measure E) E P, M.weight = w → M'.weight = w →
      (∀ i, f4 Measure.count M.freq (A i) (B i) (C i) (D i) =
        f4 Measure.count M'.freq (A i) (B i) (C i) (D i)) → M.len = M'.len) ↔
      (designMatrix w A B C D).rank = Fintype.card E := by
  classical
  rw [← injective_mulVec_iff_rank_eq_card]
  refine ⟨fun h => ?_, fun hB M M' hw hw' hf => len_eq_of_f4_eq hB M M' hw hw' hf⟩
  by_contra hB
  obtain ⟨M, M', hw, hw', hne, hf⟩ := exists_len_ne_of_not_injective hB
  exact hne (h M M' hw hw' hf)

/-- Dimension bound: if there are more edges than `n choose 2 = dim V_F`, where `n` is the
number of populations, some nonzero length perturbation `v` leaves every f-statistic
`∑ e, (w A e - w B e) (w C e - w D e) ℓ e` unchanged. -/
theorem exists_ne_zero_forall_sum_eq_zero [Fintype P] (w : P → E → ℝ)
    (h : (Fintype.card P).choose 2 < Fintype.card E) :
    ∃ v : E → ℝ, v ≠ 0 ∧
      ∀ A B C D : P, ∑ e, (w A e - w B e) * (w C e - w D e) * v e = 0 := by
  classical
  -- one row per unordered pair `{X, Y}`, `X ≠ Y`, with the representative `Quot.out`
  let ι := {z : Sym2 P // ¬ z.IsDiag}
  let A : ι → P := fun z => (Quot.out z.1).1
  let B : ι → P := fun z => (Quot.out z.1).2
  have hrank : (designMatrix w A B A B).rank < Fintype.card E :=
    (rank_le_card_height _).trans_lt (by rwa [Sym2.card_subtype_not_diag])
  have hni : ¬ Function.Injective (designMatrix w A B A B).mulVec := by
    rw [injective_mulVec_iff_rank_eq_card]
    exact hrank.ne
  obtain ⟨x, y, hxy, hne⟩ : ∃ x y, (designMatrix w A B A B) *ᵥ x =
      (designMatrix w A B A B) *ᵥ y ∧ x ≠ y := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨x, y, h, hne⟩ := hni
    exact ⟨x, y, h, hne⟩
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  have hv : (designMatrix w A B A B) *ᵥ (x - y) = 0 := by simp [mulVec_sub, hxy]
  -- every `f2` combination vanishes
  have hf2 : ∀ X Y : P, ∑ e, (w X e - w Y e) ^ 2 * (x - y) e = 0 := by
    intro X Y
    by_cases hXY : X = Y
    · simp [hXY]
    · have hz : ¬ (s(X, Y) : Sym2 P).IsDiag := by simpa using hXY
      have hrow := congrFun hv ⟨s(X, Y), hz⟩
      simp only [designMatrix, mulVec, dotProduct, Pi.zero_apply] at hrow
      rcases hq : Quot.out (r := Sym2.Rel P) s(X, Y) with ⟨a, b⟩
      have hout : s(a, b) = s(X, Y) := by
        have h := Quot.out_eq (r := Sym2.Rel P) s(X, Y)
        rw [hq] at h
        exact h
      simp only [A, B, hq] at hrow
      rcases Sym2.eq_iff.mp hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1 h2
        rw [← hrow]
        exact Finset.sum_congr rfl fun e _ => by ring
      · subst h1 h2
        rw [← hrow]
        exact Finset.sum_congr rfl fun e _ => by ring
  intro A' B' C' D'
  have hpol : ∀ e, (w A' e - w B' e) * (w C' e - w D' e) * (x - y) e =
      ((w A' e - w D' e) ^ 2 * (x - y) e + (w B' e - w C' e) ^ 2 * (x - y) e -
        (w A' e - w C' e) ^ 2 * (x - y) e - (w B' e - w D' e) ^ 2 * (x - y) e) / 2 :=
    fun e => by ring
  simp_rw [hpol, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hf2]
  norm_num

/-- With more edges than `n choose 2`, where `n` is the number of populations, no family of
f-statistics identifies the edge lengths: the design matrix of any family
`(A i, B i, C i, D i)` has a nontrivial kernel. -/
theorem not_injective_of_choose_two_lt [Fintype P] (w : P → E → ℝ)
    (h : (Fintype.card P).choose 2 < Fintype.card E) (A B C D : ι → P) :
    ¬ Function.Injective (designMatrix w A B C D).mulVec := by
  classical
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_forall_sum_eq_zero w h
  have hker : (designMatrix w A B C D) *ᵥ v = 0 := by
    funext i
    simp only [designMatrix, mulVec, dotProduct, Pi.zero_apply]
    rw [← hv (A i) (B i) (C i) (D i)]
  exact fun hinj => hv0 (hinj (hker.trans (mulVec_zero _).symm))

/-- Positive lengths: if a real matrix `G` (for instance a design matrix) is not of full column
rank and every length is positive, a kernel direction gives a different, still positive, length
vector with the same image under `G` (the same predicted statistics). -/
theorem exists_pos_ne_mulVec_eq_of_not_injective {G : Matrix ι E ℝ}
    (hG : ¬ Function.Injective G.mulVec) {len : E → ℝ} (hlen : ∀ e, 0 < len e) :
    ∃ len' : E → ℝ, (∀ e, 0 < len' e) ∧ len' ≠ len ∧ G *ᵥ len' = G *ᵥ len := by
  obtain ⟨x, y, hxy, hne⟩ : ∃ x y, G *ᵥ x = G *ᵥ y ∧ x ≠ y := by
    simp only [Function.Injective, not_forall] at hG
    obtain ⟨x, y, h, hne⟩ := hG
    exact ⟨x, y, h, hne⟩
  set v := x - y with hvdef
  have hv0 : v ≠ 0 := sub_ne_zero.mpr hne
  have hv : G *ᵥ v = 0 := by simp [v, mulVec_sub, hxy]
  obtain ⟨e0, -⟩ := Function.ne_iff.mp hv0
  have hne' : (Finset.univ : Finset E).Nonempty := ⟨e0, Finset.mem_univ _⟩
  set m0 := Finset.univ.inf' hne' len
  have hm0 : 0 < m0 := (Finset.lt_inf'_iff hne').mpr fun e _ => hlen e
  set c := ∑ e, |v e| + 1
  have hc : 0 < c := by
    have hsum : 0 ≤ ∑ e, |v e| := Finset.sum_nonneg fun e _ => abs_nonneg _
    simp only [c]
    linarith
  have hle : ∀ e, |v e| ≤ c := fun e => by
    have := Finset.single_le_sum (f := fun e => |v e|) (fun e _ => abs_nonneg _)
      (Finset.mem_univ e)
    simp only [c]
    linarith
  set t := m0 / (2 * c)
  have ht : 0 < t := div_pos hm0 (by linarith [hc])
  refine ⟨len + t • v, fun e => ?_, fun h => hv0 ?_, ?_⟩
  · have hme : m0 ≤ len e := Finset.inf'_le _ (Finset.mem_univ e)
    have h1 : -(t * |v e|) ≤ t * v e := by
      have := neg_abs_le (v e)
      nlinarith
    have h2 : t * |v e| ≤ m0 / 2 := by
      have : t * |v e| ≤ t * c := mul_le_mul_of_nonneg_left (hle e) ht.le
      have htc : t * c = m0 / 2 := by simp only [t]; field_simp
      linarith
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · have : t • v = 0 := by simpa using h
    exact (smul_eq_zero.mp this).resolve_left ht.ne'
  · rw [mulVec_add, mulVec_smul, hv, smul_zero, add_zero]

/-- Positive-orthant non-identifiability for drift models: with more edges than `n choose 2`,
where `n` is the number of populations, every drift model with positive lengths has a second
drift model, on the counting measure of the edge set, with the same weights, different positive
lengths, and the same value of every `f4` (hence of every f-statistic). -/
theorem exists_driftModel_pos_len_ne [Fintype P]
    [MeasurableSpace E] [DiscreteMeasurableSpace E] {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} (M : DriftModel μ E P) (h : (Fintype.card P).choose 2 < Fintype.card E)
    (hlen : ∀ e, 0 < M.len e) :
    ∃ M' : DriftModel (Measure.count : Measure E) E P, M'.weight = M.weight ∧
      (∀ e, 0 < M'.len e) ∧ M'.len ≠ M.len ∧
      ∀ A B C D : P, f4 Measure.count M'.freq A B C D = f4 μ M.freq A B C D := by
  classical
  -- the design matrix of all quadruples
  let A : P × P × P × P → P := fun q => q.1
  let B : P × P × P × P → P := fun q => q.2.1
  let C : P × P × P × P → P := fun q => q.2.2.1
  let D : P × P × P × P → P := fun q => q.2.2.2
  obtain ⟨len', hpos, hne, heq⟩ := exists_pos_ne_mulVec_eq_of_not_injective
    (not_injective_of_choose_two_lt M.weight h A B C D) hlen
  refine ⟨DriftModel.ofLen M.weight len' fun e => (hpos e).le, rfl, hpos, hne,
    fun A' B' C' D' => ?_⟩
  have h1 := congrFun (f4_eq_designMatrix_mulVec
    (DriftModel.ofLen M.weight len' fun e => (hpos e).le) A B C D) (A', B', C', D')
  have h2 := congrFun (f4_eq_designMatrix_mulVec M A B C D) (A', B', C', D')
  have h3 := congrFun heq (A', B', C', D')
  exact h1.trans (h3.trans h2.symm)

end MathlibExt.Biology.PopulationGenetics.QpGraph
