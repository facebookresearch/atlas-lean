/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The successive projection algorithm recovers the archetypes of a separable matrix

A data matrix with columns `m j` (vectors of a real inner product space `E`) is *separable*
(`Separable`) with `r` archetypes `w 0, …, w (r - 1)` if the archetypes are linearly
independent, every column is a nonnegative combination `m j = ∑ k, h k j • w k` with
`∑ k, h k j ≤ 1`, and every archetype appears among the columns. This is Assumption 1 of
Gillis and Vavasis (the `W` full rank, `H = [I, H'] Π` with column sums of `H'` at most one);
nonnegativity of `W` is not needed.

The successive projection algorithm (SPA) picks a column of largest residual norm, projects
all columns onto the orthogonal complement of the picked columns, and repeats. `IsSPARun m S`
says that the list `S` (most recent pick first) is a run of SPA, with arbitrary tie-breaking.
This is Algorithm 1 of Gillis and Vavasis with `f = ‖·‖²`; they break ties by the norm of the
original column, while the results here hold for every tie-breaking rule.

## Main results

* `norm_sum_smul_le`, `eq_single_of_norm_sum_smul_eq`: Lemma 1 of Gillis and Vavasis for
  `f = ‖·‖²`: a sub-convex combination of linearly independent vectors of norm at most `M`
  has norm at most `M`, with equality only at a vertex `h = Pi.single k 1`.
* `IsSPARun.map_nodup`, `IsSPARun.mem_range`: **Theorem 1 of Gillis and Vavasis (noiseless
  case)**: the first `r` picks of any SPA run are distinct columns, each equal to an
  archetype; `IsSPARun.range_eq`: after `r` picks every archetype has been found.
* `exists_isSPARun`: runs of every length exist.

The noisy case (Theorem 3 of Gillis and Vavasis) and general strongly convex `f` are not
covered.

## References

* N. Gillis and S. A. Vavasis, "Fast and robust recursive algorithms for separable
  nonnegative matrix factorization", *IEEE Trans. Pattern Anal. Mach. Intell.* 36 (2014),
  698–714.
* M. C. U. Araújo, T. C. B. Saldanha, R. K. H. Galvão, T. Yoneyama, H. C. Chame and
  V. Visani, "The successive projections algorithm for variable selection in spectroscopic
  multicomponent analysis", *Chemometr. Intell. Lab. Syst.* 57 (2001), 65–73.
-/

@[expose] public section

namespace Cslib.MachineLearning.MatrixFactorization.SuccessiveProjection

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [DecidableEq ι]

/-- A separable data matrix: columns `m j` are sub-convex combinations of `r` linearly
independent archetypes `w k`, and every archetype is a column (Gillis–Vavasis Assumption 1). -/
structure Separable (m : ι → E) (r : ℕ) where
  /-- The archetypes (columns of `W`). -/
  w : Fin r → E
  /-- The mixing weights (entries of `H`). -/
  h : Fin r → ι → ℝ
  /-- The archetypes are linearly independent (`W` has full column rank). -/
  linearIndependent : LinearIndependent ℝ w
  /-- The mixing weights are nonnegative. -/
  nonneg : ∀ k j, 0 ≤ h k j
  /-- Each column's weights sum to at most one. -/
  sum_le_one : ∀ j, ∑ k, h k j ≤ 1
  /-- Each column is the corresponding combination of the archetypes. -/
  eq_sum : ∀ j, m j = ∑ k, h k j • w k
  /-- Every archetype is one of the columns (separability). -/
  pure : ∀ k, ∃ j, m j = w k

/-- The residual of column `j`: its projection onto the orthogonal complement of the span of
the columns indexed by `S`. -/
noncomputable def residual (m : ι → E) (S : Finset ι) (j : ι) : E :=
  haveI := Classical.decEq E
  m j - (Submodule.span ℝ ((S.image m : Finset E) : Set E)).starProjection (m j)

/-- `S` (most recent pick first) is a run of the successive projection algorithm: each pick
maximizes the residual norm given the earlier picks (ties broken arbitrarily). -/
def IsSPARun (m : ι → E) : List ι → Prop
  | [] => True
  | j :: S => IsSPARun m S ∧ ∀ i, ‖residual m S.toFinset i‖ ≤ ‖residual m S.toFinset j‖

/-- Gillis–Vavasis Lemma 1 (`f = ‖·‖²`), bound: a sub-convex combination of vectors of norm
at most `M` has norm at most `M`. -/
theorem norm_sum_smul_le {r : ℕ} (w : Fin r → E) (h : Fin r → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ k, ‖w k‖ ≤ M) (hh : ∀ k, 0 ≤ h k) (hsum : ∑ k, h k ≤ 1) :
    ‖∑ k, h k • w k‖ ≤ M := by
  calc
    ‖∑ k, h k • w k‖ ≤ ∑ k, ‖h k • w k‖ := norm_sum_le _ _
    _ = ∑ k, h k * ‖w k‖ := by simp [norm_smul, abs_of_nonneg, hh]
    _ ≤ ∑ k, h k * M := sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hw k) (hh k)
    _ = (∑ k, h k) * M := by rw [sum_mul]
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right hsum hM
    _ = M := one_mul M

private theorem single_of_max_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {r : ℕ} {w : Fin r → E}
    (hinj : ∀ k l, w k = w l → w k ≠ 0 → k = l) (h : Fin r → ℝ) {M : ℝ}
    (hM : 0 < M) (hw : ∀ k, ‖w k‖ ≤ M) (hh : ∀ k, 0 ≤ h k)
    (hsum : ∑ k, h k ≤ 1) (heq : ‖∑ k, h k • w k‖ = M) :
    ∃ k, h = Pi.single k 1 ∧ ‖w k‖ = M := by
  classical
  let v := ∑ k, h k • w k
  have hv : ‖v‖ = M := heq
  have hbound : ‖v‖ ≤ (∑ k, h k) * M := by
    calc
      ‖v‖ ≤ ∑ k, ‖h k • w k‖ := norm_sum_le _ _
      _ = ∑ k, h k * ‖w k‖ := by simp [norm_smul, abs_of_nonneg, hh]
      _ ≤ ∑ k, h k * M := sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hw k) (hh k)
      _ = _ := by rw [sum_mul]
  have htotal : ∑ k, h k = 1 := by rw [hv] at hbound; nlinarith
  have hb (k) : inner ℝ (w k) v ≤ M ^ 2 := by
    calc
      inner ℝ (w k) v ≤ ‖w k‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ M * M := by rw [hv]; exact mul_le_mul_of_nonneg_right (hw k) hM.le
      _ = M ^ 2 := by ring
  have hi : ∑ k, h k * inner ℝ (w k) v = M ^ 2 := by
    simp_rw [← real_inner_smul_left]
    rw [← sum_inner]
    rw [real_inner_self_eq_norm_sq, hv]
  have hd : ∑ k, h k * (M ^ 2 - inner ℝ (w k) v) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, htotal, one_mul, hi, sub_self]
  have hterm (k) : h k * (M ^ 2 - inner ℝ (w k) v) = 0 := by
    apply le_antisymm
    · calc
        h k * (M ^ 2 - inner ℝ (w k) v) ≤
            ∑ l, h l * (M ^ 2 - inner ℝ (w l) v) :=
          single_le_sum (fun l _ => mul_nonneg (hh l) (sub_nonneg.mpr (hb l))) (mem_univ k)
        _ = 0 := hd
    · exact mul_nonneg (hh k) (sub_nonneg.mpr (hb k))
  have hequal (k) (hk : 0 < h k) : w k = v := by
    have hik : inner ℝ (w k) v = M ^ 2 := by
      have := (mul_eq_zero.mp (hterm k)).resolve_left hk.ne'
      linarith
    have hn : ‖w k - v‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq_real, hik, hv]
      have := (sq_le_sq₀ (norm_nonneg _) hM.le).mpr (hw k)
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (w k - v)]))
  obtain ⟨k, hk⟩ : ∃ k, 0 < h k := by
    by_contra! hn
    have hz : ∀ k, h k = 0 := fun k => le_antisymm (hn k) (hh k)
    simp [hz] at htotal
  have hv0 : v ≠ 0 := by intro hz; simp [hz] at hv; linarith
  have hz (l) (hl : l ≠ k) : h l = 0 := by
    by_contra hn
    exact hl (hinj l k ((hequal l (lt_of_le_of_ne (hh l) (Ne.symm hn))).trans
      (hequal k hk).symm) (by rw [hequal l (lt_of_le_of_ne (hh l) (Ne.symm hn))]; exact hv0))
  have hk1 : h k = 1 := by
    rw [sum_eq_single k (fun l _ hl => hz l hl) (by simp)] at htotal
    exact htotal
  refine ⟨k, ?_, by rw [hequal k hk, hv]⟩
  ext l
  by_cases hl : l = k
  · subst l; simp [hk1]
  · simp [hl, hz l hl]

/-- Gillis–Vavasis Lemma 1 (`f = ‖·‖²`), equality case: for linearly independent vectors of
norm at most `M > 0`, a sub-convex combination of norm `M` is a vertex `w k` with
`‖w k‖ = M`. -/
theorem eq_single_of_norm_sum_smul_eq {r : ℕ} {w : Fin r → E} (hli : LinearIndependent ℝ w)
    (h : Fin r → ℝ) {M : ℝ} (hM : 0 < M) (hw : ∀ k, ‖w k‖ ≤ M) (hh : ∀ k, 0 ≤ h k)
    (hsum : ∑ k, h k ≤ 1) (heq : ‖∑ k, h k • w k‖ = M) :
    ∃ k, h = Pi.single k 1 ∧ ‖w k‖ = M := by
  exact single_of_max_norm (fun k l hkl _ => hli.injective hkl) h hM hw hh hsum heq

private theorem next_archetype {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} [DecidableEq ι] {m : ι → E} {r : ℕ}
    (hm : Separable m r) (S : List ι) (hn : (S.map m).Nodup)
    (hs : ∀ j ∈ S, m j ∈ Set.range hm.w) (hlen : S.length < r) (j : ι)
    (hj : ∀ i, ‖residual m S.toFinset i‖ ≤ ‖residual m S.toFinset j‖) :
    m j ∈ Set.range hm.w ∧ m j ∉ S.map m := by
  classical
  let A := (S.map m).toFinset
  let U := Submodule.span ℝ ((S.toFinset.image m : Finset E) : Set E)
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - U.starProjection
  have hp (i) : P (m i) = residual m S.toFinset i := rfl
  have hzero (x : E) : P x = 0 ↔ x ∈ U := by
    change x - U.starProjection x = 0 ↔ x ∈ U
    rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]
  have hspan (k : Fin r) (hk : hm.w k ∉ A) :
      U ≤ Submodule.span ℝ (hm.w '' {k}ᶜ) := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    obtain ⟨l, hl⟩ := hs i (List.mem_toFinset.mp hi)
    apply Submodule.subset_span
    refine ⟨l, ?_, hl⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hlk
    subst l
    apply hk
    simpa [A, hl] using List.mem_map.mpr ⟨i, List.mem_toFinset.mp hi, rfl⟩
  have hpicked (k : Fin r) (hk : hm.w k ∈ A) : P (hm.w k) = 0 := by
    apply (hzero _).mpr
    apply Submodule.subset_span
    obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    exact mem_image.mpr ⟨i, List.mem_toFinset.mpr hi, he⟩
  have hinj (k l : Fin r) (hkl : P (hm.w k) = P (hm.w l))
      (hk0 : P (hm.w k) ≠ 0) : k = l := by
    by_contra hne
    have hk : hm.w k ∉ A := fun ha => hk0 (hpicked k ha)
    have hdiff : hm.w k - hm.w l ∈ U := (hzero _).mp (by rw [map_sub, hkl, sub_self])
    apply hm.linearIndependent.notMem_span k
    have hl : hm.w l ∈ Submodule.span ℝ (hm.w '' {k}ᶜ) :=
      Submodule.subset_span ⟨l, by simpa using Ne.symm hne, rfl⟩
    simpa using (Submodule.span ℝ (hm.w '' {k}ᶜ)).add_mem (hspan k hk hdiff) hl
  have hcard : A.card < (univ.image hm.w).card := by
    rw [card_image_of_injective _ hm.linearIndependent.injective, card_univ, Fintype.card_fin]
    simpa [A, List.toFinset_card_of_nodup hn] using hlen
  obtain ⟨x, hx, hxa⟩ := exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨k₀, _, rfl⟩ := mem_image.mp hx
  have hk₀ : P (hm.w k₀) ≠ 0 := by
    intro hz
    exact hm.linearIndependent.notMem_span k₀ (hspan k₀ hxa ((hzero _).mp hz))
  have : Nonempty (Fin r) := ⟨k₀⟩
  obtain ⟨kmax, _, hmax⟩ := univ.exists_max_image (fun k => ‖P (hm.w k)‖) univ_nonempty
  let M := ‖P (hm.w kmax)‖
  have hM : 0 < M := (norm_pos_iff.mpr hk₀).trans_le (hmax k₀ (mem_univ k₀))
  have hw (k) : ‖P (hm.w k)‖ ≤ M := hmax k (mem_univ k)
  have hcomb (i) : residual m S.toFinset i = ∑ k, hm.h k i • P (hm.w k) := by
    rw [← hp, hm.eq_sum i, map_sum]
    simp only [map_smul]
  have hle : ‖residual m S.toFinset j‖ ≤ M := by
    rw [hcomb]
    exact norm_sum_smul_le _ _ hM.le hw (fun k => hm.nonneg k j) (hm.sum_le_one j)
  obtain ⟨imax, himax⟩ := hm.pure kmax
  have heq : ‖residual m S.toFinset j‖ = M := le_antisymm hle (by
    simpa [← hp, himax, M] using hj imax)
  obtain ⟨k, hk, hknorm⟩ := single_of_max_norm hinj (fun k => hm.h k j) hM hw
    (fun k => hm.nonneg k j) (hm.sum_le_one j) (by rw [← hcomb, heq])
  have hjw : m j = hm.w k := by
    rw [hm.eq_sum j]
    change ∑ l, (fun k => hm.h k j) l • hm.w l = hm.w k
    rw [hk]
    simp
  refine ⟨⟨k, hjw.symm⟩, ?_⟩
  intro hmem
  have hz := hpicked k (by simpa [A, hjw] using hmem)
  rw [hz, norm_zero] at hknorm
  linarith

private theorem run_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} [DecidableEq ι] {m : ι → E} {r : ℕ}
    (hm : Separable m r) (S : List ι) (hS : IsSPARun m S) (hlen : S.length ≤ r) :
    (S.map m).Nodup ∧ ∀ j ∈ S, m j ∈ Set.range hm.w := by
  induction S with
  | nil => exact ⟨List.nodup_nil, by simp⟩
  | cons j S ih =>
    obtain ⟨hprev, hmax⟩ := hS
    have hlt : S.length < r := by simpa using hlen
    obtain ⟨hn, hs⟩ := ih hprev hlt.le
    obtain ⟨hj, hjnew⟩ := next_archetype hm S hn hs hlt j hmax
    refine ⟨by simpa using And.intro hjnew hn, ?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hj
    · exact hs i hi

/-- **SPA recovers archetypes** (Gillis–Vavasis Theorem 1, noiseless case): in the first `r`
picks of any SPA run on a separable matrix with `r` archetypes, the picked columns are
pairwise distinct. -/
theorem IsSPARun.map_nodup {m : ι → E} {r : ℕ} (hm : Separable m r) {S : List ι}
    (hS : IsSPARun m S) (hlen : S.length ≤ r) : (S.map m).Nodup := by
  exact (run_invariant hm S hS hlen).1

/-- **SPA recovers archetypes** (Gillis–Vavasis Theorem 1, noiseless case): each of the first
`r` picks of any SPA run is an archetype. -/
theorem IsSPARun.mem_range {m : ι → E} {r : ℕ} (hm : Separable m r) {S : List ι}
    (hS : IsSPARun m S) (hlen : S.length ≤ r) : ∀ j ∈ S, m j ∈ Set.range hm.w := by
  exact (run_invariant hm S hS hlen).2

/-- After exactly `r` picks, SPA has found every archetype. -/
theorem IsSPARun.range_eq {m : ι → E} {r : ℕ} (hm : Separable m r) {S : List ι}
    (hS : IsSPARun m S) (hlen : S.length = r) : {e | ∃ j ∈ S, m j = e} = Set.range hm.w := by
  classical
  have hn := hS.map_nodup hm hlen.le
  have hs := hS.mem_range hm hlen.le
  have hsub : (S.map m).toFinset ⊆ univ.image hm.w := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    obtain ⟨k, hk⟩ := hs j hj
    exact mem_image.mpr ⟨k, mem_univ k, hk⟩
  have heq : (S.map m).toFinset = univ.image hm.w := by
    apply eq_of_subset_of_card_le hsub
    rw [List.toFinset_card_of_nodup hn, List.length_map, hlen,
      card_image_of_injective _ hm.linearIndependent.injective, card_univ, Fintype.card_fin]
  ext e
  change (∃ j ∈ S, m j = e) ↔ e ∈ Set.range hm.w
  have hmem : e ∈ (S.map m).toFinset ↔ ∃ j ∈ S, m j = e := by
    simp only [List.mem_toFinset, List.mem_map]
  rw [← hmem, heq]
  simp

/-- SPA runs of every length exist (on a nonempty set of columns). -/
theorem exists_isSPARun [Finite ι] [Nonempty ι] (m : ι → E) (n : ℕ) :
    ∃ S : List ι, S.length = n ∧ IsSPARun m S := by
  classical
  let := Fintype.ofFinite ι
  induction n with
  | zero => exact ⟨[], rfl, trivial⟩
  | succ n ih =>
    obtain ⟨S, hlen, hS⟩ := ih
    obtain ⟨j, _, hj⟩ := univ.exists_max_image
      (fun i => ‖residual m S.toFinset i‖) univ_nonempty
    exact ⟨j :: S, by simp [hlen], hS, fun i => hj i (mem_univ i)⟩

end Cslib.MachineLearning.MatrixFactorization.SuccessiveProjection

