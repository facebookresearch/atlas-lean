/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian

/-!
# Ky Fan eigenvalue inequality

For Hermitian `A, B`, sum of `k` largest eigenvalues of `A + B` ≤ sum
for `A` plus sum for `B`.

Source: Ky Fan, On a theorem of Weyl concerning eigenvalues of linear
transformations. I, PNAS 35 (1949), 652-655, DOI 10.1073/pnas.35.11.652.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.KyFanWanted

open scoped BigOperators

/-- **Prefix sum of a finite real sequence.** For real numbers $\lambda_0, \dots, \lambda_{n-1}$
and a natural number $k \le n$, the prefix sum of length $k$ is $\sum_{i < k} \lambda_i$, the
sum of the first $k$ entries. Applied to the eigenvalues of a Hermitian matrix, listed in
decreasing order, it is the sum of the $k$ largest ones. -/
noncomputable def eigPrefSum {n : ℕ} (eig : Fin n → ℝ) (k : ℕ)
    (hk : k ≤ n) : ℝ :=
  ∑ i ∈ Finset.range k, if hi : i < k then eig (Fin.castLE hk ⟨i, hi⟩) else 0

@[simp]
theorem eigPrefSum_zero {n : ℕ} (eig : Fin n → ℝ) (hk : 0 ≤ n) : eigPrefSum eig 0 hk = 0 := by
  simp [eigPrefSum]

theorem eigPrefSum_eq_sum {n : ℕ} (eig : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    eigPrefSum eig k hk = ∑ i : Fin k, eig (Fin.castLE hk i) := by
  rw [eigPrefSum, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => dite_eq_left i.isLt

theorem eigPrefSum_succ {n : ℕ} (eig : Fin n → ℝ) (k : ℕ) (hk : k + 1 ≤ n) :
    eigPrefSum eig (k + 1) hk = eigPrefSum eig k (Nat.le_of_succ_le hk) + eig ⟨k, hk⟩ := by
  rw [eigPrefSum_eq_sum, eigPrefSum_eq_sum, Fin.sum_univ_castSucc]
  rfl

/-- Telescoping sum of successive differences over a range. -/
private lemma sum_range_sub_succ (a : ℕ → ℝ) (t : ℕ) :
    ∑ i ∈ Finset.range t, (a i - a (i + 1)) = a 0 - a t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Weighted telescoping identity used to evaluate the Abel mean. -/
private lemma sum_range_succ_mul_sub (a : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, ((i : ℝ) + 1) * (a i - a (i + 1)) =
    ∑ i ∈ Finset.range m, a i - (m : ℝ) * a m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Telescoping sum of successive differences over an interval. -/
private lemma sum_Ico_sub_succ (a : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (a i - a (i + 1)) = a m - a n := by
  rw [Finset.sum_Ico_eq_sub _ hmn, sum_range_sub_succ, sum_range_sub_succ]
  ring

/-- Closed form for the Abel mean with capped weights. -/
private lemma kyfan_identity (a : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n) (hk1 : 1 ≤ k) :
    (k : ℝ) * a (n - 1) +
      ∑ i ∈ Finset.range (n - 1), min ((i : ℝ) + 1) (k : ℝ) * (a i - a (i + 1)) =
      ∑ i ∈ Finset.range k, a i := by
  have hkn : k - 1 ≤ n - 1 := Nat.sub_le_sub_right hk 1
  have hsplit : Finset.range (n - 1) =
      Finset.range (k - 1) ∪ Finset.Ico (k - 1) (n - 1) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hkn).symm
  have hdisj : Disjoint (Finset.range (k - 1)) (Finset.Ico (k - 1) (n - 1)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 := Finset.mem_range.mp hi1
    have h2 := (Finset.mem_Ico.mp hi2).1
    omega
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk1]
    simp
  have hp1 : (∑ i ∈ Finset.range (k - 1),
      min ((i : ℝ) + 1) (k : ℝ) * (a i - a (i + 1))) =
      (∑ i ∈ Finset.range (k - 1), a i) - ((k : ℝ) - 1) * a (k - 1) := by
    have e : ∀ i ∈ Finset.range (k - 1),
        min ((i : ℝ) + 1) (k : ℝ) * (a i - a (i + 1)) =
        ((i : ℝ) + 1) * (a i - a (i + 1)) := by
      intro i hi
      have hi' : i + 1 ≤ k := by
        have h := Finset.mem_range.mp hi
        omega
      have hle : ((i : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hi'
      rw [min_eq_left hle]
    rw [Finset.sum_congr rfl e, sum_range_succ_mul_sub, hc]
  have hp2 : (∑ i ∈ Finset.Ico (k - 1) (n - 1),
      min ((i : ℝ) + 1) (k : ℝ) * (a i - a (i + 1))) =
      (k : ℝ) * (a (k - 1) - a (n - 1)) := by
    have e : ∀ i ∈ Finset.Ico (k - 1) (n - 1),
        min ((i : ℝ) + 1) (k : ℝ) * (a i - a (i + 1)) =
        (k : ℝ) * (a i - a (i + 1)) := by
      intro i hi
      have hi' : k ≤ i + 1 := by
        have h := (Finset.mem_Ico.mp hi).1
        omega
      have hle : (k : ℝ) ≤ ((i : ℝ) + 1) := by exact_mod_cast hi'
      rw [min_eq_right hle]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, sum_Ico_sub_succ _ _ _ hkn]
  rw [hsplit, Finset.sum_union hdisj, hp1, hp2]
  have hkk : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  have hrr : (∑ i ∈ Finset.range (k - 1 + 1), a i) =
      (∑ i ∈ Finset.range (k - 1), a i) + a (k - 1) :=
    Finset.sum_range_succ _ _
  rw [hkk] at hrr
  rw [hrr]
  ring

/-- Rearrangement bound: a weighted average with weights in `[0, 1]` totalling `k`
is at most the sum of the first `k` values of a decreasing sequence. -/
private lemma kyfan_rearrange
    (Λ W : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n)
    (hW0 : ∀ i ∈ Finset.range n, 0 ≤ W i)
    (hW1 : ∀ i ∈ Finset.range n, W i ≤ 1)
    (hWsum : ∑ i ∈ Finset.range n, W i = (k : ℝ))
    (hΛ : ∀ i j : ℕ, i ≤ j → j < n → Λ j ≤ Λ i) :
    ∑ i ∈ Finset.range n, Λ i * W i ≤ ∑ i ∈ Finset.range k, Λ i := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have hW0' : ∀ i ∈ Finset.range n, W i = 0 := by
      have hsum0 : (∑ i ∈ Finset.range n, W i) = 0 := by simpa using hWsum
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => hW0 i hi)).mp hsum0
    have hlhs : (∑ i ∈ Finset.range n, Λ i * W i) = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hW0' i hi, mul_zero])
    rw [hlhs]
    simp
  · have hk1 : 1 ≤ k := by omega
    have hn : 1 ≤ n := le_trans hk1 hk
    have hSmem : ∀ j : ℕ, j ≤ n → ∀ i ∈ Finset.range j, i ∈ Finset.range n := by
      intro j hj i hi
      have h := Finset.mem_range.mp hi
      exact Finset.mem_range.mpr (lt_of_lt_of_le h hj)
    have hSle : ∀ j : ℕ, j ≤ n → (∑ i ∈ Finset.range j, W i) ≤ (j : ℝ) := by
      intro j hj
      calc (∑ i ∈ Finset.range j, W i) ≤ ∑ _i ∈ Finset.range j, (1 : ℝ) :=
            Finset.sum_le_sum (fun i hi => hW1 i (hSmem j hj i hi))
        _ = (j : ℝ) := by simp
    have hSk : ∀ j : ℕ, j ≤ n → (∑ i ∈ Finset.range j, W i) ≤ (k : ℝ) := by
      intro j hj
      calc (∑ i ∈ Finset.range j, W i) ≤ ∑ i ∈ Finset.range n, W i :=
            Finset.sum_le_sum_of_subset_of_nonneg
              ((Finset.range_subset).mpr
                (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le hx hj)))
              (fun i hi _ => hW0 i hi)
        _ = (k : ℝ) := hWsum
    have hbp := Finset.sum_range_by_parts' W Λ n
    simp only [smul_eq_mul] at hbp
    rw [hWsum] at hbp
    have hbound : ∀ i ∈ Finset.range (n - 1),
        (∑ i_1 ∈ Finset.range (i + 1), W i_1) * (Λ i - Λ (i + 1)) ≤
        min ((i : ℝ) + 1) (k : ℝ) * (Λ i - Λ (i + 1)) := by
      intro i hi
      have hi' : i < n - 1 := Finset.mem_range.mp hi
      have hD : 0 ≤ Λ i - Λ (i + 1) := by
        have h := hΛ i (i + 1) (Nat.le_succ i) (by omega)
        linarith
      have hSmin : (∑ i_1 ∈ Finset.range (i + 1), W i_1) ≤
          min ((i : ℝ) + 1) (k : ℝ) := by
        refine le_min ?_ ?_
        · have h := hSle (i + 1) (by omega)
          simpa using h
        · exact hSk (i + 1) (by omega)
      exact mul_le_mul_of_nonneg_right hSmin hD
    have hfin := kyfan_identity Λ n k hk hk1
    have e1 : (∑ i ∈ Finset.range n, Λ i * W i) =
        ∑ i ∈ Finset.range n, W i * Λ i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e1, hbp, sub_eq_add_neg, ← Finset.sum_neg_distrib, ← hfin]
    refine add_le_add (le_refl _) (Finset.sum_le_sum (fun i hi => ?_))
    change -((∑ j ∈ Finset.range (i + 1), W j) * (Λ (i + 1) - Λ i)) ≤
      min ((i : ℝ) + 1) (k : ℝ) * (Λ i - Λ (i + 1))
    have h := hbound i hi
    have h2 : -((∑ j ∈ Finset.range (i + 1), W j) * (Λ (i + 1) - Λ i)) =
        (∑ j ∈ Finset.range (i + 1), W j) * (Λ i - Λ (i + 1)) := by ring
    rw [h2]
    exact h

/-- Rayleigh expansion of a single vector in the eigenbasis. -/
private lemma rayleigh_single
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (n : ℕ) (hn : Module.finrank ℂ E = n)
    (x : E) :
    inner ℂ x (T x) =
      ((∑ i : Fin n, hT.eigenvalues hn i *
        ‖inner ℂ ((hT.eigenvectorBasis hn) i) x‖ ^ 2 : ℝ) : ℂ) := by
  have hexp : x =
      ∑ i, inner ℂ ((hT.eigenvectorBasis hn) i) x • (hT.eigenvectorBasis hn) i :=
    ((hT.eigenvectorBasis hn).sum_repr' x).symm
  have hTexp : T x =
      ∑ i, (inner ℂ ((hT.eigenvectorBasis hn) i) x) •
        ((((hT.eigenvalues hn i : ℝ) : ℂ)) • (hT.eigenvectorBasis hn) i) := by
    conv_lhs => rw [hexp, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, hT.apply_eigenvectorBasis hn i]
    rfl
  calc inner ℂ x (T x)
      = ∑ i, (inner ℂ ((hT.eigenvectorBasis hn) i) x) *
          ((((hT.eigenvalues hn i : ℝ) : ℂ)) *
        inner ℂ x ((hT.eigenvectorBasis hn) i)) := by
          rw [hTexp, inner_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [inner_smul_right, inner_smul_right]
    _ = ((∑ i : Fin n, hT.eigenvalues hn i *
        ‖inner ℂ ((hT.eigenvectorBasis hn) i) x‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have ci : inner ℂ x ((hT.eigenvectorBasis hn) i) =
              (starRingEnd ℂ) (inner ℂ ((hT.eigenvectorBasis hn) i) x) :=
            (inner_conj_symm x ((hT.eigenvectorBasis hn) i)).symm
          rw [ci, ← mul_assoc,
            mul_comm (inner ℂ ((hT.eigenvectorBasis hn) i) x) _,
            mul_assoc, RCLike.mul_conj, Complex.ofReal_mul, Complex.ofReal_pow]
          rfl

/-- Rayleigh expansion summed over an orthonormal family. -/
private lemma rayleigh_family
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (n : ℕ) (hn : Module.finrank ℂ E = n)
    (k : ℕ) (v : Fin k → E) :
    (∑ j : Fin k, inner ℂ (v j) (T (v j))) =
      ((∑ i : Fin n, hT.eigenvalues hn i *
        ∑ j : Fin k, ‖inner ℂ ((hT.eigenvectorBasis hn) i) (v j)‖ ^ 2 : ℝ) : ℂ) := by
  have h4 : ∀ j : Fin k, inner ℂ (v j) (T (v j)) =
      ((∑ i : Fin n, hT.eigenvalues hn i *
        ‖inner ℂ ((hT.eigenvectorBasis hn) i) (v j)‖ ^ 2 : ℝ) : ℂ) :=
    fun j => rayleigh_single E T hT n hn (v j)
  calc (∑ j : Fin k, inner ℂ (v j) (T (v j)))
      = ∑ j : Fin k, ((∑ i : Fin n, hT.eigenvalues hn i *
          ‖inner ℂ ((hT.eigenvectorBasis hn) i) (v j)‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl (fun j _ => h4 j)
    _ = ((∑ i : Fin n, hT.eigenvalues hn i *
        ∑ j : Fin k, ‖inner ℂ ((hT.eigenvectorBasis hn) i) (v j)‖ ^ 2 : ℝ) : ℂ) := by
        simp only [Complex.ofReal_sum, Complex.ofReal_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]

/-- The eigenbasis weights of an orthonormal family are bounded. -/
private lemma rayleigh_weights
    (n k : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : OrthonormalBasis (Fin n) ℂ E) (v : Fin k → E) (hv : Orthonormal ℂ v) :
    (∀ i : Fin n, 0 ≤ ∑ j : Fin k, ‖inner ℂ (e i) (v j)‖ ^ 2) ∧
    (∀ i : Fin n, (∑ j : Fin k, ‖inner ℂ (e i) (v j)‖ ^ 2) ≤ 1) ∧
    ((∑ i : Fin n, ∑ j : Fin k, ‖inner ℂ (e i) (v j)‖ ^ 2) = (k : ℝ)) := by
  have hP : ∀ j : Fin k, (∑ i : Fin n, ‖inner ℂ (e i) (v j)‖ ^ 2) = 1 := by
    intro j
    rw [e.sum_sq_norm_inner_right (v j), hv.norm_eq_one j, one_pow]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  · intro i
    have hB := hv.sum_inner_products_le (e i) (s := Finset.univ)
    rw [e.orthonormal.norm_eq_one i, one_pow] at hB
    calc (∑ j : Fin k, ‖inner ℂ (e i) (v j)‖ ^ 2)
        = ∑ j : Fin k, ‖inner ℂ (v j) (e i)‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← inner_conj_symm, RCLike.norm_conj]
      _ ≤ 1 := hB
  · rw [Finset.sum_comm]
    simp only [hP, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]

/-- Half of the Ky Fan maximum principle: Rayleigh sums over orthonormal
families are bounded by the top eigenvalue sum. -/
private lemma kyfan_orthonormal_bound
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (n : ℕ) (hn : Module.finrank ℂ E = n)
    (k : ℕ) (hk : k ≤ n) (v : Fin k → E) (hv : Orthonormal ℂ v) :
    (∑ j : Fin k, inner ℂ (v j) (T (v j))).re ≤
      eigPrefSum (hT.eigenvalues hn) k hk := by
  have h5 := rayleigh_family E T hT n hn k v
  have hw := rayleigh_weights n k E (hT.eigenvectorBasis hn) v hv
  obtain ⟨hw0, hw1, hws⟩ := hw
  set Λ : ℕ → ℝ :=
    (fun i => if h : i < n then hT.eigenvalues hn ⟨i, h⟩ else 0) with hΛdef
  set W : ℕ → ℝ := (fun i => if h : i < n then
    (∑ j : Fin k, ‖inner ℂ ((hT.eigenvectorBasis hn) ⟨i, h⟩) (v j)‖ ^ 2) else 0) with hWdef
  have hΛ : ∀ i j : ℕ, i ≤ j → j < n → Λ j ≤ Λ i := by
    intro i j hij hj
    have hi : i < n := lt_of_le_of_lt hij hj
    change Λ j ≤ Λ i
    simp only [hΛdef, dite_eq_left hj, dite_eq_left hi]
    exact (hT.eigenvalues_antitone hn) (Fin.le_def.mpr hij)
  have hW0 : ∀ i ∈ Finset.range n, 0 ≤ W i := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    change 0 ≤ W i
    simp only [hWdef, dite_eq_left hin]
    exact hw0 ⟨i, hin⟩
  have hW1 : ∀ i ∈ Finset.range n, W i ≤ 1 := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    change W i ≤ 1
    simp only [hWdef, dite_eq_left hin]
    exact hw1 ⟨i, hin⟩
  have hΛval : ∀ i : Fin n, Λ (↑i) = (hT.eigenvalues hn) i := by
    intro i
    show Λ ↑i = _
    simp only [hΛdef, dite_eq_left i.isLt, Fin.eta i i.isLt]
  have hWval : ∀ i : Fin n, W (↑i) =
      (∑ j : Fin k, ‖inner ℂ ((hT.eigenvectorBasis hn) i) (v j)‖ ^ 2) := by
    intro i
    show W ↑i = _
    simp only [hWdef, dite_eq_left i.isLt, Fin.eta i i.isLt]
  have hWsum : (∑ i ∈ Finset.range n, W i) = (k : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => W i) n, ← hws]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show W ↑i = _
    simp only [hWdef, dite_eq_left i.isLt, Fin.eta i i.isLt]
  have hD : (∑ i ∈ Finset.range n, Λ i * W i) ≤ (∑ i ∈ Finset.range k, Λ i) :=
    kyfan_rearrange Λ W n k hk hW0 hW1 hWsum hΛ
  have hbridge : (∑ i : Fin n, (hT.eigenvalues hn) i *
      (∑ j : Fin k, ‖inner ℂ ((hT.eigenvectorBasis hn) i) (v j)‖ ^ 2)) =
      (∑ i ∈ Finset.range n, Λ i * W i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => Λ i * W i) n]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hΛval i, hWval i]
  have hbridge2 : eigPrefSum (hT.eigenvalues hn) k hk =
      (∑ i ∈ Finset.range k, Λ i) := by
    unfold eigPrefSum
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i < k := Finset.mem_range.mp hi
    have hn' : i < n := Nat.lt_of_lt_of_le hik hk
    change (if hi : i < k then (hT.eigenvalues hn) (Fin.castLE hk ⟨i, hi⟩) else 0) = Λ i
    simp only [dite_eq_left hik, dite_eq_left hn', hΛdef, Fin.castLE_mk]
  rw [h5, Complex.ofReal_re, hbridge, hbridge2]
  exact hD

/-- The top eigenvectors attain the eigenvalue prefix sum. -/
private lemma rayleigh_top_eig
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (n : ℕ) (hn : Module.finrank ℂ E = n)
    (k : ℕ) (hk : k ≤ n) :
    (∑ j : Fin k, inner ℂ ((hT.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
      (T ((hT.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩))) =
      (((eigPrefSum (hT.eigenvalues hn) k hk) : ℝ) : ℂ) := by
  have hterm : ∀ i : ℕ, ∀ h : i < n,
      inner ℂ ((hT.eigenvectorBasis hn) ⟨i, h⟩)
        (T ((hT.eigenvectorBasis hn) ⟨i, h⟩)) =
        (((hT.eigenvalues hn ⟨i, h⟩) : ℝ) : ℂ) := by
    intro i h
    rw [hT.apply_eigenvectorBasis hn ⟨i, h⟩, inner_smul_right]
    have h1 : inner ℂ ((hT.eigenvectorBasis hn) ⟨i, h⟩)
        ((hT.eigenvectorBasis hn) ⟨i, h⟩) = 1 := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ),
        (hT.eigenvectorBasis hn).orthonormal.norm_eq_one ⟨i, h⟩]
      simp
    rw [h1, mul_one]
    rfl
  have hF : ∀ j : Fin k, (fun i => (if h : i < n then
      inner ℂ ((hT.eigenvectorBasis hn) ⟨i, h⟩)
        (T ((hT.eigenvectorBasis hn) ⟨i, h⟩)) else 0)) (↑j) =
      inner ℂ ((hT.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
      (T ((hT.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)) := by
    intro j
    change (if h : ↑j < n then inner ℂ ((hT.eigenvectorBasis hn) ⟨↑j, h⟩)
      (T ((hT.eigenvectorBasis hn) ⟨↑j, h⟩)) else 0) = _
    simp only [dite_eq_left (Nat.lt_of_lt_of_le j.isLt hk)]
  have step1 : (∑ j : Fin k, inner ℂ
      ((hT.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
      (T ((hT.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩))) =
      (∑ i ∈ Finset.range k, (if h : i < n then
        inner ℂ ((hT.eigenvectorBasis hn) ⟨i, h⟩)
          (T ((hT.eigenvectorBasis hn) ⟨i, h⟩)) else 0)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < n then
      inner ℂ ((hT.eigenvectorBasis hn) ⟨i, h⟩)
        (T ((hT.eigenvectorBasis hn) ⟨i, h⟩)) else 0)) k]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact (hF j).symm
  have step2 : (∑ i ∈ Finset.range k, (if h : i < n then
      inner ℂ ((hT.eigenvectorBasis hn) ⟨i, h⟩)
        (T ((hT.eigenvectorBasis hn) ⟨i, h⟩)) else 0)) =
      (((∑ i ∈ Finset.range k,
        (if h : i < n then hT.eigenvalues hn ⟨i, h⟩ else 0)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i < k := Finset.mem_range.mp hi
    have hn' : i < n := Nat.lt_of_lt_of_le hik hk
    change (if h : i < n then inner ℂ ((hT.eigenvectorBasis hn) ⟨i, h⟩)
        (T ((hT.eigenvectorBasis hn) ⟨i, h⟩)) else 0) =
      ((if h : i < n then hT.eigenvalues hn ⟨i, h⟩ else 0 : ℝ) : ℂ)
    simp only [dite_eq_left hn']
    exact hterm i hn'
  have step3 : (∑ i ∈ Finset.range k,
      (if h : i < n then hT.eigenvalues hn ⟨i, h⟩ else 0)) =
      eigPrefSum (hT.eigenvalues hn) k hk := by
    unfold eigPrefSum
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i < k := Finset.mem_range.mp hi
    have hn' : i < n := Nat.lt_of_lt_of_le hik hk
    change (if h : i < n then hT.eigenvalues hn ⟨i, h⟩ else 0) =
      (if hi : i < k then hT.eigenvalues hn (Fin.castLE hk ⟨i, hi⟩) else 0)
    simp only [dite_eq_left hn', dite_eq_left hik, Fin.castLE_mk]
  rw [step1, step2, step3]

/--
**Ky Fan inequality for sums of largest eigenvalues.** Let $A$ and $B$ be Hermitian $n \times n$
complex matrices and let $k \le n$. Then the sum of the $k$ largest eigenvalues of $A + B$ is at
most the sum of the $k$ largest eigenvalues of $A$ plus the sum of the $k$ largest eigenvalues
of $B$, where eigenvalues are counted with multiplicity.

Proves `Wanted` entry `ky_fan_eigenvalue_sum_le`.

Source: Ky Fan, On a theorem of Weyl, PNAS 35 (1949), 652-655, DOI 10.1073/pnas.35.11.652.
-/
theorem ky_fan_eigenvalue_sum_le
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : ℕ) (hk : k ≤ n) :
    let hA_sym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    let hB_sym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB)
    let hAB_sym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.add hB))
    eigPrefSum (hAB_sym.eigenvalues finrank_euclideanSpace_fin) k hk ≤
      eigPrefSum (hA_sym.eigenvalues finrank_euclideanSpace_fin) k hk +
        eigPrefSum (hB_sym.eigenvalues finrank_euclideanSpace_fin) k hk := by
  intro hA_sym hB_sym hAB_sym
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n :=
    finrank_euclideanSpace_fin
  have hTAB : (A + B).toEuclideanLin = A.toEuclideanLin + B.toEuclideanLin :=
    map_add Matrix.toEuclideanLin A B
  have hv : Orthonormal ℂ ((hAB_sym.eigenvectorBasis hn) ∘
      fun j : Fin k => (⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩ : Fin n)) :=
    Orthonormal.comp (hAB_sym.eigenvectorBasis hn).orthonormal _
      (fun a b hab => Fin.ext (by simpa [Fin.mk.injEq] using hab))
  have htop : (∑ j : Fin k, inner ℂ
      ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
      ((A + B).toEuclideanLin
        ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩))) =
      (((eigPrefSum (hAB_sym.eigenvalues hn) k hk) : ℝ) : ℂ) :=
    rayleigh_top_eig _ _ hAB_sym n hn k hk
  have hsplit : (∑ j : Fin k, inner ℂ
      ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
      ((A + B).toEuclideanLin
        ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩))) =
      (∑ j : Fin k, inner ℂ
        ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
        (A.toEuclideanLin
          ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩))) +
      (∑ j : Fin k, inner ℂ
        ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
        (B.toEuclideanLin
          ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hTAB, LinearMap.add_apply, inner_add_right]
  have hvA : Orthonormal ℂ (fun j : Fin k => ((hAB_sym.eigenvectorBasis hn)
      ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)) :=
    hv
  have hAle : ((∑ j : Fin k, inner ℂ
      ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
      (A.toEuclideanLin
        ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)))).re ≤
      eigPrefSum (hA_sym.eigenvalues hn) k hk :=
    kyfan_orthonormal_bound _ _ hA_sym n hn k hk _ hvA
  have hBle : ((∑ j : Fin k, inner ℂ
      ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
      (B.toEuclideanLin
        ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)))).re ≤
      eigPrefSum (hB_sym.eigenvalues hn) k hk :=
    kyfan_orthonormal_bound _ _ hB_sym n hn k hk _ hvA
  have hfin : eigPrefSum (hAB_sym.eigenvalues hn) k hk =
      ((∑ j : Fin k, inner ℂ
        ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
        (A.toEuclideanLin
          ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)))).re +
      ((∑ j : Fin k, inner ℂ
        ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)
        (B.toEuclideanLin
          ((hAB_sym.eigenvectorBasis hn) ⟨↑j, Nat.lt_of_lt_of_le j.isLt hk⟩)))).re := by
    have h := congrArg Complex.re (htop.symm.trans hsplit)
    rwa [Complex.ofReal_re, Complex.add_re] at h
  rw [hfin]
  exact add_le_add hAle hBle

end MathlibExt.Analysis.InnerProductSpace.KyFanWanted
