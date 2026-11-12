/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexWidthFreeEnergy
import Code.FrontierD.SixVertexParticleHole
import Code.FrontierD.SixVertexBethePerronContinuation
import Code.FrontierD.SixVertexCoordinateBetheOne

open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexHalfFilledSectorTop_ge_two_add_pow
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N)
    {c : Real} (hc : 0 < c) :
    2 + c ^ N <= sixVertexSectorTopEigenvalue N n (by omega) c := by
  classical
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  let A := sixVertexSectorTransfer N n c
  let top := sixVertexSectorTopEigenvalue N n (by omega) c
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexSectorTop_exists_positive_eigenvector (by omega : n <= N) hc
  have hne : even ≠ odd :=
    (sixVertexInfinityGraph_adj_alternating hn hhalf.le).ne
  have hcross : A even odd = c ^ (2 * n) := by
    have hadj := sixVertexInfinityGraph_adj_alternating hn hhalf.le
    have hrowne : sixVertexSectorRow even ≠ sixVertexSectorRow odd :=
      fun h => hne (sixVertexSectorRow_injective h)
    change sixVertexTransfer N c (sixVertexSectorRow even)
      (sixVertexSectorRow odd) = c ^ (2 * n)
    rw [sixVertexTransfer, if_neg hrowne, if_pos hadj.2.1, hadj.2.2]
  have hcross' : A odd even = c ^ (2 * n) := by
    calc
      A odd even = A even odd :=
        sixVertexTransfer_symmetric N c
          (sixVertexSectorRow odd) (sixVertexSectorRow even)
      _ = c ^ (2 * n) := hcross
  have hdiagEven : A even even = 2 := by
    simp [A, sixVertexSectorTransfer, sixVertexTransfer]
  have hdiagOdd : A odd odd = 2 := by
    simp [A, sixVertexSectorTransfer, sixVertexTransfer]
  have hrowEven :
      2 * v even + c ^ (2 * n) * v odd <= (A *ᵥ fun i => v i) even := by
    rw [Matrix.mulVec, dotProduct]
    calc
      2 * v even + c ^ (2 * n) * v odd =
          ∑ i ∈ ({even, odd} : Finset (SixVertexSector N n)),
            A even i * v i := by
              simp [hne, hdiagEven, hcross]
      _ <= ∑ i, A even i * v i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro i _ _
        exact mul_nonneg (sixVertexSectorTransfer_nonneg hc.le even i)
          (hvpos i).le
  have hrowOdd :
      2 * v odd + c ^ (2 * n) * v even <= (A *ᵥ fun i => v i) odd := by
    rw [Matrix.mulVec, dotProduct]
    calc
      2 * v odd + c ^ (2 * n) * v even =
          ∑ i ∈ ({even, odd} : Finset (SixVertexSector N n)),
            A odd i * v i := by
              simp [hne, hdiagOdd, hcross', add_comm]
      _ <= ∑ i, A odd i * v i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro i _ _
        exact mul_nonneg (sixVertexSectorTransfer_nonneg hc.le odd i)
          (hvpos i).le
  have heven := congrFun hveig even
  have hodd := congrFun hveig odd
  change (A *ᵥ fun i => v i) even = top * v even at heven
  change (A *ᵥ fun i => v i) odd = top * v odd at hodd
  rw [heven] at hrowEven
  rw [hodd] at hrowOdd
  have ha : 0 < c ^ (2 * n) := pow_pos hc _
  have htop : 2 + c ^ (2 * n) <= top := by
    by_contra hnot
    have hlt : top - 2 < c ^ (2 * n) := by linarith
    have hltEven := mul_lt_mul_of_pos_right hlt (hvpos even)
    have hltOdd := mul_lt_mul_of_pos_right hlt (hvpos odd)
    have hoddEven : v odd < v even := by
      have hmul : c ^ (2 * n) * v odd < c ^ (2 * n) * v even := calc
        c ^ (2 * n) * v odd <= (top - 2) * v even := by linarith
        _ < c ^ (2 * n) * v even := hltEven
      exact lt_of_mul_lt_mul_left hmul ha.le
    have hevenOdd : v even < v odd := by
      have hmul : c ^ (2 * n) * v even < c ^ (2 * n) * v odd := calc
        c ^ (2 * n) * v even <= (top - 2) * v odd := by linarith
        _ < c ^ (2 * n) * v odd := hltOdd
      exact lt_of_mul_lt_mul_left hmul ha.le
    exact (lt_asymm hoddEven hevenOdd).elim
  simpa [hhalf] using htop


theorem sixVertexSectorTopEigenvalue_zero
    (N : Nat) {c : Real} (hc : 0 < c) :
    sixVertexSectorTopEigenvalue N 0 (Nat.zero_le N) c = 2 := by
  classical
  let x := sixVertexPackedSector N 0 (Nat.zero_le N)
  let A := sixVertexSectorTransfer N 0 c
  let top := sixVertexSectorTopEigenvalue N 0 (Nat.zero_le N) c
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexSectorTop_exists_positive_eigenvector (Nat.zero_le N) hc
  have hall (y : SixVertexSector N 0) : y = x := by
    apply Subtype.ext
    have hy : (y : Finset (Fin N)) = ∅ := Finset.card_eq_zero.mp y.2
    have hx : (x : Finset (Fin N)) = ∅ := Finset.card_eq_zero.mp x.2
    exact hy.trans hx.symm
  have hmul : (A *ᵥ fun i => v i) x = 2 * v x := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single x]
    · simp [A, sixVertexSectorTransfer, sixVertexTransfer]
    · intro y _ hyx
      exact (hyx (hall y)).elim
    · simp
  have hx := congrFun hveig x
  change (A *ᵥ fun i => v i) x = top * v x at hx
  rw [hmul] at hx
  exact (mul_right_cancel₀ (hvpos x).ne' hx.symm)



theorem sixVertexSectorTopEigenvalue_full
    (N : Nat) {c : Real} (hc : 0 < c) :
    sixVertexSectorTopEigenvalue N N (le_refl N) c = 2 := by
  calc
    sixVertexSectorTopEigenvalue N N (le_refl N) c =
        sixVertexSectorTopEigenvalue N 0 (Nat.zero_le N) c := by
      simpa using
        (sixVertexSectorTopEigenvalue_particleHole
          (N := N) (n := 0) (Nat.zero_le N) c)
    _ = 2 := sixVertexSectorTopEigenvalue_zero N hc




theorem sixVertexSectorTopEigenvalue_one
    {N : Nat} (hN : 0 < N) {c : Real} (hc : 0 < c) :
    sixVertexSectorTopEigenvalue N 1 (by omega) c =
      2 + (N - 1 : Nat) * c ^ 2 := by
  classical
  let v : SixVertexSector N 1 -> Real := fun _ => 1
  have hv : forall x, 0 < v x := by
    intro x
    simp [v]
  have hcard : Fintype.card (SixVertexSector N 1) = N := by
    simpa using Fintype.card_congr (sixVertexOneSectorEquiv N)
  have heig : sixVertexSectorTransfer N 1 c *ᵥ v =
      (2 + (N - 1 : Nat) * c ^ 2) • v := by
    funext x
    rw [Matrix.mulVec, dotProduct]
    have hsum :
        (∑ y : SixVertexSector N 1,
            (if x = y then 2 else c ^ 2) * v y) =
          2 + (N - 1 : Nat) * c ^ 2 := by
      calc
        _ = ∑ y : SixVertexSector N 1,
            ((if x = y then 2 - c ^ 2 else 0) + c ^ 2) := by
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hxy : x = y <;> simp [hxy, v]
        _ = 2 + (N - 1 : Nat) * c ^ 2 := by
              rw [Finset.sum_add_distrib]
              simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
                Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
              rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne')]
              push_cast
              ring
    simp_rw [sixVertexSectorTransfer_one_apply]
    rw [hsum]
    simp [v]
  exact (sixVertexSector_eigenvalue_eq_top_of_positive_eigenvector
    (N := N) (n := 1) (by omega) hc v hv heig).symm



theorem natCast_succ_le_real_pow_of_two_le
    {c : Real} (hc : 2 <= c) (k : Nat) :
    ((k + 1 : Nat) : Real) <= c ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        ((Nat.succ k + 1 : Nat) : Real) <=
            2 * ((k + 1 : Nat) : Real) := by
              push_cast
              have hk : (0 : Real) <= k := by positivity
              linarith
        _ <= c * ((k + 1 : Nat) : Real) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ <= c * c ^ k :=
          mul_le_mul_of_nonneg_left ih (by linarith)
        _ = c ^ Nat.succ k := by
          rw [pow_succ]
          ring



theorem sixVertexSectorTopEigenvalue_one_le_halfFilled
    {N : Nat} (hN : 4 <= N) (hhalf : 2 * (N / 2) = N)
    {c : Real} (hc : 0 < c) (hc2 : 2 <= c) :
    sixVertexSectorTopEigenvalue N 1 (by omega) c <=
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  have hhalfPos : 0 < N / 2 := by omega
  have hcentralLower : 2 + c ^ N <=
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
    simpa using sixVertexHalfFilledSectorTop_ge_two_add_pow
      hhalfPos hhalf hc
  obtain ⟨k, rfl⟩ : exists k : Nat, N = k + 2 := by
    exact ⟨N - 2, by omega⟩
  rw [sixVertexSectorTopEigenvalue_one (by omega) hc]
  apply le_trans _ hcentralLower
  gcongr
  have hcoeff := natCast_succ_le_real_pow_of_two_le hc2 k
  have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg c)
  norm_num at hmul ⊢
  calc
    ((k : Real) + 1) * c ^ 2 <= c ^ k * c ^ 2 := hmul
    _ = c ^ (k + 2) := by rw [pow_add]



def SixVertexStrictLowerHalfDominance (N : Nat) (c : Real) : Prop :=
  ∀ n : Nat, (hn0 : 0 < n) -> (hn : n < N / 2) ->
    sixVertexSectorTopEigenvalue N n
        (hn.le.trans (Nat.div_le_self N 2)) c <=
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c



def SixVertexStrictLowerHalfDominanceAboveOne (N : Nat) (c : Real) : Prop :=
  ∀ n : Nat, (hn1 : 1 < n) -> (hn : n < N / 2) ->
    sixVertexSectorTopEigenvalue N n
        (hn.le.trans (Nat.div_le_self N 2)) c <=
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c




theorem sixVertexWidthTopEigenvalue_eq_halfFilled_iff
    (N : Nat) (c : Real) :
    sixVertexWidthTopEigenvalue N c =
        sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c ↔
      ∀ m : Fin (N + 1),
        sixVertexWidthSectorTopEigenvalue N c m <=
          sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c := by
  constructor
  · intro h m
    exact (sixVertexWidthSectorTopEigenvalue_le N c m).trans_eq h
  · intro h
    obtain ⟨m, hm⟩ := sixVertexWidthTopEigenvalue_exists_sector N c
    apply le_antisymm
    · rw [← hm]
      exact h m
    · let middle : Fin (N + 1) := ⟨N / 2, by omega⟩
      have hmiddle := sixVertexWidthSectorTopEigenvalue_le N c middle
      simpa [sixVertexWidthSectorTopEigenvalue, middle] using hmiddle



theorem sixVertexWidthTopEigenvalue_eq_halfFilled_of_lowerHalf
    (N : Nat) (hN : Even N) (c : Real)
    (hdom : ∀ n : Nat, (hn : n <= N / 2) ->
      sixVertexSectorTopEigenvalue N n (hn.trans (Nat.div_le_self N 2)) c <=
        sixVertexSectorTopEigenvalue N (N / 2)
          (Nat.div_le_self N 2) c) :
    sixVertexWidthTopEigenvalue N c =
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  apply (sixVertexWidthTopEigenvalue_eq_halfFilled_iff N c).2
  intro m
  unfold sixVertexWidthSectorTopEigenvalue
  by_cases hm : m.val <= N / 2
  · exact hdom m.val hm
  · have hmN : m.val <= N := sixVertexWidthSectorIndex_le N m
    have hcomp : N - m.val <= N / 2 := by
      obtain ⟨k, hk⟩ := hN
      subst N
      omega
    have hparticle := sixVertexSectorTopEigenvalue_particleHole
      (N := N) (n := N - m.val) (Nat.sub_le N m.val) c
    have heq : sixVertexSectorTopEigenvalue N m.val hmN c =
        sixVertexSectorTopEigenvalue N (N - m.val)
          (Nat.sub_le N m.val) c := by
      simpa [Nat.sub_sub_self hmN] using hparticle
    rw [heq]
    exact hdom (N - m.val) hcomp



theorem sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalf
    (N : Nat) (hN : Even N) (hNpos : 0 < N)
    {c : Real} (hc : 0 < c)
    (hdom : SixVertexStrictLowerHalfDominance N c) :
    sixVertexWidthTopEigenvalue N c =
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  have hhalf : 2 * (N / 2) = N := Nat.two_mul_div_two_of_even hN
  have hhalfPos : 0 < N / 2 := by omega
  have hcentralLower : 2 + c ^ N <=
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
    simpa using sixVertexHalfFilledSectorTop_ge_two_add_pow
      hhalfPos hhalf hc
  apply sixVertexWidthTopEigenvalue_eq_halfFilled_of_lowerHalf N hN c
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    rw [sixVertexSectorTopEigenvalue_zero N hc]
    exact (le_add_of_nonneg_right (pow_nonneg hc.le N)).trans hcentralLower
  by_cases hnHalf : n = N / 2
  · subst n
    exact le_rfl
  · exact hdom n (Nat.pos_of_ne_zero hn0) (lt_of_le_of_ne hn hnHalf)




theorem sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalfAboveOne
    (N : Nat) (hN : Even N) (hN4 : 4 <= N)
    {c : Real} (hc : 0 < c) (hc2 : 2 <= c)
    (hdom : SixVertexStrictLowerHalfDominanceAboveOne N c) :
    sixVertexWidthTopEigenvalue N c =
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  apply sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalf
    N hN (by omega) hc
  intro n hn0 hn
  by_cases hn1 : n = 1
  · subst n
    exact sixVertexSectorTopEigenvalue_one_le_halfFilled hN4
      (Nat.two_mul_div_two_of_even hN) hc hc2
  · exact hdom n (by omega) hn

end

end StatMech.FrontierD
