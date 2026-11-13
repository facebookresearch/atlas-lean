/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFiniteRoots










open Finset

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexTheta_zero_pair (c q : Real) :
    sixVertexTheta c 0 q + sixVertexTheta c 0 (-q) = 0 := by
  have h := sixVertexTheta_neg c 0 q
  norm_num at h
  linarith



theorem sixVertexTheta_symmetric_pair_bounds
    {c x : Real} (hc : 2 < c) (hx : 0 < x) (hxpi : x < Real.pi)
    (q : Real) :
    -2 * Real.pi <
        sixVertexTheta c x q + sixVertexTheta c x (-q) ∧
      sixVertexTheta c x q + sixVertexTheta c x (-q) < 0 := by
  have hqLower := strictAnti_sixVertexTheta_left hc q hxpi
  have hnqLower := strictAnti_sixVertexTheta_left hc (-q) hxpi
  have hqUpper := strictAnti_sixVertexTheta_left hc q hx
  have hnqUpper := strictAnti_sixVertexTheta_left hc (-q) hx
  have hpi := sixVertexTheta_pi_pair c q
  have hzero := sixVertexTheta_zero_pair c q
  constructor <;> linarith



theorem sum_sixVertexTheta_symmetric_bounds
    {c x : Real} (hc : 2 < c) {n : Nat} (hn : 0 < n)
    {p : Fin n -> Real} (hsymm : SixVertexRootSymmetric p)
    (hx : 0 < x) (hxpi : x < Real.pi) :
    -(n : Real) * Real.pi <
        ∑ k, sixVertexTheta c x (p k) ∧
      ∑ k, sixVertexTheta c x (p k) < 0 := by
  let S := ∑ k, sixVertexTheta c x (p k)
  have hrev : (∑ k : Fin n, sixVertexTheta c x (p k.rev)) = S := by
    apply Fintype.sum_equiv Fin.revPerm
    intro k
    rfl
  have hpair :
      S + S = ∑ k, (sixVertexTheta c x (p k) +
        sixVertexTheta c x (-p k)) := by
    calc
      S + S = S + ∑ k : Fin n, sixVertexTheta c x (p k.rev) := by
        rw [hrev]
      _ = S + ∑ k : Fin n, sixVertexTheta c x (-p k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [hsymm]
      _ = _ := Finset.sum_add_distrib.symm
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hlower :
      (∑ _k : Fin n, -2 * Real.pi) <
        ∑ k, (sixVertexTheta c x (p k) +
          sixVertexTheta c x (-p k)) := by
    apply Finset.sum_lt_sum
    · intro k _
      exact (sixVertexTheta_symmetric_pair_bounds hc hx hxpi (p k)).1.le
    · obtain ⟨k, hk⟩ := hnonempty
      exact ⟨k, hk,
        (sixVertexTheta_symmetric_pair_bounds hc hx hxpi (p k)).1⟩
  have hupper :
      (∑ k, (sixVertexTheta c x (p k) +
          sixVertexTheta c x (-p k))) <
        ∑ _k : Fin n, (0 : Real) := by
    apply Finset.sum_lt_sum
    · intro k _
      exact (sixVertexTheta_symmetric_pair_bounds hc hx hxpi (p k)).2.le
    · obtain ⟨k, hk⟩ := hnonempty
      exact ⟨k, hk,
        (sixVertexTheta_symmetric_pair_bounds hc hx hxpi (p k)).2⟩
  simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hlower hupper
  dsimp only [S] at hpair ⊢
  constructor <;> nlinarith





theorem sixVertexPositiveHalfBetheRoots_quantile_upper
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    sixVertexPositiveHalfBetheRoots hc k j <
      Real.pi / 2 +
        Real.pi * (2 * (j : Real) + 1) /
          (sixVertexFourWidth 0 k : Real) := by
  let m := k + 1
  let i : Fin (m + m) := Fin.natAdd m j
  let p := sixVertexHalfFilledBetheRoots hc k
  have hp : 0 < p i := by
    simpa [p, i, m, sixVertexPositiveHalfBetheRoots] using
      sixVertexPositiveHalfBetheRoots_pos hc k j
  have hpPi : p i < Real.pi := by
    simpa [p, i, m, sixVertexPositiveHalfBetheRoots] using
      sixVertexPositiveHalfBetheRoots_lt_pi hc k j
  have hsum := sum_sixVertexTheta_symmetric_bounds hc (n := m + m)
    (by simp [m]) (sixVertexHalfFilledBetheRoots_mem_open hc k).2.1 hp hpPi
  have hroot := sixVertexHalfFilledBetheRoots_is_solution hc k i
  have hquantum : sixVertexCentralQuantumNumber i = (j : Real) + 1 / 2 := by
    rw [sixVertexCentralQuantumNumber_eq]
    dsimp [i, m]
    push_cast
    ring
  rw [hquantum] at hroot
  change (sixVertexFourWidth 0 k : Real) * p i =
    2 * Real.pi * ((j : Real) + 1 / 2) -
      ∑ q, sixVertexTheta c (p i) (p q) at hroot
  have hN : (0 : Real) < sixVertexFourWidth 0 k := by
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hsumLower :
      -(2 * (k + 1 : Real)) * Real.pi <
        ∑ q, sixVertexTheta c (p i) (p q) := by
    calc
      -(2 * (k + 1 : Real)) * Real.pi =
          -((m + m : Nat) : Real) * Real.pi := by
        push_cast
        simp [m]
        ring
      _ < ∑ q, sixVertexTheta c (p i) (p q) := by
        simpa [p] using hsum.1
  have hwidth : (sixVertexFourWidth 0 k : Real) = 4 * (k + 1 : Real) := by
    simp [sixVertexFourWidth]
  have hbound : p i <
      Real.pi / 2 +
        Real.pi * (2 * (j : Real) + 1) /
          (sixVertexFourWidth 0 k : Real) := by
    rw [hwidth] at hroot hN ⊢
    rw [← sub_lt_iff_lt_add', lt_div_iff₀ hN]
    nlinarith [Real.pi_pos]
  simpa [p, i, m, sixVertexPositiveHalfBetheRoots] using hbound

end

end StatMech.FrontierD
