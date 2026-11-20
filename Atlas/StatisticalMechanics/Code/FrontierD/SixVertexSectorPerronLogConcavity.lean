/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexCentralSectorDominance










open Finset Matrix Filter Topology

namespace StatMech.FrontierD

noncomputable section



noncomputable def sixVertexSectorPerronProfile
    (N : Nat) (c : Real) (n : Nat) : Real :=
  sixVertexSectorTopEigenvalue N (min n N) (min_le_right n N) c

theorem sixVertexSectorPerronProfile_eq
    {N n : Nat} (hn : n <= N) (c : Real) :
    sixVertexSectorPerronProfile N c n =
      sixVertexSectorTopEigenvalue N n hn c := by
  simp [sixVertexSectorPerronProfile, min_eq_left hn]

theorem sixVertexSectorPerronProfile_pos
    {N n : Nat} (hn : n <= N) {c : Real} (hc : 0 < c) :
    0 < sixVertexSectorPerronProfile N c n := by
  rw [sixVertexSectorPerronProfile_eq hn]
  exact sixVertexSectorTopEigenvalue_pos hn hc

theorem sixVertexSectorPerronProfile_particleHole
    {N n : Nat} (hn : n <= N) (c : Real) :
    sixVertexSectorPerronProfile N c (N - n) =
      sixVertexSectorPerronProfile N c n := by
  rw [sixVertexSectorPerronProfile_eq (Nat.sub_le N n),
    sixVertexSectorPerronProfile_eq hn]
  exact sixVertexSectorTopEigenvalue_particleHole hn c


def SixVertexSectorPerronLogConcave (N : Nat) (c : Real) : Prop :=
  forall n : Nat, 0 < n -> n < N ->
    sixVertexSectorPerronProfile N c (n - 1) *
        sixVertexSectorPerronProfile N c (n + 1) <=
      sixVertexSectorPerronProfile N c n ^ 2


noncomputable def sixVertexSectorTraceProfile
    (N M : Nat) (c : Real) (n : Nat) : Real :=
  Matrix.trace
    (sixVertexSectorTransfer N (min n N) c ^ M)

theorem sixVertexSectorTraceProfile_eq
    {N M n : Nat} (hn : n <= N) (c : Real) :
    sixVertexSectorTraceProfile N M c n =
      Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  unfold sixVertexSectorTraceProfile
  rw [min_eq_left hn]



def SixVertexSectorTraceLogConcave (N : Nat) (c : Real) : Prop :=
  forall M n : Nat, 0 < M -> 0 < n -> n < N ->
    sixVertexSectorTraceProfile N M c (n - 1) *
        sixVertexSectorTraceProfile N M c (n + 1) <=
      sixVertexSectorTraceProfile N M c n ^ 2



theorem sixVertexSectorPerronLogConcave_of_traceLogConcave
    (N : Nat) {c : Real} (hc : 0 < c)
    (htrace : SixVertexSectorTraceLogConcave N c) :
    SixVertexSectorPerronLogConcave N c := by
  intro n hn0 hnN
  have hprev : n - 1 <= N := by omega
  have hmid : n <= N := hnN.le
  have hnext : n + 1 <= N := by omega
  let fprev : Nat -> Real := fun M =>
    Real.log (sixVertexSectorTraceProfile N M c (n - 1)) / (M : Real)
  let fmid : Nat -> Real := fun M =>
    Real.log (sixVertexSectorTraceProfile N M c n) / (M : Real)
  let fnext : Nat -> Real := fun M =>
    Real.log (sixVertexSectorTraceProfile N M c (n + 1)) / (M : Real)
  have hprevLim : Tendsto fprev atTop
      (nhds (Real.log (sixVertexSectorPerronProfile N c (n - 1)))) := by
    simpa [fprev, sixVertexSectorTraceProfile_eq hprev,
      sixVertexSectorPerronProfile_eq hprev] using
      (sixVertexSector_log_trace_div_height_tendsto_log_top hprev hc)
  have hmidLim : Tendsto fmid atTop
      (nhds (Real.log (sixVertexSectorPerronProfile N c n))) := by
    simpa [fmid, sixVertexSectorTraceProfile_eq hmid,
      sixVertexSectorPerronProfile_eq hmid] using
      (sixVertexSector_log_trace_div_height_tendsto_log_top hmid hc)
  have hnextLim : Tendsto fnext atTop
      (nhds (Real.log (sixVertexSectorPerronProfile N c (n + 1)))) := by
    simpa [fnext, sixVertexSectorTraceProfile_eq hnext,
      sixVertexSectorPerronProfile_eq hnext] using
      (sixVertexSector_log_trace_div_height_tendsto_log_top hnext hc)
  have hevent : ∀ᶠ M in atTop, fprev M + fnext M <= 2 * fmid M := by
    filter_upwards [eventually_gt_atTop (0 : Nat)] with M hM
    change 0 < M at hM
    have hp : 0 < sixVertexSectorTraceProfile N M c (n - 1) := by
      rw [sixVertexSectorTraceProfile_eq hprev]
      exact sixVertexSector_trace_pow_pos hprev hc M
    have hm : 0 < sixVertexSectorTraceProfile N M c n := by
      rw [sixVertexSectorTraceProfile_eq hmid]
      exact sixVertexSector_trace_pow_pos hmid hc M
    have hn : 0 < sixVertexSectorTraceProfile N M c (n + 1) := by
      rw [sixVertexSectorTraceProfile_eq hnext]
      exact sixVertexSector_trace_pow_pos hnext hc M
    have hprod := htrace M n hM hn0 hnN
    have hlog :
        Real.log (sixVertexSectorTraceProfile N M c (n - 1)) +
            Real.log (sixVertexSectorTraceProfile N M c (n + 1)) <=
          2 * Real.log (sixVertexSectorTraceProfile N M c n) := by
      calc
        _ = Real.log (sixVertexSectorTraceProfile N M c (n - 1) *
              sixVertexSectorTraceProfile N M c (n + 1)) :=
          (Real.log_mul hp.ne' hn.ne').symm
        _ <= Real.log (sixVertexSectorTraceProfile N M c n ^ 2) :=
          Real.log_le_log (mul_pos hp hn) hprod
        _ = _ := by rw [Real.log_pow]; norm_num
    have hMreal : (0 : Real) < M := by exact_mod_cast hM
    have hdiv := (div_le_div_iff_of_pos_right hMreal).2 hlog
    calc
      fprev M + fnext M =
          (Real.log (sixVertexSectorTraceProfile N M c (n - 1)) +
            Real.log (sixVertexSectorTraceProfile N M c (n + 1))) /
              (M : Real) := by dsimp [fprev, fnext]; ring
      _ <= 2 * Real.log (sixVertexSectorTraceProfile N M c n) /
          (M : Real) := hdiv
      _ = 2 * fmid M := by dsimp [fmid]; ring
  have hlogConcave :
      Real.log (sixVertexSectorPerronProfile N c (n - 1)) +
          Real.log (sixVertexSectorPerronProfile N c (n + 1)) <=
        2 * Real.log (sixVertexSectorPerronProfile N c n) := by
    exact le_of_tendsto_of_tendsto
      (hprevLim.add hnextLim) (tendsto_const_nhds.mul hmidLim) hevent
  have hp := sixVertexSectorPerronProfile_pos hprev hc
  have hm := sixVertexSectorPerronProfile_pos hmid hc
  have hn := sixVertexSectorPerronProfile_pos hnext hc
  have hlogProduct :
      Real.log (sixVertexSectorPerronProfile N c (n - 1) *
          sixVertexSectorPerronProfile N c (n + 1)) <=
        Real.log (sixVertexSectorPerronProfile N c n ^ 2) := by
    rw [Real.log_mul hp.ne' hn.ne', Real.log_pow]
    exact hlogConcave
  exact (Real.log_le_log_iff (mul_pos hp hn) (pow_pos hm 2)).1 hlogProduct


theorem adjacentRatio_antitone_of_pos_logConcave
    (a : Nat -> Real) (N : Nat)
    (hpos : forall n, n <= N -> 0 < a n)
    (hlc : forall n, 0 < n -> n < N ->
      a (n - 1) * a (n + 1) <= a n ^ 2)
    {i j : Nat} (hij : i <= j) (hj : j < N) :
    a (j + 1) / a j <= a (i + 1) / a i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      have hjN : j < N := by omega
      have hj1N : j + 1 < N := by omega
      have hlocal := hlc (j + 1) (by omega) hj1N
      have hratio : a (j + 2) / a (j + 1) <= a (j + 1) / a j := by
        rw [div_le_div_iff₀ (hpos (j + 1) (by omega))
          (hpos j (by omega))]
        simpa [pow_two, Nat.add_sub_cancel, mul_comm] using hlocal
      exact hratio.trans (ih hjN)



theorem adjacent_le_of_pos_logConcave_symmetric
    (a : Nat -> Real) (N : Nat) (hN : Even N)
    (hpos : forall n, n <= N -> 0 < a n)
    (hsym : forall n, n <= N -> a (N - n) = a n)
    (hlc : forall n, 0 < n -> n < N ->
      a (n - 1) * a (n + 1) <= a n ^ 2)
    {i : Nat} (hi : i < N / 2) :
    a i <= a (i + 1) := by
  let j := N - 1 - i
  have hiN : i <= N := by omega
  have hi1N : i + 1 <= N := by omega
  have hjN : j < N := by
    dsimp [j]
    omega
  have hij : i <= j := by
    obtain ⟨m, rfl⟩ := hN
    dsimp [j] at *
    omega
  have hratio := adjacentRatio_antitone_of_pos_logConcave
    a N hpos hlc hij hjN
  have hjEq : a (j + 1) = a i := by
    rw [← hsym i hiN]
    congr 1
    dsimp [j]
    omega
  have hjPrevEq : a j = a (i + 1) := by
    rw [← hsym (i + 1) hi1N]
    congr 1
    dsimp [j]
    omega
  rw [hjEq, hjPrevEq] at hratio
  rw [div_le_div_iff₀ (hpos (i + 1) hi1N) (hpos i hiN)] at hratio
  have hsquares : a i ^ 2 <= a (i + 1) ^ 2 := by
    simpa [pow_two] using hratio
  exact (sq_le_sq₀ (hpos i hiN).le (hpos (i + 1) hi1N).le).1 hsquares


theorem lowerHalf_le_middle_of_pos_logConcave_symmetric
    (a : Nat -> Real) (N : Nat) (hN : Even N)
    (hpos : forall n, n <= N -> 0 < a n)
    (hsym : forall n, n <= N -> a (N - n) = a n)
    (hlc : forall n, 0 < n -> n < N ->
      a (n - 1) * a (n + 1) <= a n ^ 2)
    {i : Nat} (hi : i <= N / 2) :
    a i <= a (N / 2) := by
  let middle := N / 2
  change a i <= a middle
  have hiMiddle : i <= middle := hi
  refine Nat.decreasingInduction (n := middle) ?_ le_rfl hiMiddle
  intro j hj ih
  exact (adjacent_le_of_pos_logConcave_symmetric
    a N hN hpos hsym hlc (by
      dsimp [middle] at *
      omega)).trans ih



theorem sixVertexSectorPerronProfile_lowerHalf_le_middle_of_logConcave
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hlc : SixVertexSectorPerronLogConcave N c)
    (n : Nat) (hn : n <= N / 2) :
    sixVertexSectorTopEigenvalue N n
        (hn.trans (Nat.div_le_self N 2)) c <=
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  let a := sixVertexSectorPerronProfile N c
  have hpos : forall m, m <= N -> 0 < a m := by
    intro m hm
    exact sixVertexSectorPerronProfile_pos hm hc
  have hsym : forall m, m <= N -> a (N - m) = a m := by
    intro m hm
    exact sixVertexSectorPerronProfile_particleHole hm c
  have hmono := lowerHalf_le_middle_of_pos_logConcave_symmetric
    a N hN hpos hsym hlc (i := n) hn
  simpa [a, sixVertexSectorPerronProfile_eq
    (hn.trans (Nat.div_le_self N 2)),
    sixVertexSectorPerronProfile_eq (Nat.div_le_self N 2)] using hmono



theorem sixVertexWidthTopEigenvalue_eq_halfFilled_of_logConcave
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hlc : SixVertexSectorPerronLogConcave N c) :
    sixVertexWidthTopEigenvalue N c =
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  apply sixVertexWidthTopEigenvalue_eq_halfFilled_of_lowerHalf N hN c
  intro n hn
  exact sixVertexSectorPerronProfile_lowerHalf_le_middle_of_logConcave
    N hN hc hlc n hn

end

end StatMech.FrontierD
