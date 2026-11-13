/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalResidualCompletions









namespace StatMech.FrontierD

noncomputable section

theorem natChoose_logConcave_of_pos (n k : Nat) (hk : 0 < k) :
    Nat.choose n (k - 1) * Nat.choose n (k + 1) <=
      Nat.choose n k * Nat.choose n k := by
  by_cases hkn : k <= n
  · have hprev : Nat.choose n (k - 1) * (n - (k - 1)) =
        Nat.choose n k * k := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simpa using (Nat.choose_succ_right_eq n j).symm
    have hnext : Nat.choose n (k + 1) * (k + 1) =
        Nat.choose n k * (n - k) :=
      Nat.choose_succ_right_eq n k
    have hsub : n - (k - 1) = n - k + 1 := by omega
    have hfactor : k * (n - k) <= (n - (k - 1)) * (k + 1) := by
      rw [hsub]
      nlinarith
    have hbig : 0 < (n - (k - 1)) * (k + 1) := by
      rw [hsub]
      positivity
    have heq :
        (Nat.choose n (k - 1) * Nat.choose n (k + 1)) *
            ((n - (k - 1)) * (k + 1)) =
          (Nat.choose n k * Nat.choose n k) * (k * (n - k)) := by
      calc
        _ = (Nat.choose n (k - 1) * (n - (k - 1))) *
              (Nat.choose n (k + 1) * (k + 1)) := by ring
        _ = (Nat.choose n k * k) * (Nat.choose n k * (n - k)) := by
          rw [hprev, hnext]
        _ = _ := by ring
    have hmul :
        (Nat.choose n (k - 1) * Nat.choose n (k + 1)) *
            ((n - (k - 1)) * (k + 1)) <=
          (Nat.choose n k * Nat.choose n k) *
            ((n - (k - 1)) * (k + 1)) := by
      rw [heq]
      exact Nat.mul_le_mul_left _ hfactor
    exact Nat.le_of_mul_le_mul_right hmul hbig
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    rw [Nat.choose_eq_zero_of_lt hnk,
      Nat.choose_eq_zero_of_lt (hnk.trans_le (Nat.le_add_right k 1))]
    simp

def sixVertexHorizontalLowerSector
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hpos : 0 < middle.val) : Fin (T.width + 1) :=
  ⟨middle.val - 1, by omega⟩

def sixVertexHorizontalUpperSector
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hlt : middle.val < T.width) : Fin (T.width + 1) :=
  ⟨middle.val + 1, by omega⟩

theorem sixVertexHorizontalProfileChooseCount_logConcave
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hpos : 0 < middle.val) (hlt : middle.val < T.width)
    (profile : Option (SixVertexHorizontalCompletionProfile T)) :
    sixVertexHorizontalProfileChooseCount
          (sixVertexHorizontalLowerSector middle hpos) profile *
        sixVertexHorizontalProfileChooseCount
          (sixVertexHorizontalUpperSector middle hlt) profile <=
      sixVertexHorizontalProfileChooseCount middle profile *
        sixVertexHorizontalProfileChooseCount middle profile := by
  cases profile with
  | none => rfl
  | some profile =>
      unfold sixVertexHorizontalProfileChooseCount
        sixVertexHorizontalLowerSector sixVertexHorizontalUpperSector
      change
        (if profile.forcedTrue.val <= middle.val - 1 then
            Nat.choose profile.free.val
              (middle.val - 1 - profile.forcedTrue.val) else 0) *
          (if profile.forcedTrue.val <= middle.val + 1 then
            Nat.choose profile.free.val
              (middle.val + 1 - profile.forcedTrue.val) else 0) <=
        (if profile.forcedTrue.val <= middle.val then
            Nat.choose profile.free.val
              (middle.val - profile.forcedTrue.val) else 0) *
          (if profile.forcedTrue.val <= middle.val then
            Nat.choose profile.free.val
              (middle.val - profile.forcedTrue.val) else 0)
      by_cases hforced : profile.forcedTrue.val <= middle.val - 1
      · have hforcedMiddle : profile.forcedTrue.val <= middle.val := by omega
        have hforcedUpper : profile.forcedTrue.val <= middle.val + 1 := by omega
        rw [if_pos hforced, if_pos hforcedUpper, if_pos hforcedMiddle]
        have hk : 0 < middle.val - profile.forcedTrue.val := by omega
        have hlower : middle.val - 1 - profile.forcedTrue.val =
            (middle.val - profile.forcedTrue.val) - 1 := by omega
        have hupper : middle.val + 1 - profile.forcedTrue.val =
            (middle.val - profile.forcedTrue.val) + 1 := by omega
        rw [hlower, hupper]
        exact natChoose_logConcave_of_pos _ _ hk
      · rw [if_neg hforced]
        simp

theorem sixVertexHorizontalDiagonalProfileDeficit_eq_zero
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hpos : 0 < middle.val) (hlt : middle.val < T.width)
    (profile : Option (SixVertexHorizontalCompletionProfile T)) :
    sixVertexHorizontalProfileDeficit
        (sixVertexHorizontalLowerSector middle hpos)
        (sixVertexHorizontalUpperSector middle hlt) middle middle
        (profile, profile) = 0 := by
  rw [sixVertexHorizontalProfileDeficit_eq_sub]
  unfold sixVertexHorizontalPairProfileChooseWeight
  exact Nat.sub_eq_zero_of_le
    (sixVertexHorizontalProfileChooseCount_logConcave
      middle hpos hlt profile)

theorem sixVertexHorizontalActualDeficitToken_profiles_ne
    {T : EvenTorus} {grade : Nat × Nat}
    (middle : Fin (T.width + 1))
    (hpos : 0 < middle.val) (hlt : middle.val < T.width)
    (token : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hpos)
      (sixVertexHorizontalUpperSector middle hlt) middle middle) :
    token.1.1 ≠ token.1.2 := by
  intro heq
  have hpositive : 0 < sixVertexHorizontalProfileDeficit
      (sixVertexHorizontalLowerSector middle hpos)
      (sixVertexHorizontalUpperSector middle hlt) middle middle token.1 := by
    have hindex := token.2.2.isLt
    omega
  have hpair : token.1 = (token.1.1, token.1.1) := by
    apply Prod.ext
    · rfl
    · exact heq.symm
  rw [hpair, sixVertexHorizontalDiagonalProfileDeficit_eq_zero
    middle hpos hlt token.1.1] at hpositive
  omega

end

end StatMech.FrontierD
