/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib











namespace StatMech.FrontierD



def IntUnitSteps (f : Nat → Int) : Prop :=
  ∀ n, f (n + 1) ≤ f n + 1 ∧ f n ≤ f (n + 1) + 1


theorem exists_eq_of_intUnitSteps_between
    {f : Nat → Int} (hstep : IntUnitSteps f)
    {a b : Nat} (hab : a ≤ b) {r : Int}
    (har : f a ≤ r) (hrb : r ≤ f b) :
    ∃ n, a ≤ n ∧ n ≤ b ∧ f n = r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero =>
      refine ⟨a, le_rfl, le_rfl, ?_⟩
      simpa using (le_antisymm hrb har).symm
  | succ d ih =>
      by_cases hprev : r ≤ f (a + d)
      · obtain ⟨n, han, hnb, hn⟩ := ih (by omega) hprev
        exact ⟨n, han, hnb.trans (by omega), hn⟩
      · refine ⟨a + (d + 1), by omega, le_rfl, ?_⟩
        have hs := hstep (a + d)
        have hindex : a + d + 1 = a + (d + 1) := by omega
        rw [hindex] at hs
        omega



theorem exists_intUnitStep_bracketedPlateau
    {f : Nat → Int} (hstep : IntUnitSteps f)
    (hzero : f 0 = 0) {N : Nat} {r : Int}
    (hr : 0 < r) (hreach : r + 1 ≤ f N) :
    ∃ a b : Nat,
      0 < a ∧ a ≤ b ∧ b < N ∧
        f (a - 1) = r - 1 ∧
        (∀ n, a ≤ n → n ≤ b → f n = r) ∧
        (∀ n < b + 1, f n < r + 1) ∧
        f (b + 1) = r + 1 := by
  classical
  have hhit : ∃ n : Nat, n ≤ N ∧ f n = r + 1 := by
    obtain ⟨n, h0n, hnN, hn⟩ :=
      exists_eq_of_intUnitSteps_between hstep (a := 0) (b := N)
        (r := r + 1)
        (Nat.zero_le N) (by rw [hzero]; omega) hreach
    exact ⟨n, hnN, hn⟩
  let t := Nat.find hhit
  have htSpec : t ≤ N ∧ f t = r + 1 := Nat.find_spec hhit
  have htpos : 0 < t := by
    by_contra ht
    push Not at ht
    have : t = 0 := by omega
    rw [this, hzero] at htSpec
    omega
  have hbefore : ∀ n < t, f n < r + 1 := by
    intro n hnt
    by_contra hn
    push Not at hn
    obtain ⟨m, h0m, hmn, hm⟩ :=
      exists_eq_of_intUnitSteps_between hstep (a := 0) (b := n)
        (r := r + 1) (Nat.zero_le n) (by rw [hzero]; omega) hn
    have hmN : m ≤ N := hmn.trans (hnt.le.trans htSpec.1)
    have htlem : t ≤ m := Nat.find_min' hhit ⟨hmN, hm⟩
    omega
  let S : Finset Nat := (Finset.range t).filter fun n => f n = r
  have hSne : S.Nonempty := by
    obtain ⟨n, h0n, hnt, hn⟩ :=
      exists_eq_of_intUnitSteps_between hstep (a := 0) (b := t)
        (r := r) (Nat.zero_le t) (by rw [hzero]; omega)
        (by rw [htSpec.2]; omega)
    have hne : n ≠ t := by
      intro h
      subst n
      omega
    have hnlt : n < t := Nat.lt_of_le_of_ne hnt hne
    exact ⟨n, by simp [S, hnlt, hn]⟩
  let b := S.max' hSne
  have hbmem : b ∈ S := S.max'_mem hSne
  have hbmem' : b < t ∧ f b = r := by simpa [S] using hbmem
  have hbt : b < t := hbmem'.1
  have hbr : f b = r := hbmem'.2
  have hnoAfter : ∀ n, b < n → n < t → f n ≠ r := by
    intro n hbn hnt hnr
    have hnS : n ∈ S := by simp [S, hnt, hnr]
    have hle : n ≤ b := S.le_max' n hnS
    omega
  have htEq : t = b + 1 := by
    by_contra hne
    have hb1t : b + 1 < t := by omega
    have hb1lt : f (b + 1) < r := by
      have hlt := hbefore (b + 1) hb1t
      have hneR := hnoAfter (b + 1) (by omega) hb1t
      omega
    obtain ⟨m, hbm, hmt, hm⟩ :=
      exists_eq_of_intUnitSteps_between hstep (a := b + 1) (b := t)
        (r := r) (by omega) (by omega) (by rw [htSpec.2]; omega)
    have hmlt : m < t := by
      by_contra h
      have : m = t := by omega
      subst m
      omega
    exact hnoAfter m (by omega) hmlt hm
  have hbN : b < N := by omega
  have hbnext : f (b + 1) = r + 1 := by
    rw [← htEq]
    exact htSpec.2
  let A : Finset Nat := (Finset.range (b + 1)).filter fun n =>
    ∀ m, n ≤ m → m ≤ b → f m = r
  have hbA : b ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    intro m hbm hmb
    have : m = b := by omega
    simpa [this] using hbr
  have hAne : A.Nonempty := ⟨b, hbA⟩
  let a := A.min' hAne
  have hamem : a ∈ A := A.min'_mem hAne
  have hab : a ≤ b := by
    exact A.min'_le b hbA
  have hamem' : a < b + 1 ∧
      ∀ m, a ≤ m → m ≤ b → f m = r := by
    simpa [A] using hamem
  have haPlateau : ∀ n, a ≤ n → n ≤ b → f n = r := by
    exact hamem'.2
  have har : f a = r := haPlateau a le_rfl hab
  have hapos : 0 < a := by
    by_contra ha
    push Not at ha
    have : a = 0 := by omega
    rw [this, hzero] at har
    omega
  have hprevNe : f (a - 1) ≠ r := by
    intro hprev
    have hap : a - 1 < b + 1 := by omega
    have hprevA : a - 1 ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_range]
      refine ⟨hap, ?_⟩
      intro m hpm hmb
      by_cases hm : m = a - 1
      · simpa [hm] using hprev
      · apply haPlateau m
        · omega
        · exact hmb
    have hale : a ≤ a - 1 := A.min'_le (a - 1) hprevA
    omega
  have hprevlt : f (a - 1) < r + 1 := by
    apply hbefore
    omega
  have hprev : f (a - 1) = r - 1 := by
    have hs := hstep (a - 1)
    have hidx : a - 1 + 1 = a := by omega
    rw [hidx, har] at hs
    omega
  have hfirst : ∀ n < b + 1, f n < r + 1 := by
    intro n hn
    apply hbefore n
    omega
  exact ⟨a, b, hapos, hab, hbN, hprev, haPlateau, hfirst, hbnext⟩

end StatMech.FrontierD
