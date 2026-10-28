/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact acyclic path-parent data, assembled from independently checked bounded source blocks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData14

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact earlier path and source letter of each of the 1795 actual auxiliary definitions. -/
def y522TPathData (i : Fin 1795) : ℕ × Fin 11 :=
  if h : i.val < 128 then y522TPathData00 ⟨i.val - 0, by omega⟩
  else if h : i.val < 256 then y522TPathData01 ⟨i.val - 128, by omega⟩
  else if h : i.val < 384 then y522TPathData02 ⟨i.val - 256, by omega⟩
  else if h : i.val < 512 then y522TPathData03 ⟨i.val - 384, by omega⟩
  else if h : i.val < 640 then y522TPathData04 ⟨i.val - 512, by omega⟩
  else if h : i.val < 768 then y522TPathData05 ⟨i.val - 640, by omega⟩
  else if h : i.val < 896 then y522TPathData06 ⟨i.val - 768, by omega⟩
  else if h : i.val < 1024 then y522TPathData07 ⟨i.val - 896, by omega⟩
  else if h : i.val < 1152 then y522TPathData08 ⟨i.val - 1024, by omega⟩
  else if h : i.val < 1280 then y522TPathData09 ⟨i.val - 1152, by omega⟩
  else if h : i.val < 1408 then y522TPathData10 ⟨i.val - 1280, by omega⟩
  else if h : i.val < 1536 then y522TPathData11 ⟨i.val - 1408, by omega⟩
  else if h : i.val < 1664 then y522TPathData12 ⟨i.val - 1536, by omega⟩
  else if h : i.val < 1792 then y522TPathData13 ⟨i.val - 1664, by omega⟩
  else y522TPathData14 ⟨i.val - 1792, by omega⟩

private theorem y522TPath_shift {size offset : ℕ} (data : Fin size → ℕ × Fin 11)
    (hd : ∀ j, 0 < offset + j.val → (data j).1 < offset + j.val)
    (i : Fin 1795) (ho : offset ≤ i.val) (hu : i.val < offset + size) (hi : i ≠ 0) :
    (data ⟨i.val - offset, by omega⟩).1 < i.val := by
  let j : Fin size := ⟨i.val - offset, by omega⟩
  change (data j).1 < i.val
  have he : offset + j.val = i.val := by dsimp only [j]; omega
  have hp : 0 < i.val := by
    have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
    omega
  have h := hd j (by rw [he]; exact hp)
  simpa only [he] using h

/-- Every nonempty auxiliary path refers strictly to an earlier actual path. -/
theorem y522TPathData_prior (i : Fin 1795) (hi : i ≠ 0) :
    (y522TPathData i).1 < i.val := by
  by_cases h0 : i.val < 128
  · unfold y522TPathData
    rw [dite_eq_left h0]
    exact y522TPath_shift
      y522TPathData00 y522TPathData00_prior i
      (by omega) (by omega) hi
  · by_cases h1 : i.val < 256
    · unfold y522TPathData
      rw [dite_eq_right h0, dite_eq_left h1]
      exact y522TPath_shift
        y522TPathData01 y522TPathData01_prior i
        (by omega) (by omega) hi
    · by_cases h2 : i.val < 384
      · unfold y522TPathData
        rw [dite_eq_right h0, dite_eq_right h1,
          dite_eq_left h2]
        exact y522TPath_shift
          y522TPathData02 y522TPathData02_prior i
          (by omega) (by omega) hi
      · by_cases h3 : i.val < 512
        · unfold y522TPathData
          rw [dite_eq_right h0, dite_eq_right h1,
            dite_eq_right h2, dite_eq_left h3]
          exact y522TPath_shift
            y522TPathData03 y522TPathData03_prior i
            (by omega) (by omega) hi
        · by_cases h4 : i.val < 640
          · unfold y522TPathData
            rw [dite_eq_right h0, dite_eq_right h1,
              dite_eq_right h2, dite_eq_right h3,
              dite_eq_left h4]
            exact y522TPath_shift
              y522TPathData04 y522TPathData04_prior i
              (by omega) (by omega) hi
          · by_cases h5 : i.val < 768
            · unfold y522TPathData
              rw [dite_eq_right h0, dite_eq_right h1,
                dite_eq_right h2, dite_eq_right h3,
                dite_eq_right h4, dite_eq_left h5]
              exact y522TPath_shift
                y522TPathData05 y522TPathData05_prior i
                (by omega) (by omega) hi
            · by_cases h6 : i.val < 896
              · unfold y522TPathData
                rw [dite_eq_right h0, dite_eq_right h1,
                  dite_eq_right h2, dite_eq_right h3,
                  dite_eq_right h4, dite_eq_right h5,
                  dite_eq_left h6]
                exact y522TPath_shift
                  y522TPathData06 y522TPathData06_prior i
                  (by omega) (by omega) hi
              · by_cases h7 : i.val < 1024
                · unfold y522TPathData
                  rw [dite_eq_right h0, dite_eq_right h1,
                    dite_eq_right h2, dite_eq_right h3,
                    dite_eq_right h4, dite_eq_right h5,
                    dite_eq_right h6, dite_eq_left h7]
                  exact y522TPath_shift
                    y522TPathData07 y522TPathData07_prior i
                    (by omega) (by omega) hi
                · by_cases h8 : i.val < 1152
                  · unfold y522TPathData
                    rw [dite_eq_right h0, dite_eq_right h1,
                      dite_eq_right h2, dite_eq_right h3,
                      dite_eq_right h4, dite_eq_right h5,
                      dite_eq_right h6, dite_eq_right h7,
                      dite_eq_left h8]
                    exact y522TPath_shift
                      y522TPathData08 y522TPathData08_prior i
                      (by omega) (by omega) hi
                  · by_cases h9 : i.val < 1280
                    · unfold y522TPathData
                      rw [dite_eq_right h0, dite_eq_right h1,
                        dite_eq_right h2, dite_eq_right h3,
                        dite_eq_right h4, dite_eq_right h5,
                        dite_eq_right h6, dite_eq_right h7,
                        dite_eq_right h8, dite_eq_left h9]
                      exact y522TPath_shift
                        y522TPathData09 y522TPathData09_prior i
                        (by omega) (by omega) hi
                    · by_cases h10 : i.val < 1408
                      · unfold y522TPathData
                        rw [dite_eq_right h0, dite_eq_right h1,
                          dite_eq_right h2, dite_eq_right h3,
                          dite_eq_right h4, dite_eq_right h5,
                          dite_eq_right h6, dite_eq_right h7,
                          dite_eq_right h8, dite_eq_right h9,
                          dite_eq_left h10]
                        exact y522TPath_shift
                          y522TPathData10 y522TPathData10_prior i
                          (by omega) (by omega) hi
                      · by_cases h11 : i.val < 1536
                        · unfold y522TPathData
                          rw [dite_eq_right h0, dite_eq_right h1,
                            dite_eq_right h2, dite_eq_right h3,
                            dite_eq_right h4, dite_eq_right h5,
                            dite_eq_right h6, dite_eq_right h7,
                            dite_eq_right h8, dite_eq_right h9,
                            dite_eq_right h10, dite_eq_left h11]
                          exact y522TPath_shift
                            y522TPathData11 y522TPathData11_prior i
                            (by omega) (by omega) hi
                        · by_cases h12 : i.val < 1664
                          · unfold y522TPathData
                            rw [dite_eq_right h0, dite_eq_right h1,
                              dite_eq_right h2, dite_eq_right h3,
                              dite_eq_right h4, dite_eq_right h5,
                              dite_eq_right h6, dite_eq_right h7,
                              dite_eq_right h8, dite_eq_right h9,
                              dite_eq_right h10, dite_eq_right h11,
                              dite_eq_left h12]
                            exact y522TPath_shift
                              y522TPathData12 y522TPathData12_prior i
                              (by omega) (by omega) hi
                          · by_cases h13 : i.val < 1792
                            · unfold y522TPathData
                              rw [dite_eq_right h0, dite_eq_right h1,
                                dite_eq_right h2, dite_eq_right h3,
                                dite_eq_right h4, dite_eq_right h5,
                                dite_eq_right h6, dite_eq_right h7,
                                dite_eq_right h8, dite_eq_right h9,
                                dite_eq_right h10, dite_eq_right h11,
                                dite_eq_right h12, dite_eq_left h13]
                              exact y522TPath_shift
                                y522TPathData13 y522TPathData13_prior i
                                (by omega) (by omega) hi
                            · unfold y522TPathData
                              rw [dite_eq_right h0, dite_eq_right h1,
                                dite_eq_right h2, dite_eq_right h3,
                                dite_eq_right h4, dite_eq_right h5,
                                dite_eq_right h6, dite_eq_right h7,
                                dite_eq_right h8, dite_eq_right h9,
                                dite_eq_right h10, dite_eq_right h11,
                                dite_eq_right h12, dite_eq_right h13]
                              exact y522TPath_shift
                                y522TPathData14 y522TPathData14_prior i
                                (by omega) (by omega) hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
