/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctP

/-! # Tight field bounds by one packed check

`colLeB w B x` checks `|field| ≤ B` for all `4096` fields of both parts of a signed packed vector
with two additions and two conjunctions of big numbers: a constant `2^(w-1) - 1 - B` is added to
every field (no carries, given a coarse bound below `2^(w-1)`), and the top bits of all fields
must stay clear.  `tbnd_of_check` turns a coarse `TBnd` into a tight one, so that packed words can
use small field widths (bounds from the generic letter lemmas are very coarse). -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The constant `c` in each of the `4096` fields of width `w`. -/
def repC (w c : ℕ) : ℕ := dblM w c 1 12

/-- Fields of the constant pattern. -/
theorem fld_repC (w c : ℕ) (hc : c < 2 ^ w) (i : ℕ) (hi : i < 4096) : fld w (repC w c) i = c := by
  have h := fld_dblM w c 1 (by norm_num) (by simpa using hc) 12 i (by simpa using hi)
  rw [repC, h, Nat.mod_one, fld_zero_right, Nat.mod_eq_of_lt hc]

/-- The constant pattern fits in `4096` fields. -/
theorem repC_lt (w c : ℕ) (hc : c < 2 ^ w) : repC w c < 2 ^ (w * 2 ^ 12) := by
  have h := dblM_lt w c 1 (by simpa using hc) 12
  simpa [repC] using h

/-- One part of a packed column has all fields at most `B`. -/
def partLeB (w B P : ℕ) : Bool := (P + repC w (2 ^ (w - 1) - 1 - B)) &&& repC w (2 ^ (w - 1)) == 0

/-- Both parts of a packed column have all fields at most `B`. -/
def colLeB (w B : ℕ) (x : SVec) : Bool := partLeB w B x.1 && partLeB w B x.2

/-- A field below `2^w` whose top bit is clear is below `2^(w-1)`. -/
theorem lt_of_top_clear (w n : ℕ) (hw : 1 ≤ w) (hn : n < 2 ^ w) (ht : n &&& 2 ^ (w - 1) = 0) :
    n < 2 ^ (w - 1) := by
  have hb : n.testBit (w - 1) = false := by
    have h := congrArg (fun m => m.testBit (w - 1)) ht
    simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, Nat.zero_testBit] at h
    exact h
  by_contra hc
  push Not at hc
  have hlt : n < 2 ^ (w - 1) + 2 ^ (w - 1) := by
    have : 2 ^ w = 2 ^ (w - 1) + 2 ^ (w - 1) := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    omega
  have : n.testBit (w - 1) = true := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hc
    (by rw [pow_succ]; omega)
  rw [hb] at this
  exact Bool.false_ne_true this

/-- A part check gives the tight bound on every field. -/
theorem fld_le_of_partLeB {w B0 B P : ℕ} (hw : 1 ≤ w) (hP : P < 2 ^ (w * 2 ^ 12))
    (hP0 : ∀ i < 2 ^ 12, fld w P i ≤ B0) (hB0 : B0 < 2 ^ (w - 1)) (hB : B < 2 ^ (w - 1))
    (h : partLeB w B P = true) : ∀ i < 2 ^ 12, fld w P i ≤ B := by
  intro i hi
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hhalf : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hc : 2 ^ (w - 1) - 1 - B < 2 ^ w := by omega
  have hadd := fld_add w (2 ^ 12) P (repC w (2 ^ (w - 1) - 1 - B)) hP (repC_lt w _ hc)
    (fun j hj => by
      rw [fld_repC w _ hc j (by simpa using hj)]
      have := hP0 j hj
      omega)
  simp only [partLeB, beq_iff_eq] at h
  have h0 := congrArg (fun m => fld w m i) h
  simp only [fld_land, fld_zero_right_zero] at h0
  rw [hadd.2 i hi, fld_repC w _ hc i (by simpa using hi),
    fld_repC w _ hhalf i (by simpa using hi)] at h0
  have hlt := lt_of_top_clear w _ hw (by have := hP0 i hi; omega) h0
  omega

/-- A column check turns a coarse bound into a tight bound. -/
theorem sbnd_of_colLeB {w B0 B : ℕ} {x : SVec} (hw : 1 ≤ w) (hx : SBnd w (2 ^ 12) B0 x)
    (hB0 : B0 < 2 ^ (w - 1)) (hB : B < 2 ^ (w - 1)) (h : colLeB w B x = true) :
    SBnd w (2 ^ 12) B x := by
  simp only [colLeB, Bool.and_eq_true] at h
  refine ⟨hx.1, hx.2.1, fun i hi => ⟨?_, ?_⟩⟩
  · exact fld_le_of_partLeB hw hx.1 (fun j hj => (hx.2.2 j hj).1) hB0 hB h.1 i hi
  · exact fld_le_of_partLeB hw hx.2.1 (fun j hj => (hx.2.2 j hj).2) hB0 hB h.2 i hi

/-- Tight tensor bounds from coarse bounds and one packed check per column. -/
theorem tbnd_of_check {w B0 B : ℕ} {X : List SVec} (hw : 1 ≤ w) (hX : TBnd w B0 X)
    (hB0 : B0 < 2 ^ (w - 1)) (hB : B < 2 ^ (w - 1))
    (h : (List.range 24).all (fun i => colLeB w B (tcol X i)) = true) : TBnd w B X := by
  intro i hi
  simp only [List.all_eq_true, List.mem_range] at h
  exact sbnd_of_colLeB hw (hX i hi) hB0 hB (h i hi)

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
