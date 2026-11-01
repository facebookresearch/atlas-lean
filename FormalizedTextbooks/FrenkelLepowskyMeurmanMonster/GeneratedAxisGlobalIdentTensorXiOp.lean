/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXi

/-! # The packed Xi operator

`tensorXi` computes the rational Xi tensor operator `generatedAxisGlobalRationalTensorXi` on
packed numerators, with denominator multiplied by sixteen. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-- A list sum over `List.range` is the corresponding finite sum. -/
theorem list_sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ n : ℕ,
    (List.map f (List.range n)).sum = ∑ i ∈ Finset.range n, f i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
                 simp

/-- Grey labels below 64 determine their grey index. -/
theorem xiA_injective : Function.Injective (fun n : Fin 64 => xiA n.val) := by
  intro n m h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · have := congrFun h ⟨i, hi⟩
    simp only [xiA] at this
    cases hn : n.val.testBit i <;> cases hm : m.val.testBit i <;> simp_all
  · have h1 : n.val < 2 ^ i := lt_of_lt_of_le n.isLt
      (by calc (64 : ℕ) = 2 ^ 6 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : m.val < 2 ^ i := lt_of_lt_of_le m.isLt
      (by calc (64 : ℕ) = 2 ^ 6 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

/-- Grey labels below 64 enumerate all grey indices. -/
theorem xiA_bijective : Function.Bijective (fun n : Fin 64 => xiA n.val) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨xiA_injective, ?_⟩
  simp [XiGrayIndex, ZMod.card]

/-- Reindexing a sum over grey indices by grey labels. -/
theorem sum_xiGray {M : Type*} [AddCommMonoid M] (f : XiGrayIndex → M) :
    ∑ a : XiGrayIndex, f a = ∑ n ∈ Finset.range 64, f (xiA n) := by
  rw [← Fintype.sum_bijective _ xiA_bijective (fun n : Fin 64 => f (xiA n.val)) f
    (fun _ => rfl), Fin.sum_univ_eq_sum_range (fun n => f (xiA n)) 64]

/-- The integral sign of a sum in `ZMod 2` is the product of the signs. -/
theorem intSign_add (x y : ZMod 2) :
    generatedAxisGlobalIntSign (x + y) =
      generatedAxisGlobalIntSign x * generatedAxisGlobalIntSign y := by
  fin_cases x <;> fin_cases y <;> decide

/-- The Gamma quadratic at a spin label is the Gamma bitset. -/
theorem xi_gamma_bits (m : Fin 4096) :
    xiGrayQuadratic (generatedAxisGlobalXiGammaIndex (golayLabelCoefficients m)) =
      if xiGammaB m.val then 1 else 0 := by
  have hc : ∀ i : Fin 6, spinDot (xiGrayCocodeBasis i) (golayLabelCoefficients m) =
      if bpar (m.val &&& (xiGrayCocodeLabel i).val) 12 then 1 else 0 := by
    intro i
    exact spinDot_coeff (xiGrayCocodeLabel i) m
  rw [generatedAxisGlobalXiGammaIndex, xiGrayQuadratic_dual_weight]
  have hv : ∀ b : Bool,
      ((if b = true then (1 : ZMod 2) else 0)).val = if b = true then 1 else 0 := by
    intro b; cases b <;> rfl
  have hsum : (∑ i : Fin 6, (spinDot (xiGrayCocodeBasis i) (golayLabelCoefficients m)).val) =
      xiGammaCount m.val := by
    simp only [hc, hv]
    rw [Fin.sum_univ_six]
    simp only [xiGammaCount, xiCocodeLabels, xiGrayCocodeLabel, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
    ring_nf
    rfl
  rw [hsum]
  by_cases h : 2 ≤ xiGammaCount m.val % 4
  · simp [h, (xiGammaCount_iff m.val).mp h]
  · have h' : xiGammaB m.val = false := by
      cases hb : xiGammaB m.val
      · rfl
      · exact absurd ((xiGammaCount_iff m.val).mpr hb) h
    simp [h, h']

/-- The translation labels are below 4096. -/
theorem xiCodeTab_lt (n : ℕ) (hn : n < 64) : xiCodeTab.getD n 0 < 4096 := by
  have := xiCodeTab_spec ⟨n, hn⟩
  simp only at this
  rw [this]
  exact (generatedAxisGlobalSpinLabel _).isLt

/-- The spin index after a grey translation. -/
theorem xi_translate (k : Fin 4096) (n : ℕ) (hn : n < 64) :
    golayLabelCoefficients k + xiGrayCode (xiA n) =
      golayLabelCoefficients ⟨k.val ^^^ xiCodeTab.getD n 0,
        Nat.xor_lt_two_pow (n := 12) k.isLt (xiCodeTab_lt n hn)⟩ := by
  have hs := xiCodeTab_spec ⟨n, hn⟩
  have key : generatedAxisGlobalSpinLabel (golayLabelCoefficients k + xiGrayCode (xiA n)) =
      ⟨k.val ^^^ xiCodeTab.getD n 0, Nat.xor_lt_two_pow (n := 12) k.isLt (xiCodeTab_lt n hn)⟩ := by
    apply Fin.ext
    rw [spinLabel_add]
    exact congrArg (fun z => k.val ^^^ z) hs.symm
  calc golayLabelCoefficients k + xiGrayCode (xiA n)
      = golayLabelCoefficients (generatedAxisGlobalSpinLabel
          (golayLabelCoefficients k + xiGrayCode (xiA n))) :=
        (generatedAxisGlobalSpinLabel_decode _).symm
    _ = _ := congrArg golayLabelCoefficients key

/-- The sign bookkeeping of the Xi phase. -/
theorem intSign_phase_aux : ∀ (c : ZMod 2) (b : Bool),
    generatedAxisGlobalIntSign c * generatedAxisGlobalIntSign (if b = true then 1 else 0) *
        generatedAxisGlobalIntSign 1 =
      (if decide (c = 1) = true then 1 else -1) * (if b = true then -1 else 1) := by
  decide

/-- The Xi spin phase in packed form. -/
theorem xi_phase (k : Fin 4096) (n : ℕ) (hn : n < 64) :
    generatedAxisGlobalIntSign (generatedAxisGlobalXiSpinPhase (xiA n) (golayLabelCoefficients k)) =
      (if xiQBits.testBit n then 1 else -1) *
        (if xiGammaB (k.val ^^^ xiCodeTab.getD n 0) then -1 else 1) := by
  rw [generatedAxisGlobalXiSpinPhase, xi_translate k n hn, xi_gamma_bits]
  have hq := xiQBits_spec ⟨n, hn⟩
  simp only at hq
  rw [intSign_add, intSign_add, hq]
  exact intSign_phase_aux _ _

/-! ## The packed operator -/

/-- Multiply every field of a column by the Gamma sign of its label. -/
def colXiPre (w : ℕ) (x : SVec) : SVec :=
  sflip (allMask w (2 ^ 12)) (xiGammaMask w) x

/-- The 64-term grey Gaussian numerator of one packed column. -/
def colXiG (w : ℕ) (x : SVec) : SVec :=
  ssum ((List.range 64).map (fun n =>
    scond (!xiQBits.testBit n) (strs w 12 (bitsOf (xiCodeTab.getD n 0)) (colXiPre w x))))

/-- Whether the spatial Xi numerator of output column `i` and tetrad slot `b` is negative. -/
def xiNeg (i b : ℕ) : Bool := decide (i % 4 = 0) ^^ decide (i % 4 ≠ b)

/-- The packed Xi tensor operator on numerators; the denominator gains a factor sixteen. -/
def tensorXi (w : ℕ) (X : List SVec) : List SVec :=
  let Gs := X.map (colXiG w)
  (List.range 24).map (fun i =>
    ssum ((List.range 4).map (fun b => scond (xiNeg i b) (tcol Gs (4 * (i / 4) + b)))))

/-- The spatial Xi numerators are the signs `xiNeg`. -/
theorem co1XiNumerator_xiNeg : ∀ (i : Fin 24) (b : Fin 4),
    co1XiNumerator i (generatedAxisGlobalXiColumn i b) = if xiNeg i.val b.val then -1 else 1 := by
  decide +kernel

/-- The Gamma pre-multiplication: bounds and values. -/
theorem colXiPre_spec {w B : ℕ} {x : SVec} (hx : SBnd w (2 ^ 12) B x) (hB : B < 2 ^ w) :
    SBnd w (2 ^ 12) B (colXiPre w x) ∧ ∀ m < 2 ^ 12,
      sval w (colXiPre w x) m = (if xiGammaB m then -1 else 1) * sval w x m := by
  obtain ⟨h1, h2⟩ := sflip_spec hx _ _ (xiGammaMask_isFieldMask w) hB
  refine ⟨h1, fun m hm => ?_⟩
  unfold colXiPre
  rw [h2 m hm]
  split_ifs <;> ring

/-- The packed grey Gaussian: bounds and values. -/
theorem colXiG_spec {w B : ℕ} {x : SVec} (hx : SBnd w (2 ^ 12) B x) (hB : 64 * B < 2 ^ w) :
    SBnd w (2 ^ 12) (64 * B) (colXiG w x) ∧ ∀ k : Fin 4096,
      sval w (colXiG w x) k.val = ∑ n ∈ Finset.range 64,
        (if xiQBits.testBit n then 1 else -1) *
          ((if xiGammaB (k.val ^^^ xiCodeTab.getD n 0) then -1 else 1) *
            sval w x (k.val ^^^ xiCodeTab.getD n 0)) := by
  have hB1 : B < 2 ^ w := by omega
  obtain ⟨p1, p2⟩ := colXiPre_spec hx hB1
  have hterm : ∀ y ∈ (List.range 64).map (fun n =>
      scond (!xiQBits.testBit n) (strs w 12 (bitsOf (xiCodeTab.getD n 0)) (colXiPre w x))),
      SBnd w (2 ^ 12) B y := by
    intro y hy
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hy
    exact (scond_spec _ (strs_spec _ p1 (bitsOf_lt _)).1).1
  obtain ⟨s1, s2⟩ := ssum_spec _ hterm (by simpa using hB)
  refine ⟨(s1.mono (by simp) : SBnd w (2 ^ 12) (64 * B) _), fun k => ?_⟩
  unfold colXiG
  rw [s2 k.val k.isLt, List.map_map, list_sum_map_range]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n < 64 := Finset.mem_range.mp hn
  have hc := xiCodeTab_lt n hn'
  simp only [Function.comp_apply]
  rw [(scond_spec _ (strs_spec _ p1 (bitsOf_lt _)).1).2,
    (strs_spec _ p1 (bitsOf_lt _)).2 k.val k.isLt, xorBits_bitsOf _ hc,
    p2 _ (Nat.xor_lt_two_pow (n := 12) k.isLt hc)]
  cases xiQBits.testBit n <;> simp

/-- The packed Gamma pre-multiplication fixes zero. -/
theorem colXiPre_zero (w : ℕ) : colXiPre w szero = szero := by
  simp [colXiPre, sflip, sadd, ssel, sneg, szero]

/-- Conditional negation fixes zero. -/
theorem scond_zero (neg : Bool) : scond neg szero = szero := by
  cases neg <;> rfl

/-- A list sum of zero vectors vanishes. -/
theorem ssum_zero_map {α : Type*} (f : α → SVec) (hf : ∀ a, f a = szero) :
    ∀ l : List α, ssum (l.map f) = szero
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, ssum, hf a, ssum_zero_map f hf l]
    rfl

/-- The packed grey Gaussian fixes zero. -/
theorem colXiG_zero (w : ℕ) : colXiG w szero = szero := by
  unfold colXiG
  apply ssum_zero_map
  intro n
  rw [colXiPre_zero, strs_zero, scond_zero]

/-- Columns of a list built over `List.range`. -/
theorem tcol_range_map (f : ℕ → SVec) (n i : ℕ) (hi : i < n) :
    tcol ((List.range n).map f) i = f i := by
  unfold tcol
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- The packed Xi operator: bounds and the exact rational Xi formula. -/
theorem tensorXi_spec {w B : ℕ} {X : List SVec} (hX : TBnd w B X) (hB : 4 * (64 * B) < 2 ^ w)
    (D : ℚ) :
    TBnd w (4 * (64 * B)) (tensorXi w X) ∧
      tensorRat w (tensorXi w X) (16 * D) =
        generatedAxisGlobalRationalTensorXi (tensorRat w X D) := by
  have hB64 : 64 * B < 2 ^ w := by omega
  have hG : ∀ j < 24, SBnd w (2 ^ 12) (64 * B) (tcol (X.map (colXiG w)) j) := by
    intro j hj
    rw [tcol_map _ (colXiG_zero w)]
    exact (colXiG_spec (hX j hj) hB64).1
  have hout : ∀ i < 24, SBnd w (2 ^ 12) (4 * (64 * B)) (tcol (tensorXi w X) i) ∧
      ∀ k : Fin 4096, sval w (tcol (tensorXi w X) i) k.val =
        ∑ b ∈ Finset.range 4, (if xiNeg i b then -1 else 1) *
          sval w (colXiG w (tcol X (4 * (i / 4) + b))) k.val := by
    intro i hi
    have hcol : tcol (tensorXi w X) i = ssum ((List.range 4).map (fun b =>
        scond (xiNeg i b) (tcol (X.map (colXiG w)) (4 * (i / 4) + b)))) := by
      unfold tensorXi
      exact tcol_range_map _ 24 i hi
    have hidx : ∀ b < 4, 4 * (i / 4) + b < 24 := by intro b hb; omega
    have hterm : ∀ y ∈ (List.range 4).map (fun b =>
        scond (xiNeg i b) (tcol (X.map (colXiG w)) (4 * (i / 4) + b))),
        SBnd w (2 ^ 12) (64 * B) y := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      exact (scond_spec _ (hG _ (hidx b (List.mem_range.mp hb)))).1
    obtain ⟨s1, s2⟩ := ssum_spec _ hterm (by simpa using hB)
    rw [hcol]
    refine ⟨(s1.mono (by simp) : SBnd w (2 ^ 12) (4 * (64 * B)) _), fun k => ?_⟩
    rw [s2 k.val k.isLt, List.map_map, list_sum_map_range]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [Function.comp_apply]
    rw [(scond_spec _ (hG _ (hidx b (Finset.mem_range.mp hb)))).2, tcol_map _ (colXiG_zero w)]
  refine ⟨fun i hi => (hout i hi).1, ?_⟩
  funext k i
  simp only [tensorRat, generatedAxisGlobalRationalTensorXi]
  rw [(hout i.val i.isLt).2 k, sum_xiGray, Finset.sum_comm]
  rw [← Fin.sum_univ_eq_sum_range (fun b => (if xiNeg i.val b then -1 else 1) *
    sval w (colXiG w (tcol X (4 * (i.val / 4) + b))) k.val) 4]
  push_cast
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  have hcolb : 4 * (i.val / 4) + b.val < 24 := by omega
  rw [(colXiG_spec (hX _ hcolb) hB64).2 k]
  push_cast
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_range.mp hn
  have hl : generatedAxisGlobalSpinLabel (golayLabelCoefficients k + xiGrayCode (xiA n)) =
      ⟨k.val ^^^ xiCodeTab.getD n 0, Nat.xor_lt_two_pow (n := 12) k.isLt (xiCodeTab_lt n hn')⟩ := by
    rw [xi_translate k n hn', generatedAxisGlobalSpinLabel_coeff]
  rw [xi_phase k n hn', co1XiNumerator_xiNeg i b, hl]
  simp only [generatedAxisGlobalXiColumn]
  split_ifs <;> push_cast <;> ring

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
