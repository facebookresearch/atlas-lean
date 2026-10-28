/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairVec

/-! # Word images of complete representations

The image of a representation under a word of identification letters: the matrix block by the
spatial alphabet, the short block by a fast checked transport onto a target list in source
order (regrouped by kind with `ShortData.ofList`), and the tensor block by any exact tensor
transport (for example `tensorWordAll_actual`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

/-- Regroup a flat list by kind: pair labels, singleton octad blocks, the remaining labels. -/
def ShortData.ofList (T : List (ℕ × ℤ)) : ShortData :=
  ⟨T.filter (fun p => decide (p.1 < 552)),
    (T.filter (fun p => decide (552 ≤ p.1) && decide (p.1 < 49128))).map
      (fun p => ((p.1 - 552) / 64, [((p.1 - 552) % 64, p.2)])),
    T.filter (fun p => decide (49128 ≤ p.1))⟩

/-- A short block splits along a predicate. -/
theorem shortVec_filter (T : List (ℕ × ℤ)) (q : ℕ × ℤ → Bool) :
    shortVec T = shortVec (T.filter q) + shortVec (T.filter (fun p => !q p)) := by
  induction T with
  | nil => simp [shortVec]
  | cons p T ih =>
    rw [shortVec_cons, ih, List.filter_cons, List.filter_cons]
    cases hq : q p
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, shortVec_cons]
      abel
    · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, shortVec_cons]
      abel

/-- The flat octad terms of singleton blocks are the original terms. -/
theorem octsFlat_singletons (T : List (ℕ × ℤ)) (hT : ∀ p ∈ T, 552 ≤ p.1) :
    octsFlat (T.map (fun p => ((p.1 - 552) / 64, [((p.1 - 552) % 64, p.2)]))) = T := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    rw [List.map_cons, octsFlat, ih (fun q hq => hT q (by simp [hq]))]
    have h := hT p (by simp)
    simp only [octFlat, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    have hl : 552 + 64 * ((p.1 - 552) / 64) + (p.1 - 552) % 64 = p.1 := by
      have := Nat.div_add_mod (p.1 - 552) 64
      omega
    rw [hl]

/-- Short blocks of concatenations. -/
theorem shortVec_append (A B : List (ℕ × ℤ)) : shortVec (A ++ B) = shortVec A + shortVec B := by
  simp only [shortVec, List.map_append, List.sum_append]

/-- Regrouping keeps the short block. -/
theorem shortVec_ofList (T : List (ℕ × ℤ)) : shortVec (ShortData.ofList T).flat = shortVec T := by
  unfold ShortData.flat ShortData.ofList
  simp only
  rw [octsFlat_singletons _ (fun p hp => by
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.2.1), shortVec_append, shortVec_append]
  conv_rhs => rw [shortVec_filter T (fun p => decide (p.1 < 552)),
    shortVec_filter (T.filter (fun p => !decide (p.1 < 552)))
      (fun p => decide (552 ≤ p.1) && decide (p.1 < 49128)), List.filter_filter,
    List.filter_filter]
  rw [add_assoc]
  have h1 : T.filter (fun p => (decide (552 ≤ p.1) && decide (p.1 < 49128)) &&
      !decide (p.1 < 552)) = T.filter (fun p => decide (552 ≤ p.1) && decide (p.1 < 49128)) := by
    apply List.filter_congr
    intro p _
    by_cases ha : p.1 < 552
    · have hb : p.1 < 49128 := by omega
      have hc : ¬ 552 ≤ p.1 := by omega
      simp [ha, hb, hc]
    · by_cases hb : p.1 < 49128
      · have hc : 552 ≤ p.1 := by omega
        simp [ha, hb, hc]
      · have hc : 552 ≤ p.1 := by omega
        simp [ha, hb, hc]
  have h2 : T.filter (fun p => !(decide (552 ≤ p.1) && decide (p.1 < 49128)) &&
      !decide (p.1 < 552)) = T.filter (fun p => decide (49128 ≤ p.1)) := by
    apply List.filter_congr
    intro p _
    by_cases ha : p.1 < 552
    · have hb : p.1 < 49128 := by omega
      have hc : ¬ 552 ≤ p.1 := by omega
      have hd : ¬ 49128 ≤ p.1 := by omega
      simp [ha, hb, hc, hd]
    · by_cases hb : p.1 < 49128
      · have hc : 552 ≤ p.1 := by omega
        have hd : ¬ 49128 ≤ p.1 := by omega
        simp [ha, hb, hc, hd]
      · have hc : 552 ≤ p.1 := by omega
        have hd : 49128 ≤ p.1 := by omega
        simp [ha, hb, hc, hd]
  rw [h1, h2]

/-- Regrouped lists with labels below `98280` are valid short data. -/
theorem ofList_ok (T : List (ℕ × ℤ)) (hT : T.all (fun p => decide (p.1 < 98280)) = true) :
    (ShortData.ofList T).ok = true := by
  simp only [List.all_eq_true, decide_eq_true_eq] at hT
  simp only [ShortData.ok, ShortData.ofList, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, List.mem_filter, List.mem_map]
  refine ⟨⟨fun p hp => hp.2, ?_⟩, fun p hp => ⟨hp.2, hT p hp.1⟩⟩
  rintro b ⟨p, ⟨hp, h1, h2⟩, rfl⟩
  refine ⟨by simp only; omega, ?_⟩
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rw [hq]
  exact Nat.mod_lt _ (by decide)

/-- The image of a representation under a word of identification letters. -/
theorem IdentVec.word_actual (V : IdentVec) (w : List (IdentLetter × QMaskP))
    (hw : w.all (fun p => identLetterCheckP p.1 p.2) = true) (D : QMaskP) (hD : D.ok = true)
    (hcols : ∀ i : Fin 24, qmWordP (w.map Prod.snd) (2 ^ i.val, false) =
      (fld 24 D.colsP i.val, D.coeff.testBit i.val))
    (hrows : ∀ i : Fin 24, fld 24 D.rowsP i.val = rowsOf (fun j => fld 24 D.colsP j.val) i)
    (T : List (ℕ × ℤ)) (hS : shortCheckF D V.sh.flat T = true)
    (T' : GeneratedAxisGlobalRationalTensor)
    (hT : localTensorRepresentation (identWordFiber (w.map Prod.fst))
      (generatedAxisGlobalRationalTensorReal V.ten) = generatedAxisGlobalRationalTensorReal T')
    (x : GriessSpace) (hx : griessConwayEncode x = V.real) :
    griessConwayEncode (rhoLocal (identWordLocal (w.map Prod.fst)) x) =
      (⟨V.mat.act identSpatialAlphabet (w.map Prod.fst), ShortData.ofList T, V.sden, T'⟩ :
        IdentVec).real := by
  have hd := identCheckedWordP_valid w hw D hcols hrows
  have hS' : shortCheck D.toData V.sh.flat T = true := by rw [← shortCheckF_eq D hD]; exact hS
  change griessConwayEncode (localGriessRepresentation (identWordFiber (w.map Prod.fst)) x) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply, hx]
  apply Prod.ext
  · rw [IdentVec.real_fst, IdentVec.real_fst]
    exact identWord_matrix _ V.mat
  · apply Prod.ext
    · change localShortOperator (identWordFiber (w.map Prod.fst)) V.real.2.1 = _
      rw [IdentVec.real_short, IdentVec.real_short, map_smul, shortVec_ofList,
        shortVec_transport _ D.toData hd _ _ hS']
    · change localTensorRepresentation (identWordFiber (w.map Prod.fst)) V.real.2.2 = _
      rw [IdentVec.real_tensor, IdentVec.real_tensor]
      exact hT

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
