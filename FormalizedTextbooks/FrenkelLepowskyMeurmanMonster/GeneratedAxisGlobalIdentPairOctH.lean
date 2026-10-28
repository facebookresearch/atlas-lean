/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctP

/-! # The packed octad transform with a segmented packer

The range-halving packer `packR` of `GeneratedAxisGlobalIdentPairOctP` has a large per-node cost
in the kernel on its deep levels.  `packH` halves the index range only down to segments of `2^10`
fields and packs each segment directly by shifted single terms (`packF`).  The octad coordinate of
any exact packing is the integer octad coordinate (`octZ_eq_of_pack`); the resulting short part
`triShortOH` equals `triShortF` (`triShortOH_eq`), and `pairTriGMH` equals `pairTriGM`
(`pairTriGMH_eq`, worker `gident`), with the identification criteria `ident_forward_GMH` and
`ident_inverse_GMH`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-! ## Direct packing by shifted single terms -/

/-- One term as a signed packed vector. -/
def sglS (w : ℕ) (p : ℕ × ℤ) : SVec := (p.2.toNat <<< (w * p.1), (-p.2).toNat <<< (w * p.1))

/-- Direct packing: sum of shifted single terms. -/
def packF (w : ℕ) (l : List (ℕ × ℤ)) : SVec := l.foldr (fun p acc => sadd (sglS w p) acc) szero

theorem fld_small (w x j : ℕ) (hx : x < 2 ^ w) : fld w x j = if j = 0 then x else 0 := by
  split_ifs with h
  · subst h
    rw [fld_zero_right]
    exact Nat.mod_eq_of_lt hx
  · exact fld_eq_zero_of_lt w x 1 j (by simpa using hx) (by omega)

theorem sglS_spec (w n : ℕ) (p : ℕ × ℤ) (hp : p.1 < n) (hc : p.2.natAbs < 2 ^ w) :
    SBnd w n p.2.natAbs (sglS w p) ∧
      ∀ i < n, sval w (sglS w p) i = if p.1 = i then p.2 else 0 := by
  obtain ⟨h1, h2⟩ := natAbs_toNat_le p.2
  have hlt : ∀ x, x ≤ p.2.natAbs → x <<< (w * p.1) < 2 ^ (w * n) := by
    intro x hx
    rw [Nat.shiftLeft_eq]
    calc x * 2 ^ (w * p.1) < 2 ^ w * 2 ^ (w * p.1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = 2 ^ (w * (p.1 + 1)) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (w * n) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  have hf : ∀ x, x ≤ p.2.natAbs → ∀ i, fld w (x <<< (w * p.1)) i = if p.1 = i then x else 0 := by
    intro x hx i
    rw [fld_shiftLeft, fld_small w x _ (by omega)]
    by_cases h : p.1 = i
    · subst h; simp
    · by_cases h' : p.1 ≤ i
      · rw [ite_eq_left h', ite_eq_right (by omega), ite_eq_right h]
      · rw [ite_eq_right h', ite_eq_right h]
  refine ⟨⟨hlt _ h1, hlt _ h2, fun i _ => ?_⟩, fun i _ => ?_⟩
  · simp only [sglS]
    rw [hf _ h1, hf _ h2]
    split_ifs
    · exact ⟨h1, h2⟩
    · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · simp only [sval, sglS]
    rw [hf _ h1, hf _ h2]
    split_ifs
    · exact toNat_sub_toNat p.2
    · simp

/-- The direct packer is exact. -/
theorem packF_spec (w n : ℕ) : ∀ l : List (ℕ × ℤ), (∀ p ∈ l, p.1 < n) → absSum l < 2 ^ w →
    SBnd w n (absSum l) (packF w l) ∧ ∀ i < n, sval w (packF w l) i = idxSum l i
  | [], _, _ => by
    refine ⟨SBnd_zero _ _ _, fun i _ => ?_⟩
    simp [packF, sval_zero, idxSum]
  | p :: l, hl, hS => by
    have hS' : absSum (p :: l) = p.2.natAbs + absSum l := by simp [absSum]
    obtain ⟨a1, a2⟩ := sglS_spec w n p (hl p (by simp)) (by omega)
    obtain ⟨b1, b2⟩ := packF_spec w n l (fun q hq => hl q (by simp [hq])) (by omega)
    obtain ⟨c1, c2⟩ := sadd_spec a1 b1 (by omega)
    have hpk : packF w (p :: l) = sadd (sglS w p) (packF w l) := rfl
    rw [hpk, hS']
    refine ⟨c1, fun i hi => ?_⟩
    rw [c2 i hi, a2 i hi, b2 i hi]
    simp [idxSum]

/-! ## Range halving down to segments of `2^c` fields -/

/-- Range halving above level `c`, direct packing on segments of `2^c` fields. -/
def packH (w c : ℕ) : ℕ → List (ℕ × ℤ) → SVec
  | _, [] => szero
  | 0, l => packF w l
  | k + 1, l => if k < c then packF w l else
    sadd (packH w c k (l.filter (fun p => decide (p.1 < 2 ^ k))))
      (sshl (w * 2 ^ k) (packH w c k ((l.filter (fun p => decide (2 ^ k ≤ p.1))).map
        (fun p => (p.1 - 2 ^ k, p.2)))))

/-- The segmented packer is exact. -/
theorem packH_spec (w c : ℕ) : ∀ (k : ℕ) (l : List (ℕ × ℤ)), (∀ p ∈ l, p.1 < 2 ^ k) →
    absSum l < 2 ^ w →
    SBnd w (2 ^ k) (absSum l) (packH w c k l) ∧ ∀ i < 2 ^ k, sval w (packH w c k l) i = idxSum l i
  | k, [], _, _ => by
    have hz : packH w c k [] = szero := by cases k <;> rfl
    rw [hz]
    refine ⟨SBnd_zero _ _ _, fun i _ => ?_⟩
    simp only [sval_zero, idxSum, List.map_nil, List.sum_nil]
  | 0, p :: l, hl, hS => packF_spec w _ (p :: l) hl hS
  | k + 1, p :: l, hl, hS => by
    by_cases hkc : k < c
    · have hpk : packH w c (k + 1) (p :: l) = packF w (p :: l) := by
        simp only [packH, hkc, ↓reduceIte]
      rw [hpk]
      exact packF_spec w _ (p :: l) hl hS
    set L := p :: l with hL
    set lo := L.filter (fun p => decide (p.1 < 2 ^ k)) with hlo
    set hi := (L.filter (fun p => decide (2 ^ k ≤ p.1))).map (fun p => (p.1 - 2 ^ k, p.2))
      with hhi
    have hsplit := absSum_split k L
    rw [← hlo, ← hhi] at hsplit
    have hlo1 : ∀ q ∈ lo, q.1 < 2 ^ k := by
      intro q hq
      rw [hlo, List.mem_filter] at hq
      simpa using hq.2
    have hhi1 : ∀ q ∈ hi, q.1 < 2 ^ k := by
      intro q hq
      rw [hhi, List.mem_map] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      rw [List.mem_filter] at hr
      have h1 := hl r hr.1
      have h2 : 2 ^ k ≤ r.1 := by simpa using hr.2
      rw [pow_succ] at h1
      simp only
      omega
    obtain ⟨a1, a2⟩ := packH_spec w c k lo hlo1 (by omega)
    obtain ⟨b1, b2⟩ := packH_spec w c k hi hhi1 (by omega)
    obtain ⟨e1, e2⟩ := sbnd_extend a1
    obtain ⟨s1, s2⟩ := sshl_spec b1
    obtain ⟨d1, d2⟩ := sadd_spec e1 s1 (by omega)
    have hpk : packH w c (k + 1) L =
        sadd (packH w c k lo) (sshl (w * 2 ^ k) (packH w c k hi)) := by
      rw [hlo, hhi, hL]
      simp only [packH, hkc, ↓reduceIte]
    rw [hpk, hsplit]
    refine ⟨d1, fun i hi' => ?_⟩
    rw [d2 i hi', s2 i, idxSum_split k L i, ← hlo]
    by_cases hik : 2 ^ k ≤ i
    · rw [ite_eq_left hik, e2 i hik, b2 _ (by rw [pow_succ] at hi'; omega), hhi,
        idxSum_map_sub _ _ _ (fun q hq => by rw [List.mem_filter] at hq; simpa using hq.2) hik,
        idxSum_eq_zero lo i (fun q hq => by have := hlo1 q hq; omega), zero_add]
    · rw [ite_eq_right hik, a2 i (by omega),
        idxSum_eq_zero (L.filter (fun p => decide (2 ^ k ≤ p.1))) i (fun q hq => by
          rw [List.mem_filter] at hq; have : 2 ^ k ≤ q.1 := by simpa using hq.2
          omega), add_zero]

/-! ## The octad transform of an exact packing -/

/-- The packed transform of a given packing of the octad terms. -/
def octPackXP (w : ℕ) (fwd : Bool) (P : SVec) : SVec :=
  whtP w (if fwd then P else sflip (allMask w (2 ^ 16)) (rep64 w identOctDiagTable) P) 6

/-- The octad coordinate from any exact packing of the octad terms. -/
theorem octZ_eq_of_pack (w : ℕ) (fwd : Bool) (L : IdentVec) (hok : octPackOk w L = true)
    (P : SVec) (hP : SBnd w (2 ^ 16) (absSum (octLFlat L)) P)
    (hv : ∀ t < 2 ^ 16, sval w P t = idxSum (octLFlat L) t) (o e : ℕ) :
    octZ w fwd (octPackXP w fwd P) o e =
      (L.sh.oct.map (fun b => if b.1 = o then
        (b.2.map (fun q => q.2 * octMT fwd e q.1)).sum else 0)).sum := by
  obtain ⟨h1, h2⟩ := octPackOk_spec w L hok
  have hS : absSum (octLFlat L) < 2 ^ w := by omega
  -- the input of the network
  have hin : SBnd w (2 ^ 16) (absSum (octLFlat L))
      (if fwd then P else sflip (allMask w (2 ^ 16)) (rep64 w identOctDiagTable) P) ∧
      ∀ t < 2 ^ 16, sval w (if fwd then P else
        sflip (allMask w (2 ^ 16)) (rep64 w identOctDiagTable) P) t =
        (if fwd then 1 else octD t) * idxSum (octLFlat L) t := by
    cases fwd
    · obtain ⟨f1, f2⟩ := sflip_spec hP (rep64 w identOctDiagTable)
        (fun t => identOctDiagTable.testBit (t % 64) = true) (rep64_isFieldMask w _) hS
      refine ⟨f1, fun t ht => ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [f2 t ht, hv t ht]
      unfold octD
      split_ifs <;> ring
    · refine ⟨hP, fun t ht => ?_⟩
      simp only [↓reduceIte, one_mul]
      exact hv t ht
  obtain ⟨b1, b2⟩ := whtP_spec w _ _ hin.1 h2 6 le_rfl
  have hX : ∀ t < 2 ^ 16, sval w (octPackXP w fwd P) t =
      whtVal (fun s => (if fwd then 1 else octD s) * idxSum (octLFlat L) s) 6 t := by
    intro t ht
    unfold octPackXP
    rw [b2 t ht]
    apply whtVal_congr
    intro u hu
    apply hin.2
    have : (2 : ℕ) ^ 6 = 64 := by norm_num
    rw [this] at hu ⊢
    have : (2 : ℕ) ^ 16 = 65536 := by norm_num
    rw [this] at ht ⊢
    omega
  have hF : ∀ x, octMT fwd e (x % 64) = octMT fwd e x := by
    intro x
    simp only [octMT, Nat.mod_mod]
  have hflat : (L.sh.oct.map (fun b => if b.1 = o then
      (b.2.map (fun q => q.2 * octMT fwd e q.1)).sum else 0)).sum =
      ((octLFlat L).map (fun p => if p.1 / 64 = o then p.2 * octMT fwd e (p.1 % 64) else 0)).sum :=
    octFlat_blocks o (octMT fwd e) hF L.sh.oct
  rw [hflat]
  have hs : svalS w (octPackXP w fwd P) (64 * o + octTw e) =
      sval w (octPackXP w fwd P) (64 * o + octTw e) := by
    simp only [svalS, sval, fldS_eq]
  unfold octZ
  rw [hs]
  have htw := octTw_lt e
  by_cases ho : o < 1024
  · have ht : 64 * o + octTw e < 2 ^ 16 := by norm_num; omega
    rw [hX _ ht, whtVal_block _ o _ htw, Finset.mul_sum]
    have key : ∀ u ∈ Finset.range 64,
        (if fwd then octD e else 1) * ((if bpar (octTw e &&& u) 6 then -1 else 1) *
          ((if fwd then 1 else octD (64 * o + u)) * idxSum (octLFlat L) (64 * o + u))) =
        octMT fwd e u * idxSum (octLFlat L) (64 * o + u) := by
      intro u hu
      have hu' : u < 64 := Finset.mem_range.mp hu
      rw [octMT_tw fwd e u, Nat.mod_eq_of_lt hu']
      have hD : octD (64 * o + u) = octD u := by
        unfold octD
        rw [show (64 * o + u) % 64 = u % 64 by omega]
      cases fwd
      · simp only [Bool.false_eq_true, ↓reduceIte, hD]
        ring
      · simp only [↓reduceIte]
        ring
    rw [Finset.sum_congr rfl key, sum_block_idx]
  · have ht : 2 ^ 16 ≤ 64 * o + octTw e := by norm_num; omega
    have z1 := fld_eq_zero_of_lt w _ _ _ b1.1 ht
    have z2 := fld_eq_zero_of_lt w _ _ _ b1.2.1 ht
    have hP' : octPackXP w fwd P = whtP w (if fwd then P else
        sflip (allMask w (2 ^ 16)) (rep64 w identOctDiagTable) P) 6 := rfl
    rw [hP']
    simp only [sval, z1, z2, Nat.cast_zero, sub_zero, mul_zero]
    symm
    rw [List.map_congr_left (g := fun _ => (0 : ℤ)) (fun p hp => by
      have := h1 p hp
      rw [ite_eq_right (by norm_num at this; omega)])]
    simp

/-! ## Short part and pairings with the segmented packer -/

/-- The packed octad transform with the segmented packer (segments of `2^10` fields). -/
def octPackXH (w : ℕ) (fwd : Bool) (L : IdentVec) : SVec :=
  octPackXP w fwd (packH w 10 16 (octLFlat L))

/-- The segmented-packer octad coordinate is the integer octad coordinate. -/
theorem octZH_eq (w : ℕ) (fwd : Bool) (L : IdentVec) (hok : octPackOk w L = true) (o e : ℕ) :
    octZ w fwd (octPackXH w fwd L) o e =
      (L.sh.oct.map (fun b => if b.1 = o then
        (b.2.map (fun q => q.2 * octMT fwd e q.1)).sum else 0)).sum := by
  obtain ⟨h1, h2⟩ := octPackOk_spec w L hok
  obtain ⟨a1, a2⟩ := packH_spec w 10 16 (octLFlat L) h1 (by omega)
  exact octZ_eq_of_pack w fwd L hok _ a1 a2 o e

/-- The short part with the segmented packer; falls back to `triShortF`. -/
def triShortOH (w : ℕ) (fwd : Bool) (L W : IdentVec) : ℚ :=
  if octPackOk w L then
    W.sden * ((W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF fwd L q.1)).sum +
      L.sden * (((W.sh.oct.map (fun b => (b.2.map (fun q =>
        q.2 * octZ w fwd (octPackXH w fwd L) b.1 q.1)).sum)).sum : ℤ) : ℚ) / 8 +
      (W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF fwd L q.1)).sum)
  else triShortF fwd L W

/-- The segmented-packer short part is the fast short part. -/
theorem triShortOH_eq (w : ℕ) (fwd : Bool) (L W : IdentVec) :
    triShortOH w fwd L W = triShortF fwd L W := by
  unfold triShortOH
  split_ifs with h
  · rw [← triShortG_eq_F]
    unfold triShortG
    have ht : ∀ o e, triOctT fwd L o e =
        L.sden * ((octZ w fwd (octPackXH w fwd L) o e : ℤ) : ℚ) / 8 := by
      intro o e
      unfold triOctT
      rw [octZH_eq w fwd L h o e]
    have hB : (W.sh.oct.map (fun b =>
        (b.2.map (fun q => (q.2 : ℚ) * triOctT fwd L b.1 q.1)).sum)).sum =
        L.sden * (((W.sh.oct.map (fun b => (b.2.map (fun q =>
          q.2 * octZ w fwd (octPackXH w fwd L) b.1 q.1)).sum)).sum : ℤ) : ℚ) / 8 := by
      simp only [ht]
      exact octSum_cast _ _ _
    rw [hB]
  · rfl

/-- `pairTriGM` with the segmented-packer octad transform. -/
def pairTriGMH (wo w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W + triShortOH wo fwd L W +
    ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCF fwd W q.1)).sum +
      (tdotM w (trialityTensorT w (!fwd) X) Y : ℚ) / (2 * D * E)) / 2

/-- The segmented-packer pairing is `pairTriGM`. -/
theorem pairTriGMH_eq (wo w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) :
    pairTriGMH wo w fwd L W X Y D E = pairTriGM w fwd L W X Y D E := by
  unfold pairTriGMH pairTriGM
  rw [triShortOH_eq, triShortG_eq_F]

/-- Forward identification from `pairTriGMH`. -/
theorem ident_forward_GMH (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriGMH wo w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward_GM i j h g L W hL hW hLt hWt hX hY hB hBC hx hy
    (by rw [← pairTriGMH_eq wo, hp])

/-- Inverse identification from `pairTriGMH`. -/
theorem ident_inverse_GMH (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriGMH wo w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse_GM i j h g L W hL hW hLt hWt hX hY hB hBC hx hy
    (by rw [← pairTriGMH_eq wo, hp])
end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
