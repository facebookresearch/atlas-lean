/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairPacket

/-! # Identifications from self pairings (factory core)

The exact pairing of the triality image of `L` with `W` is split into the parts of `pairTriGMZ`.
Instead of predicted numerical values, every part is compared in the kernel with the matching
self part of `W` (matrix block, collapsed pair / octad / odd self sums, packed tensor self dot);
the self parts add up to the packet self pairing of `W` (`packet_self`), which is the Griess norm
`128` of the axis (`self_eq_128`).  `ident_forward_self` / `ident_inverse_self` turn the six
kernel comparisons into the whole-vector identification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-! ## Collapsed self sums of a representation -/

/-- The collapsed self sum of the pair terms. -/
def selfPairsZ (V : IdentVec) : ℤ := (V.sh.pairs.map (fun q => q.2 * idxSum V.sh.pairs q.1)).sum

/-- The collapsed self sum of the odd terms. -/
def selfOddZ (V : IdentVec) : ℤ := (V.sh.odd.map (fun q => q.2 * idxSum V.sh.odd q.1)).sum

/-- The collapsed self sum of the octad terms. -/
def selfOctZ (V : IdentVec) : ℤ :=
  ((octLFlat V).map (fun p => p.2 * idxSum (octLFlat V) p.1)).sum

/-- The self pairing of the matrix block. -/
def selfMatQ (V : IdentVec) : ℚ := ∑ i : Fin 24, ∑ j : Fin 24, V.mat.entry i j * V.mat.entry i j

theorem list_sum_cast_mul (l : List (ℕ × ℤ)) (f : ℕ → ℤ) :
    (l.map (fun p => (p.2 : ℚ) * (f p.1 : ℚ))).sum =
      (((l.map (fun p => p.2 * f p.1)).sum : ℤ) : ℚ) := by
  rw [Int.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp

/-- The octad flat terms are the flat octad labels shifted by `552`. -/
theorem octsFlat_eq_octLFlat (oct : List (ℕ × List (ℕ × ℤ)))
    (h : ∀ b ∈ oct, ∀ q ∈ b.2, q.1 < 64) :
    octsFlat oct = (oct.flatMap (fun b => b.2.map (fun q => (64 * b.1 + q.1 % 64, q.2)))).map
      (fun p => (552 + p.1, p.2)) := by
  induction oct with
  | nil => rfl
  | cons b bs ih =>
    rw [octsFlat, List.flatMap_cons, List.map_append, ih (fun b' hb' => h b' (by simp [hb']))]
    congr 1
    unfold octFlat
    rw [List.map_map]
    apply List.map_congr_left
    intro q hq
    have := h b (by simp) q hq
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    rw [Nat.mod_eq_of_lt this]
    ring

/-- The octad lookup is an index sum of the flat octad terms. -/
theorem octLookupQ_eq_idxSum (oct : List (ℕ × List (ℕ × ℤ)))
    (h : ∀ b ∈ oct, ∀ q ∈ b.2, q.1 < 64) (o e : ℕ) (he : e < 64) :
    octLookupQ oct o e =
      (idxSum (oct.flatMap (fun b => b.2.map (fun q => (64 * b.1 + q.1 % 64, q.2))))
        (64 * o + e) : ℚ) := by
  induction oct with
  | nil => simp [octLookupQ, idxSum]
  | cons b bs ih =>
    have ih' := ih (fun b' hb' => h b' (by simp [hb']))
    unfold octLookupQ at ih' ⊢
    unfold idxSum at ih' ⊢
    rw [List.map_cons, List.sum_cons, ih', List.flatMap_cons, List.map_append, List.sum_append,
      Int.cast_add]
    congr 1
    rw [List.map_map]
    split_ifs with hb
    · rw [lookupQ_eq]
      unfold idxSum
      congr 2
      apply List.map_congr_left
      intro q hq
      have := h b (by simp) q hq
      simp only [Function.comp_apply]
      rw [Nat.mod_eq_of_lt this]
      congr 1
      apply propext
      constructor
      · intro hq1; subst hq1; rw [hb]
      · intro hq1; omega
    · symm
      rw [Int.cast_eq_zero]
      apply List.sum_eq_zero
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      have := h b (by simp) q hq
      simp only [Function.comp_apply]
      rw [ite_eq_right]
      intro hq1
      apply hb
      omega

/-- The short self pairing of a representation as collapsed self sums. -/
theorem short_self (V : IdentVec) (hok : V.sh.ok = true) :
    (∑ r, shortFunQ V.sh.flat r * shortFunQ V.sh.flat r) =
      (selfPairsZ V : ℚ) + (selfOctZ V : ℚ) + (selfOddZ V : ℚ) := by
  have hok' := hok
  simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨hp, ho⟩, hd⟩ := hok'
  have hoct : ∀ b ∈ V.sh.oct, ∀ q ∈ b.2, q.1 < 64 := fun b hb q hq => (ho b hb).2 q hq
  have hpair : ∀ q ∈ V.sh.pairs,
      shortFunQ V.sh.flat (shortDecode q.1) = (idxSum V.sh.pairs q.1 : ℚ) := by
    intro q hq
    have hq1 := hp q hq
    have hdec : shortDecode q.1 = Sum.inl (⟨q.1 / 276 % 2, Nat.mod_lt _ (by decide)⟩,
        ⟨q.1 % 276, Nat.mod_lt _ (by decide)⟩) := by simp [shortDecode, hq1]
    rw [hdec, shortFunQ_flat_pair _ hok, lookupQ_eq]
    simp only
    congr 2
    omega
  have hodd : ∀ q ∈ V.sh.odd,
      shortFunQ V.sh.flat (shortDecode q.1) = (idxSum V.sh.odd q.1 : ℚ) := by
    intro q hq
    have hq1 := hd q hq
    rw [shortDecode_odd_eq' q.1 hq1.1 hq1.2, shortFunQ_flat_odd _ hok, lookupQ_eq]
    simp only
    rw [show 49128 + 24 * ((q.1 - 49128) / 24) + (q.1 - 49128) % 24 = q.1 by omega]
  have hoctL : ∀ p ∈ octLFlat V,
      shortFunQ V.sh.flat (shortDecode (552 + p.1)) = (idxSum (octLFlat V) p.1 : ℚ) := by
    intro p hp'
    unfold octLFlat at hp'
    rw [List.mem_flatMap] at hp'
    obtain ⟨b, hb, hpb⟩ := hp'
    rw [List.mem_map] at hpb
    obtain ⟨q, hq, rfl⟩ := hpb
    have hb1 := (ho b hb).1
    have hq1 := hoct b hb q hq
    simp only
    rw [Nat.mod_eq_of_lt hq1, show 552 + (64 * b.1 + q.1) = 552 + 64 * b.1 + q.1 by ring,
      shortDecode_oct_eq' b.1 q.1 hb1 hq1, shortFunQ_flat_oct _ hok,
      octLookupQ_eq_idxSum _ hoct _ _ hq1]
    rfl
  have hflat : octsFlat V.sh.oct = (octLFlat V).map (fun p => (552 + p.1, p.2)) :=
    octsFlat_eq_octLFlat _ hoct
  rw [sum_mul_shortFunQ]
  generalize hX : shortFunQ V.sh.flat = X at hpair hodd hoctL ⊢
  rw [ShortData.flat, List.map_append, List.map_append, List.sum_append, List.sum_append, hflat]
  congr 1
  congr 1
  · unfold selfPairsZ
    rw [← list_sum_cast_mul]
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [hpair q hq]
  · unfold selfOctZ
    rw [List.map_map, ← list_sum_cast_mul]
    congr 1
    apply List.map_congr_left
    intro p hp'
    simp only [Function.comp_apply]
    rw [hoctL p hp']
  · unfold selfOddZ
    rw [← list_sum_cast_mul]
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [hodd q hq]

/-- The tensor self pairing of a packed tensor. -/
theorem tensor_self (V : IdentVec) {w : ℕ} {Y : List SVec} {E : ℚ}
    (hT : V.ten = tensorRat w Y E) :
    (∑ k : Fin 4096, ∑ j : Fin 24, V.packet.2.2 (golayLabelCoefficients k) j *
        V.packet.2.2 (golayLabelCoefficients k) j) / 2 = (tdot w Y Y : ℚ) / (2 * (E * E)) := by
  rw [← tdot_rat, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  show V.ten (generatedAxisGlobalSpinLabel (golayLabelCoefficients k)) j *
      V.ten (generatedAxisGlobalSpinLabel (golayLabelCoefficients k)) j / 2 = _
  rw [generatedAxisGlobalSpinLabel_coeff, hT]

/-- The self pairing of the matrix block of the packet. -/
theorem mat_self (V : IdentVec) :
    (∑ i : Fin 24, ∑ j : Fin 24, V.packet.1 i j * V.packet.1 i j) = selfMatQ V := by
  unfold selfMatQ IdentVec.packet
  simp only [MatRep.toMat_apply]

/-- The packet self pairing of a representation. -/
theorem packet_self (V : IdentVec) (hok : V.sh.ok = true) {w : ℕ} {Y : List SVec} {E : ℚ}
    (hT : V.ten = tensorRat w Y E) :
    packetPairQ V.packet V.packet = selfMatQ V +
      V.sden * V.sden * ((selfPairsZ V : ℚ) + (selfOctZ V : ℚ) + (selfOddZ V : ℚ)) +
        (tdot w Y Y : ℚ) / (2 * (E * E)) := by
  have h1 := mat_self V
  have h2 := tensor_self V hT
  have h3 := short_self V hok
  have h4 : (∑ r, V.packet.2.1 r * V.packet.2.1 r) =
      V.sden * V.sden * (∑ r, shortFunQ V.sh.flat r * shortFunQ V.sh.flat r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    show V.sden * shortFunQ V.sh.flat r * (V.sden * shortFunQ V.sh.flat r) = _
    ring
  rw [packetPairQ, h1, h4, h3, h2]

/-- The self pairing of the representation of an axis of norm `128`. -/
theorem self_eq_128 (V : IdentVec) (hok : V.sh.ok = true) {w : ℕ} {Y : List SVec} {E : ℚ}
    (hT : V.ten = tensorRat w Y E) (y : GriessSpace) (hy : griessConwayEncode y = V.real)
    (hn : griessForm y y = 128) :
    selfMatQ V + V.sden * V.sden * ((selfPairsZ V : ℚ) + (selfOctZ V : ℚ) + (selfOddZ V : ℚ)) +
        (tdot w Y Y : ℚ) / (2 * (E * E)) = 128 := by
  rw [← packet_self V hok hT]
  have h := packetPairQ_actual y y V.packet V.packet hy hy
  rw [hn] at h
  exact_mod_cast h.symm

/-! ## Packed collapsed self sums -/

/-- The packed octad self sum (falls back to the collapsed sum). -/
def selfOctP (V : IdentVec) : ℤ :=
  if octPackOk 32 V then
    ((octLFlat V).map (fun p => p.2 * svalS 32 (packH 32 10 16 (octLFlat V)) p.1)).sum
  else selfOctZ V

theorem selfOctP_eq (V : IdentVec) : selfOctP V = selfOctZ V := by
  unfold selfOctP
  split_ifs with h
  · obtain ⟨h1, h2⟩ := octPackOk_spec 32 V h
    obtain ⟨_, a2⟩ := packH_spec 32 10 16 (octLFlat V) h1 (by omega)
    unfold selfOctZ
    congr 1
    apply List.map_congr_left
    intro p hp
    rw [svalS_eq_sval, a2 p.1 (h1 p hp)]
  · rfl

/-- The odd terms as flat terms with index `lab - 49128`. -/
def oddLFlat (V : IdentVec) : List (ℕ × ℤ) := V.sh.odd.map (fun q => (q.1 - 49128, q.2))

/-- The applicability check of the packed odd self sum. -/
def oddPackOk (V : IdentVec) : Bool :=
  V.sh.odd.all (fun q => decide (49128 ≤ q.1) && decide (q.1 - 49128 < 2 ^ 16)) &&
    decide (absSum (oddLFlat V) < 2 ^ 32)

/-- The packed odd self sum (falls back to the collapsed sum). -/
def selfOddP (V : IdentVec) : ℤ :=
  if oddPackOk V then
    (V.sh.odd.map (fun q => q.2 * svalS 32 (packH 32 10 16 (oddLFlat V)) (q.1 - 49128))).sum
  else selfOddZ V

theorem selfOddP_eq (V : IdentVec) : selfOddP V = selfOddZ V := by
  unfold selfOddP
  split_ifs with h
  · simp only [oddPackOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hl : ∀ p ∈ oddLFlat V, p.1 < 2 ^ 16 := by
      intro p hp
      unfold oddLFlat at hp
      rw [List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact (h1 q hq).2
    obtain ⟨_, a2⟩ := packH_spec 32 10 16 (oddLFlat V) hl h2
    unfold selfOddZ
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [svalS_eq_sval, a2 _ (h1 q hq).2]
    unfold oddLFlat
    rw [idxSum_map_sub 49128 V.sh.odd q.1 (fun p hp => (h1 p hp).1) (h1 q hq).1]
  · rfl

/-! ## Integer matrix self pairing -/

/-- The self pairing of an integer matrix block: integer sums and five rational operations. -/
def selfMatZI (M : MatZ) : ℚ :=
  24 * M.scal * M.scal +
    2 * M.scal * ((((List.finRange 24).map (fun i => M.num i i)).sum : ℤ) : ℚ) /
      (M.den * 4 ^ M.k) +
    ((((List.finRange 24).map (fun i => ((List.finRange 24).map (fun j =>
      M.num i j * M.num i j)).sum)).sum : ℤ) : ℚ) / ((M.den * 4 ^ M.k) * (M.den * 4 ^ M.k))

theorem selfMatQ_eq_ZI (V : IdentVec) (M : MatZ) (hV : ∀ i j, V.mat.entry i j = M.entry i j) :
    selfMatQ V = selfMatZI M := by
  unfold selfMatQ selfMatZI
  set c : ℚ := M.den * 4 ^ M.k
  have hterm : ∀ i j : Fin 24, V.mat.entry i j * V.mat.entry i j =
      (if i = j then M.scal * M.scal + 2 * M.scal * (M.num i j : ℚ) / c else 0) +
        ((M.num i j * M.num i j : ℤ) : ℚ) / (c * c) := by
    intro i j
    rw [hV, MatZ.entry_num]
    split_ifs <;> push_cast <;> ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have e1 : ((((List.finRange 24).map (fun i => M.num i i)).sum : ℤ) : ℚ) =
      ∑ i : Fin 24, ((M.num i i : ℤ) : ℚ) := by
    rw [Int.cast_list_sum, List.map_map, Fin.sum_univ_def]
    rfl
  have e2 : ((((List.finRange 24).map (fun i => ((List.finRange 24).map (fun j =>
      M.num i j * M.num i j)).sum)).sum : ℤ) : ℚ) =
      ∑ i : Fin 24, ∑ j : Fin 24, ((M.num i j * M.num i j : ℤ) : ℚ) := by
    rw [Int.cast_list_sum, List.map_map, Fin.sum_univ_def]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [Int.cast_list_sum, List.map_map, Fin.sum_univ_def]
    rfl
  have e3 : ∑ x : Fin 24, 2 * M.scal * ((M.num x x : ℤ) : ℚ) / c =
      2 * M.scal * (∑ x : Fin 24, ((M.num x x : ℤ) : ℚ)) / c := by
    rw [Finset.mul_sum, Finset.sum_div]
  have e4 : ∑ x : Fin 24, ∑ y : Fin 24, ((M.num x y * M.num x y : ℤ) : ℚ) / (c * c) =
      (∑ x : Fin 24, ∑ y : Fin 24, ((M.num x y * M.num x y : ℤ) : ℚ)) / (c * c) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_div]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, e1, e2, e3, e4]
  ring

/-! ## The identification from self pairings -/

/-- Forward identification: every part of the pairing equals the matching self part of the
target (both sides evaluated by the kernel), and the target has norm `128`. -/
theorem ident_forward_self (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hCC : 2 * (2 * 4096 * (C * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hok : octPackOk wo L = true)
    (hm : triMatF true L W = selfMatQ W)
    (hp : pairSumQ true L W = W.sden * (selfPairsZ W : ℚ))
    (hn : L.sden * (octSumZ wo true L W : ℚ) / 8 = W.sden * (selfOctP W : ℚ))
    (ha : (oddWZ w true X W : ℚ) / (2 * D) = W.sden * (selfOddP W : ℚ))
    (ht : L.sden * (oddLZ w true Y L : ℚ) / E +
      (tdotM w (trialityTensorT w (!true) X) Y : ℚ) / (2 * D * E) =
        (tdotM w Y Y : ℚ) / (E * E)) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) := by
  apply ident_forward_GMZ i j h g L W hL hW hLt hWt hX hY hB hBC hx hy (wo := wo)
  rw [pairTriGMZ_parts hok rfl rfl rfl rfl rfl rfl]
  have h128 := self_eq_128 W hW hWt _ hy (identLocal_norm j g)
  rw [selfOctP_eq] at hn
  rw [selfOddP_eq] at ha
  rw [tdotM_eq hY hY hCC] at ht
  rw [← h128, hm, hp]
  have : W.sden * (W.sden * (selfPairsZ W : ℚ) + L.sden * (octSumZ wo true L W : ℚ) / 8 +
      (oddWZ w true X W : ℚ) / (2 * D)) =
      W.sden * W.sden * ((selfPairsZ W : ℚ) + (selfOctZ W : ℚ) + (selfOddZ W : ℚ)) := by
    rw [mul_div_assoc] at hn
    rw [show L.sden * (octSumZ wo true L W : ℚ) / 8 = L.sden * ((octSumZ wo true L W : ℚ) / 8)
      by ring, hn, ha]
    ring
  rw [this, ht]
  ring

/-- Inverse identification from self pairings. -/
theorem ident_inverse_self (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hCC : 2 * (2 * 4096 * (C * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hok : octPackOk wo L = true)
    (hm : triMatF false L W = selfMatQ W)
    (hp : pairSumQ false L W = W.sden * (selfPairsZ W : ℚ))
    (hn : L.sden * (octSumZ wo false L W : ℚ) / 8 = W.sden * (selfOctP W : ℚ))
    (ha : (oddWZ w false X W : ℚ) / (2 * D) = W.sden * (selfOddP W : ℚ))
    (ht : L.sden * (oddLZ w false Y L : ℚ) / E +
      (tdotM w (trialityTensorT w (!false) X) Y : ℚ) / (2 * D * E) =
        (tdotM w Y Y : ℚ) / (E * E)) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) := by
  apply ident_inverse_GMZ i j h g L W hL hW hLt hWt hX hY hB hBC hx hy (wo := wo)
  rw [pairTriGMZ_parts hok rfl rfl rfl rfl rfl rfl]
  have h128 := self_eq_128 W hW hWt _ hy (identLocal_norm j g)
  rw [selfOctP_eq] at hn
  rw [selfOddP_eq] at ha
  rw [tdotM_eq hY hY hCC] at ht
  rw [← h128, hm, hp]
  have : W.sden * (W.sden * (selfPairsZ W : ℚ) + L.sden * (octSumZ wo false L W : ℚ) / 8 +
      (oddWZ w false X W : ℚ) / (2 * D)) =
      W.sden * W.sden * ((selfPairsZ W : ℚ) + (selfOctZ W : ℚ) + (selfOddZ W : ℚ)) := by
    rw [mul_div_assoc] at hn
    rw [show L.sden * (octSumZ wo false L W : ℚ) / 8 = L.sden * ((octSumZ wo false L W : ℚ) / 8)
      by ring, hn, ha]
    ring
  rw [this, ht]
  ring
end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
