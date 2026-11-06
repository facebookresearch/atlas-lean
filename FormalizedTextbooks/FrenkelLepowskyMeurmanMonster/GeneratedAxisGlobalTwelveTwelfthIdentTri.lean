/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairTri

/-! # Forward triality images of identification vectors

For an identification vector `L` (`GeneratedAxisGlobalIdent.IdentVec`) whose tensor block is
packed (`L.ten = tensorRat w X D`), `twTriVec` is an identification vector for the forward
triality image, built blockwise from `L`:

* the odd short terms are read off the packed tensor (`twTriOdd`: every packed column is unpacked
  by halving, and the two label halves are added with the Golay weight sign);
* the octad blocks are the octad Fourier transforms of the merged octad blocks of `L`
  (`twTriOct`, over a checked list of the occurring octads);
* the tensor block is the packed source-tensor part `trialityTensorT` plus the packed odd-short
  part (`twTriTen`);
* the matrix block and the pair terms are literal data, checked entrywise against the triality
  formulas (`twMatCheck`, `twPairCheck`).

`twTriVec_packet` states that its rational packet is `generatedAxisGlobalRationalTriality
L.packet`; hence (`twTriVec_actual`) it represents `sExtra x` whenever `L` represents `x`. The
short scale of the image is `1 / (2 D)`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-! ## Unpacking packed numbers -/

/-- All `2 ^ m` fields of width `w` of a packed number, in order (by halving). -/
def twUnpack (w : ℕ) : ℕ → ℕ → List ℕ
  | 0, P => [P &&& ((1 <<< w) - 1)]
  | m + 1, P => twUnpack w m (P &&& ((1 <<< (w * (1 <<< m))) - 1)) ++
      twUnpack w m (P >>> (w * (1 <<< m)))

/-- Unpacking produces `2 ^ m` fields. -/
theorem twUnpack_length (w : ℕ) : ∀ (m P : ℕ), (twUnpack w m P).length = 2 ^ m
  | 0, P => rfl
  | m + 1, P => by
    rw [twUnpack, List.length_append, twUnpack_length w m, twUnpack_length w m, pow_succ]
    ring

/-- The low fields of a number below a field bound are its fields. -/
theorem twFld_low (w n P k : ℕ) (hk : k < n) :
    fld w (P &&& (2 ^ (w * n) - 1)) k = fld w P k := by
  have h1 : 2 ^ (w * n) - 1 = allMask w n := rfl
  rw [h1, fld_land, fld_allMask]
  simp only [hk, ↓reduceIte]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (fld_lt w P k)]

/-- Unpacked fields are the fields. -/
theorem twUnpack_getD (w : ℕ) : ∀ (m P k : ℕ), k < 2 ^ m → (twUnpack w m P).getD k 0 = fld w P k
  | 0, P, k, hk => by
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [twUnpack, List.getD_cons_zero, Nat.one_shiftLeft]
    rw [fld_zero_right, Nat.and_two_pow_sub_one_eq_mod]
  | m + 1, P, k, hk => by
    rw [twUnpack]
    simp only [Nat.one_shiftLeft]
    have hl : (twUnpack w m (P &&& (2 ^ (w * 2 ^ m) - 1))).length = 2 ^ m :=
      twUnpack_length w m _
    by_cases hkm : k < 2 ^ m
    · rw [List.getD_append _ _ _ _ (by rw [hl]; exact hkm), twUnpack_getD w m _ k hkm,
        twFld_low w (2 ^ m) P k hkm]
    · have hk' : k - 2 ^ m < 2 ^ m := by rw [pow_succ] at hk; omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, twUnpack_getD w m _ _ hk',
        fld_shiftRight]
      congr 1
      omega

attribute [irreducible] twUnpack

/-- The signed values of all `4096` fields of a signed packed vector. -/
def twColVals (w : ℕ) (x : SVec) : List ℤ :=
  List.zipWith (fun (a b : ℕ) => (a : ℤ) - (b : ℤ)) (twUnpack w 12 x.1) (twUnpack w 12 x.2)

/-- The column values have length `4096`. -/
theorem twColVals_length (w : ℕ) (x : SVec) : (twColVals w x).length = 4096 := by
  rw [twColVals, List.length_zipWith, twUnpack_length, twUnpack_length]
  rfl

/-- An unpacked field as an optional list entry. -/
theorem twUnpack_getElem? (w P k : ℕ) (hk : k < 4096) :
    (twUnpack w 12 P)[k]? = some (fld w P k) := by
  have hl : k < (twUnpack w 12 P).length := by rw [twUnpack_length]; exact hk
  rw [List.getElem?_eq_getElem hl, ← List.getD_eq_getElem _ 0 hl, twUnpack_getD w 12 P k hk]

/-- The column values are the signed field values. -/
theorem twColVals_getD (w : ℕ) (x : SVec) (k : ℕ) (hk : k < 4096) :
    (twColVals w x).getD k 0 = sval w x k := by
  unfold twColVals
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, twUnpack_getElem? w x.1 k hk,
    twUnpack_getElem? w x.2 k hk]
  simp [sval]

/-! ## Sparse lookups -/

/-- A conditional with a true condition. -/
theorem twIte_true {α : Type} {c : Prop} [Decidable c] (a b : α) (h : c) :
    (if c then a else b) = a := by simp [h]

/-- A conditional with a false condition. -/
theorem twIte_false {α : Type} {c : Prop} [Decidable c] (a b : α) (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- Lookup in a list with a head term. -/
theorem twLookupQ_cons (p : ℕ × ℤ) (L : List (ℕ × ℤ)) (lab : ℕ) :
    lookupQ (p :: L) lab = (if p.1 = lab then (p.2 : ℚ) else 0) + lookupQ L lab := by
  simp [lookupQ]

/-- Lookup in a concatenation. -/
theorem twLookupQ_append (A B : List (ℕ × ℤ)) (lab : ℕ) :
    lookupQ (A ++ B) lab = lookupQ A lab + lookupQ B lab := by
  simp [lookupQ, List.map_append, List.sum_append]

/-- Lookup in the empty list. -/
theorem twLookupQ_nil (lab : ℕ) : lookupQ [] lab = 0 := rfl

/-- Lookup in a flattened list. -/
theorem twLookupQ_flatMap (f : ℕ → List (ℕ × ℤ)) (lab : ℕ) :
    ∀ l : List ℕ, lookupQ (l.flatMap f) lab = (l.map (fun j => lookupQ (f j) lab)).sum
  | [] => rfl
  | j :: l => by
    rw [List.flatMap_cons, twLookupQ_append, twLookupQ_flatMap f lab l, List.map_cons,
      List.sum_cons]

/-- A sum over `List.range n` with a single possibly nonzero term. -/
theorem twSum_range_single (g : ℕ → ℚ) (i : ℕ) :
    ∀ n, i < n → (∀ j, j < n → j ≠ i → g j = 0) → ((List.range n).map g).sum = g i
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, hg => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton]
    by_cases hn : i = n
    · subst hn
      have h0 : ((List.range i).map g).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        have := List.mem_range.mp hj
        exact hg j (by omega) (by omega)
      rw [h0, zero_add]
    · rw [twSum_range_single g i n (by omega) (fun j hj hji => hg j (by omega) hji),
        hg n (by omega) (Ne.symm hn), add_zero]

/-! ## Odd short terms of the image -/

/-- The integral Golay weight sign `(-1)^(weight / 4)` of a code label, from the packed table. -/
def twWsgn (d : ℕ) : ℤ := if qBits.testBit d then -1 else 1

/-- The table sign is the Golay weight sign. -/
theorem twWsgn_eq (d : ℕ) (hd : d < 2048) :
    twWsgn d =
      generatedAxisGlobalIntSign ((golayMaskWeight (golayEncodedMask d) / 4 : ℕ) : ZMod 2) := by
  rw [intSign_weight, twWsgn]
  have h := qBits_spec ⟨d, by omega⟩
  simp only [Nat.mod_eq_of_lt hd] at h
  rw [h]

/-- The odd terms of column `j` from the two folded halves, starting at code label `d`. -/
def twOddWalk (j : ℕ) : ℕ → List ℤ → List ℤ → List (ℕ × ℤ)
  | d, a :: as, b :: bs =>
      if twWsgn d * (a + b) = 0 then twOddWalk j (d + 1) as bs
      else (49128 + 24 * d + j, twWsgn d * (a + b)) :: twOddWalk j (d + 1) as bs
  | _, _, _ => []

/-- Lookups in the odd walk. -/
theorem twOddWalk_lookup (j i : ℕ) (hj : j < 24) (hi : i < 24) :
    ∀ (as bs : List ℤ) (d0 d : ℕ), as.length = bs.length →
      lookupQ (twOddWalk j d0 as bs) (49128 + 24 * d + i) =
        if i = j ∧ d0 ≤ d ∧ d < d0 + as.length then
          ((twWsgn d * (as.getD (d - d0) 0 + bs.getD (d - d0) 0) : ℤ) : ℚ) else 0
  | [], bs, d0, d, _ => by simp [twOddWalk, twLookupQ_nil]
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, d0, d, h => by
    have ih := twOddWalk_lookup j i hj hi as bs (d0 + 1) d (by simpa using h)
    have hrest : lookupQ (twOddWalk j d0 (a :: as) (b :: bs)) (49128 + 24 * d + i) =
        (if d = d0 ∧ i = j then ((twWsgn d0 * (a + b) : ℤ) : ℚ) else 0) +
          lookupQ (twOddWalk j (d0 + 1) as bs) (49128 + 24 * d + i) := by
      simp only [twOddWalk]
      by_cases hv : twWsgn d0 * (a + b) = 0
      · rw [twIte_true _ _ hv, hv]
        simp
      · rw [twIte_false _ _ hv, twLookupQ_cons]
        by_cases hc : d = d0 ∧ i = j
        · have e : 49128 + 24 * d0 + j = 49128 + 24 * d + i := by omega
          rw [twIte_true _ _ e, twIte_true _ _ hc]
        · have e : ¬ (49128 + 24 * d0 + j = 49128 + 24 * d + i) := by omega
          rw [twIte_false _ _ e, twIte_false _ _ hc]
    rw [hrest, ih]
    simp only [List.length_cons]
    rcases lt_trichotomy d d0 with hd | hd | hd
    · have h1 : ¬ (d = d0 ∧ i = j) := by omega
      have h2 : ¬ (i = j ∧ d0 + 1 ≤ d ∧ d < d0 + 1 + as.length) := by omega
      have h3 : ¬ (i = j ∧ d0 ≤ d ∧ d < d0 + (as.length + 1)) := by omega
      rw [twIte_false _ _ h1, twIte_false _ _ h2, twIte_false _ _ h3, add_zero]
    · subst hd
      have h2 : ¬ (i = j ∧ d + 1 ≤ d ∧ d < d + 1 + as.length) := by omega
      rw [twIte_false _ _ h2, add_zero, Nat.sub_self]
      by_cases hij : i = j
      · have h1 : d = d ∧ i = j := ⟨rfl, hij⟩
        have h3 : i = j ∧ d ≤ d ∧ d < d + (as.length + 1) := ⟨hij, le_rfl, by omega⟩
        rw [twIte_true _ _ h1, twIte_true _ _ h3]
        simp
      · have h1 : ¬ (d = d ∧ i = j) := fun h => hij h.2
        have h3 : ¬ (i = j ∧ d ≤ d ∧ d < d + (as.length + 1)) := fun h => hij h.1
        rw [twIte_false _ _ h1, twIte_false _ _ h3]
    · have h1 : ¬ (d = d0 ∧ i = j) := by omega
      have hs : d - d0 = (d - (d0 + 1)) + 1 := by omega
      rw [twIte_false _ _ h1, zero_add]
      by_cases hc : i = j ∧ d0 + 1 ≤ d ∧ d < d0 + 1 + as.length
      · have hc' : i = j ∧ d0 ≤ d ∧ d < d0 + (as.length + 1) := by omega
        rw [twIte_true _ _ hc, twIte_true _ _ hc', hs]
        simp
      · have hc' : ¬ (i = j ∧ d0 ≤ d ∧ d < d0 + (as.length + 1)) := by omega
        rw [twIte_false _ _ hc, twIte_false _ _ hc']

/-- Every odd walk term has an odd label of column `j` with a code label in range. -/
theorem twOddWalk_mem (j : ℕ) :
    ∀ (as bs : List ℤ) (d0 : ℕ), ∀ p ∈ twOddWalk j d0 as bs,
      ∃ d, d0 ≤ d ∧ d < d0 + as.length ∧ p.1 = 49128 + 24 * d + j
  | [], bs, d0, p, hp => by simp [twOddWalk] at hp
  | _ :: _, [], _, p, hp => by simp [twOddWalk] at hp
  | a :: as, b :: bs, d0, p, hp => by
    have ih := twOddWalk_mem j as bs (d0 + 1)
    simp only [twOddWalk] at hp
    split_ifs at hp
    · obtain ⟨d, h1, h2, h3⟩ := ih p hp
      exact ⟨d, by omega, by simp; omega, h3⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨d0, le_rfl, by simp, rfl⟩
      · obtain ⟨d, h1, h2, h3⟩ := ih p hp
        exact ⟨d, by omega, by simp; omega, h3⟩

/-- The odd terms of column `j` of a packed tensor. -/
def twOddCol (w : ℕ) (X : List SVec) (j : ℕ) : List (ℕ × ℤ) :=
  twOddWalk j 0 ((twColVals w (tcol X j)).take 2048) ((twColVals w (tcol X j)).drop 2048)

/-- The odd short terms of the triality image of a packed tensor. -/
def twTriOdd (w : ℕ) (X : List SVec) : List (ℕ × ℤ) := (List.range 24).flatMap (twOddCol w X)

/-- Lookups in one odd column. -/
theorem twOddCol_lookup (w : ℕ) (X : List SVec) (j d i : ℕ) (hj : j < 24) (hd : d < 2048)
    (hi : i < 24) :
    lookupQ (twOddCol w X j) (49128 + 24 * d + i) =
      if i = j then ((twWsgn d * (sval w (tcol X j) d + sval w (tcol X j) (d + 2048)) : ℤ) : ℚ)
      else 0 := by
  have hlen := twColVals_length w (tcol X j)
  have l1 : ((twColVals w (tcol X j)).take 2048).length = 2048 := by
    rw [List.length_take, hlen]; rfl
  have l2 : ((twColVals w (tcol X j)).drop 2048).length = 2048 := by
    rw [List.length_drop, hlen]
  rw [twOddCol, twOddWalk_lookup j i hj hi _ _ 0 d (by rw [l1, l2]), l1]
  by_cases hij : i = j
  · have hc : i = j ∧ 0 ≤ d ∧ d < 0 + 2048 := ⟨hij, Nat.zero_le _, by omega⟩
    rw [twIte_true _ _ hc, twIte_true _ _ hij, Nat.sub_zero]
    have g1 : ((twColVals w (tcol X j)).take 2048).getD d 0 = sval w (tcol X j) d := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_take, twIte_true _ _ hd,
        ← List.getD_eq_getElem?_getD, twColVals_getD w _ d (by omega)]
    have g2 : ((twColVals w (tcol X j)).drop 2048).getD d 0 = sval w (tcol X j) (d + 2048) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
        twColVals_getD w _ (2048 + d) (by omega), Nat.add_comm]
    rw [g1, g2]
  · have hc : ¬ (i = j ∧ 0 ≤ d ∧ d < 0 + 2048) := fun h => hij h.1
    rw [twIte_false _ _ hc, twIte_false _ _ hij]

/-- Lookups in the odd short terms of the image. -/
theorem twTriOdd_lookup (w : ℕ) (X : List SVec) (d i : ℕ) (hd : d < 2048) (hi : i < 24) :
    lookupQ (twTriOdd w X) (49128 + 24 * d + i) =
      ((twWsgn d * (sval w (tcol X i) d + sval w (tcol X i) (d + 2048)) : ℤ) : ℚ) := by
  have h := twSum_range_single (fun j => lookupQ (twOddCol w X j) (49128 + 24 * d + i)) i 24 hi
    (fun j hj hji => by
      rw [twOddCol_lookup w X j d i hj hd hi, twIte_false _ _ (Ne.symm hji)])
  change lookupQ ((List.range 24).flatMap (twOddCol w X)) (49128 + 24 * d + i) = _
  rw [twLookupQ_flatMap, h]
  rw [twOddCol_lookup w X i d i hi hd hi, twIte_true _ _ rfl]

/-- Every odd short term of the image has an odd label. -/
theorem twTriOdd_labels (w : ℕ) (X : List SVec) :
    ∀ p ∈ twTriOdd w X, 49128 ≤ p.1 ∧ p.1 < 98280 := by
  intro p hp
  rw [twTriOdd, List.mem_flatMap] at hp
  obtain ⟨j, hj, hp⟩ := hp
  have hj24 := List.mem_range.mp hj
  obtain ⟨d, -, h2, h3⟩ := twOddWalk_mem j _ _ 0 p hp
  have hlen := twColVals_length w (tcol X j)
  have l1 : ((twColVals w (tcol X j)).take 2048).length = 2048 := by
    rw [List.length_take, hlen]; rfl
  rw [l1] at h2
  omega

/-! ## Octad blocks of the image -/

/-- All entries of the octad blocks of `B` with octad label `o`, merged. -/
def twMergeOct (B : List (ℕ × List (ℕ × ℤ))) (o : ℕ) : List (ℕ × ℤ) :=
  (B.filter (fun b => b.1 == o)).flatMap Prod.snd

/-- The octad Fourier transform of a block, scaled by `K`, without zero entries. -/
def twFourierOct (K : ℤ) (es : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  ((List.range 64).map (fun e => (e, K * (es.map (fun q => octMT true e q.1 * q.2)).sum))).filter
    (fun q => q.2 != 0)

/-- The octad blocks of the image over a list of octad labels. -/
def twTriOct (K : ℤ) (B : List (ℕ × List (ℕ × ℤ))) (os : List ℕ) : List (ℕ × List (ℕ × ℤ)) :=
  os.map (fun o => (o, twFourierOct K (twMergeOct B o)))

/-- Dropping zero terms does not change lookups. -/
theorem twLookupQ_filter (lab : ℕ) :
    ∀ L : List (ℕ × ℤ), lookupQ (L.filter (fun q => q.2 != 0)) lab = lookupQ L lab
  | [] => rfl
  | q :: L => by
    rw [List.filter_cons, twLookupQ_cons]
    by_cases hq : q.2 = 0
    · have : (q.2 != 0) = false := by simp [hq]
      rw [this]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [twLookupQ_filter lab L, hq]
      simp
    · have : (q.2 != 0) = true := by simp [hq]
      rw [this]
      simp only [↓reduceIte]
      rw [twLookupQ_cons, twLookupQ_filter lab L]

/-- Lookups in a list indexed by `List.range n`. -/
theorem twLookupQ_range (v : ℕ → ℤ) (lab : ℕ) :
    ∀ n, lookupQ ((List.range n).map (fun e => (e, v e))) lab = if lab < n then (v lab : ℚ) else 0
  | 0 => by simp [twLookupQ_nil]
  | n + 1 => by
    rw [List.range_succ, List.map_append, twLookupQ_append, twLookupQ_range v lab n,
      List.map_singleton, twLookupQ_cons, twLookupQ_nil, add_zero]
    by_cases h1 : lab < n
    · have h2 : lab < n + 1 := by omega
      have h3 : ¬ (n = lab) := by omega
      rw [twIte_true _ _ h1, twIte_true _ _ h2, twIte_false _ _ h3, add_zero]
    · rw [twIte_false _ _ h1, zero_add]
      by_cases h2 : lab = n
      · subst h2
        rw [twIte_true _ _ rfl, twIte_true _ _ (Nat.lt_succ_self lab)]
      · have h3 : ¬ lab < n + 1 := by omega
        rw [twIte_false _ _ (Ne.symm h2), twIte_false _ _ h3]

/-- Lookups in a Fourier block. -/
theorem twFourierOct_lookup (K : ℤ) (es : List (ℕ × ℤ)) (e : ℕ) (he : e < 64) :
    lookupQ (twFourierOct K es) e =
      ((K * (es.map (fun q => octMT true e q.1 * q.2)).sum : ℤ) : ℚ) := by
  rw [twFourierOct, twLookupQ_filter, twLookupQ_range _ e 64, twIte_true _ _ he]

/-- Lookups in blocks over a duplicate-free label list. -/
theorem twOctLookupQ_map (F : ℕ → List (ℕ × ℤ)) (o f : ℕ) :
    ∀ os : List ℕ, os.Nodup →
      octLookupQ (os.map (fun o' => (o', F o'))) o f = if o ∈ os then lookupQ (F o) f else 0
  | [], _ => by simp [octLookupQ]
  | o' :: os, h => by
    have hn := List.nodup_cons.mp h
    have ih := twOctLookupQ_map F o f os hn.2
    have hc : octLookupQ (List.map (fun o'' => (o'', F o'')) (o' :: os)) o f =
        (if o' = o then lookupQ (F o') f else 0) +
          octLookupQ (List.map (fun o'' => (o'', F o'')) os) o f := by
      simp [octLookupQ]
    rw [hc, ih]
    by_cases h1 : o' = o
    · subst h1
      rw [twIte_true _ _ rfl, twIte_false _ _ hn.1, add_zero,
        twIte_true _ _ List.mem_cons_self]
    · rw [twIte_false _ _ h1, zero_add]
      by_cases h2 : o ∈ os
      · rw [twIte_true _ _ h2, twIte_true _ _ (List.mem_cons_of_mem _ h2)]
      · have h3 : ¬ o ∈ o' :: os := by
          simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm h1, h2⟩
        rw [twIte_false _ _ h2, twIte_false _ _ h3]

/-- Sums over a merged block are sums over the blocks with that label. -/
theorem twMergeOct_sum (g : ℕ × ℤ → ℤ) (o : ℕ) :
    ∀ B : List (ℕ × List (ℕ × ℤ)),
      ((twMergeOct B o).map g).sum = (B.map (fun b => if b.1 = o then (b.2.map g).sum else 0)).sum
  | [] => rfl
  | b :: B => by
    have ih := twMergeOct_sum g o B
    unfold twMergeOct at ih ⊢
    rw [List.filter_cons]
    by_cases hb : b.1 = o
    · have : (b.1 == o) = true := by simp [hb]
      rw [this]
      simp only [↓reduceIte, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, hb]
      rw [ih]
    · have : (b.1 == o) = false := by simp [hb]
      rw [this]
      simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, hb, zero_add]
      exact ih

/-- The table Fourier coefficient is the triality matrix entry. -/
theorem twOctMT_eq (e f : Fin 64) : (octMT true e.val f.val : ℚ) = trialityIntegerMatrix e f := by
  rw [octMT_eq, octM]
  simp only [↓reduceIte, Nat.mod_eq_of_lt e.isLt, Nat.mod_eq_of_lt f.isLt]

/-- The octad Fourier sum of a block with labels below `64`. -/
theorem twFourier_sum (e : Fin 64) :
    ∀ es : List (ℕ × ℤ), es.all (fun q => decide (q.1 < 64)) = true →
      (∑ f : Fin 64, (trialityIntegerMatrix e f : ℚ) / 8 * lookupQ es f.val) =
        (((es.map (fun q => octMT true e.val q.1 * q.2)).sum : ℤ) : ℚ) / 8
  | [], _ => by simp [twLookupQ_nil]
  | q :: es, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := twFourier_sum e es h.2
    have hs : ∀ f : Fin 64, (trialityIntegerMatrix e f : ℚ) / 8 * lookupQ (q :: es) f.val =
        (if (⟨q.1, h.1⟩ : Fin 64) = f then (trialityIntegerMatrix e f : ℚ) / 8 * q.2 else 0) +
          (trialityIntegerMatrix e f : ℚ) / 8 * lookupQ es f.val := by
      intro f
      rw [twLookupQ_cons]
      by_cases hf : q.1 = f.val
      · have : (⟨q.1, h.1⟩ : Fin 64) = f := Fin.ext hf
        rw [twIte_true _ _ hf, twIte_true _ _ this]
        ring
      · have : ¬ (⟨q.1, h.1⟩ : Fin 64) = f := fun h' => hf (by rw [← h'])
        rw [twIte_false _ _ hf, twIte_false _ _ this]
        ring
    rw [Finset.sum_congr rfl (fun f _ => hs f), Finset.sum_add_distrib, Finset.sum_ite_eq,
      twIte_true _ _ (Finset.mem_univ _), ih, List.map_cons, List.sum_cons]
    have hm := twOctMT_eq e ⟨q.1, h.1⟩
    simp only at hm
    push_cast
    rw [hm]
    ring

/-! ## The tensor block of the image -/

/-- Lookups as integer sums. -/
theorem twLookupQ_int (lab : ℕ) :
    ∀ L : List (ℕ × ℤ),
      lookupQ L lab = (((L.map (fun p => if p.1 = lab then p.2 else 0)).sum : ℤ) : ℚ)
  | [] => rfl
  | p :: L => by
    rw [twLookupQ_cons, twLookupQ_int lab L, List.map_cons, List.sum_cons]
    push_cast
    split_ifs <;> simp

/-- The integral coordinate sign `(-1)^(c_j)` of an odd code label, from the generator masks. -/
def twCsgn (d j : ℕ) : ℤ := if bpar (d &&& gcol j) 12 then -1 else 1

/-- The coordinate sign is the Golay code coordinate sign. -/
theorem twCsgn_eq (d j : ℕ) :
    twCsgn d j = if (golayEncodedMask d).testBit j then -1 else 1 := by
  rw [twCsgn, golayEncodedMask_testBit]

/-- Coordinate signs are units. -/
theorem twCsgn_natAbs (d j : ℕ) : (twCsgn d j).natAbs = 1 := by
  unfold twCsgn
  split_ifs <;> rfl

/-- The packed odd-short part of column `j` of the image tensor (numerators over `2 D`). -/
def twCPart (w : ℕ) (K3 : ℤ) (odd : List (ℕ × ℤ)) (j : ℕ) : SVec :=
  ssum ((odd.filter (fun q => oddJ q.1 == j)).map
    (fun q => unitVec w (oddD q.1) (twCsgn (oddD q.1) j * (K3 * q.2))))

/-- The packed tensor block of the image. -/
def twTriTen (w : ℕ) (K3 : ℤ) (X : List SVec) (odd : List (ℕ × ℤ)) : List SVec :=
  (List.range 24).map (fun j => sadd (tcol (trialityTensorT w false X) j) (twCPart w K3 odd j))

set_option maxRecDepth 100000 in
/-- Bounds and values of the packed odd-short part. -/
theorem twCPart_spec (w : ℕ) (K3 : ℤ) (odd : List (ℕ × ℤ)) (Bv : ℕ) (j : ℕ)
    (hBv : ∀ q ∈ odd, (K3 * q.2).natAbs ≤ Bv) (hB : odd.length * Bv < 2 ^ w) :
    SBnd w (2 ^ 12) (odd.length * Bv) (twCPart w K3 odd j) ∧
      ∀ k < 4096, sval w (twCPart w K3 odd j) k =
        ((odd.filter (fun q => oddJ q.1 == j)).map (fun q =>
          if k = oddD q.1 then twCsgn (oddD q.1) j * (K3 * q.2)
          else if k = oddD q.1 + 2048 then -(twCsgn (oddD q.1) j * (K3 * q.2)) else 0)).sum := by
  have hval : ∀ q ∈ odd.filter (fun q => oddJ q.1 == j),
      (twCsgn (oddD q.1) j * (K3 * q.2)).natAbs ≤ Bv ∧
        (twCsgn (oddD q.1) j * (K3 * q.2)).natAbs < 2 ^ w := by
    intro q hq
    have hq' := (List.mem_filter.mp hq).1
    have h1 : (twCsgn (oddD q.1) j * (K3 * q.2)).natAbs ≤ Bv := by
      rw [Int.natAbs_mul, twCsgn_natAbs, one_mul]
      exact hBv q hq'
    have hpos : 1 ≤ odd.length := List.length_pos_of_mem hq'
    refine ⟨h1, lt_of_le_of_lt h1 (lt_of_le_of_lt ?_ hB)⟩
    nlinarith
  have hd : ∀ l : ℕ, oddD l < 2048 := fun l => Nat.mod_lt _ (by decide)
  have hxs : ∀ x ∈ (odd.filter (fun q => oddJ q.1 == j)).map
      (fun q => unitVec w (oddD q.1) (twCsgn (oddD q.1) j * (K3 * q.2))), SBnd w (2 ^ 12) Bv x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact (unitVec_spec w _ _ (hd q.1) (hval q hq).2).1.mono (hval q hq).1
  have hlen : ((odd.filter (fun q => oddJ q.1 == j)).map
      (fun q => unitVec w (oddD q.1) (twCsgn (oddD q.1) j * (K3 * q.2)))).length ≤ odd.length := by
    rw [List.length_map]
    exact List.length_filter_le _ _
  obtain ⟨h1, h2⟩ := ssum_spec _ hxs (lt_of_le_of_lt (Nat.mul_le_mul_right _ hlen) hB)
  refine ⟨h1.mono (Nat.mul_le_mul_right _ hlen), fun k hk => ?_⟩
  rw [twCPart, h2 k (by norm_num; exact hk), List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  exact (unitVec_spec w _ _ (hd q.1) (hval q hq).2).2 k

/-- One odd term of the packed odd-short part. -/
theorem twCPart_term (K3 : ℤ) (j k : ℕ) (hj : j < 24) (hk : k < 4096) (l : ℕ) (c : ℤ)
    (h1 : 49128 ≤ l) (h2 : l < 98280) :
    (if oddJ l = j then
      (if k = oddD l then twCsgn (oddD l) j * (K3 * c)
        else if k = oddD l + 2048 then -(twCsgn (oddD l) j * (K3 * c)) else 0) else 0) =
      (if 2048 ≤ k then -1 else 1) * twCsgn (k % 2048) j * K3 *
        (if l = 49128 + 24 * (k % 2048) + j then c else 0) := by
  unfold oddD oddJ
  by_cases hJ : (l - 49128) % 24 = j
  · by_cases hD : (l - 49128) / 24 % 2048 = k % 2048
    · have hl : l = 49128 + 24 * (k % 2048) + j := by omega
      rw [twIte_true _ _ hJ, twIte_true _ _ hl, hD]
      by_cases hk2 : 2048 ≤ k
      · have e1 : ¬ k = k % 2048 := by omega
        have e2 : k = k % 2048 + 2048 := by omega
        rw [twIte_false _ _ e1, twIte_true _ _ e2, twIte_true _ _ hk2]
        ring
      · have e1 : k = k % 2048 := by omega
        rw [twIte_true _ _ e1, twIte_false _ _ hk2]
        ring
    · have hl : ¬ l = 49128 + 24 * (k % 2048) + j := by omega
      have e1 : ¬ k = (l - 49128) / 24 % 2048 := by omega
      have e2 : ¬ k = (l - 49128) / 24 % 2048 + 2048 := by omega
      rw [twIte_true _ _ hJ, twIte_false _ _ e1, twIte_false _ _ e2, twIte_false _ _ hl]
      ring
  · have hl : ¬ l = 49128 + 24 * (k % 2048) + j := by omega
    rw [twIte_false _ _ hJ, twIte_false _ _ hl]
    ring

/-- The packed odd-short part is the odd lookup, with signs and scale. -/
theorem twCPart_sum (K3 : ℤ) (j k : ℕ) (hj : j < 24) (hk : k < 4096) :
    ∀ odd : List (ℕ × ℤ), (∀ q ∈ odd, 49128 ≤ q.1 ∧ q.1 < 98280) →
      ((odd.filter (fun q => oddJ q.1 == j)).map (fun q =>
          if k = oddD q.1 then twCsgn (oddD q.1) j * (K3 * q.2)
          else if k = oddD q.1 + 2048 then -(twCsgn (oddD q.1) j * (K3 * q.2)) else 0)).sum =
        (if 2048 ≤ k then -1 else 1) * twCsgn (k % 2048) j * K3 *
          (odd.map (fun q => if q.1 = 49128 + 24 * (k % 2048) + j then q.2 else 0)).sum
  | [], _ => by simp
  | q :: odd, h => by
    have ih := twCPart_sum K3 j k hj hk odd (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    have hq := h q List.mem_cons_self
    have ht := twCPart_term K3 j k hj hk q.1 q.2 hq.1 hq.2
    rw [List.filter_cons, List.map_cons, List.sum_cons, mul_add, ← ht, ← ih]
    by_cases hJ : oddJ q.1 = j
    · have : (oddJ q.1 == j) = true := by simp [hJ]
      rw [this]
      simp only [↓reduceIte, List.map_cons, List.sum_cons]
      rw [twIte_true _ _ hJ]
    · have : (oddJ q.1 == j) = false := by simp [hJ]
      rw [this]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [twIte_false _ _ hJ, zero_add]

/-! ## Checks of the literal blocks -/

/-- The triality matrix entry from a source representation. -/
def twTriMatEntry (L : IdentVec) (i j : Fin 24) : ℚ :=
  if i = j then L.mat.entry i i else
    L.sden * (lookupQ L.sh.pairs (generatedAxisGlobalFinitePairIndex i j).val +
      lookupQ L.sh.pairs (276 + (generatedAxisGlobalFinitePairIndex i j).val)) / 2

/-- Entrywise check of a literal image matrix. -/
def twMatCheck (M' : MatRep) (L : IdentVec) : Bool :=
  (List.finRange 24).all (fun i => (List.finRange 24).all (fun j =>
    decide (M'.entry i j = twTriMatEntry L i j)))

/-- The triality pair coordinate from a source representation. -/
def twTriPairEntry (L : IdentVec) (s p : ℕ) : ℚ :=
  if s = 0 then L.mat.entry (pairCoordsF p).1 (pairCoordsF p).2 +
      (L.sden * lookupQ L.sh.pairs p - L.sden * lookupQ L.sh.pairs (276 + p)) / 2
  else (L.sden * lookupQ L.sh.pairs p - L.sden * lookupQ L.sh.pairs (276 + p)) / 2 -
      L.mat.entry (pairCoordsF p).1 (pairCoordsF p).2

/-- Check of literal image pair terms at the short scale `1 / (2 D)`. -/
def twPairCheck (P' : List (ℕ × ℤ)) (L : IdentVec) (D : ℚ) : Bool :=
  P'.all (fun q => decide (q.1 < 552)) &&
    (List.finRange 2).all (fun s => (List.finRange 276).all (fun p =>
      decide (lookupQ P' (276 * s.val + p.val) / (2 * D) = twTriPairEntry L s.val p.val)))

/-- A strictly increasing list of naturals (linear check). -/
def twIncr : List ℕ → Bool
  | a :: b :: l => decide (a < b) && twIncr (b :: l)
  | _ => true

/-- The head of a strictly increasing list is below every later entry. -/
theorem twIncr_lt : ∀ (a : ℕ) (l : List ℕ), twIncr (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, x, hx => by simp at hx
  | a, b :: l, h, x, hx => by
    simp only [twIncr, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (twIncr_lt b l h.2 x hx)

/-- A strictly increasing list has no duplicates. -/
theorem twIncr_nodup : ∀ l : List ℕ, twIncr l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [a], _ => List.nodup_singleton a
  | a :: b :: l, h => by
    have h' := h
    simp only [twIncr, Bool.and_eq_true, decide_eq_true_eq] at h'
    apply List.nodup_cons.mpr
    refine ⟨fun hm => ?_, twIncr_nodup (b :: l) h'.2⟩
    exact lt_irrefl a (twIncr_lt a (b :: l) h a hm)

/-- The membership mask of a list of naturals. -/
def twOctMask (os : List ℕ) : ℕ := os.foldr (fun o m => m ||| (1 <<< o)) 0

/-- Bits of the membership mask are the members. -/
theorem twOctMask_testBit (x : ℕ) : ∀ os : List ℕ, (twOctMask os).testBit x = true ↔ x ∈ os
  | [] => by simp [twOctMask]
  | o :: os => by
    have ih := twOctMask_testBit x os
    simp only [twOctMask, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h

/-- Check of the octad label list: below `759`, strictly increasing, covering every block of
`L`. -/
def twOctCheck (os : List ℕ) (L : IdentVec) : Bool :=
  os.all (fun o => decide (o < 759)) && twIncr os &&
    L.sh.oct.all (fun b => (twOctMask os).testBit b.1)

/-- Consequences of the octad label check. -/
theorem twOctCheck_spec (os : List ℕ) (L : IdentVec) (h : twOctCheck os L = true) :
    (∀ o ∈ os, o < 759) ∧ os.Nodup ∧ ∀ b ∈ L.sh.oct, b.1 ∈ os := by
  simp only [twOctCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, twIncr_nodup os h.1.2, fun b hb => (twOctMask_testBit b.1 os).mp (h.2 b hb)⟩

/-- The fast coordinate pair of a pair index is the catalogue pair. -/
theorem twPairCoordsF (p : Fin 276) :
    pairCoordsF p.val = generatedAxisGlobalPairCoordinates p := by
  rw [pairCoordsF_eq, pairCoords]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt p.isLt)

/-! ## The image vector -/

/-- The identification vector of the forward triality image of `L`. -/
def twTriVec (w : ℕ) (L : IdentVec) (X : List SVec) (D : ℚ) (M' : MatRep) (P' : List (ℕ × ℤ))
    (os : List ℕ) (Ko K3 : ℤ) : IdentVec :=
  ⟨M', ⟨P', twTriOct Ko L.sh.oct os, twTriOdd w X⟩, 1 / (2 * D),
    tensorRat w (twTriTen w K3 X L.sh.odd) (2 * D)⟩

/-- The tensor block of the image vector. -/
theorem twTriVec_ten (w : ℕ) (L : IdentVec) (X : List SVec) (D : ℚ) (M' : MatRep)
    (P' : List (ℕ × ℤ)) (os : List ℕ) (Ko K3 : ℤ) :
    (twTriVec w L X D M' P' os Ko K3).ten = tensorRat w (twTriTen w K3 X L.sh.odd) (2 * D) := rfl

/-- The short block of the image vector satisfies the range conditions. -/
theorem twTriVec_ok (w : ℕ) (L : IdentVec) (X : List SVec) (D : ℚ) (M' : MatRep)
    (P' : List (ℕ × ℤ)) (os : List ℕ) (Ko K3 : ℤ) (hP : twPairCheck P' L D = true)
    (hO : twOctCheck os L = true) : (twTriVec w L X D M' P' os Ko K3).sh.ok = true := by
  have hO' := twOctCheck_spec os L hO
  simp only [twPairCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hP
  simp only [twTriVec, ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨hP.1, ?_⟩, fun q hq => twTriOdd_labels w X q hq⟩
  intro b hb
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hb
  refine ⟨hO'.1 o ho, ?_⟩
  intro q hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq).1
  exact List.mem_range.mp he

/-- Bounds of the packed tensor block of the image. -/
theorem twTriTen_bnd (w B Bv : ℕ) (K3 : ℤ) (X : List SVec) (odd : List (ℕ × ℤ))
    (hX : TBnd w B X) (hBv : ∀ q ∈ odd, (K3 * q.2).natAbs ≤ Bv)
    (hB : 4 * B + odd.length * Bv < 2 ^ w) :
    TBnd w (4 * B + odd.length * Bv) (twTriTen w K3 X odd) := by
  intro j hj
  rw [twTriTen, tcol_range_map _ 24 j hj]
  have hT := (trialityTensorT_spec false hX (by omega)).1 j hj
  have hC := (twCPart_spec w K3 odd Bv j hBv (by omega)).1
  exact (sadd_spec hT hC hB).1

/-- Bit `11` of a spin label is its upper half. -/
theorem twTestBit11 (k : ℕ) (hk : k < 4096) : k.testBit 11 = decide (2048 ≤ k) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> norm_num at h ⊢ <;> omega

/-- A list sum of integer values over `8`. -/
theorem twCastSumDiv {α : Type} (T : α → ℤ) :
    ∀ l : List α, (l.map (fun b => ((T b : ℤ) : ℚ) / 8)).sum = (((l.map T).sum : ℤ) : ℚ) / 8
  | [] => by simp
  | b :: l => by
    rw [List.map_cons, List.sum_cons, twCastSumDiv T l, List.map_cons, List.sum_cons]
    push_cast
    ring

set_option maxHeartbeats 1000000 in
-- One elaboration covering all three blocks and the three short label kinds.
/-- The rational packet of the image vector is the triality image of the packet of `L`. -/
theorem twTriVec_packet (w B Bv : ℕ) (L : IdentVec) (X : List SVec) (D : ℚ) (M' : MatRep)
    (P' : List (ℕ × ℤ)) (os : List ℕ) (Ko K3 : ℤ) (hL : L.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hD : D ≠ 0) (hX : TBnd w B X)
    (hBv : L.sh.odd.all (fun q => decide ((K3 * q.2).natAbs ≤ Bv)) = true)
    (hB : 4 * B + L.sh.odd.length * Bv < 2 ^ w)
    (hK3 : (K3 : ℚ) = L.sden * (2 * D)) (hKo : (Ko : ℚ) / (2 * D) = L.sden / 8)
    (hM : twMatCheck M' L = true) (hP : twPairCheck P' L D = true)
    (hO : twOctCheck os L = true) :
    (twTriVec w L X D M' P' os Ko K3).packet = generatedAxisGlobalRationalTriality L.packet := by
  have hok := twTriVec_ok w L X D M' P' os Ko K3 hP hO
  have hL' := hL
  simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hL'
  obtain ⟨⟨-, hLo⟩, hLd⟩ := hL'
  simp only [twMatCheck, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at hM
  have hP' := hP
  simp only [twPairCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at hP'
  obtain ⟨-, hOn, hOc⟩ := twOctCheck_spec os L hO
  simp only [List.all_eq_true, decide_eq_true_eq] at hBv
  have h2D : (2 : ℚ) * D ≠ 0 := mul_ne_zero two_ne_zero hD
  have eP : (twTriVec w L X D M' P' os Ko K3).sh.pairs = P' := rfl
  have eO : (twTriVec w L X D M' P' os Ko K3).sh.oct = twTriOct Ko L.sh.oct os := rfl
  have eD : (twTriVec w L X D M' P' os Ko K3).sh.odd = twTriOdd w X := rfl
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- the matrix block
    change M'.toMat = generatedAxisGlobalTrialityMatrixQ L.packet
    ext i j
    rw [MatRep.toMat_apply, hM i j, twTriMatEntry, generatedAxisGlobalTrialityMatrixQ]
    by_cases hij : i = j
    · rw [twIte_true _ _ hij, twIte_true _ _ hij]
      subst hij
      change _ = L.mat.toMat i i
      rw [MatRep.toMat_apply]
    · rw [twIte_false _ _ hij, twIte_false _ _ hij]
      change _ = (L.sden * shortFunQ L.sh.flat _ + L.sden * shortFunQ L.sh.flat _) / 2
      rw [shortFunQ_flat_pair L.sh hL, shortFunQ_flat_pair L.sh hL]
      simp only [Fin.val_zero, Fin.val_one, mul_zero, zero_add, mul_one]
      ring
  · -- the short block
    funext r
    change (1 / (2 * D)) * shortFunQ (twTriVec w L X D M' P' os Ko K3).sh.flat r =
      generatedAxisGlobalTrialityShortQ L.packet r
    rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
    · -- pair labels
      rw [shortFunQ_flat_pair _ hok, eP, show (1 / (2 * D)) * lookupQ P' (276 * s.val + p.val) =
        lookupQ P' (276 * s.val + p.val) / (2 * D) by ring, hP'.2 s p, twTriPairEntry,
        twPairCoordsF]
      simp only [generatedAxisGlobalTrialityShortQ, IdentVec.packet, MatRep.toMat_apply]
      rw [shortFunQ_flat_pair L.sh hL, shortFunQ_flat_pair L.sh hL]
      fin_cases s <;> simp
    · -- octad labels
      rw [shortFunQ_flat_oct _ hok, eO]
      simp only [generatedAxisGlobalTrialityShortQ, IdentVec.packet]
      have hR : (∑ f : Fin 64, (trialityIntegerMatrix e f : ℚ) / 8 *
          (L.sden * shortFunQ L.sh.flat (Sum.inr (Sum.inl (o, f))))) =
          L.sden * (L.sh.oct.map (fun b => if b.1 = o.val then
            (((b.2.map (fun q => octMT true e.val q.1 * q.2)).sum : ℤ) : ℚ) / 8 else 0)).sum := by
        have h1 : ∀ f : Fin 64, (trialityIntegerMatrix e f : ℚ) / 8 *
            (L.sden * shortFunQ L.sh.flat (Sum.inr (Sum.inl (o, f)))) =
            L.sden * (L.sh.oct.map (fun b => if b.1 = o.val then
              (trialityIntegerMatrix e f : ℚ) / 8 * lookupQ b.2 f.val else 0)).sum := by
          intro f
          rw [shortFunQ_flat_oct L.sh hL, octLookupQ, mul_left_comm, ← List.sum_map_mul_left]
          congr 1
          apply congrArg List.sum
          apply List.map_congr_left
          intro b _
          split_ifs <;> ring
        rw [Finset.sum_congr rfl (fun f _ => h1 f), ← Finset.mul_sum, finset_sum_list_sum]
        congr 1
        apply congrArg List.sum
        apply List.map_congr_left
        intro b hb
        by_cases hbo : b.1 = o.val
        · simp only [hbo, ↓reduceIte]
          exact twFourier_sum e b.2
            (List.all_eq_true.mpr (fun q hq => decide_eq_true ((hLo b hb).2 q hq)))
        · simp only [hbo, ↓reduceIte, Finset.sum_const_zero]
      rw [hR, twTriOct, twOctLookupQ_map _ _ _ os hOn]
      have hR2 : (L.sh.oct.map (fun b => if b.1 = o.val then
            (((b.2.map (fun q => octMT true e.val q.1 * q.2)).sum : ℤ) : ℚ) / 8 else 0)).sum =
          (((L.sh.oct.map (fun b => if b.1 = o.val then
            (b.2.map (fun q => octMT true e.val q.1 * q.2)).sum else 0)).sum : ℤ) : ℚ) / 8 := by
        rw [← twCastSumDiv]
        apply congrArg List.sum
        apply List.map_congr_left
        intro b _
        split_ifs <;> simp
      rw [hR2]
      by_cases ho : o.val ∈ os
      · rw [twIte_true _ _ ho, twFourierOct_lookup _ _ _ e.isLt,
          twMergeOct_sum (fun q => octMT true e.val q.1 * q.2) o.val L.sh.oct]
        rw [Int.cast_mul]
        have hk : (1 / (2 * D)) * (Ko : ℚ) = L.sden / 8 := by rw [← hKo]; ring
        rw [← mul_assoc, hk]
        ring
      · rw [twIte_false _ _ ho, mul_zero]
        have h0 : (L.sh.oct.map (fun b => if b.1 = o.val then
            (b.2.map (fun q => octMT true e.val q.1 * q.2)).sum else 0)).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          have hbo : ¬ b.1 = o.val := fun h => ho (h ▸ hOc b hb)
          rw [twIte_false _ _ hbo]
        rw [h0]
        simp
    · -- odd labels
      rw [shortFunQ_flat_odd _ hok, eD]
      simp only [generatedAxisGlobalTrialityShortQ, IdentVec.packet]
      rw [generatedAxisGlobalSpinLabel_coeff, generatedAxisGlobalSpinLabel_coeff, hLt,
        twTriOdd_lookup w X d.val i.val d.isLt i.isLt, twWsgn_eq d.val d.isLt]
      simp only [tensorRat]
      push_cast
      field_simp
  · -- the tensor block
    funext t i
    obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
    have hpk : L.packet.2.2 = fun t i => tensorRat w X D (generatedAxisGlobalSpinLabel t) i := by
      funext t i
      change L.ten _ _ = _
      rw [hLt]
    change tensorRat w (twTriTen w K3 X L.sh.odd) (2 * D)
        (generatedAxisGlobalSpinLabel (golayLabelCoefficients k)) i =
      generatedAxisGlobalTrialityScaledTensorQ L.packet.2.1 L.packet.2.2
        (golayLabelCoefficients k) i
    rw [hpk, trialityTensorT_fwd hX (by omega) D L.packet.2.1 (golayLabelCoefficients k) i,
      generatedAxisGlobalSpinLabel_coeff]
    have hcol := tcol_range_map (fun j => sadd (tcol (trialityTensorT w false X) j)
      (twCPart w K3 L.sh.odd j)) 24 i.val i.isLt
    have hT := (trialityTensorT_spec false hX (by omega)).1 i.val i.isLt
    obtain ⟨hC, hCv⟩ := twCPart_spec w K3 L.sh.odd Bv i.val hBv (by omega)
    have hsum := (sadd_spec hT hC hB).2 k.val
      (by rw [show (2 : ℕ) ^ 12 = 4096 by norm_num]; exact k.isLt)
    simp only [tensorRat]
    rw [twTriTen, hcol, hsum, hCv k.val k.isLt,
      twCPart_sum K3 i.val k.val i.isLt k.isLt L.sh.odd (fun q hq => hLd q hq)]
    unfold trialityCPartFwd
    simp only [generatedAxisGlobalSpinLabel_coeff, generatedAxisGlobalSpinLabelLow]
    change _ = (generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℚ) *
        (if (golayEncodedMask (k.val % 2048)).testBit i.val then -1 else 1) *
        (L.sden * shortFunQ L.sh.flat (Sum.inr (Sum.inr (⟨k.val % 2048, by omega⟩, i)))) +
      (sval w (tcol (trialityTensorT w false X) i.val) k.val : ℚ) / (2 * D)
    rw [shortFunQ_flat_odd L.sh hL, twLookupQ_int]
    have hz : (if (golayEncodedMask (k.val % 2048)).testBit i.val then (-1 : ℚ) else 1) =
        ((twCsgn (k.val % 2048) i.val : ℤ) : ℚ) := by
      rw [twCsgn_eq]
      split_ifs <;> simp
    have hb : golayLabelCoefficients k 11 = if 2048 ≤ k.val then 1 else 0 := by
      have h11 : k.val.testBit 11 = decide (2048 ≤ k.val) := twTestBit11 k.val k.isLt
      unfold golayLabelCoefficients
      change (if k.val.testBit 11 then (1 : ZMod 2) else 0) = _
      rw [h11]
      by_cases h : 2048 ≤ k.val <;> simp [h]
    have hs : (generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℚ) =
        ((if 2048 ≤ k.val then -1 else 1 : ℤ) : ℚ) := by
      rw [hb]
      by_cases h : 2048 ≤ k.val <;> simp [h, generatedAxisGlobalIntSign]
    rw [hz, hs]
    push_cast
    rw [hK3]
    field_simp
    ring

/-- A representation of `x` gives a representation of its forward triality image. -/
theorem twTriVec_actual (w B Bv : ℕ) (L : IdentVec) (X : List SVec) (D : ℚ) (M' : MatRep)
    (P' : List (ℕ × ℤ)) (os : List ℕ) (Ko K3 : ℤ) (hL : L.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hD : D ≠ 0) (hX : TBnd w B X)
    (hBv : L.sh.odd.all (fun q => decide ((K3 * q.2).natAbs ≤ Bv)) = true)
    (hB : 4 * B + L.sh.odd.length * Bv < 2 ^ w)
    (hK3 : (K3 : ℚ) = L.sden * (2 * D)) (hKo : (Ko : ℚ) / (2 * D) = L.sden / 8)
    (hM : twMatCheck M' L = true) (hP : twPairCheck P' L D = true)
    (hO : twOctCheck os L = true) (x : GriessSpace) (hx : griessConwayEncode x = L.real) :
    griessConwayEncode (sExtra x) = (twTriVec w L X D M' P' os Ko K3).real := by
  rw [generatedAxisGlobalRationalTriality_of_actual x L.packet hx, IdentVec.real,
    twTriVec_packet w B Bv L X D M' P' os Ko K3 hL hLt hD hX hBv hB hK3 hKo hM hP hO]

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
