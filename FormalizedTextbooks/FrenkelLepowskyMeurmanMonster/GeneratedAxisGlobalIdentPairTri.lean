/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairVec

/-! # Exact pairings of triality images from sparse representations

For representations `L` and `W` (`IdentVec`) of two Griess vectors, the Griess pairing of the
forward or inverse triality image of the first with the second is an explicit finite rational
expression `pairTri`: a matrix part (diagonal and the pair terms of `L`), a short part (one term
per short term of `W`; octad terms paired blockwise with the octad Fourier matrix), a tensor part
from the odd short terms of `L`, and the tensor-to-tensor part `Σ tPartQ · W.ten`, which is the
part to be evaluated on packed tensors.  Every finite reindexing (pair orientations, the two spin
labels of an odd label, octad blocks) is proved; no coordinate is omitted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-! ## Lookups -/

/-- The sum of the numerators of a list at one flat label. -/
def lookupQ (L : List (ℕ × ℤ)) (lab : ℕ) : ℚ :=
  (L.map (fun p => if p.1 = lab then (p.2 : ℚ) else 0)).sum

/-- The sum of the numerators of the octad blocks at one octad label. -/
def octLookupQ (B : List (ℕ × List (ℕ × ℤ))) (o f : ℕ) : ℚ :=
  (B.map (fun b => if b.1 = o then lookupQ b.2 f else 0)).sum

theorem shortDecode_pair_eq (j : ℕ) (hj : j < 552) (s : Fin 2) (p : Fin 276) :
    shortDecode j = Sum.inl (s, p) ↔ j = 276 * s.val + p.val := by
  have h : shortDecode j = Sum.inl (⟨j / 276 % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨j % 276, Nat.mod_lt _ (by decide)⟩) := by
    simp [shortDecode, hj]
  rw [h]
  simp only [Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff]
  omega

theorem shortDecode_pair_ne_oct (j : ℕ) (hj : j < 552) (o : Fin 759) (e : Fin 64) :
    shortDecode j ≠ Sum.inr (Sum.inl (o, e)) := by
  simp [shortDecode, hj]

theorem shortDecode_pair_ne_odd (j : ℕ) (hj : j < 552) (d : Fin 2048) (i : Fin 24) :
    shortDecode j ≠ Sum.inr (Sum.inr (d, i)) := by
  simp [shortDecode, hj]

theorem shortDecode_oct_eq' (o e : ℕ) (ho : o < 759) (he : e < 64) :
    shortDecode (552 + 64 * o + e) = Sum.inr (Sum.inl (⟨o, ho⟩, ⟨e, he⟩)) := by
  have h1 : ¬ 552 + 64 * o + e < 552 := by omega
  have h2 : 552 + 64 * o + e < 49128 := by omega
  simp only [shortDecode, h1, h2, ↓reduceIte, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
  constructor <;> apply Fin.ext <;> simp only <;> omega

theorem shortDecode_odd_eq' (j : ℕ) (h1 : 49128 ≤ j) (h2 : j < 98280) :
    shortDecode j = Sum.inr (Sum.inr (⟨(j - 49128) / 24, by omega⟩,
      ⟨(j - 49128) % 24, Nat.mod_lt _ (by decide)⟩)) := by
  have h3 : ¬ j < 552 := by omega
  have h4 : ¬ j < 49128 := by omega
  have h5 : (j - 49128) / 24 % 2048 = (j - 49128) / 24 := Nat.mod_eq_of_lt (by omega)
  simp only [shortDecode, h3, h4, ↓reduceIte, h5]

/-- Pair coordinates of a valid block are the pair lookups. -/
theorem shortFunQ_flat_pair (S : ShortData) (hS : S.ok = true) (s : Fin 2) (p : Fin 276) :
    shortFunQ S.flat (Sum.inl (s, p)) = lookupQ S.pairs (276 * s.val + p.val) := by
  simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨hp, ho⟩, hd⟩ := hS
  rw [ShortData.flat, shortFunQ_append, shortFunQ_append]
  have h1 : shortFunQ S.pairs (Sum.inl (s, p)) = lookupQ S.pairs (276 * s.val + p.val) := by
    unfold shortFunQ lookupQ
    congr 1
    apply List.map_congr_left
    intro q hq
    simp only [shortDecode_pair_eq q.1 (hp q hq) s p]
  have h2 : ∀ B : List (ℕ × List (ℕ × ℤ)),
      (∀ b ∈ B, b.1 < 759 ∧ ∀ q ∈ b.2, q.1 < 64) →
      shortFunQ (octsFlat B) (Sum.inl (s, p)) = 0 := by
    intro B hB
    induction B with
    | nil => rfl
    | cons b B ih =>
      rw [octsFlat, shortFunQ_append, ih (fun b' hb' => hB b' (by simp [hb']))]
      have hb := hB b (by simp)
      unfold shortFunQ octFlat
      simp only [List.map_map, add_zero]
      apply List.sum_eq_zero
      intro x hx
      simp only [List.mem_map, Function.comp_apply] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      rw [shortDecode_oct_eq' b.1 q.1 hb.1 (hb.2 q hq)]
      simp
  have h3 : shortFunQ S.odd (Sum.inl (s, p)) = 0 := by
    unfold shortFunQ
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    have := hd q hq
    rw [shortDecode_odd_eq' q.1 this.1 this.2]
    simp
  rw [h1, h2 S.oct (fun b hb => ⟨(ho b hb).1, (ho b hb).2⟩), h3]
  ring


/-- Octad coordinates of a valid block are the octad lookups. -/
theorem shortFunQ_flat_oct (S : ShortData) (hS : S.ok = true) (o : Fin 759) (f : Fin 64) :
    shortFunQ S.flat (Sum.inr (Sum.inl (o, f))) = octLookupQ S.oct o.val f.val := by
  simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨hp, ho⟩, hd⟩ := hS
  rw [ShortData.flat, shortFunQ_append, shortFunQ_append]
  have h1 : shortFunQ S.pairs (Sum.inr (Sum.inl (o, f))) = 0 := by
    unfold shortFunQ
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    simp [shortDecode_pair_ne_oct q.1 (hp q hq)]
  have h2 : ∀ B : List (ℕ × List (ℕ × ℤ)),
      (∀ b ∈ B, b.1 < 759 ∧ ∀ q ∈ b.2, q.1 < 64) →
      shortFunQ (octsFlat B) (Sum.inr (Sum.inl (o, f))) = octLookupQ B o.val f.val := by
    intro B hB
    induction B with
    | nil => rfl
    | cons b B ih =>
      rw [octsFlat, shortFunQ_append, ih (fun b' hb' => hB b' (by simp [hb']))]
      have hb := hB b (by simp)
      unfold octLookupQ
      simp only [List.map_cons, List.sum_cons]
      congr 1
      unfold shortFunQ octFlat lookupQ
      simp only [List.map_map]
      by_cases hbo : b.1 = o.val
      · simp only [hbo, ↓reduceIte]
        congr 1
        apply List.map_congr_left
        intro q hq
        simp only [Function.comp_apply]
        rw [← hbo, shortDecode_oct_eq' b.1 q.1 hb.1 (hb.2 q hq)]
        by_cases hqf : q.1 = f.val
        · have : (⟨b.1, hb.1⟩ : Fin 759) = o := Fin.ext hbo
          simp [this, hqf]
        · have h' : (⟨q.1, hb.2 q hq⟩ : Fin 64) ≠ f := fun h => hqf (congrArg Fin.val h)
          simp [h', hqf]
      · simp only [hbo, ↓reduceIte]
        apply List.sum_eq_zero
        intro x hx
        simp only [List.mem_map, Function.comp_apply] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        rw [shortDecode_oct_eq' b.1 q.1 hb.1 (hb.2 q hq)]
        have h' : (⟨b.1, hb.1⟩ : Fin 759) ≠ o := fun h => hbo (congrArg Fin.val h)
        simp [h']
  have h3 : shortFunQ S.odd (Sum.inr (Sum.inl (o, f))) = 0 := by
    unfold shortFunQ
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    have := hd q hq
    rw [shortDecode_odd_eq' q.1 this.1 this.2]
    simp
  rw [h1, h2 S.oct (fun b hb => ⟨(ho b hb).1, (ho b hb).2⟩), h3]
  ring

/-- Odd coordinates of a valid block are the odd lookups. -/
theorem shortFunQ_flat_odd (S : ShortData) (hS : S.ok = true) (d : Fin 2048) (i : Fin 24) :
    shortFunQ S.flat (Sum.inr (Sum.inr (d, i))) = lookupQ S.odd (49128 + 24 * d.val + i.val) := by
  simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨hp, ho⟩, hd⟩ := hS
  rw [ShortData.flat, shortFunQ_append, shortFunQ_append]
  have h1 : shortFunQ S.pairs (Sum.inr (Sum.inr (d, i))) = 0 := by
    unfold shortFunQ
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    simp [shortDecode_pair_ne_odd q.1 (hp q hq)]
  have h2 : ∀ B : List (ℕ × List (ℕ × ℤ)),
      (∀ b ∈ B, b.1 < 759 ∧ ∀ q ∈ b.2, q.1 < 64) →
      shortFunQ (octsFlat B) (Sum.inr (Sum.inr (d, i))) = 0 := by
    intro B hB
    induction B with
    | nil => rfl
    | cons b B ih =>
      rw [octsFlat, shortFunQ_append, ih (fun b' hb' => hB b' (by simp [hb']))]
      have hb := hB b (by simp)
      unfold shortFunQ octFlat
      simp only [List.map_map, add_zero]
      apply List.sum_eq_zero
      intro x hx
      simp only [List.mem_map, Function.comp_apply] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      rw [shortDecode_oct_eq' b.1 q.1 hb.1 (hb.2 q hq)]
      simp
  have h3 : shortFunQ S.odd (Sum.inr (Sum.inr (d, i))) =
      lookupQ S.odd (49128 + 24 * d.val + i.val) := by
    unfold shortFunQ lookupQ
    congr 1
    apply List.map_congr_left
    intro q hq
    have hq' := hd q hq
    rw [shortDecode_odd_eq' q.1 hq'.1 hq'.2]
    have hiff : (Sum.inr (Sum.inr (⟨(q.1 - 49128) / 24, by omega⟩,
        ⟨(q.1 - 49128) % 24, Nat.mod_lt _ (by decide)⟩)) : GriessShortIndex) =
        Sum.inr (Sum.inr (d, i)) ↔ q.1 = 49128 + 24 * d.val + i.val := by
      simp only [Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff]
      omega
    simp only [hiff]
  rw [h1, h2 S.oct (fun b hb => ⟨(ho b hb).1, (ho b hb).2⟩), h3]
  ring

/-! ## Finite reindexing -/

/-- The two orientations of a coordinate pair. -/
theorem sum_pair_indicator (X : Fin 24 → Fin 24 → ℚ) (p : Fin 276) :
    (∑ i : Fin 24, ∑ j : Fin 24,
      if i ≠ j ∧ generatedAxisGlobalFinitePairIndex i j = p then X i j else 0) =
      X (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 +
      X (generatedAxisGlobalPairCoordinates p).2 (generatedAxisGlobalPairCoordinates p).1 := by
  have hfacts : ∀ p : Fin 276, (identPairFin p).1 < (identPairFin p).2 ∧
      generatedAxisGlobalFinitePairIndex (identPairFin p).1 (identPairFin p).2 = p ∧
      generatedAxisGlobalFinitePairIndex (identPairFin p).2 (identPairFin p).1 = p := by
    decide +kernel
  obtain ⟨hlt, h12, h21⟩ := hfacts p
  rw [identPairFin_actual] at hlt h12 h21
  set c := generatedAxisGlobalPairCoordinates p with hc
  have hiff : ∀ i j : Fin 24, (i ≠ j ∧ generatedAxisGlobalFinitePairIndex i j = p) ↔
      ((i = c.1 ∧ j = c.2) ∨ (i = c.2 ∧ j = c.1)) := by
    intro i j
    constructor
    · rintro ⟨hij, hp⟩
      have h := generatedAxisGlobalFinitePairIndex_coordinates i j hij
      rw [hp, ← hc] at h
      split_ifs at h with hl
      · left; rw [h]; exact ⟨rfl, rfl⟩
      · right; rw [h]; exact ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨ne_of_lt hlt, h12⟩
      · exact ⟨ne_of_gt hlt, h21⟩
  have hne : c.1 ≠ c.2 := ne_of_lt hlt
  simp_rw [hiff]
  have hsplit : ∀ i j : Fin 24, (if (i = c.1 ∧ j = c.2) ∨ (i = c.2 ∧ j = c.1) then X i j else 0) =
      (if i = c.1 then (if j = c.2 then X i j else 0) else 0) +
        (if i = c.2 then (if j = c.1 then X i j else 0) else 0) := by
    intro i j
    by_cases h1 : i = c.1 <;> by_cases h2 : j = c.2 <;> by_cases h3 : i = c.2 <;>
      by_cases h4 : j = c.1 <;> simp_all
  simp_rw [hsplit, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

/-- Odd labels determine their two spin labels. -/
theorem sum_odd_indicator (F : Fin 4096 → Fin 24 → ℚ) (lab : ℕ) (h1 : 49128 ≤ lab)
    (h2 : lab < 98280) :
    (∑ k : Fin 4096, ∑ j : Fin 24,
      if lab = 49128 + 24 * (k.val % 2048) + j.val then F k j else 0) =
      F ⟨(lab - 49128) / 24, by omega⟩ ⟨(lab - 49128) % 24, Nat.mod_lt _ (by decide)⟩ +
      F ⟨(lab - 49128) / 24 + 2048, by omega⟩ ⟨(lab - 49128) % 24, Nat.mod_lt _ (by decide)⟩ := by
  set i0 : Fin 24 := ⟨(lab - 49128) % 24, Nat.mod_lt _ (by decide)⟩
  have hinner : ∀ k : Fin 4096, (∑ j : Fin 24,
      if lab = 49128 + 24 * (k.val % 2048) + j.val then F k j else 0) =
      if k.val % 2048 = (lab - 49128) / 24 then F k i0 else 0 := by
    intro k
    have hc : ∀ j : Fin 24, (lab = 49128 + 24 * (k.val % 2048) + j.val) ↔
        (j = i0 ∧ k.val % 2048 = (lab - 49128) / 24) := by
      intro j
      constructor
      · intro h
        exact ⟨Fin.ext (by simp only [i0]; omega), by omega⟩
      · rintro ⟨rfl, hk⟩
        simp only [i0]
        omega
    simp_rw [hc]
    by_cases hk : k.val % 2048 = (lab - 49128) / 24
    · simp [hk]
    · simp [hk]
  simp_rw [hinner]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hset : (Finset.univ.filter (fun k : Fin 4096 => k.val % 2048 = (lab - 49128) / 24)) =
      {⟨(lab - 49128) / 24, by omega⟩, ⟨(lab - 49128) / 24 + 2048, by omega⟩} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    have := k.isLt
    omega
  rw [hset, Finset.sum_pair]
  intro h
  have := congrArg Fin.val h
  simp at this

/-! ## The pairing formula -/

/-- The coordinate pair of a pair label. -/
def pairCoords (p : ℕ) : Fin 24 × Fin 24 :=
  generatedAxisGlobalPairCoordinates ⟨p % 276, Nat.mod_lt _ (by decide)⟩

/-- The octad Fourier coefficient of the forward (`fwd`) or inverse triality. -/
def octM (fwd : Bool) (e f : ℕ) : ℚ :=
  if fwd then (trialityIntegerMatrix ⟨e % 64, Nat.mod_lt _ (by decide)⟩
      ⟨f % 64, Nat.mod_lt _ (by decide)⟩ : ℚ)
  else (trialityIntegerMatrix ⟨f % 64, Nat.mod_lt _ (by decide)⟩
      ⟨e % 64, Nat.mod_lt _ (by decide)⟩ : ℚ)

/-- The sign of an odd code label: `(-1)^(weight / 4)`. -/
def oddWeightSign (d : ℕ) : ℚ :=
  (generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d) / 4 : ℕ) : ℚ)

/-- The coordinate sign `(-1)^(c_j)` of an odd code label. -/
def oddCoordSign (d j : ℕ) : ℚ := if (golayEncodedMask d).testBit j then -1 else 1

/-- The odd code label of an odd flat label. -/
def oddD (lab : ℕ) : ℕ := (lab - 49128) / 24 % 2048

/-- The coordinate of an odd flat label. -/
def oddJ (lab : ℕ) : ℕ := (lab - 49128) % 24

/-- Matrix part of the pairing of a triality image `L` (forward or inverse) with `W`. -/
def triMatQ (fwd : Bool) (L W : IdentVec) : ℚ :=
  (∑ i : Fin 24, L.mat.entry i i * W.mat.entry i i) +
    (L.sh.pairs.map (fun q => L.sden * (q.2 : ℚ) / 2 *
      (if fwd then 1 else if q.1 < 276 then 1 else -1) *
      (W.mat.entry (pairCoords q.1).1 (pairCoords q.1).2 +
        W.mat.entry (pairCoords q.1).2 (pairCoords q.1).1))).sum

/-- The short coordinate of the triality image of `L` at a pair label. -/
def triPairQ (fwd : Bool) (L : IdentVec) (lab : ℕ) : ℚ :=
  let m := L.mat.entry (pairCoords lab).1 (pairCoords lab).2
  let s0 := L.sden * lookupQ L.sh.pairs (lab % 276)
  let s1 := L.sden * lookupQ L.sh.pairs (276 + lab % 276)
  if fwd then (if lab < 276 then m + (s0 - s1) / 2 else (s0 - s1) / 2 - m)
  else (if lab < 276 then m + (s0 + s1) / 2 else m - (s0 + s1) / 2)

/-- The short coordinate of the triality image of `L` at an octad label `(o, e)`. -/
def triOctQ (fwd : Bool) (L : IdentVec) (o e : ℕ) : ℚ :=
  L.sden * (L.sh.oct.map (fun b => if b.1 = o then
    (b.2.map (fun q => (q.2 : ℚ) * octM fwd e q.1 / 8)).sum else 0)).sum

/-- The short coordinate of the triality image of `L` at an odd label. -/
def triOddQ (fwd : Bool) (L : IdentVec) (lab : ℕ) : ℚ :=
  let d := oddD lab
  let j : Fin 24 := ⟨oddJ lab, Nat.mod_lt _ (by decide)⟩
  let t0 := L.ten ⟨d, by unfold d oddD; omega⟩ j
  let t1 := L.ten ⟨d + 2048, by unfold d oddD; omega⟩ j
  if fwd then oddWeightSign d * (t0 + t1) / 2 else oddCoordSign d j.val * (t0 - t1) / 2

/-- Short part of the pairing. -/
def triShortQ (fwd : Bool) (L W : IdentVec) : ℚ :=
  W.sden * ((W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairQ fwd L q.1)).sum +
    (W.sh.oct.map (fun b => (b.2.map (fun q => (q.2 : ℚ) * triOctQ fwd L b.1 q.1)).sum)).sum +
    (W.sh.odd.map (fun q => (q.2 : ℚ) * triOddQ fwd L q.1)).sum)

/-- The tensor pairing contribution of one odd term of `L`. -/
def triTCQ (fwd : Bool) (W : IdentVec) (lab : ℕ) : ℚ :=
  let d := oddD lab
  let j : Fin 24 := ⟨oddJ lab, Nat.mod_lt _ (by decide)⟩
  let w0 := W.ten ⟨d, by unfold d oddD; omega⟩ j
  let w1 := W.ten ⟨d + 2048, by unfold d oddD; omega⟩ j
  if fwd then oddCoordSign d j.val * (w0 - w1) else oddWeightSign d * (w0 + w1)

/-- The tensor-to-tensor term of the triality formula (the part computed on packed tensors). -/
def tPartQ (fwd : Bool) (T : GeneratedAxisGlobalRationalTensor) (k : Fin 4096) (j : Fin 24) : ℚ :=
  let d := k.val % 2048
  let t0 := T ⟨d, by unfold d; omega⟩ j
  let t1 := T ⟨d + 2048, by unfold d; omega⟩ j
  if fwd then oddWeightSign d * oddCoordSign d j.val * (t0 - t1) / 2
  else (generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℚ) * oddWeightSign d *
    oddCoordSign d j.val * (t0 + t1) / 2

/-- Tensor part of the pairing. -/
def triTensorQ (fwd : Bool) (L W : IdentVec) : ℚ :=
  ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCQ fwd W q.1)).sum +
    ∑ k : Fin 4096, ∑ j : Fin 24, tPartQ fwd L.ten k j * W.ten k j) / 2

/-- The exact pairing of the forward (`fwd = true`) or inverse triality image of `L` with `W`. -/
def pairTri (fwd : Bool) (L W : IdentVec) : ℚ :=
  triMatQ fwd L W + triShortQ fwd L W + triTensorQ fwd L W

/-! ## Forward pairing -/

/-- A Finset sum of a list sum is the list sum of the Finset sums. -/
theorem finset_sum_list_sum {α ι : Type} [Fintype ι] (l : List α) (f : α → ι → ℚ) :
    (∑ i, (l.map (fun a => f a i)).sum) = (l.map (fun a => ∑ i, f a i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- Constant multiples pass into list sums. -/
theorem list_sum_map_mul {α : Type} (l : List α) (f : α → ℚ) (c : ℚ) :
    (l.map f).sum * c = (l.map (fun a => f a * c)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, add_mul, ih]

/-- A list sum of zeros vanishes. -/
theorem list_sum_map_zero {α : Type} (l : List α) : (l.map (fun _ => (0 : ℚ))).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, add_zero]

/-- The two pair lookups of one pair index combine into one list sum. -/
theorem lookupQ_pair_sum (L : List (ℕ × ℤ)) (hL : ∀ q ∈ L, q.1 < 552) (p : ℕ) (hp : p < 276) :
    lookupQ L p + lookupQ L (276 + p) =
      (L.map (fun q => if q.1 % 276 = p then (q.2 : ℚ) else 0)).sum := by
  unfold lookupQ
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro q hq
  have := hL q hq
  split_ifs <;> first | ring1 | (exfalso; omega)

/-- The matrix part of the forward pairing. -/
theorem triMat_forward (L W : IdentVec) (hL : L.sh.ok = true) :
    (∑ i : Fin 24, ∑ j : Fin 24,
      (generatedAxisGlobalRationalTriality L.packet).1 i j * W.packet.1 i j) =
      triMatQ true L W := by
  have hp : ∀ q ∈ L.sh.pairs, q.1 < 552 := by
    have h := hL
    simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hterm : ∀ i j : Fin 24,
      (generatedAxisGlobalRationalTriality L.packet).1 i j * W.packet.1 i j =
        (if i = j then L.mat.entry i i * W.mat.entry i j else 0) +
        (L.sh.pairs.map (fun q => L.sden * (q.2 : ℚ) / 2 *
          (if i ≠ j ∧ generatedAxisGlobalFinitePairIndex i j =
              ⟨q.1 % 276, Nat.mod_lt _ (by decide)⟩ then W.mat.entry i j else 0))).sum := by
    intro i j
    simp only [generatedAxisGlobalRationalTriality, generatedAxisGlobalTrialityMatrixQ,
      IdentVec.packet, MatRep.toMat_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, ne_eq, not_true_eq_false, false_and, mul_zero,
        list_sum_map_zero, add_zero]
    · simp only [hij, ↓reduceIte, zero_add, ne_eq, not_false_eq_true, true_and]
      rw [shortFunQ_flat_pair _ hL, shortFunQ_flat_pair _ hL]
      simp only [Fin.isValue, Fin.val_zero, mul_zero, zero_add, Fin.val_one, mul_one]
      rw [← mul_add, lookupQ_pair_sum _ hp _ (generatedAxisGlobalFinitePairIndex i j).isLt]
      have hR : (L.sh.pairs.map (fun q => L.sden * (q.2 : ℚ) / 2 *
          (if generatedAxisGlobalFinitePairIndex i j = ⟨q.1 % 276, Nat.mod_lt _ (by decide)⟩
            then W.mat.entry i j else 0))) =
          (L.sh.pairs.map (fun q =>
            (if q.1 % 276 = (generatedAxisGlobalFinitePairIndex i j).val then (q.2 : ℚ) else 0) *
              (L.sden / 2 * W.mat.entry i j))) := by
        apply List.map_congr_left
        intro q _
        by_cases hq : q.1 % 276 = (generatedAxisGlobalFinitePairIndex i j).val
        · have : generatedAxisGlobalFinitePairIndex i j =
              ⟨q.1 % 276, Nat.mod_lt _ (by decide)⟩ := Fin.ext hq.symm
          simp only [this, ↓reduceIte]
          ring
        · have : generatedAxisGlobalFinitePairIndex i j ≠
              ⟨q.1 % 276, Nat.mod_lt _ (by decide)⟩ := fun h => hq (congrArg Fin.val h).symm
          simp only [hq, ↓reduceIte, this]
          ring
      rw [hR, ← list_sum_map_mul]
      ring
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [triMatQ]
  congr 1
  · simp [Finset.sum_ite_eq]
  · simp_rw [finset_sum_list_sum]
    congr 1
    apply List.map_congr_left
    intro q _
    simp_rw [← Finset.mul_sum]
    rw [sum_pair_indicator]
    simp [pairCoords]

/-- The forward triality short coordinate at a pair label. -/
theorem triShortQ_pair_forward (L : IdentVec) (hL : L.sh.ok = true) (lab : ℕ) (hlab : lab < 552) :
    generatedAxisGlobalTrialityShortQ L.packet (shortDecode lab) = triPairQ true L lab := by
  have hd : shortDecode lab = Sum.inl (⟨lab / 276 % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨lab % 276, Nat.mod_lt _ (by decide)⟩) := by simp [shortDecode, hlab]
  rw [hd]
  simp only [generatedAxisGlobalTrialityShortQ, IdentVec.packet, MatRep.toMat_apply]
  rw [shortFunQ_flat_pair _ hL, shortFunQ_flat_pair _ hL]
  simp only [triPairQ, pairCoords, Fin.isValue, Fin.val_zero, mul_zero, zero_add, Fin.val_one,
    mul_one, ↓reduceIte]
  by_cases h : lab < 276
  · have : (⟨lab / 276 % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := by
      apply Fin.ext; simp only [Fin.val_zero]; omega
    simp only [this, ↓reduceIte, h]
  · have : (⟨lab / 276 % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) ≠ 0 := by
      intro h'
      have := congrArg Fin.val h'
      simp only [Fin.val_zero] at this
      omega
    simp only [this, ↓reduceIte, h]

/-- Lookup of a single label in a list with labels below `64`. -/
theorem sum_fin64_lookupQ (G : Fin 64 → ℚ) (L : List (ℕ × ℤ)) (hL : ∀ q ∈ L, q.1 < 64) :
    (∑ f : Fin 64, G f * lookupQ L f.val) =
      (L.map (fun q => (q.2 : ℚ) * G ⟨q.1 % 64, Nat.mod_lt _ (by decide)⟩)).sum := by
  induction L with
  | nil => simp [lookupQ]
  | cons q L ih =>
    have hcons : ∀ f : Fin 64, lookupQ (q :: L) f.val =
        (if q.1 = f.val then (q.2 : ℚ) else 0) + lookupQ L f.val := by
      intro f
      simp [lookupQ]
    simp only [hcons, mul_add, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [ih (fun q' hq' => hL q' (by simp [hq']))]
    congr 1
    have hq := hL q (by simp)
    have h64 : q.1 % 64 = q.1 := Nat.mod_eq_of_lt hq
    rw [Finset.sum_eq_single (⟨q.1, hq⟩ : Fin 64)]
    · simp only [↓reduceIte]
      have : (⟨q.1 % 64, Nat.mod_lt _ (by decide)⟩ : Fin 64) = ⟨q.1, hq⟩ := Fin.ext h64
      rw [this]
      ring
    · intro f _ hf
      have : q.1 ≠ f.val := fun h => hf (Fin.ext h.symm)
      simp [this]
    · simp

/-- The forward triality short coordinate at an octad label. -/
theorem triShortQ_oct_forward (L : IdentVec) (hL : L.sh.ok = true) (o e : ℕ) (ho : o < 759)
    (he : e < 64) :
    generatedAxisGlobalTrialityShortQ L.packet (Sum.inr (Sum.inl (⟨o, ho⟩, ⟨e, he⟩))) =
      triOctQ true L o e := by
  have hoct : ∀ b ∈ L.sh.oct, ∀ q ∈ b.2, q.1 < 64 := by
    have h := hL
    simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact fun b hb => (h.1.2 b hb).2
  simp only [generatedAxisGlobalTrialityShortQ, IdentVec.packet]
  simp_rw [shortFunQ_flat_oct _ hL]
  simp only [octLookupQ, triOctQ]
  have hsw : ∀ f : Fin 64, (trialityIntegerMatrix ⟨e, he⟩ f : ℚ) / 8 *
      (L.sden * (L.sh.oct.map (fun b => if b.1 = o then lookupQ b.2 f.val else 0)).sum) =
      L.sden * (L.sh.oct.map (fun b => if b.1 = o then
        (trialityIntegerMatrix ⟨e, he⟩ f : ℚ) / 8 * lookupQ b.2 f.val else 0)).sum := by
    intro f
    rw [mul_left_comm]
    congr 1
    rw [mul_comm, list_sum_map_mul]
    congr 1
    apply List.map_congr_left
    intro b _
    split_ifs <;> ring
  simp_rw [hsw, ← Finset.mul_sum]
  congr 1
  rw [finset_sum_list_sum]
  congr 1
  apply List.map_congr_left
  intro b hb
  by_cases hbo : b.1 = o
  · simp only [hbo, ↓reduceIte]
    rw [sum_fin64_lookupQ _ _ (hoct b hb)]
    congr 1
    apply List.map_congr_left
    intro q hq
    have h64 : e % 64 = e := Nat.mod_eq_of_lt he
    simp only [octM, ↓reduceIte]
    have : (⟨e % 64, Nat.mod_lt _ (by decide)⟩ : Fin 64) = ⟨e, he⟩ := Fin.ext h64
    rw [this]
    ring
  · simp [hbo]

/-- The forward triality short coordinate at an odd label. -/
theorem triShortQ_odd_forward (L : IdentVec) (lab : ℕ) (h1 : 49128 ≤ lab) (h2 : lab < 98280) :
    generatedAxisGlobalTrialityShortQ L.packet (shortDecode lab) = triOddQ true L lab := by
  rw [shortDecode_odd_eq' lab h1 h2]
  simp only [generatedAxisGlobalTrialityShortQ, IdentVec.packet, generatedAxisGlobalSpinLabel_coeff,
    triOddQ, oddWeightSign, oddD, oddJ, ↓reduceIte]
  have hd : (lab - 49128) / 24 % 2048 = (lab - 49128) / 24 := Nat.mod_eq_of_lt (by omega)
  simp only [hd]

/-- The short part of the forward pairing. -/
theorem triShort_forward (L W : IdentVec) (hL : L.sh.ok = true) (hW : W.sh.ok = true) :
    (∑ r, (generatedAxisGlobalRationalTriality L.packet).2.1 r * W.packet.2.1 r) =
      triShortQ true L W := by
  have hW' := hW
  simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hW'
  obtain ⟨⟨hp, ho⟩, hd⟩ := hW'
  have h1 : (∑ r, (generatedAxisGlobalRationalTriality L.packet).2.1 r * W.packet.2.1 r) =
      W.sden * ∑ r, generatedAxisGlobalTrialityShortQ L.packet r * shortFunQ W.sh.flat r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [generatedAxisGlobalRationalTriality, IdentVec.packet]
    ring
  rw [h1, sum_mul_shortFunQ, triShortQ]
  apply congrArg (fun x => W.sden * x)
  rw [ShortData.flat, List.map_append, List.map_append, List.sum_append, List.sum_append]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · refine congrArg List.sum (List.map_congr_left ?_)
    intro q hq
    rw [triShortQ_pair_forward L hL q.1 (hp q hq)]
  · have hB : ∀ B : List (ℕ × List (ℕ × ℤ)), (∀ b ∈ B, b.1 < 759 ∧ ∀ q ∈ b.2, q.1 < 64) →
        ((octsFlat B).map (fun q => (q.2 : ℚ) *
          generatedAxisGlobalTrialityShortQ L.packet (shortDecode q.1))).sum =
        (B.map (fun b => (b.2.map (fun q => (q.2 : ℚ) * triOctQ true L b.1 q.1)).sum)).sum := by
      intro B hB
      induction B with
      | nil => rfl
      | cons b B ih =>
        rw [octsFlat, List.map_append, List.sum_append, ih (fun b' hb' => hB b' (by simp [hb'])),
          List.map_cons, List.sum_cons]
        refine congrArg (· + _) ?_
        have hb := hB b (by simp)
        rw [octFlat, List.map_map]
        refine congrArg List.sum (List.map_congr_left ?_)
        intro q hq
        simp only [Function.comp_apply]
        rw [shortDecode_oct_eq' b.1 q.1 hb.1 (hb.2 q hq),
          triShortQ_oct_forward L hL b.1 q.1 hb.1 (hb.2 q hq)]
    exact hB W.sh.oct (fun b hb => ⟨(ho b hb).1, (ho b hb).2⟩)
  · refine congrArg List.sum (List.map_congr_left ?_)
    intro q hq
    rw [triShortQ_odd_forward L q.1 (hd q hq).1 (hd q hq).2]

/-- A lookup inside a product spreads over the list. -/
theorem list_lookup_mul (l : List (ℕ × ℤ)) (n : ℕ) (a b c : ℚ) :
    a * (b * (l.map (fun p => if p.1 = n then (p.2 : ℚ) else 0)).sum) * c =
      (l.map (fun q => b * (q.2 : ℚ) * (if q.1 = n then a * c else 0))).sum := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    split_ifs <;> ring

/-- The tensor part of the forward pairing. -/
theorem triTensor_forward (L W : IdentVec) (hL : L.sh.ok = true) :
    (∑ k : Fin 4096, ∑ j : Fin 24,
      (generatedAxisGlobalRationalTriality L.packet).2.2 (golayLabelCoefficients k) j *
        W.packet.2.2 (golayLabelCoefficients k) j) / 2 = triTensorQ true L W := by
  have hd : ∀ q ∈ L.sh.odd, 49128 ≤ q.1 ∧ q.1 < 98280 := by
    have h := hL
    simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.2
  rw [triTensorQ]
  apply congrArg (fun x => x / 2)
  have hterm : ∀ (k : Fin 4096) (j : Fin 24),
      (generatedAxisGlobalRationalTriality L.packet).2.2 (golayLabelCoefficients k) j *
        W.packet.2.2 (golayLabelCoefficients k) j =
      (L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) *
        (if q.1 = 49128 + 24 * (k.val % 2048) + j.val then
          (generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℚ) *
            oddCoordSign (k.val % 2048) j.val * W.ten k j else 0))).sum +
      tPartQ true L.ten k j * W.ten k j := by
    intro k j
    simp only [generatedAxisGlobalRationalTriality, generatedAxisGlobalTrialityScaledTensorQ,
      IdentVec.packet, generatedAxisGlobalSpinLabel_coeff, generatedAxisGlobalSpinLabelLow]
    rw [shortFunQ_flat_odd _ hL]
    simp only [tPartQ, oddCoordSign, oddWeightSign, ↓reduceIte, lookupQ]
    rw [add_mul]
    refine congrArg (· + _) ?_
    exact list_lookup_mul _ _ _ _ _
  have hC : (∑ k : Fin 4096, ∑ j : Fin 24, (L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) *
      (if q.1 = 49128 + 24 * (k.val % 2048) + j.val then
        (generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℚ) *
          oddCoordSign (k.val % 2048) j.val * W.ten k j else 0))).sum) =
      (L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCQ true W q.1)).sum := by
    simp_rw [finset_sum_list_sum]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro q hq
    simp_rw [← Finset.mul_sum]
    refine congrArg (fun x => L.sden * (q.2 : ℚ) * x) ?_
    rw [sum_odd_indicator (fun k j =>
      (generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℚ) *
        oddCoordSign (k.val % 2048) j.val * W.ten k j) q.1 (hd q hq).1 (hd q hq).2]
    have hlo := golayLabel_low_last ⟨(q.1 - 49128) / 24, by have := (hd q hq).2; omega⟩
    have hhi := golayLabel_high_last ⟨(q.1 - 49128) / 24, by have := (hd q hq).2; omega⟩
    have hm1 : ((q.1 - 49128) / 24) % 2048 = (q.1 - 49128) / 24 := by
      have := (hd q hq).2
      exact Nat.mod_eq_of_lt (by omega)
    have hm2 : ((q.1 - 49128) / 24 + 2048) % 2048 = (q.1 - 49128) / 24 := by
      have := (hd q hq).2
      omega
    simp only [triTCQ, oddD, oddJ, hm1, hm2, hlo, hhi, ↓reduceIte, generatedAxisGlobalIntSign]
    norm_num
    ring
  calc (∑ k : Fin 4096, ∑ j : Fin 24,
        (generatedAxisGlobalRationalTriality L.packet).2.2 (golayLabelCoefficients k) j *
          W.packet.2.2 (golayLabelCoefficients k) j)
      = ∑ k : Fin 4096, ∑ j : Fin 24, ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) *
          (if q.1 = 49128 + 24 * (k.val % 2048) + j.val then
            (generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℚ) *
              oddCoordSign (k.val % 2048) j.val * W.ten k j else 0))).sum +
          tPartQ true L.ten k j * W.ten k j) :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => hterm k j))
    _ = (∑ k : Fin 4096, ∑ j : Fin 24, (L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) *
          (if q.1 = 49128 + 24 * (k.val % 2048) + j.val then
            (generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℚ) *
              oddCoordSign (k.val % 2048) j.val * W.ten k j else 0))).sum) +
          ∑ k : Fin 4096, ∑ j : Fin 24, tPartQ true L.ten k j * W.ten k j := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hC]

/-- The exact forward pairing of two representations. -/
theorem pairTri_forward_spec (L W : IdentVec) (hL : L.sh.ok = true) (hW : W.sh.ok = true) :
    packetPairQ (generatedAxisGlobalRationalTriality L.packet) W.packet = pairTri true L W := by
  rw [packetPairQ, pairTri, triMat_forward L W hL, triShort_forward L W hL hW,
    triTensor_forward L W hL]

/-- The Griess pairing of a forward triality image with a second vector, from representations. -/
theorem pairTri_forward_actual (x y : GriessSpace) (L W : IdentVec) (hL : L.sh.ok = true)
    (hW : W.sh.ok = true) (hx : griessConwayEncode x = L.real)
    (hy : griessConwayEncode y = W.real) :
    griessForm (sExtra x) y = (pairTri true L W : ℝ) := by
  rw [packetPairQ_triality x y L.packet W.packet hx hy, pairTri_forward_spec L W hL hW]

/-! ## Inverse pairing -/

/-- The two pair lookups of one pair index, with opposite signs. -/
theorem lookupQ_pair_sub (L : List (ℕ × ℤ)) (hL : ∀ q ∈ L, q.1 < 552) (p : ℕ) (hp : p < 276) :
    lookupQ L p - lookupQ L (276 + p) =
      (L.map (fun q => if q.1 % 276 = p then
        (if q.1 < 276 then (q.2 : ℚ) else -(q.2 : ℚ)) else 0)).sum := by
  unfold lookupQ
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih (fun q' hq' => hL q' (by simp [hq']))]
    have := hL q (by simp)
    split_ifs <;> first | ring1 | (exfalso; omega)

/-- The matrix part of the inverse pairing. -/
theorem triMat_inverse (L W : IdentVec) (hL : L.sh.ok = true) :
    (∑ i : Fin 24, ∑ j : Fin 24,
      (generatedAxisGlobalRationalInverse L.packet).1 i j * W.packet.1 i j) =
      triMatQ false L W := by
  have hp : ∀ q ∈ L.sh.pairs, q.1 < 552 := by
    have h := hL
    simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hterm : ∀ i j : Fin 24,
      (generatedAxisGlobalRationalInverse L.packet).1 i j * W.packet.1 i j =
        (if i = j then L.mat.entry i i * W.mat.entry i j else 0) +
        (L.sh.pairs.map (fun q => L.sden * (q.2 : ℚ) / 2 * (if q.1 < 276 then 1 else -1) *
          (if i ≠ j ∧ generatedAxisGlobalFinitePairIndex i j =
              ⟨q.1 % 276, Nat.mod_lt _ (by decide)⟩ then W.mat.entry i j else 0))).sum := by
    intro i j
    simp only [generatedAxisGlobalRationalInverse, generatedAxisGlobalInverseMatrixQ,
      IdentVec.packet, MatRep.toMat_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, ne_eq, not_true_eq_false, false_and, mul_zero,
        list_sum_map_zero, add_zero]
    · simp only [hij, ↓reduceIte, zero_add, ne_eq, not_false_eq_true, true_and]
      rw [shortFunQ_flat_pair _ hL, shortFunQ_flat_pair _ hL]
      simp only [Fin.isValue, Fin.val_zero, mul_zero, zero_add, Fin.val_one, mul_one]
      rw [← mul_sub, lookupQ_pair_sub _ hp _ (generatedAxisGlobalFinitePairIndex i j).isLt]
      have hR : (L.sh.pairs.map (fun q => L.sden * (q.2 : ℚ) / 2 * (if q.1 < 276 then 1 else -1) *
          (if generatedAxisGlobalFinitePairIndex i j = ⟨q.1 % 276, Nat.mod_lt _ (by decide)⟩
            then W.mat.entry i j else 0))) =
          (L.sh.pairs.map (fun q =>
            (if q.1 % 276 = (generatedAxisGlobalFinitePairIndex i j).val then
              (if q.1 < 276 then (q.2 : ℚ) else -(q.2 : ℚ)) else 0) *
              (L.sden / 2 * W.mat.entry i j))) := by
        apply List.map_congr_left
        intro q _
        by_cases hq : q.1 % 276 = (generatedAxisGlobalFinitePairIndex i j).val
        · have : generatedAxisGlobalFinitePairIndex i j =
              ⟨q.1 % 276, Nat.mod_lt _ (by decide)⟩ := Fin.ext hq.symm
          simp only [this, ↓reduceIte]
          split_ifs <;> ring
        · have : generatedAxisGlobalFinitePairIndex i j ≠
              ⟨q.1 % 276, Nat.mod_lt _ (by decide)⟩ := fun h => hq (congrArg Fin.val h).symm
          simp only [hq, ↓reduceIte, this]
          ring
      rw [hR, ← list_sum_map_mul]
      ring
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [triMatQ]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp [Finset.sum_ite_eq]
  · simp_rw [finset_sum_list_sum]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro q _
    simp_rw [← Finset.mul_sum]
    rw [sum_pair_indicator]
    simp [pairCoords]

/-- The inverse triality short coordinate at a pair label. -/
theorem triShortQ_pair_inverse (L : IdentVec) (hL : L.sh.ok = true) (lab : ℕ) (hlab : lab < 552) :
    generatedAxisGlobalInverseShortQ L.packet (shortDecode lab) = triPairQ false L lab := by
  have hd : shortDecode lab = Sum.inl (⟨lab / 276 % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨lab % 276, Nat.mod_lt _ (by decide)⟩) := by simp [shortDecode, hlab]
  rw [hd]
  simp only [generatedAxisGlobalInverseShortQ, IdentVec.packet, MatRep.toMat_apply]
  rw [shortFunQ_flat_pair _ hL, shortFunQ_flat_pair _ hL]
  simp only [triPairQ, pairCoords, Fin.isValue, Fin.val_zero, mul_zero, zero_add, Fin.val_one,
    mul_one, Bool.false_eq_true, ↓reduceIte]
  by_cases h : lab < 276
  · have : (⟨lab / 276 % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := by
      apply Fin.ext; simp only [Fin.val_zero]; omega
    simp only [this, ↓reduceIte, h]
  · have : (⟨lab / 276 % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) ≠ 0 := by
      intro h'
      have := congrArg Fin.val h'
      simp only [Fin.val_zero] at this
      omega
    simp only [this, ↓reduceIte, h]

/-- The inverse triality short coordinate at an octad label. -/
theorem triShortQ_oct_inverse (L : IdentVec) (hL : L.sh.ok = true) (o e : ℕ) (ho : o < 759)
    (he : e < 64) :
    generatedAxisGlobalInverseShortQ L.packet (Sum.inr (Sum.inl (⟨o, ho⟩, ⟨e, he⟩))) =
      triOctQ false L o e := by
  have hoct : ∀ b ∈ L.sh.oct, ∀ q ∈ b.2, q.1 < 64 := by
    have h := hL
    simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact fun b hb => (h.1.2 b hb).2
  simp only [generatedAxisGlobalInverseShortQ, IdentVec.packet]
  simp_rw [shortFunQ_flat_oct _ hL]
  simp only [octLookupQ, triOctQ]
  have hsw : ∀ f : Fin 64, (trialityIntegerMatrix f ⟨e, he⟩ : ℚ) / 8 *
      (L.sden * (L.sh.oct.map (fun b => if b.1 = o then lookupQ b.2 f.val else 0)).sum) =
      L.sden * (L.sh.oct.map (fun b => if b.1 = o then
        (trialityIntegerMatrix f ⟨e, he⟩ : ℚ) / 8 * lookupQ b.2 f.val else 0)).sum := by
    intro f
    rw [mul_left_comm]
    congr 1
    rw [mul_comm, list_sum_map_mul]
    congr 1
    apply List.map_congr_left
    intro b _
    split_ifs <;> ring
  simp_rw [hsw, ← Finset.mul_sum]
  congr 1
  rw [finset_sum_list_sum]
  congr 1
  apply List.map_congr_left
  intro b hb
  by_cases hbo : b.1 = o
  · simp only [hbo, ↓reduceIte]
    rw [sum_fin64_lookupQ _ _ (hoct b hb)]
    congr 1
    apply List.map_congr_left
    intro q hq
    have h64 : e % 64 = e := Nat.mod_eq_of_lt he
    simp only [octM, Bool.false_eq_true, ↓reduceIte]
    have : (⟨e % 64, Nat.mod_lt _ (by decide)⟩ : Fin 64) = ⟨e, he⟩ := Fin.ext h64
    rw [this]
    ring
  · simp [hbo]

/-- The inverse triality short coordinate at an odd label. -/
theorem triShortQ_odd_inverse (L : IdentVec) (lab : ℕ) (h1 : 49128 ≤ lab) (h2 : lab < 98280) :
    generatedAxisGlobalInverseShortQ L.packet (shortDecode lab) = triOddQ false L lab := by
  rw [shortDecode_odd_eq' lab h1 h2]
  simp only [generatedAxisGlobalInverseShortQ, IdentVec.packet, generatedAxisGlobalSpinLabel_coeff,
    triOddQ, oddCoordSign, oddD, oddJ, Bool.false_eq_true, ↓reduceIte]
  have hd : (lab - 49128) / 24 % 2048 = (lab - 49128) / 24 := Nat.mod_eq_of_lt (by omega)
  simp only [hd]

/-- The short part of the inverse pairing. -/
theorem triShort_inverse (L W : IdentVec) (hL : L.sh.ok = true) (hW : W.sh.ok = true) :
    (∑ r, (generatedAxisGlobalRationalInverse L.packet).2.1 r * W.packet.2.1 r) =
      triShortQ false L W := by
  have hW' := hW
  simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hW'
  obtain ⟨⟨hp, ho⟩, hd⟩ := hW'
  have h1 : (∑ r, (generatedAxisGlobalRationalInverse L.packet).2.1 r * W.packet.2.1 r) =
      W.sden * ∑ r, generatedAxisGlobalInverseShortQ L.packet r * shortFunQ W.sh.flat r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [generatedAxisGlobalRationalInverse, IdentVec.packet]
    ring
  rw [h1, sum_mul_shortFunQ, triShortQ]
  apply congrArg (fun x => W.sden * x)
  rw [ShortData.flat, List.map_append, List.map_append, List.sum_append, List.sum_append]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · refine congrArg List.sum (List.map_congr_left ?_)
    intro q hq
    rw [triShortQ_pair_inverse L hL q.1 (hp q hq)]
  · have hB : ∀ B : List (ℕ × List (ℕ × ℤ)), (∀ b ∈ B, b.1 < 759 ∧ ∀ q ∈ b.2, q.1 < 64) →
        ((octsFlat B).map (fun q => (q.2 : ℚ) *
          generatedAxisGlobalInverseShortQ L.packet (shortDecode q.1))).sum =
        (B.map (fun b => (b.2.map (fun q => (q.2 : ℚ) * triOctQ false L b.1 q.1)).sum)).sum := by
      intro B hB
      induction B with
      | nil => rfl
      | cons b B ih =>
        rw [octsFlat, List.map_append, List.sum_append, ih (fun b' hb' => hB b' (by simp [hb'])),
          List.map_cons, List.sum_cons]
        refine congrArg (· + _) ?_
        have hb := hB b (by simp)
        rw [octFlat, List.map_map]
        refine congrArg List.sum (List.map_congr_left ?_)
        intro q hq
        simp only [Function.comp_apply]
        rw [shortDecode_oct_eq' b.1 q.1 hb.1 (hb.2 q hq),
          triShortQ_oct_inverse L hL b.1 q.1 hb.1 (hb.2 q hq)]
    exact hB W.sh.oct (fun b hb => ⟨(ho b hb).1, (ho b hb).2⟩)
  · refine congrArg List.sum (List.map_congr_left ?_)
    intro q hq
    rw [triShortQ_odd_inverse L q.1 (hd q hq).1 (hd q hq).2]

/-- The tensor part of the inverse pairing. -/
theorem triTensor_inverse (L W : IdentVec) (hL : L.sh.ok = true) :
    (∑ k : Fin 4096, ∑ j : Fin 24,
      (generatedAxisGlobalRationalInverse L.packet).2.2 (golayLabelCoefficients k) j *
        W.packet.2.2 (golayLabelCoefficients k) j) / 2 = triTensorQ false L W := by
  have hd : ∀ q ∈ L.sh.odd, 49128 ≤ q.1 ∧ q.1 < 98280 := by
    have h := hL
    simp only [ShortData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.2
  rw [triTensorQ]
  apply congrArg (fun x => x / 2)
  have hterm : ∀ (k : Fin 4096) (j : Fin 24),
      (generatedAxisGlobalRationalInverse L.packet).2.2 (golayLabelCoefficients k) j *
        W.packet.2.2 (golayLabelCoefficients k) j =
      (L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) *
        (if q.1 = 49128 + 24 * (k.val % 2048) + j.val then
          oddWeightSign (k.val % 2048) * W.ten k j else 0))).sum +
      tPartQ false L.ten k j * W.ten k j := by
    intro k j
    simp only [generatedAxisGlobalRationalInverse, generatedAxisGlobalInverseTensorQ,
      IdentVec.packet, generatedAxisGlobalSpinLabel_coeff, generatedAxisGlobalSpinLabelLow]
    rw [shortFunQ_flat_odd _ hL]
    simp only [tPartQ, oddCoordSign, oddWeightSign, Bool.false_eq_true, ↓reduceIte, lookupQ]
    rw [add_mul]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact list_lookup_mul _ _ _ _ _
    · ring
  have hC : (∑ k : Fin 4096, ∑ j : Fin 24, (L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) *
      (if q.1 = 49128 + 24 * (k.val % 2048) + j.val then
        oddWeightSign (k.val % 2048) * W.ten k j else 0))).sum) =
      (L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCQ false W q.1)).sum := by
    simp_rw [finset_sum_list_sum]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro q hq
    simp_rw [← Finset.mul_sum]
    refine congrArg (fun x => L.sden * (q.2 : ℚ) * x) ?_
    rw [sum_odd_indicator (fun k j => oddWeightSign (k.val % 2048) * W.ten k j) q.1
      (hd q hq).1 (hd q hq).2]
    have hm1 : ((q.1 - 49128) / 24) % 2048 = (q.1 - 49128) / 24 := by
      have := (hd q hq).2
      exact Nat.mod_eq_of_lt (by omega)
    have hm2 : ((q.1 - 49128) / 24 + 2048) % 2048 = (q.1 - 49128) / 24 := by
      have := (hd q hq).2
      omega
    simp only [triTCQ, oddD, oddJ, hm1, hm2, Bool.false_eq_true, ↓reduceIte]
    ring
  calc (∑ k : Fin 4096, ∑ j : Fin 24,
        (generatedAxisGlobalRationalInverse L.packet).2.2 (golayLabelCoefficients k) j *
          W.packet.2.2 (golayLabelCoefficients k) j)
      = ∑ k : Fin 4096, ∑ j : Fin 24, ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) *
          (if q.1 = 49128 + 24 * (k.val % 2048) + j.val then
            oddWeightSign (k.val % 2048) * W.ten k j else 0))).sum +
          tPartQ false L.ten k j * W.ten k j) :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => hterm k j))
    _ = (∑ k : Fin 4096, ∑ j : Fin 24, (L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) *
          (if q.1 = 49128 + 24 * (k.val % 2048) + j.val then
            oddWeightSign (k.val % 2048) * W.ten k j else 0))).sum) +
          ∑ k : Fin 4096, ∑ j : Fin 24, tPartQ false L.ten k j * W.ten k j := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by rw [hC]

/-- The exact inverse pairing of two representations. -/
theorem pairTri_inverse_spec (L W : IdentVec) (hL : L.sh.ok = true) (hW : W.sh.ok = true) :
    packetPairQ (generatedAxisGlobalRationalInverse L.packet) W.packet = pairTri false L W := by
  rw [packetPairQ, pairTri, triMat_inverse L W hL, triShort_inverse L W hL hW,
    triTensor_inverse L W hL]

/-- The Griess pairing of an inverse triality image with a second vector, from representations. -/
theorem pairTri_inverse_actual (x y : GriessSpace) (L W : IdentVec) (hL : L.sh.ok = true)
    (hW : W.sh.ok = true) (hx : griessConwayEncode x = L.real)
    (hy : griessConwayEncode y = W.real) :
    griessForm (sExtra.symm x) y = (pairTri false L W : ℝ) := by
  rw [packetPairQ_inverse x y L.packet W.packet hx hy, pairTri_inverse_spec L W hL hW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
