/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOddZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWord

/-! # Matrix pairing parts with integer spatial vectors

Rational arithmetic is slow in the kernel.  Matrix blocks with integer data (`MatZ`: rank-one
terms `n / den • (z / 2^k)(z / 2^k)ᵀ` plus a scalar) are transported by integer letter actions
(`wordZ`, the xi letter adding one power of two), and their entries need one integer sum and one
division (`MatZ.entry`, `MatZ.act_entry`).  `triMatZ` / `pairSumZ` are `triMatF` / `pairSumQ`
with these entries (`triMatF_eq_Z`, `pairSumQ_eq_Z`); `fifthSrcMat_act_entry` covers the Fifth
source block. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-! ## Integer spatial vectors -/

/-- Coordinate `i` of an integer vector (`0` outside the list). -/
def zget (z : List ℤ) (i : ℕ) : ℤ := z.getD i 0

/-- A rational vector is an integer vector over `2^k`. -/
def ZRel (v : List ℚ) (z : List ℤ) (k : ℕ) : Prop :=
  ∀ i : Fin 24, vecQ v i = (zget z i.val : ℚ) / 2 ^ k

theorem zget_ofFn (f : Fin 24 → ℤ) (i : Fin 24) : zget (List.ofFn f) i.val = f i := by
  unfold zget
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem getD_map_div (z : List ℤ) (k : ℕ) : ∀ i : ℕ,
    (z.map (fun a : ℤ => (a : ℚ) / 2 ^ k)).getD i 0 = (z.getD i 0 : ℚ) / 2 ^ k := by
  induction z with
  | nil => intro i; simp
  | cons a z ih =>
    intro i
    cases i with
    | zero => simp only [List.map_cons, List.getD_cons_zero]
    | succ n => simp only [List.map_cons, List.getD_cons_succ]; exact ih n

theorem zrel_map (z : List ℤ) (k : ℕ) : ZRel (z.map (fun a : ℤ => (a : ℚ) / 2 ^ k)) z k := by
  intro i
  unfold vecQ zget
  exact getD_map_div z k i.val

/-- Integer xi (numerators over one more power of two). -/
def xiZ (z : List ℤ) : List ℤ :=
  List.ofFn (fun i : Fin 24 =>
    co1XiNumerator i (generatedAxisGlobalXiColumn i 0) *
        zget z (generatedAxisGlobalXiColumn i 0).val +
      co1XiNumerator i (generatedAxisGlobalXiColumn i 1) *
        zget z (generatedAxisGlobalXiColumn i 1).val +
      co1XiNumerator i (generatedAxisGlobalXiColumn i 2) *
        zget z (generatedAxisGlobalXiColumn i 2).val +
      co1XiNumerator i (generatedAxisGlobalXiColumn i 3) *
        zget z (generatedAxisGlobalXiColumn i 3).val)

theorem xiZ_rel (v : List ℚ) (z : List ℤ) (k : ℕ) (h : ZRel v z k) :
    ZRel (sourceSpatialVec 0 v) (xiZ z) (k + 1) := by
  intro i
  rw [sourceSpatialVec, vecQ_matVec, xiZ, zget_ofFn]
  show generatedAxisGlobalRationalSpatialXi (vecQ v) i = _
  have h' : ∀ j : Fin 24, vecQ v j = (zget z j.val : ℚ) / 2 ^ k := h
  unfold generatedAxisGlobalRationalSpatialXi
  rw [Fin.sum_univ_four]
  simp only [h', Int.cast_add, Int.cast_mul, pow_succ]
  ring

/-- The coordinate read by a monomial source letter. -/
def monoPermIdx (l : Fin 2 × Bool) (i : Fin 24) : Fin 24 :=
  if l.2 then omegaOrbitPermutation l.1 i else (omegaOrbitPermutation l.1).symm i

/-- Integer monomial source letter. -/
def monoZ (l : Fin 2 × Bool) (z : List ℤ) : List ℤ :=
  List.ofFn (fun i : Fin 24 => zget z (monoPermIdx l i).val)

theorem monoZ_rel (l : Fin 2 × Bool) (v : List ℚ) (z : List ℤ) (k : ℕ) (h : ZRel v z k) :
    ZRel (sourceSpatialVec (monoLetterIndex l) v) (monoZ l z) k := by
  intro i
  rw [sourceSpatialVec, vecQ_matVec, monoZ, zget_ofFn]
  obtain ⟨a, b⟩ := l
  fin_cases a <;> cases b
  · change vecQ v ((omegaOrbitPermutation 0).symm i) = _
    exact h _
  · change vecQ v (omegaOrbitPermutation 0 i) = _
    exact h _
  · change vecQ v ((omegaOrbitPermutation 1).symm i) = _
    exact h _
  · change vecQ v (omegaOrbitPermutation 1 i) = _
    exact h _

/-- Integer source sign letter. -/
def signZ (a : Fin 4096) (z : List ℤ) : List ℤ :=
  List.ofFn (fun i : Fin 24 =>
    if (golayEncodedMask a.val).testBit i.val then -zget z i.val else zget z i.val)

theorem signZ_rel (a : Fin 4096) (v : List ℚ) (z : List ℤ) (k : ℕ) (h : ZRel v z k) :
    ZRel (signSpatialVec a v) (signZ a z) k := by
  intro i
  rw [signSpatialVec, vecQ_matVec, signZ, zget_ofFn]
  have h' : ∀ j : Fin 24, vecQ v j = (zget z j.val : ℚ) / 2 ^ k := h
  simp only [h']
  split_ifs <;> simp [neg_div]

/-- Integer spatial action of a letter. -/
def letterZ : IdentLetter → List ℤ → List ℤ
  | .xi, z => xiZ z
  | .mono l, z => monoZ l z
  | .sign a _, z => signZ a z
  | .qel _, z => z

/-- The power of two gained by a letter. -/
def letterE : IdentLetter → ℕ
  | .xi => 1
  | _ => 0

theorem letterZ_rel (x : IdentLetter) (v : List ℚ) (z : List ℤ) (k : ℕ) (h : ZRel v z k) :
    ZRel (identLetterVec x v) (letterZ x z) (k + letterE x) := by
  cases x with
  | xi => exact xiZ_rel v z k h
  | mono l => exact monoZ_rel l v z k h
  | sign a ε => exact signZ_rel a v z k h
  | qel g => exact h

/-- Integer spatial action of a word (the head letter acts last). -/
def wordZ : List IdentLetter → List ℤ → List ℤ
  | [], z => z
  | x :: w, z => letterZ x (wordZ w z)

/-- The power of two gained by a word. -/
def wordE : List IdentLetter → ℕ
  | [] => 0
  | x :: w => letterE x + wordE w

theorem wordZ_rel (v : List ℚ) (z : List ℤ) (k : ℕ) (h : ZRel v z k) :
    ∀ w : List IdentLetter,
      ZRel (spWordVec identSpatialAlphabet w v) (wordZ w z) (k + wordE w)
  | [] => by simpa [spWordVec, wordZ, wordE] using h
  | x :: w => by
    have ih := wordZ_rel v z k h w
    have := letterZ_rel x _ _ _ ih
    rw [show k + wordE w + letterE x = k + wordE (x :: w) by simp [wordE]; omega] at this
    exact this

/-! ## Integer matrix blocks -/

/-- A matrix block `scal • 1 + Σ (n / den) • (z / 2^k) (z / 2^k)ᵀ` with integer data. -/
structure MatZ where
  /-- The scalar part. -/
  scal : ℚ
  /-- The common denominator of the term coefficients. -/
  den : ℕ
  /-- The rank-one terms: integer coefficient and integer vector. -/
  terms : List (ℤ × List ℤ)
  /-- The vectors are integer vectors over `2^k`. -/
  k : ℕ

/-- The rational representation of an integer matrix block. -/
def MatZ.toRep (M : MatZ) : MatRep :=
  ⟨M.scal, M.terms.map (fun t => ((t.1 : ℚ) / M.den, t.2.map (fun z : ℤ => (z : ℚ) / 2 ^ M.k)))⟩

/-- One entry of an integer matrix block: one integer sum and one division. -/
def MatZ.entry (M : MatZ) (i j : Fin 24) : ℚ :=
  (if i = j then M.scal else 0) +
    (((M.terms.map (fun t => t.1 * (zget t.2 i.val * zget t.2 j.val))).sum : ℤ) : ℚ) /
      (M.den * 4 ^ M.k)

/-- The integer matrix block transported by a word. -/
def MatZ.act (w : List IdentLetter) (M : MatZ) : MatZ :=
  ⟨M.scal, M.den, M.terms.map (fun t => (t.1, wordZ w t.2)), M.k + wordE w⟩

/-- Entries of a transported block are the entries of the transported integer block. -/
theorem MatZ.act_entry (M : MatZ) (w : List IdentLetter) (i j : Fin 24) :
    (M.toRep.act identSpatialAlphabet w).entry i j = (M.act w).entry i j := by
  unfold MatRep.act MatRep.entry MatZ.toRep MatZ.act MatZ.entry
  simp only
  congr 1
  rw [Int.cast_list_sum, div_eq_mul_inv, list_sum_map_mul]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  have hr := wordZ_rel _ t.2 M.k (zrel_map t.2 M.k) w
  simp only [Function.comp_apply, hr i, hr j, Int.cast_mul]
  rw [show (4 : ℚ) ^ (M.k + wordE w) = 2 ^ (M.k + wordE w) * 2 ^ (M.k + wordE w) by
    rw [← mul_pow]; norm_num]
  ring

/-! ## Pairing parts with integer matrix blocks -/

/-- `triMatF` with the entries of integer matrix blocks. -/
def triMatZ (fwd : Bool) (LM WM : MatZ) (L : IdentVec) : ℚ :=
  (∑ i : Fin 24, LM.entry i i * WM.entry i i) +
    (L.sh.pairs.map (fun q => L.sden * (q.2 : ℚ) / 2 *
      (if fwd then 1 else if q.1 < 276 then 1 else -1) *
      (WM.entry (pairCoordsF q.1).1 (pairCoordsF q.1).2 +
        WM.entry (pairCoordsF q.1).2 (pairCoordsF q.1).1))).sum

theorem triMatF_eq_Z (fwd : Bool) (L W : IdentVec) (LM WM : MatZ)
    (hL : ∀ i j, L.mat.entry i j = LM.entry i j) (hW : ∀ i j, W.mat.entry i j = WM.entry i j) :
    triMatF fwd L W = triMatZ fwd LM WM L := by
  simp only [triMatF, triMatZ, hL, hW]

/-- `triPairF` with the entries of an integer matrix block. -/
def triPairZ (fwd : Bool) (LM : MatZ) (L : IdentVec) (lab : ℕ) : ℚ :=
  let m := LM.entry (pairCoordsF lab).1 (pairCoordsF lab).2
  let s0 := L.sden * lookupQ L.sh.pairs (lab % 276)
  let s1 := L.sden * lookupQ L.sh.pairs (276 + lab % 276)
  if fwd then (if lab < 276 then m + (s0 - s1) / 2 else (s0 - s1) / 2 - m)
  else (if lab < 276 then m + (s0 + s1) / 2 else m - (s0 + s1) / 2)

/-- The pair short terms with the entries of an integer matrix block. -/
def pairSumZ (fwd : Bool) (LM : MatZ) (L W : IdentVec) : ℚ :=
  (W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairZ fwd LM L q.1)).sum

theorem pairSumQ_eq_Z (fwd : Bool) (L W : IdentVec) (LM : MatZ)
    (hL : ∀ i j, L.mat.entry i j = LM.entry i j) :
    pairSumQ fwd L W = pairSumZ fwd LM L W := by
  simp only [pairSumQ, pairSumZ, triPairF, triPairZ, hL]

/-! ## The Fifth source block -/

/-- The integer unit vector `e_i`. -/
def unitListZ (i : ℕ) : List ℤ := (List.range 24).map (fun j => if j = i then 1 else 0)

/-- The Fifth source block as an integer block. -/
def fifthSrcMatZ : MatZ :=
  ⟨1 / 4, 4, [0, 1, 2, 3, 16, 17, 18, 19].map (fun i => (1, unitListZ i)), 0⟩

theorem fifthSrcMat_eq_Z : fifthSrcMat = fifthSrcMatZ.toRep := by
  unfold fifthSrcMat fifthSrcMatZ MatZ.toRep
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Prod.mk.injEq]
  refine ⟨by norm_num, ?_⟩
  unfold unitList unitListZ
  simp only [List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  split_ifs <;> simp

/-- Entries of a transported Fifth source block from integer data. -/
theorem fifthSrcMat_act_entry (w : List IdentLetter) (i j : Fin 24) :
    (fifthSrcMat.act identSpatialAlphabet w).entry i j = (fifthSrcMatZ.act w).entry i j := by
  rw [fifthSrcMat_eq_Z, MatZ.act_entry]

/-! ## Fully integer matrix and pair parts -/

/-- The integer numerator of an entry of an integer block. -/
def MatZ.num (M : MatZ) (i j : Fin 24) : ℤ :=
  (M.terms.map (fun t => t.1 * (zget t.2 i.val * zget t.2 j.val))).sum

theorem MatZ.entry_num (M : MatZ) (i j : Fin 24) :
    M.entry i j = (if i = j then M.scal else 0) + (M.num i j : ℚ) / (M.den * 4 ^ M.k) := rfl

theorem MatZ.num_comm (M : MatZ) (i j : Fin 24) : M.num i j = M.num j i := by
  unfold MatZ.num
  congr 1
  apply List.map_congr_left
  intro t _
  ring

set_option maxRecDepth 100000 in
theorem identPairFin_ne : ∀ p : Fin 276, (identPairFin p).1 ≠ (identPairFin p).2 := by
  decide +kernel

theorem pairCoordsF_ne (p : ℕ) : (pairCoordsF p).1 ≠ (pairCoordsF p).2 :=
  identPairFin_ne _

theorem lookupQ_eq (L : List (ℕ × ℤ)) (lab : ℕ) : lookupQ L lab = (idxSum L lab : ℚ) := by
  unfold lookupQ idxSum
  rw [Int.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  split_ifs <;> simp

theorem list_sum_map_mul_left {α : Type} (l : List α) (f : α → ℚ) (c : ℚ) :
    c * (l.map f).sum = (l.map (fun a => c * f a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- The matrix part of the pairing with integer sums (five rational operations). -/
def triMatZI (fwd : Bool) (LM WM : MatZ) (L : IdentVec) : ℚ :=
  24 * LM.scal * WM.scal +
    LM.scal * ((((List.finRange 24).map (fun i => WM.num i i)).sum : ℤ) : ℚ) /
      (WM.den * 4 ^ WM.k) +
    WM.scal * ((((List.finRange 24).map (fun i => LM.num i i)).sum : ℤ) : ℚ) /
      (LM.den * 4 ^ LM.k) +
    ((((List.finRange 24).map (fun i => LM.num i i * WM.num i i)).sum : ℤ) : ℚ) /
      ((LM.den * 4 ^ LM.k) * (WM.den * 4 ^ WM.k)) +
    L.sden * (((L.sh.pairs.map (fun q => q.2 * (if fwd then 1 else if q.1 < 276 then 1 else -1) *
      WM.num (pairCoordsF q.1).1 (pairCoordsF q.1).2)).sum : ℤ) : ℚ) / (WM.den * 4 ^ WM.k)

theorem triMatF_eq_ZI (fwd : Bool) (L W : IdentVec) (LM WM : MatZ)
    (hL : ∀ i j, L.mat.entry i j = LM.entry i j) (hW : ∀ i j, W.mat.entry i j = WM.entry i j) :
    triMatF fwd L W = triMatZI fwd LM WM L := by
  rw [triMatF_eq_Z fwd L W LM WM hL hW]
  unfold triMatZ triMatZI
  set cL : ℚ := LM.den * 4 ^ LM.k
  set cW : ℚ := WM.den * 4 ^ WM.k
  have hdiag : ∑ i : Fin 24, LM.entry i i * WM.entry i i =
      ∑ i : Fin 24, (LM.scal * WM.scal + LM.scal * ((WM.num i i : ℤ) : ℚ) / cW +
        WM.scal * ((LM.num i i : ℤ) : ℚ) / cL +
        (((LM.num i i * WM.num i i : ℤ)) : ℚ) / (cL * cW)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [MatZ.entry_num, MatZ.entry_num]
    simp only [↓reduceIte, Int.cast_mul]
    ring
  have hpairs : (L.sh.pairs.map (fun q => L.sden * (q.2 : ℚ) / 2 *
      (if fwd then 1 else if q.1 < 276 then 1 else -1) *
      (WM.entry (pairCoordsF q.1).1 (pairCoordsF q.1).2 +
        WM.entry (pairCoordsF q.1).2 (pairCoordsF q.1).1))).sum =
      L.sden * (((L.sh.pairs.map (fun q => q.2 * (if fwd then 1 else if q.1 < 276 then 1 else -1) *
        WM.num (pairCoordsF q.1).1 (pairCoordsF q.1).2)).sum : ℤ) : ℚ) / cW := by
    have hterm : ∀ q : ℕ × ℤ, L.sden * (q.2 : ℚ) / 2 *
        (if fwd then 1 else if q.1 < 276 then 1 else -1) *
        (WM.entry (pairCoordsF q.1).1 (pairCoordsF q.1).2 +
          WM.entry (pairCoordsF q.1).2 (pairCoordsF q.1).1) =
        L.sden * ((q.2 * (if fwd then 1 else if q.1 < 276 then 1 else -1) *
          WM.num (pairCoordsF q.1).1 (pairCoordsF q.1).2 : ℤ) : ℚ) / cW := by
      intro q
      have hne := pairCoordsF_ne q.1
      rw [MatZ.entry_num, MatZ.entry_num, ite_eq_right hne, ite_eq_right (Ne.symm hne),
        MatZ.num_comm WM (pairCoordsF q.1).2]
      split_ifs <;> push_cast <;> ring
    rw [List.map_congr_left (fun q _ => hterm q)]
    induction L.sh.pairs with
    | nil => simp
    | cons q l ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, ih]
      ring
  have e1 : ((((List.finRange 24).map (fun i => WM.num i i)).sum : ℤ) : ℚ) =
      ∑ i : Fin 24, ((WM.num i i : ℤ) : ℚ) := by
    rw [Int.cast_list_sum, List.map_map, Fin.sum_univ_def]
    rfl
  have e2 : ((((List.finRange 24).map (fun i => LM.num i i)).sum : ℤ) : ℚ) =
      ∑ i : Fin 24, ((LM.num i i : ℤ) : ℚ) := by
    rw [Int.cast_list_sum, List.map_map, Fin.sum_univ_def]
    rfl
  have e3 : ((((List.finRange 24).map (fun i => LM.num i i * WM.num i i)).sum : ℤ) : ℚ) =
      ∑ i : Fin 24, (((LM.num i i * WM.num i i : ℤ)) : ℚ) := by
    rw [Int.cast_list_sum, List.map_map, Fin.sum_univ_def]
    rfl
  rw [hdiag, hpairs, e1, e2, e3, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum]
  push_cast
  ring

/-- The pair short terms with integer sums (three rational operations). -/
def pairSumZI (fwd : Bool) (LM : MatZ) (L W : IdentVec) : ℚ :=
  (((W.sh.pairs.map (fun q => q.2 * (if fwd then (if q.1 < 276 then 1 else -1) else 1) *
      LM.num (pairCoordsF q.1).1 (pairCoordsF q.1).2)).sum : ℤ) : ℚ) / (LM.den * 4 ^ LM.k) +
    L.sden * (((W.sh.pairs.map (fun q => q.2 *
      (if fwd then idxSum L.sh.pairs (q.1 % 276) - idxSum L.sh.pairs (276 + q.1 % 276)
       else if q.1 < 276 then idxSum L.sh.pairs (q.1 % 276) + idxSum L.sh.pairs (276 + q.1 % 276)
       else -(idxSum L.sh.pairs (q.1 % 276) + idxSum L.sh.pairs (276 + q.1 % 276))))).sum : ℤ) :
      ℚ) / 2

theorem pairSumQ_eq_ZI (fwd : Bool) (L W : IdentVec) (LM : MatZ)
    (hL : ∀ i j, L.mat.entry i j = LM.entry i j) :
    pairSumQ fwd L W = pairSumZI fwd LM L W := by
  rw [pairSumQ_eq_Z fwd L W LM hL]
  unfold pairSumZ pairSumZI
  set cL : ℚ := LM.den * 4 ^ LM.k
  have hterm : ∀ q : ℕ × ℤ, (q.2 : ℚ) * triPairZ fwd LM L q.1 =
      ((q.2 * (if fwd then (if q.1 < 276 then 1 else -1) else 1) *
        LM.num (pairCoordsF q.1).1 (pairCoordsF q.1).2 : ℤ) : ℚ) / cL +
      L.sden * ((q.2 *
        (if fwd then idxSum L.sh.pairs (q.1 % 276) - idxSum L.sh.pairs (276 + q.1 % 276)
         else if q.1 < 276 then idxSum L.sh.pairs (q.1 % 276) + idxSum L.sh.pairs (276 + q.1 % 276)
         else -(idxSum L.sh.pairs (q.1 % 276) + idxSum L.sh.pairs (276 + q.1 % 276))) : ℤ) : ℚ) /
        2 := by
    intro q
    have hne := pairCoordsF_ne q.1
    unfold triPairZ
    simp only [MatZ.entry_num, ite_eq_right hne, zero_add, lookupQ_eq]
    cases fwd <;> by_cases hq : q.1 < 276 <;> simp [hq] <;> ring
  rw [List.map_congr_left (fun q _ => hterm q)]
  induction W.sh.pairs with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, ih]
    ring
end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
