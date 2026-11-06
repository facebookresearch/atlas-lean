/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastRun

/-! # Faster integer matrix and pair parts

Two kernel bottlenecks of the integer matrix/pair parts (`triMatZI`, `pairSumZI`) on long words
and many pair terms:
* the integer word action `MatZ.act` evaluates every monomial letter through the vector literals
  of its permutation; `MatZ.actT` follows a tensor plan instead and applies a run of monomial
  letters as one composite coordinate table (`permOfNE`), `MatZ.actT_eq`;
* `pairSumZI` looks up pair coefficients of `L` by list scans (`idxSum`); `pairSumZF` reads them
  from one packed vector, and `pairSumQ_of_chk` gives the pair part from one kernel check. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators
set_option autoImplicit false

namespace MPF

/-! ## Fused monomial runs -/

/-- The coordinate table of a monomial letter. -/
def permL (l : Fin 2 × Bool) : List ℕ := (List.finRange 24).map (fun i => (monoPermIdx l i).val)

/-- Reading the coordinates of an integer vector through a table. -/
def applyP (p : List ℕ) (z : List ℤ) : List ℤ := p.map (fun j => zget z j)

/-- The composite table of a nonempty run of monomial letters (the head acts last). -/
def permOfNE (l : Fin 2 × Bool) : List (Fin 2 × Bool) → List ℕ
  | [] => permL l
  | l' :: ls => (permL l).map (fun j => (permOfNE l' ls).getD j 0)

theorem permL_length (l : Fin 2 × Bool) : (permL l).length = 24 := by simp [permL]

theorem permL_lt (l : Fin 2 × Bool) : ∀ j ∈ permL l, j < 24 := by
  intro j hj
  simp only [permL, List.mem_map] at hj
  obtain ⟨i, _, rfl⟩ := hj
  exact (monoPermIdx l i).isLt

theorem permOfNE_length (l : Fin 2 × Bool) : ∀ ls, (permOfNE l ls).length = 24
  | [] => permL_length l
  | _ :: _ => by simp [permOfNE, permL_length]

theorem monoZ_eq (l : Fin 2 × Bool) (z : List ℤ) : monoZ l z = applyP (permL l) z := by
  unfold monoZ applyP permL
  rw [List.ofFn_eq_map, List.map_map]
  rfl

theorem applyP_comp (p q : List ℕ) (z : List ℤ) (h : ∀ j ∈ p, j < q.length) :
    applyP p (applyP q z) = applyP (p.map (fun j => q.getD j 0)) z := by
  unfold applyP
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  have hjq := h j hj
  simp only [Function.comp_apply, zget]
  rw [List.getD_eq_getElem _ _ (by simpa using hjq), List.getElem_map,
    List.getD_eq_getElem _ _ hjq]

theorem wordZ_run (l : Fin 2 × Bool) : ∀ (ls : List (Fin 2 × Bool)) (z : List ℤ),
    wordZ ((l :: ls).map IdentLetter.mono) z = applyP (permOfNE l ls) z
  | [], z => by simp [wordZ, letterZ, monoZ_eq, permOfNE]
  | l' :: ls, z => by
    have ih := wordZ_run l' ls z
    rw [List.map_cons, wordZ, ih]
    simp only [letterZ]
    rw [monoZ_eq, applyP_comp _ _ _ (fun j hj => by
      rw [permOfNE_length]; exact permL_lt l j hj)]
    rfl

theorem wordZ_append : ∀ (a b : List IdentLetter) (z : List ℤ),
    wordZ (a ++ b) z = wordZ a (wordZ b z)
  | [], _, _ => rfl
  | x :: a, b, z => by rw [List.cons_append, wordZ, wordZ, wordZ_append a b z]

/-- The integer spatial action of a tensor plan (runs as composite tables). -/
def wordZT : List TPlan → List ℤ → List ℤ
  | [], z => z
  | .letter x :: ps, z => letterZ x (wordZT ps z)
  | .run [] _ :: ps, z => wordZT ps z
  | .run (l :: ls) _ :: ps, z => applyP (permOfNE l ls) (wordZT ps z)

theorem wordZT_eq : ∀ (ps : List TPlan) (z : List ℤ), wordZT ps z = wordZ (planWord ps) z
  | [], _ => rfl
  | .letter x :: ps, z => by
    rw [wordZT, wordZT_eq ps z]
    simp only [planWord, List.flatMap_cons, TPlan.word]
    rfl
  | .run [] S :: ps, z => by
    rw [wordZT, wordZT_eq ps z]
    simp [planWord, TPlan.word]
  | .run (l :: ls) S :: ps, z => by
    rw [wordZT, wordZT_eq ps z]
    simp only [planWord, List.flatMap_cons, TPlan.word]
    rw [wordZ_append, wordZ_run]

end MPF

/-- The integer matrix block transported by a tensor plan. -/
def MatZ.actT (ps : List TPlan) (M : MatZ) : MatZ :=
  ⟨M.scal, M.den, M.terms.map (fun t => (t.1, MPF.wordZT ps t.2)), M.k + wordE (planWord ps)⟩

theorem MatZ.actT_eq (ps : List TPlan) (M : MatZ) : M.actT ps = M.act (planWord ps) := by
  unfold MatZ.actT MatZ.act
  simp only [MPF.wordZT_eq]

/-! ## The pair part with packed lookups -/

/-- `pairSumZI` with the pair coefficients of `L` read from the packed vector `P`. -/
def pairSumZF (fwd : Bool) (LM : MatZ) (L W : IdentVec) (P : SVec) : ℚ :=
  (((W.sh.pairs.map (fun q => q.2 * (if fwd then (if q.1 < 276 then 1 else -1) else 1) *
      LM.num (pairCoordsF q.1).1 (pairCoordsF q.1).2)).sum : ℤ) : ℚ) / (LM.den * 4 ^ LM.k) +
    L.sden * (((W.sh.pairs.map (fun q => q.2 *
      (if fwd then svalS 32 P (q.1 % 276) - svalS 32 P (276 + q.1 % 276)
       else if q.1 < 276 then svalS 32 P (q.1 % 276) + svalS 32 P (276 + q.1 % 276)
       else -(svalS 32 P (q.1 % 276) + svalS 32 P (276 + q.1 % 276))))).sum : ℤ) : ℚ) / 2

theorem pairSumZF_eq (fwd : Bool) (LM : MatZ) (L W : IdentVec)
    (hl : ∀ p ∈ L.sh.pairs, p.1 < 552) (ha : absSum L.sh.pairs < 2 ^ 32) :
    pairSumZF fwd LM L W (packF 32 L.sh.pairs) = pairSumZI fwd LM L W := by
  obtain ⟨-, hv⟩ := packF_spec 32 552 L.sh.pairs hl ha
  have h1 : ∀ q : ℕ × ℤ, svalS 32 (packF 32 L.sh.pairs) (q.1 % 276) = idxSum L.sh.pairs (q.1 % 276) :=
    fun q => by rw [svalS_eq_sval, hv _ (by omega)]
  have h2 : ∀ q : ℕ × ℤ, svalS 32 (packF 32 L.sh.pairs) (276 + q.1 % 276) =
      idxSum L.sh.pairs (276 + q.1 % 276) := fun q => by rw [svalS_eq_sval, hv _ (by omega)]
  unfold pairSumZF pairSumZI
  simp only [h1, h2]

/-- The checked pair part: label range, packing width, and the value `p`. -/
def pairChk (fwd : Bool) (LM : MatZ) (L W : IdentVec) (p : ℚ) : Bool :=
  L.sh.pairs.all (fun q => decide (q.1 < 552)) && decide (absSum L.sh.pairs < 2 ^ 32) &&
    decide (pairSumZF fwd LM L W (packF 32 L.sh.pairs) = p)

theorem pairSumQ_of_chk (fwd : Bool) (L W : IdentVec) (LM : MatZ)
    (hL : ∀ i j, L.mat.entry i j = LM.entry i j) {p : ℚ} (h : pairChk fwd LM L W p = true) :
    pairSumQ fwd L W = p := by
  simp only [pairChk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, ha⟩, hv⟩ := h
  rw [pairSumQ_eq_ZI fwd L W LM hL, ← pairSumZF_eq fwd LM L W hl ha, hv]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
