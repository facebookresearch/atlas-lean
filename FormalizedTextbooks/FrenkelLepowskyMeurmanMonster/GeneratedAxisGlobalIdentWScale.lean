/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord

/-! # Scaled short blocks (gident2)

A short block whose values are all multiples of `k` can be stored with the values divided by `k`
and the scale multiplied by `k`: `IdentVec.real_scale`.  The factory uses this to keep the
transported short lists of the Seventh and Eighth sources (all values multiples of `256`) in
8-bit fields. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Multiply all values of a term list by `k`. -/
def scaleTerms (k : ℤ) (L : List (ℕ × ℤ)) : List (ℕ × ℤ) := L.map (fun p => (p.1, k * p.2))

/-- Multiply all values of the octad blocks by `k`. -/
def scaleOct (k : ℤ) (B : List (ℕ × List (ℕ × ℤ))) : List (ℕ × List (ℕ × ℤ)) :=
  B.map (fun b => (b.1, scaleTerms k b.2))

/-- Multiply all values of a short block by `k`. -/
def ShortData.scale (k : ℤ) (S : ShortData) : ShortData :=
  ⟨scaleTerms k S.pairs, scaleOct k S.oct, scaleTerms k S.odd⟩

/-- Scaling distributes over concatenation. -/
theorem scaleTerms_append (k : ℤ) (A B : List (ℕ × ℤ)) :
    scaleTerms k (A ++ B) = scaleTerms k A ++ scaleTerms k B := List.map_append

/-- Scaling distributes over flattening. -/
theorem scaleTerms_flatten (k : ℤ) (Ls : List (List (ℕ × ℤ))) :
    scaleTerms k Ls.flatten = (Ls.map (scaleTerms k)).flatten := by
  unfold scaleTerms
  rw [List.map_flatten]

/-- Scaling distributes over `flatMap`. -/
theorem scaleTerms_flatMap {α : Type} (k : ℤ) (l : List α) (f : α → List (ℕ × ℤ)) :
    scaleTerms k (l.flatMap f) = l.flatMap (fun a => scaleTerms k (f a)) := by
  unfold scaleTerms
  rw [List.map_flatMap]

/-- Scaling of octad blocks distributes over concatenation. -/
theorem scaleOct_append (k : ℤ) (A B : List (ℕ × List (ℕ × ℤ))) :
    scaleOct k (A ++ B) = scaleOct k A ++ scaleOct k B := List.map_append

/-- The flat terms of scaled octad blocks. -/
theorem octsFlat_scaleOct (k : ℤ) (B : List (ℕ × List (ℕ × ℤ))) :
    octsFlat (scaleOct k B) = scaleTerms k (octsFlat B) := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    simp only [scaleOct, List.map_cons, octsFlat] at ih ⊢
    rw [ih, scaleTerms_append]
    congr 1
    simp only [octFlat, scaleTerms, List.map_map]
    rfl

/-- The flat terms of a scaled short block. -/
theorem ShortData.flat_scale (k : ℤ) (S : ShortData) :
    (S.scale k).flat = scaleTerms k S.flat := by
  simp only [ShortData.flat, ShortData.scale, octsFlat_scaleOct, scaleTerms_append]

/-- The real short block of a scaled list. -/
theorem shortVec_scaleTerms (k : ℤ) (L : List (ℕ × ℤ)) :
    shortVec (scaleTerms k L) = (k : ℝ) • shortVec L := by
  induction L with
  | nil => simp [scaleTerms, shortVec]
  | cons p L ih =>
    have h : scaleTerms k (p :: L) = (p.1, k * p.2) :: scaleTerms k L := rfl
    rw [h, shortVec_cons, shortVec_cons, ih, smul_add, smul_smul]
    push_cast
    rfl

/-- Values multiplied by `k` with the scale divided by `k`: the same real coordinates. -/
theorem IdentVec.real_scale (M : MatRep) (S : ShortData) (d : ℚ) (k : ℤ)
    (T : GeneratedAxisGlobalRationalTensor) :
    (⟨M, S.scale k, d, T⟩ : IdentVec).real = (⟨M, S, d * k, T⟩ : IdentVec).real := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  rw [IdentVec.real_short, IdentVec.real_short]
  simp only
  rw [ShortData.flat_scale, shortVec_scaleTerms, smul_smul]
  push_cast
  rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
