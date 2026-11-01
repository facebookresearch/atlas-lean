/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensor

/-! # Packed Xi tensor letter

A packed implementation of the rational Xi tensor operator
`generatedAxisGlobalRationalTensorXi` (whose `_actual` lemma binds it to
`localTensorRepresentation xiSpinLocalFiber`).  The 64-term Gaussian of the spin factor is
computed as one diagonal Gamma sign mask followed by 64 signed translations of each packed
column; the spatial factor combines the four columns of each tetrad.  Small finite tables
(64 grey labels, the quadratic form, the Gamma sign bitset) are kernel-checked against the
original definitions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-- The grey index with binary label `n`. -/
def xiA (n : ℕ) : XiGrayIndex := fun i => if n.testBit i.val then 1 else 0

/-- The spin labels of the 64 grey code translations, indexed by grey label. -/
def xiCodeTab : List ℕ :=
  [0, 1024, 3087, 2063, 3073, 2049, 14, 1038, 3074, 2050, 13, 1037, 3, 1027, 3084, 2060,
    3076, 2052, 11, 1035, 5, 1029, 3082, 2058, 6, 1030, 3081, 2057, 3079, 2055, 8, 1032,
    3080, 2056, 7, 1031, 9, 1033, 3078, 2054, 10, 1034, 3077, 2053, 3083, 2059, 4, 1028,
    12, 1036, 3075, 2051, 3085, 2061, 2, 1026, 3086, 2062, 1, 1025, 15, 1039, 3072, 2048]

/-- Bit `n` is the published grey quadratic form at grey label `n`. -/
def xiQBits : ℕ := 0x8117177e177e7ee8

/-- The cocode labels of the six Gamma characters. -/
def xiCocodeLabels : List ℕ := [2048, 3087, 3086, 3085, 3083, 3079]

/-- The number of Gamma characters taking the value one at a spin label. -/
def xiGammaCount (m : ℕ) : ℕ :=
  (xiCocodeLabels.map (fun c => if bpar (m &&& c) 12 then 1 else 0)).sum

/-- The Gamma sign as a cheap predicate: the character weight is 2 or 3 modulo 4. -/
def xiGammaCheap (m : ℕ) : Bool := decide (2 ≤ xiGammaCount m % 4)

/-- The grey translation table is the actual grey code. -/
theorem xiCodeTab_spec : ∀ n : Fin 64,
    xiCodeTab.getD n.val 0 = (generatedAxisGlobalSpinLabel (xiGrayCode (xiA n.val))).val := by
  decide +kernel

/-- The quadratic bitset is the actual grey quadratic form. -/
theorem xiQBits_spec : ∀ n : Fin 64,
    xiQBits.testBit n.val = decide (xiGrayQuadratic (xiA n.val) = 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The dual quadratic form depends only on the weight modulo four. -/
theorem xiGrayQuadratic_dual_weight : ∀ f : XiGrayIndex,
    xiGrayQuadratic (xiGrayDual f) = if 2 ≤ (∑ i : Fin 6, (f i).val) % 4 then 1 else 0 := by
  decide +kernel

/-- The cocode label table is the actual grey cocode labels. -/
theorem xiCocodeLabels_spec : ∀ i : Fin 6,
    xiCocodeLabels.getD i.val 0 = (xiGrayCocodeLabel i).val := by
  decide +kernel

/-! ## The Gamma sign as a pairwise mask -/

/-- Exclusive or of products of pairs of character parities. -/
def ppredL (cs : ℕ → ℕ) (m : ℕ) : List (ℕ × ℕ) → Bool
  | [] => false
  | p :: ps => ppredL cs m ps ^^ (bpar (m &&& cs p.1) 12 && bpar (m &&& cs p.2) 12)

/-- The field mask of `ppredL`: exclusive or of conjunctions of linear masks. -/
def pmaskL (w : ℕ) (cs : ℕ → ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: ps => pmaskL w cs ps ^^^
      (linMask w 12 (cs p.1) false 12 &&& linMask w 12 (cs p.2) false 12)

/-- The pairwise mask is the field mask of the pairwise predicate. -/
theorem pmaskL_isFieldMask (w : ℕ) (cs : ℕ → ℕ) : ∀ ps : List (ℕ × ℕ),
    IsFieldMask w (2 ^ 12) (pmaskL w cs ps) (fun m => ppredL cs m ps = true)
  | [] => (zero_isFieldMask w _).congr (fun t _ => by simp [ppredL])
  | p :: ps => by
    have h1 := pmaskL_isFieldMask w cs ps
    have h2 := isFieldMask_and (linMask_isFieldMask w 12 (cs p.1) false 12 le_rfl)
      (linMask_isFieldMask w 12 (cs p.2) false 12 le_rfl)
    refine (isFieldMask_xor h1 h2).congr (fun t _ => ?_)
    simp only [ppredL, Bool.false_xor]
    cases ppredL cs t ps <;> cases bpar (t &&& cs p.1) 12 <;> cases bpar (t &&& cs p.2) 12 <;>
      simp

/-- The six Gamma character labels as a function. -/
def xiC (i : ℕ) : ℕ := xiCocodeLabels.getD i 0

/-- All fifteen pairs of the six Gamma characters. -/
def xiPairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
    (2, 5), (3, 4), (3, 5), (4, 5)]

/-- The Gamma sign predicate: an odd number of pairs of characters are both one. -/
def xiGammaB (m : ℕ) : Bool := ppredL xiC m xiPairs

/-- The Gamma field mask. -/
def xiGammaMask (w : ℕ) : ℕ := pmaskL w xiC xiPairs

/-- The Gamma field mask is the field mask of the Gamma predicate. -/
theorem xiGammaMask_isFieldMask (w : ℕ) :
    IsFieldMask w (2 ^ 12) (xiGammaMask w) (fun m => xiGammaB m = true) :=
  pmaskL_isFieldMask w xiC xiPairs

/-- Weight two or three modulo four is the odd pair count. -/
theorem xiGammaCount_iff (m : ℕ) : (2 ≤ xiGammaCount m % 4) ↔ xiGammaB m = true := by
  simp only [xiGammaCount, xiCocodeLabels, xiGammaB, xiPairs, ppredL, xiC, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, List.getD_cons_zero, List.getD_cons_succ]
  cases bpar (m &&& 2048) 12 <;> cases bpar (m &&& 3087) 12 <;> cases bpar (m &&& 3086) 12 <;>
    cases bpar (m &&& 3085) 12 <;> cases bpar (m &&& 3083) 12 <;> cases bpar (m &&& 3079) 12 <;>
    decide

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
