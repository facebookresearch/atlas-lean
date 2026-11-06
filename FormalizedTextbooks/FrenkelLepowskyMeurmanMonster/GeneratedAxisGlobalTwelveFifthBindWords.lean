/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindCosetBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLettersInv
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortFiber

/-! The Fifth source elements of the remaining identifications, as words of the packed
identification alphabet.

* Each one-xi coset representative `generatedAxisGlobalTwelveFifthBindCoset k` is literally the
  local element of an `IdentLetter` word: the inverse Xi is the square of Xi and the inverse
  source permutation letters are the signed monomial letters.
* Each explicit Fifth root word `generatedAxisGlobalFifthShortLocalWord k` is the local element of
  the word read off from its seven normalization stages (Xi, Golay sign with phase zero, source
  permutation letters), with the same fibers, so no phase is lost.

These are exact equalities in `H`; they let the packed identification lemmas be applied to the
source elements of `generatedAxisGlobalTwelveFifthBind_covered_of_identities`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- The representative words (head letter acts last), for the roots 0, 1, 6 and 12. -/
def generatedAxisGlobalTwelveFifthBindCosetLetters : Fin 4 → List IdentLetter :=
  ![[.xi, .xi, .mono (1, true)],
    [.xi, .xi, .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, true)],
    [.xi, .xi, .mono (1, true), .mono (0, true)],
    [.xi, .xi, .mono (0, true)]]

/-- Each representative is the local element of its displayed word. -/
theorem generatedAxisGlobalTwelveFifthBindCoset_eq_word (k : Fin 4) :
    generatedAxisGlobalTwelveFifthBindCoset k =
      identWordLocal (generatedAxisGlobalTwelveFifthBindCosetLetters k) := by
  unfold generatedAxisGlobalTwelveFifthBindCoset identWordLocal identWordFiber
  congr 1
  fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      generatedAxisGlobalTwelveFifthBindCosetFiber,
      generatedAxisGlobalTwelveFifthBindCosetLetters, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      IdentLetter.fiber, generatedFourthMonomialFiberLetter, Bool.false_eq_true, ite_true,
      ite_false, xiFiber_inv, mul_assoc]

/-- The letters of one normalization stage of the explicit Fifth root word `k`. -/
def generatedAxisGlobalTwelveFifthBindStageLetters (k : Fin 14) (j : Fin 7) : List IdentLetter :=
  (if generatedAxisGlobalFifthShortNormalizationXi k j then [IdentLetter.xi] else []) ++
    (IdentLetter.sign (generatedAxisGlobalFifthShortNormalizationSigns k j) 0 ::
      (generatedAxisGlobalFifthShortNormalizationWords k j).map IdentLetter.mono)

/-- The chronological concatenation of the first `n` stages (later stages at the head). -/
def generatedAxisGlobalTwelveFifthBindChainLetters (k : Fin 14) : ℕ → List IdentLetter
  | 0 => []
  | n + 1 => generatedAxisGlobalTwelveFifthBindStageLetters k ⟨n % 7, Nat.mod_lt _ (by decide)⟩ ++
      generatedAxisGlobalTwelveFifthBindChainLetters k n

/-- The full word of the explicit Fifth root word `k`. -/
def generatedAxisGlobalTwelveFifthBindRootLetters (k : Fin 14) : List IdentLetter :=
  generatedAxisGlobalTwelveFifthBindChainLetters k 7

theorem generatedAxisGlobalTwelveFifthBindStageLetters_fiber (k : Fin 14) (j : Fin 7) :
    identWordFiber (generatedAxisGlobalTwelveFifthBindStageLetters k j) =
      generatedAxisGlobalFifthShortNormalizationFiber k j := by
  unfold generatedAxisGlobalTwelveFifthBindStageLetters
    generatedAxisGlobalFifthShortNormalizationFiber
  rw [identWordFiber_append]
  congr 1
  · cases generatedAxisGlobalFifthShortNormalizationXi k j <;>
      simp [identWordFiber, IdentLetter.fiber]
  · simp [identWordFiber, IdentLetter.fiber, List.map_map, Function.comp_def]

theorem generatedAxisGlobalTwelveFifthBindChainLetters_fiber (k : Fin 14) (n : ℕ) :
    identWordFiber (generatedAxisGlobalTwelveFifthBindChainLetters k n) =
      generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthShortNormalizationFiber k
        ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n := by
  induction n with
  | zero => simp [generatedAxisGlobalTwelveFifthBindChainLetters, identWordFiber,
      generatedAxisGlobalWordChain]
  | succ n ih =>
    rw [generatedAxisGlobalTwelveFifthBindChainLetters, identWordFiber_append, ih,
      generatedAxisGlobalTwelveFifthBindStageLetters_fiber]
    rfl

/-- Each explicit Fifth root word is the local element of its full word. -/
theorem generatedAxisGlobalTwelveFifthBindRoot_eq_word (k : Fin 14) :
    generatedAxisGlobalFifthShortLocalWord k =
      identWordLocal (generatedAxisGlobalTwelveFifthBindRootLetters k) := by
  rw [← generatedAxisGlobalFifthShortWordFiber_local, identWordLocal,
    generatedAxisGlobalTwelveFifthBindRootLetters,
    generatedAxisGlobalTwelveFifthBindChainLetters_fiber]
  rfl

/-- The Fifth catalogue representative is the Fifth axis. -/
theorem generatedAxisGlobalTwelveFifthBind_rep_four :
    generatedAxisGlobalTwelveRepresentative 4 = generatedFifthAxis := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
