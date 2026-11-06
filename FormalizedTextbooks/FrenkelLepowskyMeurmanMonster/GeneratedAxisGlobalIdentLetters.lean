/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorWord

/-! # The letter alphabet of the packed identification method

Words in these letters name local elements; the packed tensor, short and matrix evaluators
(worker `gident` and helper `gident2`) all act on words of this alphabet.  A word acts in
product order: the head letter acts last, as in `generatedAxisGlobalRationalTensorFrameWord`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

/-- Letters: the source Xi, a source Golay sign lift, a source permutation letter, or an
element of the extraspecial group. -/
inductive IdentLetter
  | xi
  | sign (a : Fin 4096) (ε : ZMod 2)
  | mono (l : Fin 2 × Bool)
  | qel (g : Q)

/-- The local fiber of a letter. -/
noncomputable def IdentLetter.fiber : IdentLetter → localFiberSubgroup
  | .xi => xiSpinLocalFiber
  | .sign a ε => generatedFifthSignFiber a ε
  | .mono l => generatedFourthMonomialFiberLetter l
  | .qel g => localFiberIncl g

/-- The local fiber of a word, in product order (the head letter acts last). -/
noncomputable def identWordFiber (ls : List IdentLetter) : localFiberSubgroup :=
  (ls.map IdentLetter.fiber).prod

/-- The local element of a word. -/
noncomputable def identWordLocal (ls : List IdentLetter) : H :=
  localFiberIntoH (identWordFiber ls)

/-- Words compose by concatenation. -/
theorem identWordFiber_append (ls ms : List IdentLetter) :
    identWordFiber (ls ++ ms) = identWordFiber ls * identWordFiber ms := by
  simp [identWordFiber, List.map_append, List.prod_append]

/-- The local element of a concatenation is the product. -/
theorem identWordLocal_append (ls ms : List IdentLetter) :
    identWordLocal (ls ++ ms) = identWordLocal ls * identWordLocal ms := by
  simp [identWordLocal, identWordFiber_append, map_mul]

/-- The local element of a single letter word is the image of its fiber. -/
theorem identWordLocal_singleton (l : IdentLetter) :
    identWordLocal [l] = localFiberIntoH l.fiber := by
  simp [identWordLocal, identWordFiber]

/-- The local action of a word on Conway coordinates is the raw fiber action. -/
theorem identWordLocal_encode (ls : List IdentLetter) (x : GriessSpace) :
    griessConwayEncode (rhoLocal (identWordLocal ls) x) =
      localConwayRawRepresentation (identWordFiber ls) (griessConwayEncode x) :=
  localGriessRepresentation_encode _ _

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
