/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSelectedOctad

/-! Original selected-octad words reaching all genuine physical triples. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- All three-coordinate subsets of the actual selected octad. -/
def generatedSeventhSelectedTriple : Fin 56 → Finset (Fin 24) :=
  ![{0, 1, 2},
    {0, 1, 3},
    {0, 1, 16},
    {0, 1, 17},
    {0, 1, 18},
    {0, 1, 19},
    {0, 2, 3},
    {0, 2, 16},
    {0, 2, 17},
    {0, 2, 18},
    {0, 2, 19},
    {0, 3, 16},
    {0, 3, 17},
    {0, 3, 18},
    {0, 3, 19},
    {0, 16, 17},
    {0, 16, 18},
    {0, 16, 19},
    {0, 17, 18},
    {0, 17, 19},
    {0, 18, 19},
    {1, 2, 3},
    {1, 2, 16},
    {1, 2, 17},
    {1, 2, 18},
    {1, 2, 19},
    {1, 3, 16},
    {1, 3, 17},
    {1, 3, 18},
    {1, 3, 19},
    {1, 16, 17},
    {1, 16, 18},
    {1, 16, 19},
    {1, 17, 18},
    {1, 17, 19},
    {1, 18, 19},
    {2, 3, 16},
    {2, 3, 17},
    {2, 3, 18},
    {2, 3, 19},
    {2, 16, 17},
    {2, 16, 18},
    {2, 16, 19},
    {2, 17, 18},
    {2, 17, 19},
    {2, 18, 19},
    {3, 16, 17},
    {3, 16, 18},
    {3, 16, 19},
    {3, 17, 18},
    {3, 17, 19},
    {3, 18, 19},
    {16, 17, 18},
    {16, 17, 19},
    {16, 18, 19},
    {17, 18, 19}]

/-- Positive original permutation words reaching each selected triple. -/
def generatedSeventhSelectedTripleWord : Fin 56 → List (Fin 5) :=
  ![[2, 3, 4, 0],
    [4, 1, 4],
    [3, 4, 3, 4],
    [4, 3, 4],
    [4, 2, 0],
    [4, 4, 3, 4],
    [3, 4, 0],
    [1, 4, 3, 4],
    [4, 3, 2, 4],
    [4, 0],
    [4, 2, 3, 4],
    [3, 1, 4],
    [3, 4],
    [4, 0, 2, 0],
    [3, 4, 1, 0],
    [2, 0],
    [4],
    [0, 2, 4],
    [1, 4],
    [0, 2, 1, 4],
    [4, 1, 0],
    [4, 4, 0],
    [2, 3, 1, 4],
    [2, 3, 4],
    [3, 4, 4, 0],
    [2, 3, 4, 1, 0],
    [4, 4, 1, 0],
    [4, 4, 0, 2, 0],
    [4, 4],
    [4, 4, 2, 0],
    [1, 0],
    [1, 2, 1, 4],
    [1, 4, 4, 4, 0],
    [1, 2, 4],
    [4, 4, 1, 4],
    [1, 2, 4, 1, 0],
    [3, 2, 1, 4],
    [3, 2, 4],
    [4, 2, 4],
    [3, 2, 4, 1, 0],
    [0],
    [2, 4],
    [2, 0, 2, 4],
    [2, 1, 4],
    [4, 4, 4, 0],
    [2, 4, 1, 0],
    [2, 1, 0],
    [0, 3, 1, 4],
    [1, 4, 4, 4],
    [0, 3, 4],
    [4, 4, 4],
    [0, 3, 4, 0],
    [0, 2, 0],
    [],
    [3, 4, 4, 4],
    [4, 4, 4, 1, 0]]

/-- The actual Golay automorphism represented by each literal word. -/
def generatedSeventhSelectedTripleRep (k : Fin 56) : golayAutomorphismSubgroup :=
  ((generatedSeventhSelectedTripleWord k).map generatedFifthSelectedOctadPermutation).prod

/-- The finite coordinate evaluation of an original selected permutation word. -/
def generatedSeventhSelectedWordForward (w : List (Fin 5)) (i : Fin 24) : Fin 24 :=
  w.foldr (fun k j => generatedFifthSelectedOctadForward k j) i

/-- Each literal word evaluates using precisely the checked original coordinate arrays. -/
theorem generatedSeventh_selected_word_forward (w : List (Fin 5)) (i : Fin 24) :
    (((w.map generatedFifthSelectedOctadPermutation).prod).val i) =
      generatedSeventhSelectedWordForward w i := by
  rw [Subgroup.val_list_prod, List.map_map]
  induction w with
  | nil => rfl
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, Function.comp_apply]
    rw [ih, generatedFifthSelectedOctad_forward]
    rfl

/-- Every genuine displayed word lies in the full actual octad permutation subgroup. -/
theorem generatedSeventh_selected_triple_rep_mem (k : Fin 56) :
    generatedSeventhSelectedTripleRep k ∈ generatedFifthSelectedOctadSubgroup := by
  apply Subgroup.list_prod_mem
  intro p hp
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
  exact generatedFifthSelectedOctad_generator_mem j

/-- The 56 literal physical triples have distinct addresses. -/
theorem generatedSeventh_selected_triple_injective :
    Function.Injective generatedSeventhSelectedTriple := by decide +kernel

set_option maxHeartbeats 4000000 in
-- Only 56 words and three physical coordinate images are evaluated.
/-- Each actual original word has the asserted three-coordinate image. -/
theorem generatedSeventh_selected_triple_rep_image (k : Fin 56) :
    generatedSeventhSelectedTripleRep k • ({16, 17, 19} : Finset (Fin 24)) =
      generatedSeventhSelectedTriple k := by
  rw [Finset.smul_finset_def, Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  change ({(generatedSeventhSelectedTripleRep k).val 16,
    (generatedSeventhSelectedTripleRep k).val 17,
    (generatedSeventhSelectedTripleRep k).val 19} : Finset (Fin 24)) = _
  simp only [generatedSeventhSelectedTripleRep, generatedSeventh_selected_word_forward]
  revert k
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
