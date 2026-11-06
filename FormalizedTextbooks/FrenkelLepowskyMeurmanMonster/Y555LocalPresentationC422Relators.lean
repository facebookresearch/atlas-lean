/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal original C422/S/Q relators, proved directly in their independent presentation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Actual group value of a positive source-generator word. -/
def y422PositiveWord (w : List (Fin 9)) : Y422Presentation :=
  (w.map fun v => (PresentedGroup.of v : Y422Presentation)).prod

/-- Concatenation multiplies actual positive-word values. -/
theorem y422PositiveWord_append (a b : List (Fin 9)) :
    y422PositiveWord (a ++ b) = y422PositiveWord a * y422PositiveWord b := by
  simp only [y422PositiveWord, List.map_append, List.prod_append]

/-- Literal repeated source words evaluate to the corresponding actual group power. -/
theorem y422PositiveWord_replicate (n : ℕ) (w : List (Fin 9)) :
    y422PositiveWord (List.replicate n w).flatten = (y422PositiveWord w) ^ n := by
  induction n with
  | zero => simp [y422PositiveWord]
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, y422PositiveWord_append, ih,
      pow_succ']

/-- Exact lexicographic numbering of the thirty-six distinct original source pairs. -/
def y422OriginalPair : Fin 36 → Fin 9 × Fin 9 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
    (0, 8), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
    (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8),
    (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6),
    (4, 7), (4, 8), (5, 6), (5, 7), (5, 8), (6, 7), (6, 8),
    (7, 8)]

/-- Each numbered pair uses two distinct original source letters. -/
theorem y422OriginalPair_distinct (i : Fin 36) :
    (y422OriginalPair i).1 ≠ (y422OriginalPair i).2 := by
  revert i
  decide +kernel

/-- The exact literal source spider power. -/
def y422SpiderWord : List (Fin 9) :=
  (List.replicate 10 [0, 1, 2, 0, 5, 6, 0, 7, 8]).flatten

/-- The literal spider power is an original defining relation. -/
theorem y422SpiderWord_valid : y422PositiveWord y422SpiderWord = 1 := by
  rw [y422SpiderWord, y422PositiveWord_replicate]
  have h := PresentedGroup.one_of_mem (rels := y422Relations)
    (show y422Spider ^ 10 ∈ y422Relations from Or.inr (Or.inr (Or.inl rfl)))
  simpa [y422Spider, y422PositiveWord, PresentedGroup.of, map_pow, map_mul, mul_assoc] using h

/-- The corrected seven-letter first longest spelling, with its original ninth power. -/
def y422F12Word : List (Fin 9) :=
  (List.replicate 9 [0, 1, 5, 7, 2, 6, 3]).flatten

/-- The literal longest spelling evaluates to the original presented source word. -/
theorem y422F12Word_value :
    y422PositiveWord y422F12Word = PresentedGroup.mk y422Relations y422F12 := by
  rw [y422F12Word, y422PositiveWord_replicate]
  simp [y422PositiveWord, y422F12, map_pow, map_mul, PresentedGroup.of, mul_assoc]

/-- The exact printed Q cubic uses the corrected longest word followed by e1. -/
def y422CubicWord : List (Fin 9) := (List.replicate 3 (y422F12Word ++ [4])).flatten

/-- The literal Q cubic is an original defining relation. -/
theorem y422CubicWord_valid : y422PositiveWord y422CubicWord = 1 := by
  rw [y422CubicWord, y422PositiveWord_replicate, y422PositiveWord_append, y422F12Word_value]
  have h := PresentedGroup.one_of_mem (rels := y422Relations)
    (show y422Cubic ∈ y422Relations from Or.inr (Or.inr (Or.inr rfl)))
  simpa [y422Cubic, y422PositiveWord, map_pow, map_mul, PresentedGroup.of] using h

/-- Exactly the original pair relators, spider10, and Q, with no added equations. -/
def y422RelatorWord (r : Fin 38) : List (Fin 9) :=
  if h : r.val < 36 then
    let pair := y422OriginalPair ⟨r.val, h⟩
    let exponent := if y444Adjacent (y422Vertex pair.1) (y422Vertex pair.2) then 3 else 2
    (List.replicate exponent [pair.1, pair.2]).flatten
  else if r.val = 36 then y422SpiderWord else y422CubicWord

/-- All replay relators hold in the original independent C422/S/Q group before replay. -/
theorem y422RelatorWord_valid (r : Fin 38) : y422PositiveWord (y422RelatorWord r) = 1 := by
  unfold y422RelatorWord
  split
  · dsimp only
    rw [y422PositiveWord_replicate]
    simpa only [y422PositiveWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using y422_coxeter_relation
        (y422OriginalPair ⟨r.val, ‹r.val < 36›⟩).1
        (y422OriginalPair ⟨r.val, ‹r.val < 36›⟩).2
        (y422OriginalPair_distinct ⟨r.val, ‹r.val < 36›⟩)
  · split
    · exact y422SpiderWord_valid
    · exact y422CubicWord_valid

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
