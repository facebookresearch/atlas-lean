/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete source equations whose actual original-group validity is independently proved. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayTConsequences

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

-- Actual source-family comparison unfolds the literal finite auxiliary definition tables.
set_option maxRecDepth 100000

/-- Concatenation of signed replay words multiplies their actual original-group values. -/
theorem y431AuxReplayWordValue_append (a b : List (Fin 810 × Bool)) :
    y431AuxReplayWordValue (a ++ b) =
      y431AuxReplayWordValue a * y431AuxReplayWordValue b :=
  y322EquationWordValue_append y431AuxReplaySymbol a b

/-- Two positive symbols have their exact actual-group product as value. -/
theorem y431AuxReplayWordValue_two (a b : Fin 810) :
    y431AuxReplayWordValue [(a, true), (b, true)] =
      y431AuxReplaySymbol a * y431AuxReplaySymbol b := by
  change y431AuxReplayWordValue ([(a, true)] ++ [(b, true)]) = _
  rw [y431AuxReplayWordValue_append, y431AuxReplayWordValue_singleton,
    y431AuxReplayWordValue_singleton]

/-- Literal right-hand sides of the actual H auxiliary definitions. -/
def y431AuxReplayHRhsWord : Y431AuxReplayHRule → List (Fin 810 × Bool)
  | .one => []
  | .generator v => [(y431AuxReplayGeneratorSymbol (y431AuxOriginalLetter v), true)]
  | .mul a b _ => [(y431AuxReplayHSymbol a, true), (y431AuxReplayHSymbol b, true)]
  | .inv a _ => [(y431AuxReplayHSymbol a, false)]
  | .reverse a => [(y431AuxReplayHSymbol a, false)]

/-- Every H right-hand side has the exact actual value of its declared word operation. -/
theorem y431AuxReplayHRhsWord_value (rule : Y431AuxReplayHRule) :
    y431AuxReplayWordValue (y431AuxReplayHRhsWord rule) = y431AuxReplayHRuleValue rule := by
  cases rule with
  | one => exact y431AuxReplayWordValue_nil
  | generator v =>
    simp only [y431AuxReplayHRhsWord, y431AuxReplayHRuleValue,
      y431AuxReplayWordValue_singleton, y431AuxReplayGeneratorSymbol_value,
      y431AuxGenerator_original]
  | mul a b c =>
    simp only [y431AuxReplayHRhsWord, y431AuxReplayHRuleValue,
      y431AuxReplayWordValue_two, y431AuxReplayHSymbol_value]
  | inv a c =>
    simp only [y431AuxReplayHRhsWord, y431AuxReplayHRuleValue,
      y431AuxReplayWordValue_inverse_singleton, y431AuxReplayHSymbol_value]
  | reverse a =>
    simp only [y431AuxReplayHRhsWord, y431AuxReplayHRuleValue,
      y431AuxReplayWordValue_inverse_singleton, y431AuxReplayHSymbol_value]

/-- Literal right-hand sides of the explicit actual T auxiliary path definitions. -/
def y431AuxReplayTRhsWord : Y431AuxReplayTDefinition → List (Fin 810 × Bool)
  | .one => []
  | .append a g => [(y431AuxReplayTSymbol a, true), (y431AuxReplayGeneratorSymbol g, true)]

/-- Every T right-hand side has the exact actual value of its literal path operation. -/
theorem y431AuxReplayTRhsWord_value (rule : Y431AuxReplayTDefinition) :
    y431AuxReplayWordValue (y431AuxReplayTRhsWord rule) =
      y431AuxReplayTDefinitionValue rule := by
  cases rule with
  | one => exact y431AuxReplayWordValue_nil
  | append a g =>
    simp only [y431AuxReplayTRhsWord, y431AuxReplayTDefinitionValue,
      y431AuxReplayWordValue_two, y431AuxReplayTSymbol_value,
      y431AuxReplayGeneratorSymbol_value]

/-- The exact source equation specified by a proved original relation or actual word definition. -/
def y431AuxReplaySourceByKind : Y431AuxReplaySourceKind → Y322WordEquation (Fin 810)
  | .square g =>
    ⟨[(y431AuxReplayGeneratorSymbol g, true), (y431AuxReplayGeneratorSymbol g, true)], []⟩
  | .relator r =>
    ⟨(y431AuxRelatorWord r).map (fun i => (y431AuxReplayGeneratorSymbol i, true)), []⟩
  | .H i => ⟨[(y431AuxReplayHSymbol i, true)], y431AuxReplayHRhsWord (y431AuxReplayHRule i)⟩
  | .T i =>
    ⟨[(y431AuxReplayTSymbol i, true)], y431AuxReplayTRhsWord (y431AuxReplayTDefinition i)⟩

set_option maxRecDepth 100000 in
/-- Every specified source equation holds in the actual original C431/R presentation. -/
theorem y431AuxReplaySourceByKind_valid (kind : Y431AuxReplaySourceKind) :
    (y431AuxReplaySourceByKind kind).Valid y431AuxReplaySymbol := by
  cases kind with
  | square g =>
    change y431AuxReplayWordValue
      [(y431AuxReplayGeneratorSymbol g, true), (y431AuxReplayGeneratorSymbol g, true)] =
        y431AuxReplayWordValue []
    simpa only [y431AuxReplayWordValue_two, y431AuxReplayGeneratorSymbol_value,
      y431AuxReplayWordValue_nil] using y431AuxGenerator_square g
  | relator r =>
    change y431AuxReplayWordValue
      ((y431AuxRelatorWord r).map fun i => (y431AuxReplayGeneratorSymbol i, true)) =
        y431AuxReplayWordValue []
    rw [y431AuxReplayWordValue_positive, y431AuxReplayWordValue_nil]
    exact y431AuxRelatorWord_valid r
  | H i =>
    change y431AuxReplayWordValue [(y431AuxReplayHSymbol i, true)] =
      y431AuxReplayWordValue (y431AuxReplayHRhsWord (y431AuxReplayHRule i))
    rw [y431AuxReplayWordValue_singleton, y431AuxReplayHSymbol_value,
      y431AuxReplayHRhsWord_value]
    exact y431AuxReplayHRule_valid i
  | T i =>
    change y431AuxReplayWordValue [(y431AuxReplayTSymbol i, true)] =
      y431AuxReplayWordValue (y431AuxReplayTRhsWord (y431AuxReplayTDefinition i))
    rw [y431AuxReplayWordValue_singleton, y431AuxReplayTSymbol_value,
      y431AuxReplayTRhsWord_value]
    exact y431AuxReplayTDefinition_valid i

/-- Number the exact proved source equations in the chronological trace's declared source order. -/
def y431AuxReplaySourceFamily (i : Fin 856) : Y322WordEquation (Fin 810) :=
  y431AuxReplaySourceByKind (y431AuxReplaySourceKind i)

/-- Every numbered source holds in the original group without any replay hypothesis. -/
theorem y431AuxReplaySourceFamily_valid (i : Fin 856) :
    (y431AuxReplaySourceFamily i).Valid y431AuxReplaySymbol :=
  y431AuxReplaySourceByKind_valid (y431AuxReplaySourceKind i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
