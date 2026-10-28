/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Independent actual-source families for the finite C422 right-coset certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetSymbols
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Relators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCosetRelation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422C322

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Source equations are actual acyclic path definitions, proved squares, or proved relators. -/
inductive Y422CosetSourceKind
  | path (i : Fin 9033)
  | square (g : Fin 9)
  | relator (r : Fin 38)

/-- An exact literal equation constructed from an independently valid original-source family. -/
def y422CosetSourceEquation : Y422CosetSourceKind → Y322WordEquation (Fin 9042)
  | .path i =>
      if hi : i = 0 then ⟨[], []⟩
      else
        let previous : Fin 9033 :=
          ⟨(y422TPathData i).1, (y422TPathData_prior i hi).trans i.isLt⟩
        ⟨y422CosetPathWord i, y422CosetPathWord previous ++
          [(y422CosetGeneratorLetter (y422TPathData i).2, true)]⟩
  | .square g =>
      ⟨[g, g].map (fun i => (y422CosetGeneratorLetter i, true)), []⟩
  | .relator r =>
      ⟨(y422RelatorWord r).map (fun i => (y422CosetGeneratorLetter i, true)), []⟩

/-- Every source-family equation is proved in the actual original C422/S/Q group before replay. -/
theorem y422CosetSourceEquation_valid (kind : Y422CosetSourceKind) :
    (y422CosetSourceEquation kind).Valid y422CosetSymbol := by
  cases kind with
  | path i =>
    by_cases hi : i = 0
    · subst i
      rfl
    · dsimp only [y422CosetSourceEquation]
      rw [dite_eq_right hi]
      change y422CosetWordValue (y422CosetPathWord i) =
        y422CosetWordValue (y422CosetPathWord
          ⟨(y422TPathData i).1, (y422TPathData_prior i hi).trans i.isLt⟩ ++
          [(y422CosetGeneratorLetter (y422TPathData i).2, true)])
      rw [y422CosetPathWord_value, y422CosetWordValue_append, y422CosetPathWord_value,
        y422CosetWordValue_singleton, y422CosetGeneratorLetter_value]
      exact y422TPathValue_step i hi
  | square g =>
    change y422CosetWordValue ([g, g].map fun i => (y422CosetGeneratorLetter i, true)) =
      y422CosetWordValue []
    rw [y422CosetWordValue_positive, y422CosetWordValue_nil]
    simpa only [y422PositiveWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using
      (show (PresentedGroup.of g : Y422Presentation) * PresentedGroup.of g = 1 by
      simpa only [pow_two] using y422_generator_sq g)
  | relator r =>
    change y422CosetWordValue
      ((y422RelatorWord r).map fun i => (y422CosetGeneratorLetter i, true)) =
        y422CosetWordValue []
    rw [y422CosetWordValue_positive, y422CosetWordValue_nil]
    exact y422RelatorWord_valid r

/-- Fixed-generator coset sources use only the eight original C322 source symbols. -/
def y422CosetFixedEquation (i : Fin 8) : Y322WordEquation (Fin 9042) :=
  ⟨[(y422CosetGeneratorLetter (y422C322Letter i), true)], []⟩

/-- Every fixed-symbol source is a genuine coset fact for the actual fixed subgroup. -/
theorem y422CosetFixedEquation_valid (i : Fin 8) :
    (y422CosetFixedEquation i).CosetValid y422CosetSymbol y422C322Subgroup := by
  change y422CosetWordValue [(y422CosetGeneratorLetter (y422C322Letter i), true)] *
    (y422CosetWordValue [])⁻¹ ∈ y422C322Subgroup
  rw [y422CosetWordValue_singleton, y422CosetGeneratorLetter_value,
    y422CosetWordValue_nil, inv_one, mul_one]
  exact y422C322Letter_mem i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
