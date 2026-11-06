/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Independent actual-source families for the finite C522 right-coset certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSymbols
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522AuxRelators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCosetRelation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Source equations are actual acyclic path definitions, proved squares, or proved relators. -/
inductive Y522CosetSourceKind
  | path (i : Fin 1795)
  | square (g : Fin 11)
  | relator (r : Fin 58)

/-- An exact literal equation constructed from an independently valid original-source family. -/
def y522CosetSourceEquation : Y522CosetSourceKind → Y322WordEquation (Fin 1806)
  | .path i =>
      if hi : i = 0 then ⟨[], []⟩
      else
        let previous : Fin 1795 :=
          ⟨(y522TPathData i).1, (y522TPathData_prior i hi).trans i.isLt⟩
        ⟨y522CosetPathWord i, y522CosetPathWord previous ++
          [(y522CosetGeneratorLetter (y522TPathData i).2, true)]⟩
  | .square g =>
      ⟨[g, g].map (fun i => (y522CosetGeneratorLetter i, true)), []⟩
  | .relator r =>
      ⟨(y522AuxRelatorWord r).map (fun i => (y522CosetGeneratorLetter i, true)), []⟩

/-- Every source-family equation is proved in the actual original Y555 group before replay. -/
theorem y522CosetSourceEquation_valid (kind : Y522CosetSourceKind) :
    (y522CosetSourceEquation kind).Valid y522CosetSymbol := by
  cases kind with
  | path i =>
    by_cases hi : i = 0
    · subst i
      rfl
    · dsimp only [y522CosetSourceEquation]
      rw [dite_eq_right hi]
      change y522CosetWordValue (y522CosetPathWord i) =
        y522CosetWordValue (y522CosetPathWord
          ⟨(y522TPathData i).1, (y522TPathData_prior i hi).trans i.isLt⟩ ++
          [(y522CosetGeneratorLetter (y522TPathData i).2, true)])
      rw [y522CosetPathWord_value, y522CosetWordValue_append, y522CosetPathWord_value,
        y522CosetWordValue_singleton, y522CosetGeneratorLetter_value]
      exact y522TPathValue_step i hi
  | square g =>
    change y522CosetWordValue ([g, g].map fun i => (y522CosetGeneratorLetter i, true)) =
      y522CosetWordValue []
    rw [y522CosetWordValue_positive, y522CosetWordValue_nil]
    simpa only [y522AuxPositiveWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using y522AuxGenerator_square g
  | relator r =>
    change y522CosetWordValue
      ((y522AuxRelatorWord r).map fun i => (y522CosetGeneratorLetter i, true)) =
        y522CosetWordValue []
    rw [y522CosetWordValue_positive, y522CosetWordValue_nil]
    exact y522AuxRelatorWord_valid r

/-- Fixed-generator coset sources use only the ten independently proved fixed symbols. -/
def y522CosetFixedEquation (i : Fin 10) : Y322WordEquation (Fin 1806) :=
  ⟨[(y522CosetGeneratorLetter (y522AuxFixedSource i), true)], []⟩

/-- Every fixed-symbol source is a genuine coset fact for the actual fixed subgroup. -/
theorem y522CosetFixedEquation_valid (i : Fin 10) :
    (y522CosetFixedEquation i).CosetValid y522CosetSymbol y522TerminalFixed := by
  change y522CosetWordValue [(y522CosetGeneratorLetter (y522AuxFixedSource i), true)] *
    (y522CosetWordValue [])⁻¹ ∈ y522TerminalFixed
  rw [y522CosetWordValue_singleton, y522CosetGeneratorLetter_value,
    y522CosetWordValue_nil, inv_one, mul_one]
  exact y522AuxFixedSource_mem i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
