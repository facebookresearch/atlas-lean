/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.FirstOrder.Symbols

/-!
# Consumer tests for first-order symbol extraction

Boolean symbol names occur at several arities and on both sides of `L.Symbols`.
The nested term uses both binary arguments. A quantified implication combines
relations and equality, while free and bound variables contribute no symbols.
-/

set_option autoImplicit false

open Cslib.Logic.FOL (termSymbols formulaSymbols)

namespace CSLibExtTest.Logics.FirstOrder.Symbols

private def symbolLanguage : FirstOrder.Language where
  Functions _ := Bool
  Relations _ := Bool

private def constant {n : ℕ} (b : Bool) : symbolLanguage.Term (ℕ ⊕ Fin n) :=
  .func b (fun i : Fin 0 => i.elim0)

private def mixedTerm : symbolLanguage.Term (ℕ ⊕ Fin 2) :=
  .func false ![constant false, .func true ![.var (Sum.inr 1)]]

private def equality : symbolLanguage.BoundedFormula ℕ 2 :=
  .equal (constant false) (constant true)

private def relation : symbolLanguage.BoundedFormula ℕ 2 :=
  .rel false ![mixedTerm]

private def quantified : symbolLanguage.BoundedFormula ℕ 1 :=
  .all (.imp relation equality)

example : termSymbols (.var (Sum.inl 9) : symbolLanguage.Term (ℕ ⊕ Fin 2)) = ∅ := rfl

example : termSymbols (.var (Sum.inr 1) : symbolLanguage.Term (ℕ ⊕ Fin 2)) = ∅ := rfl

example : termSymbols (constant (n := 2) false) = {Sum.inl ⟨0, false⟩} := by
  apply Set.ext
  intro s
  simp [constant, termSymbols]

example : termSymbols mixedTerm =
    {Sum.inl ⟨2, false⟩, Sum.inl ⟨0, false⟩, Sum.inl ⟨1, true⟩} := by
  apply Set.ext
  intro s
  simp [mixedTerm, constant, termSymbols, Fin.exists_fin_two, Fin.exists_fin_one,
    or_assoc]

example : formulaSymbols (.falsum : symbolLanguage.BoundedFormula ℕ 2) = ∅ := rfl

example : formulaSymbols equality = {Sum.inl ⟨0, false⟩, Sum.inl ⟨0, true⟩} := by
  apply Set.ext
  intro s
  simp [equality, constant, formulaSymbols, termSymbols, or_comm]

example : formulaSymbols relation =
    {Sum.inr ⟨1, false⟩, Sum.inl ⟨2, false⟩, Sum.inl ⟨0, false⟩,
      Sum.inl ⟨1, true⟩} := by
  apply Set.ext
  intro s
  simp [relation, mixedTerm, constant, formulaSymbols, termSymbols,
    Fin.exists_fin_two, Fin.exists_fin_one, or_assoc]

example : formulaSymbols quantified =
    {Sum.inr ⟨1, false⟩, Sum.inl ⟨2, false⟩, Sum.inl ⟨0, false⟩,
      Sum.inl ⟨1, true⟩, Sum.inl ⟨0, true⟩} := by
  apply Set.ext
  intro s
  simp [quantified, relation, equality, mixedTerm, constant, formulaSymbols,
    termSymbols, Fin.exists_fin_two, Fin.exists_fin_one, or_assoc, or_left_comm, or_comm]

/-- A relation with the right name but the wrong arity is absent. -/
example : (Sum.inr ⟨2, false⟩ : symbolLanguage.Symbols) ∉ formulaSymbols quantified := by
  simp [quantified, relation, equality, mixedTerm, constant, formulaSymbols,
    termSymbols, Fin.exists_fin_two, Fin.exists_fin_one]
  intro h
  cases congrArg Sigma.fst h

/-- A function symbol does not also contribute a relation symbol. -/
example : (Sum.inr ⟨0, false⟩ : symbolLanguage.Symbols) ∉ formulaSymbols quantified := by
  simp [quantified, relation, equality, mixedTerm, constant, formulaSymbols,
    termSymbols, Fin.exists_fin_two, Fin.exists_fin_one]
  intro h
  cases congrArg Sigma.fst h

end CSLibExtTest.Logics.FirstOrder.Symbols
