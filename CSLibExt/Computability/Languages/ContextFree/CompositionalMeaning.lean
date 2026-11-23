/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.CompositionalFragment
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Denotational

/-!
# Meanings of the two fragment parses

The lexical environment interprets `everybody` and `someone` as the
person-restricted universal and existential quantifiers and
`admires` as the given relation. The surface parse means
every person admires some person; the inverse parse means some
person is admired by every person; every valid sentence tree means
exactly the formula of its own parse.
-/

@[expose] public section

namespace Cslib.Language.CompositionalFragment

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

/-- Base interpretation of the fragment: entities `e` by `D`, truth values
`t` by `Prop`. -/
def ID (D : Type) : Bool → Type := fun b => if b then Prop else D

/-- The environment for the empty context. -/
def envNil (I : Bool → Type) : Env I [] := fun x => nomatch x

/-- `everybody` denotes the person-restricted universal quantifier. -/
def everybodyDen (D : Type) (person : D → Prop) : Ty.denote (ID D) QTy :=
  fun P => ∀ x : D, person x → P x

/-- `someone` denotes the person-restricted existential quantifier. -/
def someoneDen (D : Type) (person : D → Prop) : Ty.denote (ID D) QTy :=
  fun P => ∃ y : D, person y ∧ P y

/-- `admires` denotes the relation `admire`. -/
def admiresDen (D : Type) (admire : D → D → Prop) : Ty.denote (ID D) RTy :=
  fun x y => admire x y

/-- The total lexical environment for `LexCtx = [Q, Q, R]`: slot 0 is
`everybody`, slot 1 is `someone`, slot 2 is `admires`. -/
def lexEnv (D : Type) (person : D → Prop) (admire : D → D → Prop) :
    Env (ID D) LexCtx :=
  Env.cons (everybodyDen D person)
    (Env.cons (someoneDen D person)
      (Env.cons (admiresDen D admire) (envNil (ID D))))

/-- The meaning of a valid `S`-rooted tree: the existing interpreter
`Tm.denote` applied to the compiled term in the lexical environment. -/
def meaning (D : Type) (person : D → Prop) (admire : D → D → Prop)
    (tr : PDerivTree Cat Token) (h : IsValidTree Token g tr)
    (hr : tr.rootOf = catS) : Prop :=
  Tm.denote (ID D) (compileAt catS tr hr h) (lexEnv D person admire)

/-- The surface parse means `∀ x, person x → ∃ y, person y ∧ admire x y`, the
inverse parse means `∃ y, person y ∧ ∀ x, person x → admire x y`, and these
two formulas are the only meanings of valid `S`-rooted trees, each attached
to its own parse. -/
theorem surface_inverse_meanings (D : Type) (person : D → Prop)
    (admire : D → D → Prop) :
    (meaning D person admire surfaceTree surfaceTree_valid rfl ↔
      ∀ x : D, person x → ∃ y : D, person y ∧ admire x y) ∧
    (meaning D person admire inverseTree inverseTree_valid rfl ↔
      ∃ y : D, person y ∧ ∀ x : D, person x → admire x y) ∧
    (∀ (tr : PDerivTree Cat Token) (h : IsValidTree Token g tr)
        (hr : tr.rootOf = catS),
      meaning D person admire tr h hr ↔
        (tr = surfaceTree ∧ ∀ x : D, person x → ∃ y : D, person y ∧ admire x y) ∨
        (tr = inverseTree ∧ ∃ y : D, person y ∧ ∀ x : D, person x → admire x y)) := by
  have hLeafSubj : ∀ (h : IsValidTree Token g (PDerivTree.leaf catSubj everybodyTok)),
      compileAt catSubj (PDerivTree.leaf catSubj everybodyTok) rfl h =
        everybodyTm := by
    intro h
    unfold compileAt
    rw [compile_leaf_everybody]
  have hLeafObj : ∀ (h : IsValidTree Token g (PDerivTree.leaf catObj someoneTok)),
      compileAt catObj (PDerivTree.leaf catObj someoneTok) rfl h =
        someoneTm := by
    intro h
    unfold compileAt
    rw [compile_leaf_someone]
  have hLeafTV : ∀ (h : IsValidTree Token g (PDerivTree.leaf catTV admiresTok)),
      compileAt catTV (PDerivTree.leaf catTV admiresTok) rfl h =
        admiresTm := by
    intro h
    unfold compileAt
    rw [compile_leaf_admires]
  have hVL : IsValidTree Token g (PDerivTree.leaf catSubj everybodyTok) := by
    simp only [IsValidTree]
    decide
  have hVO : IsValidTree Token g (PDerivTree.leaf catObj someoneTok) := by
    simp only [IsValidTree]
    decide
  have hVT : IsValidTree Token g (PDerivTree.leaf catTV admiresTok) := by
    simp only [IsValidTree]
    decide
  have hVR : IsValidTree Token g (PDerivTree.node catVP catTV catObj
      (PDerivTree.leaf catTV admiresTok)
      (PDerivTree.leaf catObj someoneTok)) := by
    simp only [IsValidTree]
    refine ⟨?_, rfl, rfl, hVT, hVO⟩
    decide
  have hVP : compileAt catVP (PDerivTree.node catVP catTV catObj
        (PDerivTree.leaf catTV admiresTok)
        (PDerivTree.leaf catObj someoneTok)) rfl hVR =
      actVP admiresTm someoneTm := by
    have hEq := compile_node_vp_apply_object
      (PDerivTree.leaf catTV admiresTok)
      (PDerivTree.leaf catObj someoneTok)
      hVT hVO rfl rfl hVR
    unfold compileAt
    rw [hEq, hLeafTV hVT, hLeafObj hVO]
  have hSP : IsValidTree Token g (PDerivTree.node catSP catSubj catTV
      (PDerivTree.leaf catSubj everybodyTok)
      (PDerivTree.leaf catTV admiresTok)) := by
    simp only [IsValidTree]
    refine ⟨?_, rfl, rfl, hVL, hVT⟩
    decide
  have hSPc : compileAt catSP (PDerivTree.node catSP catSubj catTV
        (PDerivTree.leaf catSubj everybodyTok)
        (PDerivTree.leaf catTV admiresTok)) rfl hSP =
      actSP everybodyTm admiresTm := by
    have hEq := compile_node_sp_apply_subject
      (PDerivTree.leaf catSubj everybodyTok)
      (PDerivTree.leaf catTV admiresTok)
      hVL hVT rfl rfl hSP
    unfold compileAt
    rw [hEq, hLeafSubj hVL, hLeafTV hVT]
  have hSurf : compileAt catS surfaceTree rfl surfaceTree_valid =
      actS1 everybodyTm (actVP admiresTm someoneTm) := by
    have hEq := compile_node_s_subject_wide
      (PDerivTree.leaf catSubj everybodyTok)
      (PDerivTree.node catVP catTV catObj
        (PDerivTree.leaf catTV admiresTok)
        (PDerivTree.leaf catObj someoneTok))
      hVL hVR rfl rfl surfaceTree_valid
    unfold surfaceTree compileAt
    rw [hEq, hLeafSubj hVL, hVP]
  have hInv : compileAt catS inverseTree rfl inverseTree_valid =
      actSObj (actSP everybodyTm admiresTm) someoneTm := by
    have hEq := compile_node_s_object_wide
      (PDerivTree.node catSP catSubj catTV
        (PDerivTree.leaf catSubj everybodyTok)
        (PDerivTree.leaf catTV admiresTok))
      (PDerivTree.leaf catObj someoneTok)
      hSP hVO rfl rfl inverseTree_valid
    unfold inverseTree compileAt
    rw [hEq, hSPc, hLeafObj hVO]
  have hSurfM : meaning D person admire surfaceTree surfaceTree_valid rfl ↔
      ∀ x : D, person x → ∃ y : D, person y ∧ admire x y := by
    unfold meaning
    rw [hSurf]
    rfl
  have hInvM : meaning D person admire inverseTree inverseTree_valid rfl ↔
      ∃ y : D, person y ∧ ∀ x : D, person x → admire x y := by
    unfold meaning
    rw [hInv]
    rfl
  refine ⟨hSurfM, hInvM, ?_⟩
  intro tr h hr
  have hClass : tr = surfaceTree ∨ tr = inverseTree :=
    (valid_sentence_trees tr).mp ⟨h, hr⟩
  have hNe : surfaceTree ≠ inverseTree := by decide
  obtain rfl | rfl := hClass
  · show meaning D person admire surfaceTree surfaceTree_valid rfl ↔ _
    rw [hSurfM]
    simp [hNe]
  · show meaning D person admire inverseTree inverseTree_valid rfl ↔ _
    rw [hInvM]
    simp [hNe.symm]

end Cslib.Language.CompositionalFragment

