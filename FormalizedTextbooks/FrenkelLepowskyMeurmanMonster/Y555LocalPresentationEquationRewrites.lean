/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Checked substitution of already proved equations in compressed signed generator words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationAuxiliary
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A literal equation between signed words, before any interpretation in a group. -/
structure Y322WordEquation (alphabet : Type*) where
  /-- The literal left-hand signed word. -/
  left : List (alphabet × Bool)
  /-- The literal right-hand signed word. -/
  right : List (alphabet × Bool)

/-- Interpret a signed word by the actual supplied generator values. -/
def y322EquationWordValue {alphabet G : Type*} [Group G] (values : alphabet → G)
    (word : List (alphabet × Bool)) : G :=
  FreeGroup.lift values (FreeGroup.mk word)

/-- Validity of a literal equation at the supplied actual generator values. -/
def Y322WordEquation.Valid {alphabet G : Type*} [Group G] (values : alphabet → G)
    (equation : Y322WordEquation alphabet) : Prop :=
  y322EquationWordValue values equation.left = y322EquationWordValue values equation.right

/-- Free cancellation changes no interpreted group element. -/
theorem y322EquationWordValue_reduce {alphabet G : Type*} [DecidableEq alphabet] [Group G]
    (values : alphabet → G) (word : List (alphabet × Bool)) :
    y322EquationWordValue values (FreeGroup.reduce word) =
      y322EquationWordValue values word := by
  unfold y322EquationWordValue
  rw [FreeGroup.reduce.self]

/-- Equal free reductions imply equal values in every actual group interpretation. -/
theorem y322EquationWordValue_eq_of_reduce {alphabet G : Type*}
    [DecidableEq alphabet] [Group G] (values : alphabet → G)
    (left right : List (alphabet × Bool)) (h : FreeGroup.reduce left = FreeGroup.reduce right) :
    y322EquationWordValue values left = y322EquationWordValue values right := by
  rw [← y322EquationWordValue_reduce values left,
    ← y322EquationWordValue_reduce values right, h]

/-- Free changes to either literal side preserve a previously proved equation. -/
theorem y322WordEquation_transport {alphabet G : Type*} [DecidableEq alphabet] [Group G]
    (values : alphabet → G) (source target : Y322WordEquation alphabet)
    (h : source.Valid values) (hl : FreeGroup.reduce target.left = FreeGroup.reduce source.left)
    (hr : FreeGroup.reduce target.right = FreeGroup.reduce source.right) : target.Valid values :=
  (y322EquationWordValue_eq_of_reduce values _ _ hl).trans
    (h.trans (y322EquationWordValue_eq_of_reduce values _ _ hr).symm)

/-- Concatenating literal signed words multiplies their interpreted values. -/
theorem y322EquationWordValue_append {alphabet G : Type*} [Group G]
    (values : alphabet → G) (left right : List (alphabet × Bool)) :
    y322EquationWordValue values (left ++ right) =
      y322EquationWordValue values left * y322EquationWordValue values right := by
  unfold y322EquationWordValue
  rw [← FreeGroup.mul_mk, map_mul]

/-- Reversing a signed word and reversing its signs takes its interpreted inverse. -/
theorem y322EquationWordValue_invRev {alphabet G : Type*} [Group G]
    (values : alphabet → G) (word : List (alphabet × Bool)) :
    y322EquationWordValue values (FreeGroup.invRev word) =
      (y322EquationWordValue values word)⁻¹ := by
  unfold y322EquationWordValue
  rw [← FreeGroup.inv_mk, map_inv]

/-- Orient a proved equation, optionally taking inverses of both sides. -/
def y322EquationOrient {alphabet : Type*} (equation : Y322WordEquation alphabet)
    (backward inverted : Bool) : Y322WordEquation alphabet :=
  let directed := if backward then ⟨equation.right, equation.left⟩ else equation
  if inverted then ⟨FreeGroup.invRev directed.left, FreeGroup.invRev directed.right⟩
  else directed

/-- Every selected orientation of a valid word equation is valid. -/
theorem y322EquationOrient_valid {alphabet G : Type*} [Group G] (values : alphabet → G)
    (equation : Y322WordEquation alphabet) (h : equation.Valid values)
    (backward inverted : Bool) : (y322EquationOrient equation backward inverted).Valid values := by
  cases backward <;> cases inverted <;>
    simp only [y322EquationOrient, Bool.false_eq_true, ↓reduceIte,
      Y322WordEquation.Valid, y322EquationWordValue_invRev] at *
  · exact h
  · exact congrArg Inv.inv h
  · exact h.symm
  · exact congrArg Inv.inv h.symm

/-- Insert the two sides of an equation into the same literal word context. -/
def y322EquationContext {alphabet : Type*} (equation : Y322WordEquation alphabet)
    (before after : List (alphabet × Bool)) : Y322WordEquation alphabet :=
  ⟨before ++ equation.left ++ after, before ++ equation.right ++ after⟩

/-- Multiplying both sides by the same word context preserves the actual equation. -/
theorem y322EquationContext_valid {alphabet G : Type*} [Group G] (values : alphabet → G)
    (equation : Y322WordEquation alphabet) (h : equation.Valid values)
    (before after : List (alphabet × Bool)) :
    (y322EquationContext equation before after).Valid values := by
  unfold Y322WordEquation.Valid y322EquationContext
  simp only [y322EquationWordValue_append]
  rw [h]

/-- Replace exactly the indicated occurrence of a proved equation and freely cancel the result. -/
def y322EquationSubstitute {alphabet : Type*} [DecidableEq alphabet]
    (equation : Y322WordEquation alphabet) (position : ℕ)
    (word : List (alphabet × Bool)) : Option (List (alphabet × Bool)) :=
  if (word.drop position).take equation.left.length = equation.left then
    some (FreeGroup.reduce (word.take position ++ equation.right ++
      (word.drop position).drop equation.left.length))
  else none

/-- Successful literal substitution preserves the actual interpreted group value. -/
theorem y322EquationSubstitute_valid {alphabet G : Type*} [DecidableEq alphabet] [Group G]
    (values : alphabet → G) (equation : Y322WordEquation alphabet)
    (he : equation.Valid values) (position : ℕ) (word result : List (alphabet × Bool))
    (h : y322EquationSubstitute equation position word = some result) :
    y322EquationWordValue values word = y322EquationWordValue values result := by
  unfold y322EquationSubstitute at h
  split at h <;> try contradiction
  rename_i hm
  cases h
  rw [y322EquationWordValue_reduce]
  have hw : word = word.take position ++ equation.left ++
      (word.drop position).drop equation.left.length := by
    calc
      word = word.take position ++ word.drop position :=
        (List.take_append_drop position word).symm
      _ = word.take position ++ ((word.drop position).take equation.left.length ++
          (word.drop position).drop equation.left.length) :=
        congrArg (fun tail => word.take position ++ tail)
          (List.take_append_drop equation.left.length (word.drop position)).symm
      _ = _ := by rw [hm, List.append_assoc]
  conv_lhs => rw [hw]
  simp only [y322EquationWordValue_append]
  rw [he]

/-- One substitution refers only to an already proved equation. -/
structure Y322EquationMove (earlier : ℕ) where
  /-- The strictly earlier equation used in this substitution. -/
  reference : Fin earlier
  /-- Whether to exchange the equation sides. -/
  backward : Bool
  /-- Whether to take the inverse of both sides. -/
  inverted : Bool
  /-- The zero-based start of the literal replaced word. -/
  position : ℕ

/-- Execute literal equation substitutions in a signed word. -/
def y322EquationRun {alphabet : Type*} [DecidableEq alphabet] {earlier : ℕ}
    (prior : Fin earlier → Y322WordEquation alphabet) :
    List (Y322EquationMove earlier) → List (alphabet × Bool) → Option (List (alphabet × Bool))
  | [], word => some (FreeGroup.reduce word)
  | move :: rest, word =>
      (y322EquationSubstitute
        (y322EquationOrient (prior move.reference) move.backward move.inverted)
        move.position word).bind (y322EquationRun prior rest)

/-- A successful finite run follows solely from its already proved equations. -/
theorem y322EquationRun_valid {alphabet G : Type*} [DecidableEq alphabet] [Group G]
    {earlier : ℕ} (values : alphabet → G) (prior : Fin earlier → Y322WordEquation alphabet)
    (hp : ∀ i, (prior i).Valid values) (moves : List (Y322EquationMove earlier))
    (word result : List (alphabet × Bool)) (h : y322EquationRun prior moves word = some result) :
    y322EquationWordValue values word = y322EquationWordValue values result := by
  induction moves generalizing word with
  | nil =>
    cases h
    exact (y322EquationWordValue_reduce values word).symm
  | cons move rest ih =>
    simp only [y322EquationRun] at h
    cases hs : y322EquationSubstitute
        (y322EquationOrient (prior move.reference) move.backward move.inverted)
        move.position word with
    | none => simp only [hs, Option.bind_none] at h; contradiction
    | some middle =>
      simp only [hs, Option.bind_some] at h
      exact (y322EquationSubstitute_valid values _
        (y322EquationOrient_valid values _ (hp move.reference) _ _) _ word middle hs).trans
          (ih middle h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
