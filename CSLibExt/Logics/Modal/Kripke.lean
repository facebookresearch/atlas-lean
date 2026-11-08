/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `85a3956f8d763f4003659b2ea871b54d9d9f711e`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

import Mathlib.Tactic

@[expose] public section

/-!
# Kripke semantics for basic modal logic

This file defines formulas, Kripke models, and satisfaction for the basic
normal modal language.  It also proves the central semantic invariance result
for bounded morphisms (also called p-morphisms).
-/

namespace Cslib
namespace Modal

universe u v w x y

/-- Formulas of basic normal modal logic over a type of atoms. -/
inductive Formula (α : Type u) : Type u where
  | atom : α → Formula α
  | bot : Formula α
  | imp : Formula α → Formula α → Formula α
  | box : Formula α → Formula α
  deriving DecidableEq, Repr

namespace Formula

variable {Atom : Type u}

/-- Negation as implication into falsity. -/
def neg (phi : Formula Atom) : Formula Atom := .imp phi .bot

/-- Possibility as the dual of necessity. -/
def dia (phi : Formula Atom) : Formula Atom := neg (.box (neg phi))

/-- Truth as the negation of falsity. -/
def top : Formula Atom := neg .bot

/-- Conjunction encoded using implication and falsity. -/
def and (phi psi : Formula Atom) : Formula Atom := neg (.imp phi (neg psi))

/-- Disjunction encoded using implication and falsity. -/
def or (phi psi : Formula Atom) : Formula Atom := .imp (neg phi) psi

/-- The distribution axiom for normal modal logic. -/
def axiomK (phi psi : Formula Atom) : Formula Atom :=
  .imp (.box (.imp phi psi)) (.imp (.box phi) (.box psi))

/-- The reflexivity axiom. -/
def axiomT (phi : Formula Atom) : Formula Atom := .imp (.box phi) phi

/-- The transitivity axiom. -/
def axiomFour (phi : Formula Atom) : Formula Atom := .imp (.box phi) (.box (.box phi))

/-- The seriality axiom. -/
def axiomD (phi : Formula Atom) : Formula Atom := .imp (.box phi) (dia phi)

/-- The symmetry axiom. -/
def axiomB (phi : Formula Atom) : Formula Atom := .imp phi (.box (dia phi))

/-- The euclidean axiom 5: `◇φ → □◇φ`. -/
def axiomFive (phi : Formula Atom) : Formula Atom := .imp (dia phi) (.box (dia phi))

end Formula

/-- A Kripke model consists of a nonempty collection of worlds, an accessibility relation,
and an atom valuation. -/
structure KripkeModel (World : Type u) (Atom : Type v) where
  /-- There is at least one world. -/
  nonempty_world : Nonempty World
  /-- The accessibility relation. -/
  rel : World → World → Prop
  /-- The atoms true at each world. -/
  valuation : World → Atom → Prop

namespace KripkeModel

variable {World : Type u} {Atom : Type v}

/-- Satisfaction of a modal formula at a world. -/
def Satisfies (model : KripkeModel World Atom) (world : World) : Formula Atom → Prop
  | .atom atom => model.valuation world atom
  | .bot => False
  | .imp phi psi => Satisfies model world phi → Satisfies model world psi
  | .box phi => ∀ next, model.rel world next → Satisfies model next phi

/-- A formula is globally valid in a model when it holds at every world. -/
def Valid (model : KripkeModel World Atom) (phi : Formula Atom) : Prop :=
  ∀ world, model.Satisfies world phi

@[simp] theorem satisfies_atom (model : KripkeModel World Atom) (world : World) (atom : Atom) :
    model.Satisfies world (.atom atom) ↔ model.valuation world atom := Iff.rfl

@[simp] theorem not_satisfies_bot (model : KripkeModel World Atom) (world : World) :
    ¬model.Satisfies world .bot := id

/-- Falsity is not globally valid: every Kripke model has at least one world. -/
@[simp] theorem not_valid_bot (model : KripkeModel World Atom) :
    ¬model.Valid (.bot : Formula Atom) := by
  obtain ⟨world⟩ := model.nonempty_world
  intro hValid
  exact model.not_satisfies_bot world (hValid world)

@[simp] theorem satisfies_imp (model : KripkeModel World Atom) (world : World)
    (phi psi : Formula Atom) :
    model.Satisfies world (.imp phi psi) ↔
      (model.Satisfies world phi → model.Satisfies world psi) := Iff.rfl

@[simp] theorem satisfies_box (model : KripkeModel World Atom) (world : World)
    (phi : Formula Atom) :
    model.Satisfies world (.box phi) ↔
      ∀ next, model.rel world next → model.Satisfies next phi := Iff.rfl

@[simp] theorem satisfies_neg (model : KripkeModel World Atom) (world : World)
    (phi : Formula Atom) :
    model.Satisfies world phi.neg ↔ ¬model.Satisfies world phi := by
  rfl

@[simp] theorem satisfies_top (model : KripkeModel World Atom) (world : World) :
    model.Satisfies world (Formula.top : Formula Atom) := by
  simp [Formula.top]

@[simp] theorem satisfies_and (model : KripkeModel World Atom) (world : World)
    (phi psi : Formula Atom) :
    model.Satisfies world (phi.and psi) ↔
      model.Satisfies world phi ∧ model.Satisfies world psi := by
  simp only [Formula.and, Formula.neg, Satisfies]
  constructor
  · intro h
    have hPhi : model.Satisfies world phi := Classical.byContradiction fun hNotPhi =>
      h fun hPhi => False.elim (hNotPhi hPhi)
    have hPsi : model.Satisfies world psi := Classical.byContradiction fun hNotPsi =>
      h fun _ => hNotPsi
    exact ⟨hPhi, hPsi⟩
  · rintro ⟨hPhi, hPsi⟩ hImp
    exact hImp hPhi hPsi

@[simp] theorem satisfies_or (model : KripkeModel World Atom) (world : World)
    (phi psi : Formula Atom) :
    model.Satisfies world (phi.or psi) ↔
      model.Satisfies world phi ∨ model.Satisfies world psi := by
  simp only [Formula.or, Formula.neg, Satisfies]
  constructor
  · intro h
    exact Classical.byCases (fun hPhi => Or.inl hPhi) (fun hNotPhi => Or.inr (h hNotPhi))
  · rintro (hPhi | hPsi) hNotPhi
    · exact False.elim (hNotPhi hPhi)
    · exact hPsi

/-- Possibility means satisfaction at some accessible world. -/
theorem satisfies_dia (model : KripkeModel World Atom) (world : World)
    (phi : Formula Atom) :
    model.Satisfies world phi.dia ↔
      ∃ next, model.rel world next ∧ model.Satisfies next phi := by
  simp only [Formula.dia, Formula.neg, Satisfies]
  constructor
  · intro h
    exact Classical.byContradiction fun noWitness =>
      h fun next hNext hPhi => noWitness ⟨next, hNext, hPhi⟩
  · rintro ⟨next, hNext, hPhi⟩ h
    exact h next hNext hPhi

/-- The K axiom is valid on every Kripke model. -/
theorem valid_axiomK (model : KripkeModel World Atom) (phi psi : Formula Atom) :
    model.Valid (Formula.axiomK phi psi) := by
  intro world hImp hPhi next hNext
  exact hImp next hNext (hPhi next hNext)

/-- The T axiom is valid on reflexive frames. -/
theorem valid_axiomT (model : KripkeModel World Atom)
    (reflexive : ∀ world, model.rel world world) (phi : Formula Atom) :
    model.Valid (Formula.axiomT phi) := by
  intro world hBox
  exact hBox world (reflexive world)

/-- The 4 axiom is valid on transitive frames. -/
theorem valid_axiomFour (model : KripkeModel World Atom)
    (transitive : ∀ {first second third},
      model.rel first second → model.rel second third → model.rel first third)
    (phi : Formula Atom) : model.Valid (Formula.axiomFour phi) := by
  intro world hBox next hNext after hAfter
  exact hBox after (transitive hNext hAfter)

/-- The D axiom is valid on serial frames. -/
theorem valid_axiomD (model : KripkeModel World Atom)
    (serial : ∀ world, ∃ next, model.rel world next) (phi : Formula Atom) :
    model.Valid (Formula.axiomD phi) := by
  intro world hBox
  rw [satisfies_dia]
  obtain ⟨next, hNext⟩ := serial world
  exact ⟨next, hNext, hBox next hNext⟩

/-- The B axiom is valid on symmetric frames. -/
theorem valid_axiomB (model : KripkeModel World Atom)
    (symmetric : ∀ {first second}, model.rel first second → model.rel second first)
    (phi : Formula Atom) : model.Valid (Formula.axiomB phi) := by
  intro world hPhi next hNext
  rw [satisfies_dia]
  exact ⟨world, symmetric hNext, hPhi⟩

/-- The 5 axiom is valid on euclidean frames. -/
theorem valid_axiomFive (model : KripkeModel World Atom)
    (euclidean : ∀ {first second third}, model.rel first second → model.rel first third →
      model.rel second third)
    (phi : Formula Atom) : model.Valid (Formula.axiomFive phi) := by
  intro world hDia next hNext
  rw [satisfies_dia] at hDia ⊢
  obtain ⟨other, hOther, hPhi⟩ := hDia
  exact ⟨other, euclidean hNext hOther, hPhi⟩

end KripkeModel

variable {Atom : Type u} {W : Type v} {V : Type w} {U : Type x} {X : Type y}

/--
A bounded morphism preserves atoms and has both the forward and backward
conditions on accessible worlds.
-/
structure BoundedMorphism (source : KripkeModel W Atom) (target : KripkeModel V Atom) where
  /-- The underlying map on worlds. -/
  toFun : W → V
  atom_iff : ∀ world atom,
    source.valuation world atom ↔ target.valuation (toFun world) atom
  forth : ∀ {world next}, source.rel world next → target.rel (toFun world) (toFun next)
  back : ∀ {world imageNext}, target.rel (toFun world) imageNext →
    ∃ next, source.rel world next ∧ toFun next = imageNext

namespace BoundedMorphism

variable {source : KripkeModel W Atom} {middle : KripkeModel V Atom}
  {target : KripkeModel U Atom}

instance : CoeFun (BoundedMorphism source middle) (fun _ => W → V) :=
  ⟨BoundedMorphism.toFun⟩

/-- Bounded morphisms are equal when their underlying world maps are equal. -/
@[ext]
theorem ext (first second : BoundedMorphism source middle)
    (maps_eq : ∀ world, first world = second world) : first = second := by
  cases first with
  | mk firstMap firstAtom firstForth firstBack =>
    cases second with
    | mk secondMap secondAtom secondForth secondBack =>
      have map_eq : firstMap = secondMap := funext maps_eq
      cases map_eq
      rfl

/-- The identity map is a bounded morphism. -/
def id (model : KripkeModel W Atom) : BoundedMorphism model model where
  toFun := _root_.id
  atom_iff := by simp
  forth := fun h => h
  back := by
    intro world next h
    exact ⟨next, h, rfl⟩

@[simp] theorem id_apply (model : KripkeModel W Atom) (world : W) :
    id model world = world := rfl

/-- Bounded morphisms compose. -/
def comp (second : BoundedMorphism middle target)
    (first : BoundedMorphism source middle) : BoundedMorphism source target where
  toFun := second ∘ first
  atom_iff := by
    intro world atom
    exact (first.atom_iff world atom).trans (second.atom_iff (first world) atom)
  forth := fun h => second.forth (first.forth h)
  back := by
    intro world imageNext h
    obtain ⟨middleNext, hMiddle, rfl⟩ := second.back h
    obtain ⟨sourceNext, hSource, rfl⟩ := first.back hMiddle
    exact ⟨sourceNext, hSource, rfl⟩

@[simp] theorem comp_apply (second : BoundedMorphism middle target)
    (first : BoundedMorphism source middle) (world : W) :
    second.comp first world = second (first world) := rfl

@[simp] theorem id_comp (morphism : BoundedMorphism source middle) :
    (id middle).comp morphism = morphism := by
  ext world
  rfl

@[simp] theorem comp_id (morphism : BoundedMorphism source middle) :
    morphism.comp (id source) = morphism := by
  ext world
  rfl

theorem comp_assoc {final : KripkeModel X Atom}
    (third : BoundedMorphism target final)
    (second : BoundedMorphism middle target)
    (first : BoundedMorphism source middle) :
    third.comp (second.comp first) = (third.comp second).comp first := by
  ext world
  rfl

/-- Satisfaction is invariant under bounded morphisms. -/
theorem satisfies_iff (morphism : BoundedMorphism source middle)
    (phi : Formula Atom) (world : W) :
    source.Satisfies world phi ↔ middle.Satisfies (morphism world) phi := by
  induction phi generalizing world with
  | atom atom => exact morphism.atom_iff world atom
  | bot => rfl
  | imp phi psi ihPhi ihPsi =>
      simp only [KripkeModel.Satisfies]
      constructor
      · intro h hSource
        exact (ihPsi world).mp (h ((ihPhi world).mpr hSource))
      · intro h hTarget
        exact (ihPsi world).mpr (h ((ihPhi world).mp hTarget))
  | box phi ih =>
      constructor
      · intro h imageNext hImage
        obtain ⟨next, hNext, rfl⟩ := morphism.back hImage
        exact (ih next).mp (h next hNext)
      · intro h next hNext
        exact (ih next).mpr (h (morphism next) (morphism.forth hNext))

/-- A surjective bounded morphism reflects and preserves global validity. -/
theorem valid_iff_of_surjective (morphism : BoundedMorphism source middle)
    (surjective : Function.Surjective morphism) (phi : Formula Atom) :
    source.Valid phi ↔ middle.Valid phi := by
  constructor
  · intro h imageWorld
    obtain ⟨world, rfl⟩ := surjective imageWorld
    exact (morphism.satisfies_iff phi world).mp (h world)
  · intro h world
    exact (morphism.satisfies_iff phi world).mpr (h (morphism world))

end BoundedMorphism

end Modal
end Cslib
