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

/-- **Modal formulas.** For a type $\alpha$ of atoms, the formulas of basic modal logic over
$\alpha$ are generated as follows: every atom $p \in \alpha$ is a formula; falsity $\bot$ is a
formula; if $\varphi$ and $\psi$ are formulas then so is the implication $\varphi \to \psi$; and
if $\varphi$ is a formula then so is the necessity formula $\Box\varphi$. -/
inductive Formula (α : Type u) : Type u where
  | atom : α → Formula α
  | bot : Formula α
  | imp : Formula α → Formula α → Formula α
  | box : Formula α → Formula α
  deriving DecidableEq, Repr

namespace Formula

variable {Atom : Type u}

/-- **Negation of modal formulas.** The negation of a modal formula $\varphi$ is the formula
$\neg\varphi := \varphi \to \bot$. -/
def neg (phi : Formula Atom) : Formula Atom := .imp phi .bot

/-- **The possibility operator.** For a modal formula $\varphi$, the formula $\Diamond\varphi$
("possibly $\varphi$") is $\neg\Box\neg\varphi$, where $\neg\chi$ stands for $\chi \to \bot$. -/
def dia (phi : Formula Atom) : Formula Atom := neg (.box (neg phi))

/-- **The truth constant.** The formula $\top$ is the negation $\neg\bot$ of falsity, that is,
the implication $\bot \to \bot$. -/
def top : Formula Atom := neg .bot

/-- **Conjunction.** For modal formulas $\varphi$ and $\psi$, the conjunction $\varphi \wedge \psi$
is the formula $\neg(\varphi \to \neg\psi)$, where $\neg\chi$ stands for $\chi \to \bot$. -/
def and (phi psi : Formula Atom) : Formula Atom := neg (.imp phi (neg psi))

/-- **Disjunction of modal formulas.** The disjunction of modal formulas $\varphi$ and $\psi$ is
the formula $\varphi \lor \psi := \neg\varphi \to \psi$, where $\neg\varphi$ is
$\varphi \to \bot$. -/
def or (phi psi : Formula Atom) : Formula Atom := .imp (neg phi) psi

/-- **Axiom K.** For modal formulas $\varphi$ and $\psi$, the distribution axiom K is the formula
$\Box(\varphi \to \psi) \to (\Box\varphi \to \Box\psi)$. -/
def axiomK (phi psi : Formula Atom) : Formula Atom :=
  .imp (.box (.imp phi psi)) (.imp (.box phi) (.box psi))

/-- **Axiom T.** For a modal formula $\varphi$, the reflexivity axiom T is the formula
$\Box\varphi \to \varphi$. -/
def axiomT (phi : Formula Atom) : Formula Atom := .imp (.box phi) phi

/-- **Axiom 4.** For a modal formula $\varphi$, the transitivity axiom 4 is the formula
$\Box\varphi \to \Box\Box\varphi$. -/
def axiomFour (phi : Formula Atom) : Formula Atom := .imp (.box phi) (.box (.box phi))

/-- **Axiom D.** For a modal formula $\varphi$, the seriality axiom D is the formula
$\Box\varphi \to \Diamond\varphi$, where $\Diamond\psi$ is $\neg\Box\neg\psi$ and $\neg\chi$ stands
for $\chi \to \bot$. -/
def axiomD (phi : Formula Atom) : Formula Atom := .imp (.box phi) (dia phi)

/-- **Axiom B.** For a modal formula $\varphi$, the symmetry axiom B is the formula
$\varphi \to \Box\Diamond\varphi$, where $\Diamond\psi$ is $\neg\Box\neg\psi$ and $\neg\chi$ stands
for $\chi \to \bot$. -/
def axiomB (phi : Formula Atom) : Formula Atom := .imp phi (.box (dia phi))

/-- **Axiom 5.** For a modal formula $\varphi$, the euclidean axiom 5 is the formula
$\Diamond\varphi \to \Box\Diamond\varphi$, where $\Diamond\psi$ is $\neg\Box\neg\psi$ and $\neg\chi$
stands for $\chi \to \bot$. -/
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

/-- **Satisfaction in a Kripke model.** Let $M$ be a Kripke model with accessibility relation
$R$. Satisfaction of a modal formula at a world $w$ of $M$ is defined by recursion on the
formula: $w$ satisfies an atom $p$ if and only if the valuation of $M$ makes $p$ true at $w$;
$w$ never satisfies $\bot$; $w$ satisfies $\varphi \to \psi$ if and only if $w$ satisfies
$\psi$ whenever it satisfies $\varphi$; and $w$ satisfies $\Box\varphi$ if and only if every
world $v$ with $w \mathrel{R} v$ satisfies $\varphi$. -/
def Satisfies (model : KripkeModel World Atom) (world : World) : Formula Atom → Prop
  | .atom atom => model.valuation world atom
  | .bot => False
  | .imp phi psi => Satisfies model world phi → Satisfies model world psi
  | .box phi => ∀ next, model.rel world next → Satisfies model next phi

/-- **Global validity in a Kripke model.** A formula $\varphi$ is globally valid in a Kripke
model $M$ when $\varphi$ is satisfied at every world of $M$. -/
def Valid (model : KripkeModel World Atom) (phi : Formula Atom) : Prop :=
  ∀ world, model.Satisfies world phi

@[simp] theorem satisfies_atom (model : KripkeModel World Atom) (world : World) (atom : Atom) :
    model.Satisfies world (.atom atom) ↔ model.valuation world atom := Iff.rfl

@[simp] theorem not_satisfies_bot (model : KripkeModel World Atom) (world : World) :
    ¬model.Satisfies world .bot := id

/-- **Falsity is valid in no Kripke model.** For every Kripke model $M$, the formula $\bot$ is
not valid in $M$: since $M$ has at least one world and no world satisfies $\bot$, some world
of $M$ fails to satisfy $\bot$. -/
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

/-- **Semantics of possibility.** Let $M$ be a Kripke model with accessibility relation $R$, and
let $\Diamond\varphi$ denote the formula $\neg\Box\neg\varphi$, where $\neg\chi$ is
$\chi \to \bot$. For every world $w$ and modal formula $\varphi$, $w$ satisfies $\Diamond\varphi$
in $M$ if and only if there is a world $v$ with $w \mathrel{R} v$ such that $v$ satisfies
$\varphi$ in $M$. -/
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

/-- **Axiom T is valid on reflexive Kripke models.** Let $M$ be a Kripke model whose
accessibility relation $R$ is reflexive: $R\,w\,w$ for every world $w$. Then for every formula
$\varphi$ the T axiom $\Box\varphi \to \varphi$ is globally valid in $M$. -/
theorem valid_axiomT (model : KripkeModel World Atom)
    (reflexive : ∀ world, model.rel world world) (phi : Formula Atom) :
    model.Valid (Formula.axiomT phi) := by
  intro world hBox
  exact hBox world (reflexive world)

/-- **Axiom 4 is valid on transitive Kripke models.** Let $M$ be a Kripke model whose
accessibility relation $R$ is transitive: $R\,u\,v$ and $R\,v\,w$ imply $R\,u\,w$ for all worlds
$u, v, w$. Then for every formula $\varphi$ the 4 axiom $\Box\varphi \to \Box\Box\varphi$ is
globally valid in $M$. -/
theorem valid_axiomFour (model : KripkeModel World Atom)
    (transitive : ∀ {first second third},
      model.rel first second → model.rel second third → model.rel first third)
    (phi : Formula Atom) : model.Valid (Formula.axiomFour phi) := by
  intro world hBox next hNext after hAfter
  exact hBox after (transitive hNext hAfter)

/-- **Axiom D is valid on serial Kripke models.** Let $M$ be a Kripke model whose accessibility
relation $R$ is serial: every world $w$ has some world $v$ with $R\,w\,v$. Then for every formula
$\varphi$ the D axiom $\Box\varphi \to \Diamond\varphi$, where $\Diamond\varphi$ abbreviates
$\neg\Box\neg\varphi$, is globally valid in $M$. -/
theorem valid_axiomD (model : KripkeModel World Atom)
    (serial : ∀ world, ∃ next, model.rel world next) (phi : Formula Atom) :
    model.Valid (Formula.axiomD phi) := by
  intro world hBox
  rw [satisfies_dia]
  obtain ⟨next, hNext⟩ := serial world
  exact ⟨next, hNext, hBox next hNext⟩

/-- **Axiom B is valid on symmetric Kripke models.** Let $M$ be a Kripke model whose
accessibility relation $R$ is symmetric: $R\,u\,v$ implies $R\,v\,u$ for all worlds $u, v$.
Then for every formula $\varphi$ the B axiom $\varphi \to \Box\Diamond\varphi$, where
$\Diamond\varphi$ abbreviates $\neg\Box\neg\varphi$, is globally valid in $M$. -/
theorem valid_axiomB (model : KripkeModel World Atom)
    (symmetric : ∀ {first second}, model.rel first second → model.rel second first)
    (phi : Formula Atom) : model.Valid (Formula.axiomB phi) := by
  intro world hPhi next hNext
  rw [satisfies_dia]
  exact ⟨world, symmetric hNext, hPhi⟩

/-- **Axiom 5 is valid on euclidean Kripke models.** Let $M$ be a Kripke model whose
accessibility relation $R$ is euclidean: $R\,u\,v$ and $R\,u\,w$ imply $R\,v\,w$ for all worlds
$u, v, w$. Then for every formula $\varphi$ the 5 axiom $\Diamond\varphi \to \Box\Diamond\varphi$,
where $\Diamond\varphi$ abbreviates $\neg\Box\neg\varphi$, is globally valid in $M$. -/
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
**Bounded morphism.** Let $M$ and $N$ be Kripke models over the same atoms, with sets of worlds
$W$ and $V$ and accessibility relations $R_M$ and $R_N$. A bounded morphism from $M$ to $N$ is
a map $f : W \to V$ such that every atom holds at a world $w$ in $M$ if and only if it holds
at $f(w)$ in $N$; whenever $w \mathrel{R_M} w'$, also $f(w) \mathrel{R_N} f(w')$ (forth); and
whenever $f(w) \mathrel{R_N} v'$, there is a world $w'$ with $w \mathrel{R_M} w'$ and
$f(w') = v'$ (back).

Bounded morphisms are also called p-morphisms.
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

/-- **Extensionality for bounded morphisms.** Two bounded morphisms $f$ and $g$ between the same
Kripke models are equal if $f(w) = g(w)$ for every world $w$. -/
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

/-- **Identity bounded morphism.** For every Kripke model $M$, the identity map on the worlds of
$M$ is a bounded morphism from $M$ to itself. -/
def id (model : KripkeModel W Atom) : BoundedMorphism model model where
  toFun := _root_.id
  atom_iff := by simp
  forth := fun h => h
  back := by
    intro world next h
    exact ⟨next, h, rfl⟩

@[simp] theorem id_apply (model : KripkeModel W Atom) (world : W) :
    id model world = world := rfl

/-- **Composition of bounded morphisms.** Let $M_1$, $M_2$, $M_3$ be Kripke models over the same
atoms. If $f$ is a bounded morphism from $M_1$ to $M_2$ and $g$ is a bounded morphism from $M_2$
to $M_3$, then the composite map $g \circ f$ on worlds is a bounded morphism from $M_1$ to
$M_3$. -/
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

/-- **Invariance of modal satisfaction under bounded morphisms.** Let $f$ be a bounded morphism
from a Kripke model $M$ to a Kripke model $N$ over the same atoms. Then for every modal formula
$\varphi$ and every world $w$ of $M$, $w$ satisfies $\varphi$ in $M$ if and only if $f(w)$
satisfies $\varphi$ in $N$. -/
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

/-- **Surjective bounded morphisms preserve and reflect validity.** Let $M$ and $N$ be Kripke
models over the same atoms and let $f$ be a bounded morphism from $M$ to $N$ whose map on worlds
is surjective. Then for every formula $\varphi$, $\varphi$ is globally valid in $M$ if and only
if $\varphi$ is globally valid in $N$. -/
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
