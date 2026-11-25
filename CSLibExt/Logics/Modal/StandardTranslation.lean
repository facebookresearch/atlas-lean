/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The standard translation from modal logic to first-order logic
-/
module

public import CSLibExt.Logics.Modal.Bisimulation
public import Mathlib.ModelTheory.Semantics

/-!
# The standard translation from modal logic to first-order logic

The standard translation `ST_x(φ)` of a modal formula `φ` is a first-order
formula with one free (bound) variable `x` standing for the current world,
over `modalLanguage Atom`: a binary relation `R` for accessibility and a unary
predicate `P_a` for each atom `a`. The frame language `frameLanguage` keeps
only `R`. `kripkeStructure M` interprets the modal language in a Kripke model,
and `frameStructure rel` interprets the frame language in a bare frame.

* `standardTranslation` : the translation, parametrized by the number `n` of
  bound variables in scope and the term `t` for the current world. The box
  case introduces a fresh bound variable (the highest index) for the successor
  world; the old world term is lifted by `Fin.castAdd`, which preserves
  de Bruijn levels.
* `realize_standardTranslation` : the translation is correct: `ST` holds at a
  world iff the modal formula holds there.
* `BisimulationInvariant` : a one-variable first-order formula is
  bisimulation-invariant if bisimilar worlds agree on it. The standard
  translation of every modal formula is bisimulation-invariant
  (`bisimulationInvariant_standardTranslation`).

## References

- P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001,
  §2.3 (standard translation), §2.7 (van Benthem characterization).
- J. van Benthem, *Modal Correspondence Theory*, PhD thesis, University of Amsterdam, 1976.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Cslib.Modal

open FirstOrder FirstOrder.Language

variable {Atom : Type u}

/-- Relation symbols of the modal first-order language: accessibility `R` (binary) and a
unary predicate `P_a` for each atom `a`. -/
inductive ModalRelations (Atom : Type u) : ℕ → Type u
  /-- Accessibility, binary. -/
  | relR : ModalRelations Atom 2
  /-- The predicate for atom `a`, unary. -/
  | pred : Atom → ModalRelations Atom 1

/-- **The first-order modal language.** For a set of atoms, the first-order language of modal
logic has no function symbols; its relation symbols are a binary symbol $R$ (accessibility)
and a unary symbol $P_a$ for each atom $a$. -/
def modalLanguage (Atom : Type u) : FirstOrder.Language.{u, u} where
  Functions := fun _ => PEmpty
  Relations := ModalRelations Atom

/-- **Relation symbols of the frame language.** The relation symbols of the first-order frame
language, indexed by arity: a single binary symbol $R$ for accessibility, and no symbols of any
other arity. -/
inductive FrameRelations : ℕ → Type
  /-- Accessibility, binary. -/
  | relR : FrameRelations 2

/-- The first-order language of frames: no function symbols, one binary relation `R`. -/
def frameLanguage : FirstOrder.Language where
  Functions := fun _ => PEmpty
  Relations := FrameRelations

/-- **A Kripke model as a first-order structure.** A Kripke model $M$ with set of worlds $W$
makes $W$ a structure for the modal language: the accessibility symbol $R$ is interpreted as
the accessibility relation of $M$, and the predicate $P_a$ for an atom $a$ holds at exactly
the worlds where $a$ is true under the valuation of $M$. -/
@[instance_reducible]
def kripkeStructure {W : Type v} (M : KripkeModel W Atom) :
    (modalLanguage Atom).Structure W where
  funMap f _ := f.elim
  RelMap R ts := match R with
    | .relR => M.rel (ts 0) (ts 1)
    | .pred a => M.valuation (ts 0) a

/-- **A frame as a first-order structure.** A binary relation $r$ on a set $W$ (a bare Kripke
frame) makes $W$ a structure for the frame language, in which the accessibility symbol $R$ is
interpreted as $r$: $R(w, w')$ holds if and only if $r(w, w')$. -/
@[instance_reducible]
def frameStructure {W : Type v} (rel : W → W → Prop) : frameLanguage.Structure W where
  funMap f _ := f.elim
  RelMap R ts := match R with
    | .relR => rel (ts 0) (ts 1)

/-- **Standard translation.** For $n$ variables $x_0, \dots, x_{n-1}$ in scope and a term $t$
of the modal language for the current world, the standard translation $ST_t(\varphi)$ of a
modal formula $\varphi$ is the first-order formula over the modal language in these variables
defined by recursion on $\varphi$: $ST_t(a) = P_a(t)$ for an atom $a$; $ST_t(\bot) = \bot$;
$ST_t(\varphi \to \psi) = ST_t(\varphi) \to ST_t(\psi)$; and
$ST_t(\Box \varphi) = \forall x_n \, (R(t, x_n) \to ST_{x_n}(\varphi))$, where $x_n$ is a fresh
variable and $ST_{x_n}(\varphi)$ is taken with $n + 1$ variables in scope. -/
def standardTranslation : (n : ℕ) → (modalLanguage Atom).Term (Empty ⊕ Fin n) →
    Formula Atom → (modalLanguage Atom).BoundedFormula Empty n
  | _, t, .atom a => BoundedFormula.rel (.pred a) ![t]
  | _, _, .bot => ⊥
  | _, t, .imp φ ψ => (standardTranslation _ t φ).imp (standardTranslation _ t ψ)
  | n, t, .box φ =>
    ((BoundedFormula.rel ModalRelations.relR ![t.relabel (Sum.map id (Fin.castAdd 1)),
      Term.var (Sum.inr ⟨n, by omega⟩)]).imp
      (standardTranslation (n + 1) (Term.var (Sum.inr ⟨n, by omega⟩)) φ)).all

/-- **Correctness of the standard translation.** Let $M$ be a Kripke model with set of worlds
$W$, viewed as a structure for the modal language. For every $n$, every term $t$ of the modal
language in the variables $x_0, \dots, x_{n-1}$, every modal formula $\varphi$ and every
assignment of worlds in $W$ to $x_0, \dots, x_{n-1}$, the standard translation of $\varphi$
with $n$ variables in scope and current-world term $t$ holds in $M$ under this assignment if
and only if $\varphi$ is satisfied in $M$ at the world that $t$ denotes under the
assignment. -/
theorem realize_standardTranslation {W : Type v} (M : KripkeModel W Atom) :
    ∀ (n : ℕ) (t : (modalLanguage Atom).Term (Empty ⊕ Fin n)) (φ : Formula Atom)
      (v : Empty → W) (xs : Fin n → W),
      @BoundedFormula.Realize (modalLanguage Atom) W (kripkeStructure M) Empty n
        (standardTranslation n t φ) v xs ↔
        M.Satisfies (@Term.realize (modalLanguage Atom) W (kripkeStructure M)
          (Empty ⊕ Fin n) (Sum.elim v xs) t) φ := by
  intro n t φ
  let : (modalLanguage Atom).Structure W := kripkeStructure M
  induction φ generalizing n t with
  | atom a =>
    intro v xs
    simp only [standardTranslation, BoundedFormula.Realize]
    rfl
  | bot =>
    intro v xs
    simp only [standardTranslation, BoundedFormula.Realize, KripkeModel.Satisfies]
  | imp φ ψ ihφ ihψ =>
    intro v xs
    rw [standardTranslation, BoundedFormula.realize_imp, ihφ, ihψ]
    rfl
  | box φ ih =>
    intro v xs
    rw [standardTranslation, BoundedFormula.realize_all]
    constructor
    · intro h a hrel
      have hbody := h a
      simp only [BoundedFormula.Realize] at hbody
      have hcomp : (Sum.elim v (Fin.snoc xs a)) ∘ (Sum.map id (Fin.castAdd 1)) =
          Sum.elim v xs := by
        funext y
        rcases y with y | j
        · rfl
        · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr]
          have hcast : Fin.castAdd 1 j = j.castSucc := rfl
          rw [hcast, Fin.snoc_castSucc]
      have ht : (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
          (Sum.elim v (Fin.snoc xs a)) (t.relabel (Sum.map id (Fin.castAdd 1)))) =
          @Term.realize (modalLanguage Atom) W (kripkeStructure M) _ (Sum.elim v xs) t := by
        rw [Term.realize_relabel, hcomp]
      have hnew : (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
          (Sum.elim v (Fin.snoc xs a)) (Term.var (Sum.inr (⟨n, by omega⟩ : Fin (n + 1))))) = a := by
        simp only [Term.realize_var, Sum.elim_inr]
        show @Fin.snoc n (fun _ => W) xs a (Fin.last n) = a
        exact @Fin.snoc_last n (fun _ => W) a xs
      have hrelEq : (kripkeStructure M).RelMap ModalRelations.relR
          (fun i => (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
              (Sum.elim v (Fin.snoc xs a))
              (![t.relabel (Sum.map id (Fin.castAdd 1)),
                Term.var (Sum.inr (⟨n, by omega⟩ : Fin (n + 1)))] i))) =
          M.rel (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
            (Sum.elim v xs) t) a := by
        show M.rel (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
            (Sum.elim v (Fin.snoc xs a)) (t.relabel (Sum.map id (Fin.castAdd 1))))
            (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
            (Sum.elim v (Fin.snoc xs a)) (Term.var (Sum.inr (⟨n, by omega⟩ : Fin (n + 1))))) = _
        rw [ht, hnew]
      have hsat : M.Satisfies (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
          (Sum.elim v (Fin.snoc xs a)) (Term.var (Sum.inr (⟨n, by omega⟩ : Fin (n + 1))))) φ :=
        (ih (n + 1) (Term.var (Sum.inr (⟨n, by omega⟩ : Fin (n + 1)))) v
          (Fin.snoc xs a)).mp (hbody (hrelEq ▸ hrel))
      rw [hnew] at hsat
      exact hsat
    · intro h a
      simp only [BoundedFormula.Realize]
      intro hrelArg
      have hcomp : (Sum.elim v (Fin.snoc xs a)) ∘ (Sum.map id (Fin.castAdd 1)) =
          Sum.elim v xs := by
        funext y
        rcases y with y | j
        · rfl
        · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr]
          have hcast : Fin.castAdd 1 j = j.castSucc := rfl
          rw [hcast, Fin.snoc_castSucc]
      have ht : (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
          (Sum.elim v (Fin.snoc xs a)) (t.relabel (Sum.map id (Fin.castAdd 1)))) =
          @Term.realize (modalLanguage Atom) W (kripkeStructure M) _ (Sum.elim v xs) t := by
        rw [Term.realize_relabel, hcomp]
      have hnew : (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
          (Sum.elim v (Fin.snoc xs a)) (Term.var (Sum.inr (⟨n, by omega⟩ : Fin (n + 1))))) = a := by
        simp only [Term.realize_var, Sum.elim_inr]
        show @Fin.snoc n (fun _ => W) xs a (Fin.last n) = a
        exact @Fin.snoc_last n (fun _ => W) a xs
      have hrelEq : (kripkeStructure M).RelMap ModalRelations.relR
          (fun i => (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
              (Sum.elim v (Fin.snoc xs a))
              (![t.relabel (Sum.map id (Fin.castAdd 1)),
                Term.var (Sum.inr (⟨n, by omega⟩ : Fin (n + 1)))] i))) =
          M.rel (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
            (Sum.elim v xs) t) a := by
        show M.rel (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
            (Sum.elim v (Fin.snoc xs a)) (t.relabel (Sum.map id (Fin.castAdd 1))))
            (@Term.realize (modalLanguage Atom) W (kripkeStructure M) _
            (Sum.elim v (Fin.snoc xs a)) (Term.var (Sum.inr (⟨n, by omega⟩ : Fin (n + 1))))) = _
        rw [ht, hnew]
      have hsat : M.Satisfies a φ := h a (hrelEq ▸ hrelArg)
      rw [← hnew] at hsat
      exact (ih (n + 1) (Term.var (Sum.inr (⟨n, by omega⟩ : Fin (n + 1)))) v
        (Fin.snoc xs a)).mpr hsat

/-- **Bisimulation-invariant formulas.** A first-order formula $\alpha$ over the modal language,
with one variable $x$ and no other free variables, is bisimulation-invariant if for all Kripke
models $M$ and $N$ over the same atoms, every bisimulation $Z$ between $M$ and $N$ and all
worlds $w$ of $M$ and $v$ of $N$ with $Z(w, v)$, the formula $\alpha$ holds in $M$ (viewed as
a structure for the modal language) at $x = w$ if and only if it holds in $N$ at $x = v$. -/
def BisimulationInvariant {Atom : Type u}
    (α : (modalLanguage Atom).BoundedFormula Empty 1) : Prop :=
  ∀ {W : Type v} {V : Type w} (M : KripkeModel W Atom) (N : KripkeModel V Atom)
    (R : W → V → Prop), Bisimulation M N R → ∀ (w : W) (v : V), R w v →
      (@BoundedFormula.Realize (modalLanguage Atom) W (kripkeStructure M) Empty 1 α
        (fun x => x.elim) (fun _ => w) ↔
      @BoundedFormula.Realize (modalLanguage Atom) V (kripkeStructure N) Empty 1 α
        (fun x => x.elim) (fun _ => v))

/-- **Modal formulas are bisimulation-invariant under the standard translation.** For every
modal formula $\varphi$, its standard translation $ST_x(\varphi)$ (the first-order formula over
the modal language whose single variable $x$ stands for the current world) is
bisimulation-invariant: for all Kripke models $M$ and $N$, every bisimulation $Z$ between $M$
and $N$ and all worlds $w$ of $M$ and $v$ of $N$ with $Z(w, v)$, the formula $ST_x(\varphi)$
holds in $M$ at $x = w$ if and only if it holds in $N$ at $x = v$. -/
theorem bisimulationInvariant_standardTranslation (φ : Formula Atom) :
    BisimulationInvariant (standardTranslation 1 (Term.var (Sum.inr (0 : Fin 1))) φ) := by
  intro W V M N R hR w v hr
  rw [realize_standardTranslation M, realize_standardTranslation N]
  exact hR.satisfies_iff φ w v hr

end Cslib.Modal
