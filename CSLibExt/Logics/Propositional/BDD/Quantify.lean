/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Restriction, quantification, and satisfying paths for BDDs
-/
module

public import CSLibExt.Logics.Propositional.BDD.Basic

/-!
# Restriction, quantification, and satisfying paths for BDDs

Operations on the tree-form diagrams of `Basic.lean`; on ordered input they
return reduced ordered diagrams (`restrict` reduces any input):

- `BDD.restrict x b t` (the cofactor `t[x := b]`), with
  `eval_restrict : (restrict x b t).eval σ = t.eval (Function.update σ x b)`;
- `BDD.existsVar x t` and `BDD.forallVar x t` (Boolean quantification over `x`,
  built with `apply`);
- `BDD.satPath t`, a path to a `true` leaf read as a partial assignment, with
  `eval_ofPath_satPath` (the path satisfies an ordered diagram) and
  `satPath_isSome_of_ne` (a reduced diagram other than `leaf false` has one).

`exists_evalBool_eq_false_at_iff` decides satisfiability with one variable fixed
to `false` (such as a variable playing the role of falsum) by a cofactor, and
`satPath_restrict_ofProposition` computes such a model. (Without a constraint,
every proposition over `Nat` atoms is satisfiable by the all-true valuation;
`ofProposition_satPath` still computes a model from the ROBDD.)

## References

- R. E. Bryant, *Graph-based algorithms for Boolean function manipulation*,
  IEEE Trans. Computers C-35(8), 1986, 677-691 (restriction, §4.4; satisfy-one,
  §4.6).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Logic.PL.BDD

/-! ### Restriction -/

/-- The cofactor `t[x := b]`: every test of `x` takes the `b` branch. -/
def restrict (x : Nat) (b : Bool) : BDD → BDD
  | leaf c => leaf c
  | node v lo hi =>
    if v = x then (if b then restrict x b hi else restrict x b lo)
    else mk v (restrict x b lo) (restrict x b hi)

theorem eval_restrict (x : Nat) (b : Bool) (t : BDD) (σ : Nat → Bool) :
    (restrict x b t).eval σ = t.eval (Function.update σ x b) := by
  induction t with
  | leaf c => rfl
  | node v lo hi ihlo ihhi =>
    by_cases hv : v = x
    · subst hv
      cases b <;> simp [restrict, ihlo, ihhi]
    · simp [restrict, hv, ihlo, ihhi]

theorem orderedFrom_restrict (x : Nat) (b : Bool) {n : Nat} {t : BDD} (h : OrderedFrom n t) :
    OrderedFrom n (restrict x b t) := by
  induction t generalizing n with
  | leaf c => trivial
  | node v lo hi ihlo ihhi =>
    obtain ⟨hv, hlo, hhi⟩ := h
    by_cases hvx : v = x
    · cases b
      · simpa [restrict, hvx] using (ihlo hlo).mono (by omega)
      · simpa [restrict, hvx] using (ihhi hhi).mono (by omega)
    · simpa [restrict, hvx] using orderedFrom_mk hv (ihlo hlo) (ihhi hhi)

/-- `restrict` always returns a reduced diagram, whatever its input: kept nodes are rebuilt
with `mk`. -/
theorem reduced_restrict (x : Nat) (b : Bool) (t : BDD) : Reduced (restrict x b t) := by
  induction t with
  | leaf c => trivial
  | node v lo hi ihlo ihhi =>
    by_cases hvx : v = x
    · cases b
      · simpa [restrict, hvx] using ihlo
      · simpa [restrict, hvx] using ihhi
    · simpa [restrict, hvx] using reduced_mk (v := v) ihlo ihhi

/-- Restricting an ordered diagram gives a reduced ordered one. -/
theorem isROBDD_restrict (x : Nat) (b : Bool) {t : BDD} (h : OrderedFrom 0 t) :
    IsROBDD (restrict x b t) :=
  ⟨orderedFrom_restrict x b h, reduced_restrict x b t⟩

/-! ### Quantification -/

/-- Existential quantification over `x`: `t[x := false] ∨ t[x := true]`. -/
def existsVar (x : Nat) (t : BDD) : BDD :=
  apply (· || ·) (restrict x false t) (restrict x true t)

/-- Universal quantification over `x`: `t[x := false] ∧ t[x := true]`. -/
def forallVar (x : Nat) (t : BDD) : BDD :=
  apply (· && ·) (restrict x false t) (restrict x true t)

theorem eval_existsVar (x : Nat) (t : BDD) (σ : Nat → Bool) :
    (existsVar x t).eval σ = true ↔ ∃ b, t.eval (Function.update σ x b) = true := by
  simp only [existsVar, eval_apply, eval_restrict, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨b, h⟩
    cases b
    · exact Or.inl h
    · exact Or.inr h

theorem eval_forallVar (x : Nat) (t : BDD) (σ : Nat → Bool) :
    (forallVar x t).eval σ = true ↔ ∀ b, t.eval (Function.update σ x b) = true := by
  simp only [forallVar, eval_apply, eval_restrict, Bool.and_eq_true]
  constructor
  · rintro ⟨h₀, h₁⟩ b
    cases b
    · exact h₀
    · exact h₁
  · intro h
    exact ⟨h false, h true⟩

/-- Quantifying an ordered diagram gives a reduced ordered one. -/
theorem isROBDD_existsVar (x : Nat) {t : BDD} (h : OrderedFrom 0 t) : IsROBDD (existsVar x t) :=
  isROBDD_apply _ (isROBDD_restrict x false h) (isROBDD_restrict x true h)

theorem isROBDD_forallVar (x : Nat) {t : BDD} (h : OrderedFrom 0 t) : IsROBDD (forallVar x t) :=
  isROBDD_apply _ (isROBDD_restrict x false h) (isROBDD_restrict x true h)

/-! ### Satisfying paths -/

/-- A path to a `true` leaf, preferring `hi` branches, as a list of tested variables with
the branch taken. -/
def satPath : BDD → Option (List (Nat × Bool))
  | leaf b => if b then some [] else none
  | node v lo hi =>
    match satPath hi with
    | some p => some ((v, true) :: p)
    | none => (satPath lo).map ((v, false) :: ·)

/-- The assignment read off a path: the recorded value on path variables, `false`
elsewhere. -/
def ofPath (p : List (Nat × Bool)) (x : Nat) : Bool := (p.lookup x).getD false

theorem ofPath_cons (v : Nat) (b : Bool) (p : List (Nat × Bool)) :
    ofPath ((v, b) :: p) = Function.update (ofPath p) v b := by
  funext x
  by_cases hx : x = v
  · subst hx
    simp [ofPath, List.lookup]
  · have hxv : (x == v) = false := beq_eq_false_iff_ne.mpr hx
    simp [ofPath, List.lookup, hxv, Function.update_of_ne hx]

/-- The assignment read off a satisfying path makes an ordered diagram true. -/
theorem eval_ofPath_satPath {n : Nat} {t : BDD} (h : OrderedFrom n t)
    {p : List (Nat × Bool)} (hp : satPath t = some p) : t.eval (ofPath p) = true := by
  induction t generalizing n p with
  | leaf b =>
    cases b <;> simp_all [satPath]
  | node v lo hi ihlo ihhi =>
    obtain ⟨-, hlo, hhi⟩ := h
    simp only [satPath] at hp
    split at hp
    · next q hq =>
      cases hp
      rw [ofPath_cons, eval_node, Function.update_self]
      simp only [↓reduceIte]
      rw [eval_update_of_lt hhi (by omega)]
      exact ihhi hhi hq
    · next hq =>
      obtain ⟨q, hq', rfl⟩ := Option.map_eq_some_iff.mp hp
      rw [ofPath_cons, eval_node, Function.update_self]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [eval_update_of_lt hlo (by omega)]
      exact ihlo hlo hq'

/-- A reduced diagram other than `leaf false` has a satisfying path. -/
theorem satPath_isSome_of_ne {t : BDD} (h : Reduced t) (hne : t ≠ leaf false) :
    (satPath t).isSome := by
  induction t with
  | leaf b =>
    cases b
    · exact absurd rfl hne
    · rfl
  | node v lo hi ihlo ihhi =>
    obtain ⟨hlohi, hlo, hhi⟩ := h
    simp only [satPath]
    split
    · rfl
    · next hq =>
      have hhi' : hi = leaf false := by
        by_contra hhi'
        have := ihhi hhi hhi'
        simp_all
      rw [Option.isSome_map]
      exact ihlo hlo (fun hlo' ↦ hlohi (hlo'.trans hhi'.symm))

/-- Satisfiability with one variable `f` fixed to `false` (for instance a variable that
plays the role of falsum): `A` has such a model iff the cofactor of its ROBDD at `f := false`
is not the leaf `false`. Without such a constraint, every proposition over `Nat` atoms is
satisfied by the all-true valuation. -/
theorem exists_evalBool_eq_false_at_iff {A : Proposition Nat} (f : Nat) :
    (∃ σ : Nat → Bool, σ f = false ∧ A.evalBool σ = true) ↔
      restrict f false (ofProposition A) ≠ leaf false := by
  have hR := isROBDD_restrict f false (isROBDD_ofProposition A).1
  rw [Ne, eq_leaf_false_iff hR]
  simp only [eval_restrict, eval_ofProposition, not_forall, Bool.not_eq_false]
  constructor
  · rintro ⟨σ, hσ, h⟩
    refine ⟨σ, ?_⟩
    rwa [show Function.update σ f false = σ from by rw [← hσ]; exact Function.update_eq_self _ _]
  · rintro ⟨σ, h⟩
    exact ⟨Function.update σ f false, Function.update_self .., h⟩

/-- **Satisfy-one** with one variable `f` fixed to `false`: if `A` has a model with `f` false,
the cofactor of its ROBDD at `f := false` has a satisfying path, and the path's assignment with
`f` set to `false` is such a model. -/
theorem satPath_restrict_ofProposition {A : Proposition Nat} (f : Nat)
    (h : ∃ σ : Nat → Bool, σ f = false ∧ A.evalBool σ = true) :
    ∃ p, satPath (restrict f false (ofProposition A)) = some p ∧
      A.evalBool (Function.update (ofPath p) f false) = true := by
  have hR := isROBDD_restrict f false (isROBDD_ofProposition A).1
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (satPath_isSome_of_ne hR.2 ((exists_evalBool_eq_false_at_iff f).mp h))
  refine ⟨p, hp, ?_⟩
  have := eval_ofPath_satPath hR.1 hp
  rwa [eval_restrict, eval_ofProposition] at this

/-- Every proposition over atoms alone is true under the all-true valuation. -/
theorem evalBool_allTrue (A : Proposition Nat) : A.evalBool (fun _ ↦ true) = true := by
  induction A with
  | atom x => rfl
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp only [Proposition.evalBool, ihA, ihB]
    rfl

/-- **Satisfy-one** for propositions: the ROBDD of every proposition over `Nat` atoms has a
satisfying path, and its assignment satisfies the proposition. (Every such proposition is
satisfiable, by the all-true valuation; the path is usually a different model.) -/
theorem ofProposition_satPath (A : Proposition Nat) :
    ∃ p, satPath (ofProposition A) = some p ∧ A.evalBool (ofPath p) = true := by
  have hne := ofProposition_ne_leaf_false_iff.mpr ⟨fun _ ↦ true, evalBool_allTrue A⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (satPath_isSome_of_ne (isROBDD_ofProposition A).2 hne)
  exact ⟨p, hp, eval_ofProposition A _ ▸ eval_ofPath_satPath (isROBDD_ofProposition A).1 hp⟩

end Cslib.Logic.PL.BDD
