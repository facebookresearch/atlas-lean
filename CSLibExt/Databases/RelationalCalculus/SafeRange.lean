/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalCalculus
public import CSLibExt.Databases.FunctionalDependencies

/-!
# A local safe-range check for the relational calculus

`Formula.SafeRange` is a decidable, order-independent reading of the range rules in Abiteboul,
Hull and Vianu, *Foundations of Databases*, §5.4, pp. 83–85 (Algorithm 5.4.3 and footnote 3).
It takes arbitrary formulas, not just normal forms. Levels avoid capture; `pushNeg` removes
universals and pushes negations to atoms and existentials.

The checker treats each conjunction as one flattened block: it pools the positive restrictions
of its children, then propagates them along variable equalities in that block to a fixed point.
Disjunction intersects the restrictions of its alternatives. Each existential block is checked
locally: each bound level must be restricted by its body, without importing seeds from outside
the block. Failure below a quantifier propagates even through negation.

This condition suffices for domain independence; it does not decide that semantic property.
Its acceptance class is not identified with every use of “safe range” in the text. For example,
in Example 5.4.9(b), p. 90, this local check rejects the displayed input but accepts its displayed
RANF rewrite, which brings a restricting atom inside the existential block.
-/

@[expose] public section

namespace Cslib.Databases.RelationalCalculus

variable {N A D : Type*} {S : N → Finset A} {n k : ℕ}

namespace Formula

/-- Push a pending negation (if `negative`) to atoms or existential blocks. -/
def pushNeg {n : ℕ} (p : Formula S D n) (negative : Bool) : Formula S D n := match p with
  | .rel .. | .eq .. => if negative then p.neg else p
  | .neg p => p.pushNeg (!negative)
  | .conj p q => if negative then (p.pushNeg true).disj (q.pushNeg true)
    else (p.pushNeg false).conj (q.pushNeg false)
  | .disj p q => if negative then (p.pushNeg true).conj (q.pushNeg true)
    else (p.pushNeg false).disj (q.pushNeg false)
  | .ex p => if negative then (p.pushNeg false).ex.neg else (p.pushNeg false).ex
  | .all p => if negative then (p.pushNeg true).ex else (p.pushNeg true).ex.neg

/-- Normalization preserves truth, with the indicated polarity, in every underlying domain. -/
theorem sat_pushNeg (I : Instance S D) (d : Set D) (p : Formula S D n) (b : Bool) (v : Fin n → D) :
    (p.pushNeg b).Sat I d v ↔ (if b then ¬p.Sat I d v else p.Sat I d v) := by
  classical
  induction p generalizing b with
  | rel | eq => cases b <;> simp [pushNeg, Sat]
  | neg p ih => cases b <;> simp [pushNeg, Sat, ih]
  | conj p q ih jh => cases b <;> simp [pushNeg, Sat, ih, jh]; tauto
  | disj p q ih jh => cases b <;> simp [pushNeg, Sat, ih, jh]
  | ex p ih | all p ih => cases b <;> simp [pushNeg, Sat, ih]

@[simp] theorem constants_pushNeg (p : Formula S D n) (b : Bool) :
    (p.pushNeg b).constants = p.constants := by
  induction p generalizing b <;> cases b <;> simp [pushNeg, constants, *]

@[simp] theorem vars_pushNeg (p : Formula S D n) (b : Bool) : (p.pushNeg b).vars = p.vars := by
  induction p generalizing b <;> cases b <;> simp [pushNeg, vars, *]

end Formula

/-- A conjunction under analysis. `seeds` collects positively restricted variables; `rules`
carries the two singleton implications of each variable equality. `ok` records that every
quantifier checked below this node had a restricted witness. -/
structure RangeInfo (n : ℕ) where
  seeds : Finset (Fin n)
  rules : Finset (FD (Fin n)) := ∅
  ok : Bool := true

namespace RangeInfo

/-- Propagate all equalities of the conjunction, regardless of order, until a fixed point. -/
def bounds (s : RangeInfo n) := attrClosure s.rules s.seeds

def ofEq : Term D n → Term D n → RangeInfo n
  | .var x, .var y => ⟨∅, {⟨{x}, {y}⟩, ⟨{y}, {x}⟩}, true⟩
  | .var x, .const _ | .const _, .var x => { seeds := {x} }
  | .const _, .const _ => { seeds := ∅ }

def merge (s t : RangeInfo n) : RangeInfo n :=
  ⟨s.seeds ∪ t.seeds, s.rules ∪ t.rules, s.ok && t.ok⟩

def meet (s t : RangeInfo n) : RangeInfo n :=
  { seeds := s.bounds ∩ t.bounds, ok := s.ok && t.ok }

def project (s : RangeInfo (n + 1)) : RangeInfo n :=
  { seeds := Formula.outerVars s.bounds, ok := s.ok && decide (Fin.last n ∈ s.bounds) }

end RangeInfo

namespace Formula

/-- Analyze a negation-normalized formula. A universal at this internal stage is rejected. -/
def scan {n : ℕ} (p : Formula S D n) : RangeInfo n := match p with
  | .rel r ts => { seeds := Finset.univ.biUnion fun a : S r => (ts a).vars }
  | .eq s t => RangeInfo.ofEq s t
  | .conj p q => p.scan.merge q.scan
  | .disj p q => p.scan.meet q.scan
  | .neg p => { seeds := ∅, ok := p.scan.ok }
  | .ex p => p.scan.project
  | .all _ => { seeds := ∅, ok := false }

/-- Push negations, then compute local range restrictions using the conjunction closure and
quantifier checks above. `none` means a quantified variable lacked a local restriction; it is
not a successful empty set. The computation uses no database, value equality, or semantic oracle. -/
def rangeRestriction (p : Formula S D n) : Option (Finset (Fin n)) :=
  let s := (p.pushNeg false).scan
  if s.ok then some s.bounds else none

/-- The local safe-range condition: every existential check succeeds using only its body, and
the computed restrictions equal the free variables of the formula. -/
def SafeRange (p : Formula S D n) : Prop := p.rangeRestriction = some p.vars

instance (p : Formula S D n) : Decidable p.SafeRange :=
  inferInstanceAs (Decidable (p.rangeRestriction = some p.vars))

end Formula
end Cslib.Databases.RelationalCalculus
