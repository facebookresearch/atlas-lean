/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Paul Bendich
-/
module

public import Mathlib.Topology.UnitInterval

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Topology 363, Topology 393

open Set

/-!
# Cone on a Topological Space; Suspension of a Topological Space

## References

* https://pi.math.cornell.edu/~hatcher/AT/AT.pdf (top of page 9) (for `TopologicalCone`)
* https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, bottom of page 8. (for `Suspension`)
-/

namespace MetaMathlibExt

-- Topology 363: Cone on a Topological Space

def topologicalConeSetoid.{u} (X : Type u) :
      Setoid (X × unitInterval) where
    r p q := p = q ∨ ((p.2 : ℝ) = 0 ∧ (q.2 : ℝ) = 0)
    iseqv :=
      { refl := fun _ => Or.inl rfl
        symm := fun
          | Or.inl h => Or.inl h.symm
          | Or.inr h => Or.inr ⟨h.2, h.1⟩
        trans := fun
          | Or.inl rfl, h => h
          | Or.inr h, Or.inl rfl => Or.inr h
          | Or.inr h, Or.inr h' => Or.inr ⟨h.1, h'.2⟩ }

  /-- Let X be a topological space and give
    [0,1]⊆ℝ the subspace topology. Form
    the cylinder X×[0,1] with the product
    topology. Define an equivalence relation on
    X×[0,1] by (x,t)∼(y,s) if and only if
    (x,t)=(y,s) or t=s=0. The cone on X, denoted
    C(X), is the quotient of X×[0,1] by ∼,
    carrying the quotient topology, that is, the finest
    topology on the set of equivalence classes for which
    the quotient map X×[0,1]→ C(X) is
    continuous.
  -/
  abbrev TopologicalCone.{u} (X : Type u) : Type u :=
    Quotient (topologicalConeSetoid X)

-- Topology 393: Suspension of a Topological Space

def suspensionSetoid.{u} (X : Type u) [TopologicalSpace X]  :
    Setoid (X × Set.Icc (0 : ℝ) 1) where
  r p q :=
    p = q ∨
      (((p.2 : ℝ) = 0 ∧ (q.2 : ℝ) = 0) ∨
       ((p.2 : ℝ) = 1 ∧ (q.2 : ℝ) = 1))

  iseqv := {
    refl := by
      intro p
      exact Or.inl rfl

    symm := by
      intro p q hpq
      rcases hpq with hEq | hBottom | hTop
      · exact Or.inl hEq.symm
      · exact Or.inr (Or.inl ⟨hBottom.2, hBottom.1⟩)
      · exact Or.inr (Or.inr ⟨hTop.2, hTop.1⟩)

    trans := by
      intro p q r hpq hqr
      rcases hpq with hEqPQ | hBottomPQ | hTopPQ
      · subst q
        exact hqr
      · rcases hqr with hEqQR | hBottomQR | hTopQR
        · subst r
          exact Or.inr (Or.inl hBottomPQ)
        · exact Or.inr (Or.inl ⟨hBottomPQ.1, hBottomQR.2⟩)
        · have hContradiction : (0 : ℝ) = 1 :=
            hBottomPQ.2.symm.trans hTopQR.1
          norm_num at hContradiction
      · rcases hqr with hEqQR | hBottomQR | hTopQR
        · subst r
          exact Or.inr (Or.inr hTopPQ)
        · have hContradiction : (1 : ℝ) = 0 :=
            hTopPQ.2.symm.trans hBottomQR.1
          norm_num at hContradiction
        · exact Or.inr (Or.inr ⟨hTopPQ.1, hTopQR.2⟩)
  }

/-- Let X be a topological space. Form the cylinder X × [0,1]. Define an equivalence relation by
(x,t) ∼ (y,s) iff (x,t) = (y,s) or t = s = 0 or t =s = 1.

The *suspension* on X, denoted S(X) is the quotient of X × [0,1] by ∼.
-/
def Suspension.{u} (X : Type u) [TopologicalSpace X] : Type u :=
  Quotient (suspensionSetoid.{u} X)

end MetaMathlibExt

end
