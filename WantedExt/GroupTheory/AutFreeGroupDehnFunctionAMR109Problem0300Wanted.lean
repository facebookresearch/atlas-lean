/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Dehn functions of Aut(F_n) and Out(F_n) are exponential (Bridson–Vogtmann, Question 7.1)

B. Farb (ed.), Problems on Mapping Class Groups and Related Topics, Ch. 20 (M. Bridson and K.
Vogtmann), Question 7.1: what are the Dehn functions of `Aut(F_n)` and `Out(F_n)` for `n > 3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Order.Lattice.Nat
public import WantedExt.GroupTheory.OutFreeGroupShared

@[expose] public section

namespace MathlibExt.GroupTheory.AutFreeGroupDehnFunctionAMR109Problem0300Wanted

/-!
Source: B. Farb (ed.), Problems on Mapping Class Groups and Related Topics (2006), Ch. 20 (M.
Bridson and K. Vogtmann), Question 7.1. UnsolvedMath record UM-11000300 (`AMR-109-0300`), dataset
ulamai/UnsolvedMath v1.8.0.

The answer (exponential) is stated for every finite presentation: Dehn functions of different finite
presentations of a group are equivalent, so the class is a group invariant; the statement also
asserts that a finite presentation exists. A finite presentation of `G` is a finite type of
generators `α`, a finite set of relators `R ⊆ F(α)` and an isomorphism `⟨α | R⟩ ≃* G`. The area of a
relation `w` is the least number of conjugates `u r^{±1} u⁻¹` (`r ∈ R`) with product `w`, and `δ(m)`
is the largest area of a relation of reduced length at most `m`. Equivalence is the usual `f ≼ g ⟺ f
m ≤ C g(Cm + C) + Cm + C` both ways, and exponential means equivalent to `2^m`. `Out(F_n) =
Aut(F_n)/Inn(F_n)` is the `OutFreeGroup` of `WantedExt/GroupTheory/OutFreeGroupShared.lean` (the
quotient by the normal closure of the inner automorphisms, already normal).
-/

open MathlibExt.GroupTheory.OutFreeGroupShared

/-- The area of `w` for the relators `R`: the least `N` such that `w` is a product of `N`
conjugates `u r^{±1} u⁻¹` of relators `r ∈ R` (`sInf ∅ = 0` when `w` is not such a product). -/
noncomputable def area {α : Type*} (R : Set (FreeGroup α)) (w : FreeGroup α) : ℕ :=
  sInf {N | ∃ l : List (FreeGroup α × FreeGroup α × Bool), l.length = N ∧ (∀ x ∈ l, x.2.1 ∈ R) ∧
    (l.map fun x => x.1 * (if x.2.2 then x.2.1 else x.2.1⁻¹) * x.1⁻¹).prod = w}

open Classical in
/-- The Dehn function of the presentation `⟨α | R⟩`: the largest area of a relation (an element of
the normal closure of `R`) of reduced length at most `m`. For finite `α` the set is finite. -/
noncomputable def dehnFunction {α : Type*} (R : Set (FreeGroup α)) (m : ℕ) : ℕ :=
  sSup (area R '' {w | w ∈ Subgroup.normalClosure R ∧ w.toWord.length ≤ m})

/-- `f ≼ g`: `f m ≤ C g (C m + C) + C m + C` for some `C > 0`. -/
def DehnLE (f g : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ m, f m ≤ C * g (C * m + C) + C * m + C

/-- `G` is finitely presented and the Dehn function of every finite presentation of `G` is
equivalent (`≼` both ways) to `m ↦ 2 ^ m`. -/
def HasExponentialDehnFunction (G : Type) [Group G] : Prop :=
  (∃ (α : Type) (_ : Fintype α) (R : Set (FreeGroup α)),
      R.Finite ∧ Nonempty (PresentedGroup R ≃* G)) ∧
    ∀ (α : Type) [Fintype α] (R : Set (FreeGroup α)), R.Finite → Nonempty (PresentedGroup R ≃* G) →
      DehnLE (dehnFunction R) (fun m => 2 ^ m) ∧ DehnLE (fun m => 2 ^ m) (dehnFunction R)

/-- Bridson–Vogtmann's Question 7.1 (Farb (ed.), Problems on Mapping Class Groups, Ch. 20),
answered: for `n > 3` the Dehn functions of `Aut(F_n)` and `Out(F_n)` are exponential. -/
def autOutDehnFunctionsExponential : Prop :=
  ∀ n : ℕ, 3 < n →
    HasExponentialDehnFunction (MulAut (FreeGroup (Fin n))) ∧
      HasExponentialDehnFunction (OutFreeGroup n)

/--
Resolved true: Bridson and Vogtmann proved that for `n ≥ 3` the Dehn functions of `Aut(F_n)` and
`Out(F_n)` are exponential (Hatcher–Vogtmann's exponential upper bound, the `n = 3` lower bound of
Bridson–Vogtmann and a reduction of larger `n` to it), in particular for every `n > 3`. Source: B.
Farb (ed.), Problems on Mapping Class Groups and Related Topics (2006), Ch. 20 (M. Bridson and K.
Vogtmann), Question 7.1; resolution: M. R. Bridson and K. Vogtmann, The Dehn functions of Out(F_n)
and Aut(F_n), Ann. Inst. Fourier 62 (2012), 1811-1817, arXiv:1011.1506 (upper bound:
Hatcher-Vogtmann; lower bound reduction: Handel-Mosher), Theorem 1: for n ≥ 3 the Dehn functions of
Aut(F_n) and Out(F_n) are exponential; "This theorem answers Questions 35 and 37 of [BVsurvey]",
https://arxiv.org/abs/1011.1506.
-/
public theorem_wanted autOutDehnFunctionsExponential_holds : autOutDehnFunctionsExponential

end MathlibExt.GroupTheory.AutFreeGroupDehnFunctionAMR109Problem0300Wanted
