/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Uniform omega bound for totally multiplicative sign sums

`AIM-ANALYTIC_NUMBER_THEORY-0025` (AIM Sarnak's conjecture, Lower
bounds, item 1.4): can one get a reasonable omega result, better than
the fivefold iterated log, for `|sum_{n <= X} f(n)|` uniformly over
totally multiplicative `f : N -> {+-1}`?
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.MultiplicativeSignOmegaBoundWanted

/-! UnsolvedMath record `AIM-ANALYTIC_NUMBER_THEORY-0025` (AIM Problem
Lists, Sarnak's conjecture, Lower bounds, item 1.4,
<http://aimpl.org/sarnakconjecture/1/>). The maintained list records R. McNamara's solution
(remark by J. Teräväinen). -/

open scoped BigOperators

/-- A totally multiplicative sign function `f : N -> {+-1}`, packaged
with its sign and multiplicativity conditions. -/
structure TotallyMultiplicativeSign where
  /-- The underlying function on positive integers. -/
  toFun : PNat → ℤ
  sign : ∀ n, toFun n = 1 ∨ toFun n = -1
  mul : ∀ m n, toFun (m * n) = toFun m * toFun n

/-- Partial sums `sum_{n <= X} f (n)`, with `X` ranging over the
reals. -/
noncomputable def summatory (f : TotallyMultiplicativeSign) (X : ℝ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Nat.floor X)) (fun n => ((if h : 0 < n then ↑(f.toFun ⟨n, h⟩) else 0) : ℝ))

/-- The fivefold iterated logarithm baseline of the source question. -/
noncomputable def iteratedLog5 (X : ℝ) : ℝ :=
  Real.log (Real.log (Real.log (Real.log (Real.log X))))

/-- There is an improved uniform growth rate `phi`, dominating the
fivefold iterated log in the little-o sense, such that every totally
multiplicative sign function `f` has `|sum_{n <= X} f (n)| >= c * phi X`
for arbitrarily large `X`, with `c > 0` allowed to depend on `f`. -/
def conjecture : Prop :=
  ∃ φ : ℝ → ℝ, (∀ᶠ X : ℝ in Filter.atTop, 0 ≤ φ X) ∧
    (Asymptotics.IsLittleO Filter.atTop iteratedLog5 φ) ∧ ∀ f : TotallyMultiplicativeSign,
      ∃ c : ℝ, c > 0 ∧ ∀ X₀ : ℝ, ∃ X : ℝ, X ≥ X₀ ∧ |summatory f X| ≥ c * φ X

/--
Resolved true: Resolved true per the source's own note: the AIM Sarnak-conjecture list (Problem
1.4) records, in a remark by J. Teräväinen, that R. McNamara solved it in his PhD thesis with
growth (log log X)^{1/484 - o(1)}; Helfgott and Radziwiłł (arXiv:2103.06853) outline a better
exponent. Source: AIM Problem Lists, Sarnak's conjecture, Problem 1.4 and remark by J.
Teräväinen (citing R. McNamara's PhD thesis), https://aimpl.org/sarnakconjecture/1/; R.
McNamara, PhD thesis (UCLA), eScholarship 4wr015m0, https://escholarship.org/uc/item/4wr015m0.
Moved from `OpenConjectures/NumberTheory/MultiplicativeSignOmegaBound`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.MultiplicativeSignOmegaBoundWanted
