/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import MathlibExt.Economics.Consumer.LocalNonsatiation
public import MathlibExt.Economics.Consumer.ExpenditureFunction
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Consumer duality: expenditure at the indirect utility level

A consumer chooses a bundle `x : ι → ℝ` of finitely many goods from a consumption set
`X : Set (ι → ℝ)` to maximize a utility `u : (ι → ℝ) → ℝ`, subject to the budget constraint
`p ⬝ᵥ x ≤ w` at prices `p` and wealth `w`. This file sets up the minimal interface of consumer
theory (budget set, Marshallian demand, indirect utility, expenditure function, local
nonsatiation) and proves the duality identity `e(p, v(p, w)) = w`: under local nonsatiation, if
utility maximization attains its optimum, the least cost of reaching the optimal utility level
is exactly the wealth.

Indirect utility and expenditure are real `sSup`/`sInf` values. Theorems about them assume the
optimum is attained (`IsMarshallianDemand`), so no junk value enters a conclusion. No sign
condition on prices, no continuity of utility and no convexity is needed for this identity.

## Main definitions

* `Economics.Consumer.budgetSet`: the budget set `B(p, w)`.
* `Economics.Consumer.IsMarshallianDemand`: an affordable utility maximizer.
* `Economics.Consumer.indirectUtility`: `v(p, w) = sup {u x | x ∈ B(p, w)}`.
* `Economics.Consumer.expenditure`: `e(p, ū) = inf {p ⬝ᵥ x | x ∈ X, ū ≤ u x}`.
* `Economics.Consumer.LocallyNonsatiated`: local nonsatiation of `u` on `X`, an alias of
  `MathlibExt.Economics.Consumer.LocallyNonsatiated`.

## Main results

* `Economics.Consumer.indirectUtility_eq_of_isMarshallianDemand`: `v(p, w) = u x` at a demanded
  bundle `x`.
* `Economics.Consumer.expenditure_indirectUtility_eq`: `e(p, v(p, w)) = w`.

## References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Section 3.E (Proposition 3.E.3).
* H. R. Varian, *Intermediate Microeconomics: A Modern Approach*, 9th ed., Norton (2014).
-/

@[expose] public section

namespace Economics.Consumer

/-- The budget set `B(p, w) = {x ∈ X | p ⬝ᵥ x ≤ w}`: affordable consumption
bundles at prices `p` and wealth `w`. -/
def budgetSet {ι : Type*} [Fintype ι] (X : Set (ι → ℝ)) (p : ι → ℝ) (w : ℝ) :
    Set (ι → ℝ) :=
  {x | x ∈ X ∧ p ⬝ᵥ x ≤ w}

/-- `x` is a Marshallian (utility-maximizing) demand at `(p, w)`: it is
affordable and no affordable bundle gives strictly higher utility. This is the
attainment hypothesis of the utility-maximization problem. -/
def IsMarshallianDemand {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ)
    (X : Set (ι → ℝ)) (p : ι → ℝ) (w : ℝ) (x : ι → ℝ) : Prop :=
  x ∈ budgetSet X p w ∧ ∀ y ∈ budgetSet X p w, u y ≤ u x

/-- The indirect utility `v(p, w) = sup {u x | x ∈ B(p, w)}`. As a real
supremum it is meaningful only when the supremum exists; theorems about it
assume attainment (`IsMarshallianDemand`). -/
noncomputable def indirectUtility {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ)
    (X : Set (ι → ℝ)) (p : ι → ℝ) (w : ℝ) : ℝ :=
  sSup (u '' budgetSet X p w)

-- Preserve the consumer spelling while sharing the canonical expenditure declaration.
export MathlibExt.Economics.ExpenditureFunction (expenditure)

/- Local nonsatiation is defined once, in `MathlibExt.Economics.Consumer`; this alias keeps the
name `Economics.Consumer.LocallyNonsatiated` resolving to that same constant. -/
export MathlibExt.Economics.Consumer (LocallyNonsatiated)

/-- Under attainment, the indirect utility is the utility of the demanded
bundle. -/
theorem indirectUtility_eq_of_isMarshallianDemand {ι : Type*} [Fintype ι]
    {u : (ι → ℝ) → ℝ} {X : Set (ι → ℝ)} {p : ι → ℝ} {w : ℝ} {x : ι → ℝ}
    (hx : IsMarshallianDemand u X p w x) :
    indirectUtility u X p w = u x := by
  unfold indirectUtility
  apply IsGreatest.csSup_eq
  constructor
  · exact Set.mem_image_of_mem u hx.1
  · intro b hb
    obtain ⟨y, hy, rfl⟩ := hb
    exact hx.2 y hy

/-- **Expenditure–utility duality** `e(p, v(p, w)) = w`. If utility is locally
nonsatiated on the consumption set and the utility-maximization problem at
`(p, w)` attains its optimum, then the least cost of reaching the indirect
utility level equals wealth. No sign condition on prices is needed. -/
theorem expenditure_indirectUtility_eq {ι : Type*} [Fintype ι]
    {u : (ι → ℝ) → ℝ} {X : Set (ι → ℝ)} {p : ι → ℝ} {w : ℝ} {x : ι → ℝ}
    (hLNS : LocallyNonsatiated u X) (hx : IsMarshallianDemand u X p w x) :
    expenditure u X p (indirectUtility u X p w) = w := by
  have hv : indirectUtility u X p w = u x :=
    indirectUtility_eq_of_isMarshallianDemand hx
  rw [hv]
  have hcont : Continuous (fun z : ι → ℝ => p ⬝ᵥ z) := by
    unfold dotProduct
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  have hlb : ∀ b ∈ (fun z => p ⬝ᵥ z) '' {z | z ∈ X ∧ u x ≤ u z}, w ≤ b := by
    intro b hb
    obtain ⟨y, ⟨hyX, hle⟩, rfl⟩ := hb
    by_contra hcon
    rw [not_le] at hcon
    have hca : ContinuousAt (fun z : ι → ℝ => p ⬝ᵥ z) y := hcont.continuousAt
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.mp hca (w - p ⬝ᵥ y) (sub_pos.mpr hcon)
    obtain ⟨z, hzX, hdist, hult⟩ := hLNS y hyX δ hδpos
    have hdist' := hδ hdist
    rw [Real.dist_eq] at hdist'
    have hzcost : p ⬝ᵥ z < w := by
      have hmem := abs_lt.mp hdist'
      linarith
    have hzbudget : z ∈ budgetSet X p w := ⟨hzX, le_of_lt hzcost⟩
    have hle2 := hx.2 z hzbudget
    linarith
  have hxmem : (fun z => p ⬝ᵥ z) x ∈ (fun z => p ⬝ᵥ z) '' {z | z ∈ X ∧ u x ≤ u z} :=
    Set.mem_image_of_mem _ ⟨hx.1.1, le_refl _⟩
  unfold expenditure
  apply le_antisymm
  · exact (csInf_le ⟨w, hlb⟩ hxmem).trans hx.1.2
  · exact le_csInf ⟨_, hxmem⟩ hlb

end Economics.Consumer
