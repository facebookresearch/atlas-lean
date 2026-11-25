/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval.Topology.HomotopyGroups` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e; problem `pi1_circle_mulEquiv_int`, submitter
Kim Morrison):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The adapted portion is the statement and docstring of `pi1_circle_mulEquiv_int` only.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Instances.AddCircle.Real

@[expose] public section

/-!
# The fundamental group of the circle

The fundamental group of the unit circle in `ℂ` based at `1` is isomorphic, as a
group, to the additive group `ℤ`. The proof identifies the circle with the
additive circle of period `2π` via the complex exponential and applies Mathlib's
winding-number isomorphism for the additive circle.

We use explicit basepoints throughout. This keeps the statements close to Mathlib's
current APIs, where homotopy groups are based.
-/

namespace MathlibExt.Topology.HomotopyGroupsWanted
namespace Topology

namespace Pi1Circle

/-- The kernel of the exponential homomorphism `ℝ →+ Additive Circle` is the
subgroup of integer multiples of `2π`. -/
private lemma expHom_ker :
    Circle.expHom.ker = AddSubgroup.zmultiples (2 * Real.pi) := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro h
    have h2 : Circle.exp x = 1 := Additive.toMul.injective h
    have h1 : Complex.exp ((x : ℂ) * Complex.I) = 1 := by
      simpa only [Circle.coe_exp, Circle.coe_one] using congrArg Subtype.val h2
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨n, ?_⟩
    have hn' : (x : ℂ) * Complex.I = ((n : ℝ) * (2 * Real.pi)) * Complex.I := by
      rw [hn]; push_cast; ring
    have hx : (x : ℂ) = (n : ℝ) * (2 * Real.pi) :=
      mul_right_cancel₀ Complex.I_ne_zero hn'
    have hxr : x = (n : ℝ) * (2 * Real.pi) := by
      exact_mod_cast congrArg Complex.re hx
    rw [hxr]; simp [zsmul_eq_mul]
  · rintro ⟨n, hn⟩
    rw [← hn]
    change Circle.expHom (n • (2 * Real.pi)) = 0
    rw [map_zsmul, show Circle.expHom (2 * Real.pi) = 0 from ?_]
    · simp
    · change Additive.ofMul (Circle.exp (2 * Real.pi)) = 0
      have h1 : Circle.exp (2 * Real.pi) = 1 := by
        apply Circle.ext
        have h2 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
          rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I by
            push_cast; ring]
          exact Complex.exp_two_pi_mul_I
        simpa only [Circle.coe_exp, Circle.coe_one] using h2
      rw [h1]; rfl

/-- The additive circle of period `2π` is additively isomorphic to the circle,
via the complex exponential. -/
private noncomputable def addCircleAddEquiv :
    AddCircle (2 * Real.pi) ≃+ Additive Circle :=
  AddEquiv.ofBijective
    (QuotientAddGroup.lift (AddSubgroup.zmultiples (2 * Real.pi)) Circle.expHom
      (le_of_eq expHom_ker.symm))
    ⟨fun a b hab => by
      induction a using QuotientAddGroup.induction_on with
      | _ x => induction b using QuotientAddGroup.induction_on with
        | _ y =>
          have hx : Circle.expHom x = Circle.expHom y := by
            simpa only [QuotientAddGroup.lift_mk] using hab
          have hmem : x - y ∈ Circle.expHom.ker := by
            rw [AddMonoidHom.mem_ker, map_sub, hx, sub_self]
          rw [expHom_ker] at hmem
          rw [AddSubgroup.mem_zmultiples_iff] at hmem
          obtain ⟨n, hn⟩ := hmem
          exact QuotientAddGroup.eq.mpr (by
            rw [AddSubgroup.mem_zmultiples_iff]
            exact ⟨-n, by rw [neg_smul, hn]; abel⟩),
     fun z => by
      obtain ⟨t, ht⟩ := Circle.exp_surjective z.toMul
      exact ⟨(t : AddCircle (2 * Real.pi)), congrArg Additive.ofMul ht⟩⟩

/-- The exponential homeomorphism between the additive circle of period `2π`
and the complex unit circle. -/
private noncomputable def addCircleHomeomorphCircle :
    AddCircle (2 * Real.pi) ≃ₜ Circle :=
  let e : AddCircle (2 * Real.pi) ≃ Circle :=
    addCircleAddEquiv.toEquiv.trans Additive.toMul
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hcomp : e ∘ ((↑) : ℝ → AddCircle (2 * Real.pi)) = Circle.exp := by
    funext t
    change e (t : AddCircle (2 * Real.pi)) = Circle.exp t
    exact rfl
  have hcont : Continuous e :=
    (Topology.IsQuotientMap.continuous_iff isQuotientMap_quotient_mk').mpr
      (hcomp ▸ Circle.exp.continuous)
  have hcontInv : Continuous e.symm := by
    rw [continuous_iff_isClosed]
    intro s hs
    have hpre : e.symm ⁻¹' s = e '' s := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy
        exact ⟨e.symm y, hy, by simp⟩
      · rintro ⟨z, hz, rfl⟩
        simp [hz]
    rw [hpre]
    exact hcont.isClosedMap s hs
  ⟨e, hcont, hcontInv⟩

/-- The exponential homeomorphism sends the basepoint `0` to `1`. -/
private lemma addCircleHomeomorphCircle_zero :
    addCircleHomeomorphCircle ((0 : ℝ) : AddCircle (2 * Real.pi)) = 1 := by
  rw [QuotientAddGroup.mk_zero]
  change (addCircleAddEquiv (0 : AddCircle (2 * Real.pi))).toMul = 1
  rw [map_zero]
  rfl

/-- The fundamental groups of the two circles are isomorphic, via the
exponential homeomorphism. -/
private noncomputable def fundamentalGroupCircleMulEquiv :
    FundamentalGroup (AddCircle (2 * Real.pi)) ((0 : ℝ) : AddCircle (2 * Real.pi)) ≃*
      FundamentalGroup Circle (1 : Circle) := by
  let eqv := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    addCircleHomeomorphCircle.toHomotopyEquiv
  let ff : eqv.functor.FullyFaithful := eqv.fullyFaithfulFunctor
  have hobj : eqv.functor.obj
      (FundamentalGroupoid.mk ((0 : ℝ) : AddCircle (2 * Real.pi))) =
      FundamentalGroupoid.mk (1 : Circle) := by
    have h1 : eqv.functor.obj
        (FundamentalGroupoid.mk ((0 : ℝ) : AddCircle (2 * Real.pi))) =
        FundamentalGroupoid.mk
          (addCircleHomeomorphCircle ((0 : ℝ) : AddCircle (2 * Real.pi))) :=
      rfl
    rw [h1, addCircleHomeomorphCircle_zero]
  change CategoryTheory.End (FundamentalGroupoid.mk ((0 : ℝ) : AddCircle (2 * Real.pi))) ≃*
    CategoryTheory.End (FundamentalGroupoid.mk (1 : Circle))
  exact hobj ▸ CategoryTheory.Functor.FullyFaithful.mulEquivEnd ff
    (FundamentalGroupoid.mk ((0 : ℝ) : AddCircle (2 * Real.pi)))

end Pi1Circle

set_option linter.dupNamespace false in
/- The fundamental group of the complex unit circle is infinite cyclic. -/
/-- **The fundamental group of the circle is infinite cyclic.** The fundamental group of the unit
circle in $\mathbb{C}$ based at $1$ is isomorphic, as a group, to the additive group $\mathbb{Z}$.

Source: Classical theorem in algebraic topology. Via leanprover/lean-eval@38361be, problem
`pi1_circle_mulEquiv_int`. -/
public theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  exact ⟨HomotopyGroup.pi1MulEquivFundamentalGroup.trans
    (Pi1Circle.fundamentalGroupCircleMulEquiv.symm.trans
      (AddCircle.windingNumberIso ((0 : ℝ) : AddCircle (2 * Real.pi))))⟩

end Topology

end MathlibExt.Topology.HomotopyGroupsWanted
