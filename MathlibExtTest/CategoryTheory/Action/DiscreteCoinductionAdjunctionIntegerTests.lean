/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Action.DiscreteCoinductionAdjunction
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
meta import Mathlib.Tactic.NormNum

/-!
# Concrete unit, counit and transpose values for discrete coinduction

A discrete order-two group acts trivially on the integers. The actual adjunction unit sends
three to the constant coinduced function three, and its counit recovers three. Transposing
the coefficient map multiplication by two gives value six. A second, nonconstant coinduced
function takes values four and seven; the counit selects its identity value four.
-/

open CategoryTheory CategoryTheory.DiscreteAbelianAction

noncomputable section
set_option autoImplicit false

namespace DiscreteCoinductionAdjunctionIntegerTests

private abbrev G := Multiplicative (ZMod 2)
private instance : TopologicalSpace G := ⊥
private instance : DiscreteTopology G := ⟨rfl⟩
private instance : TopologicalSpace ℤ := ⊥
private instance : DiscreteTopology ℤ := ⟨rfl⟩
private abbrev M : AddCommGrpCat := AddCommGrpCat.of ℤ
private abbrev A : DiscreteAbelianAction.{0, 0} G := trivialObject G M
private abbrev C0 := coind.{0, 0}.obj (trivialObject G M)
private abbrev adj := forgetCoindAdjunction.{0, 0} G
private def s : G := Multiplicative.ofAdd (1 : ZMod 2)
private lemma s_ne_one : s ≠ 1 := by decide

private def unitThree : underlying C0 := homToAdd (adj.unit.app A) (3 : ℤ)

private lemma unit_value (g : G) : coindFunction (trivialObject G M) unitThree g = 3 :=
  (forgetCoindAdjunction_unit_apply G A (3 : ℤ) g).trans
    (trivialObject_smul G M g⁻¹ (3 : ℤ))

example : coindFunction (trivialObject G M) unitThree s = 3 := unit_value s

example : (adj.counit.app M).hom unitThree = (3 : ℤ) := by
  rw [forgetCoindAdjunction_counit_apply]
  exact unit_value 1

private def double : (forget G).obj A ⟶ M :=
  AddCommGrpCat.ofHom
    { toFun := fun x : ℤ => 2 * x
      map_zero' := by simp
      map_add' := fun x y => mul_add (2 : ℤ) x y }

private def transposed : A ⟶ C0 := forgetCoindTranspose G A M double

example : coindFunction (trivialObject G M) (homToAdd transposed (3 : ℤ)) s = 6 := by
  rw [forgetCoindTranspose_apply G A M double (3 : ℤ) s,
    trivialObject_smul G M s⁻¹ (3 : ℤ)]
  rfl

example : (forgetCoindEvaluate G A M transposed).hom (3 : ℤ) = 6 := by
  have h := congrArg (fun f : (forget G).obj A ⟶ M => f.hom (3 : ℤ))
    (forgetCoindEvaluate_transpose G A M double)
  exact h.trans (by rfl)

private def varying : underlying C0 :=
  (show C(G, ℤ) from
    ⟨fun g => if g = 1 then (4 : ℤ) else 7, continuous_of_discreteTopology⟩)

example : (adj.counit.app M).hom varying = (4 : ℤ) := by
  rw [forgetCoindAdjunction_counit_apply]
  change (if (1 : G) = 1 then (4 : ℤ) else 7) = 4
  rw [if_pos rfl]

private lemma varying_value : coindFunction (trivialObject G M) varying s = 7 := by
  change (if s = 1 then (4 : ℤ) else 7) = 7
  rw [if_neg s_ne_one]

example : coindFunction (trivialObject G M) varying s = 7 := varying_value

example : varying ≠ 0 := by
  intro h
  have he := congrArg (fun f : underlying C0 => coindFunction (trivialObject G M) f s) h
  rw [varying_value, coindFunction_zero] at he
  exact (by norm_num : (7 : ℤ) ≠ 0) he

end DiscreteCoinductionAdjunctionIntegerTests
