/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Inner horn lifting with a prescribed base simplex

An inner fibration lifts a compatible family of inner-horn faces over
an exactly specified simplex in its base. The result records both all
prescribed source faces and the complete base equation.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

/-- Relative simplex-level inner filler against an inner fibration: an
inner horn presented as a compatible family of face maps, together with
a base simplex extending the image family, lifts to the total space.
This is the quasicategory `horn.IsCompatible.exists_lift_of_quasicategory`
(`CoreKan.lean`) relativized over an inner fibration via
`SSet.innerFibration_iff`. -/
theorem horn.IsCompatible.exists_lift_of_innerFibration
    {X S : SSet.{u}} {n : ℕ} {i : Fin (n + 2)}
    {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X}
    (p : X ⟶ S) [InnerFibration p]
    (h0 : 0 < i) (hn : i < Fin.last (n + 1)) (hf : horn.IsCompatible f)
    (t : Δ[n + 1] ⟶ S)
    (ht : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      stdSimplex.δ j ≫ t = f j hj ≫ p) :
    ∃ φ : Δ[n + 1] ⟶ X,
      (∀ (j : Fin (n + 2)) (hj : j ≠ i),
        stdSimplex.δ j ≫ φ = f j hj) ∧ φ ≫ p = t := by
  have hlp : HasLiftingProperty Λ[n + 1, i].ι p :=
    InnerFibration.mem _ (horn_ι_mem_innerHornInclusions h0 hn)
  have sq : CommSq hf.desc Λ[n + 1, i].ι p t := by
    refine CommSq.mk (horn.hom_ext' fun j hj ↦ ?_)
    rw [← Category.assoc, hf.ι_desc, ← Category.assoc, horn.ι_ι]
    exact (ht j hj).symm
  obtain ⟨φ, hφhorn, hφbase⟩ := hlp.sq_hasLift sq
  refine ⟨φ, fun j hj ↦ ?_, hφbase⟩
  calc stdSimplex.δ j ≫ φ
      = horn.ι i j hj ≫ Λ[n + 1, i].ι ≫ φ := by
        rw [← horn.ι_ι, Category.assoc]
    _ = horn.ι i j hj ≫ hf.desc := by rw [hφhorn]
    _ = f j hj := hf.ι_desc j hj

end SSet
