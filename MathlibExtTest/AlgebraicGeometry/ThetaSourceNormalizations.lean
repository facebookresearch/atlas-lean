/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ThetaQuotientOpenSources
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Tactic.NormNum

/-!
# Filtration source normalization checks

The node charts preserve a nonzero square-zero trait parameter. The
contracting action uses its actual homogeneous coaction. A groupoid
with one isomorphism class and nontrivial stabilizers fails the unique
groupoid-filler condition.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.ThetaSourceNormalizations

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.ThetaQuotientSources
open MathlibExt.AlgebraicGeometry.StackSourceFiltrations

open scoped TensorProduct

abbrev Dual := TrivSqZeroExt ℚ ℚ

def epsilon : Dual := TrivSqZeroExt.inr 1

example : epsilon ≠ 0 := by
  intro h
  have hs := congrArg TrivSqZeroExt.snd h
  norm_num [epsilon] at hs

example : epsilon * epsilon = 0 := by
  simp [epsilon]

def firstNodePoint : NodeRing Dual epsilon →+* Dual :=
  Ideal.Quotient.lift (nodeIdeal Dual epsilon)
    (MvPolynomial.eval₂Hom (RingHom.id Dual) (fun i : Fin 2 => if i = 0 then 1 else epsilon))
    (by
      change nodeIdeal Dual epsilon ≤ RingHom.ker
        (MvPolynomial.eval₂Hom (RingHom.id Dual)
          (fun i : Fin 2 => if i = 0 then 1 else epsilon))
      rw [nodeIdeal, Ideal.span_le]
      rintro a rfl
      change MvPolynomial.eval₂ (RingHom.id Dual)
        (fun i : Fin 2 => if i = 0 then 1 else epsilon)
        (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C epsilon) = 0
      simp)

example : firstNodePoint (nodeS Dual epsilon) = 1 := by
  simp [firstNodePoint, nodeS]

example : firstNodePoint (nodeT Dual epsilon) = epsilon := by
  simp [firstNodePoint, nodeT]

example : ¬ HasUniqueGroupoidFiller (A := SingleObj (Multiplicative ℤ)) := by
  rintro ⟨e⟩
  have h : (Multiplicative.ofAdd 0 : Multiplicative ℤ) = Multiplicative.ofAdd 1 := by
    apply e.functor.map_injective
      (X := SingleObj.star (Multiplicative ℤ)) (Y := SingleObj.star (Multiplicative ℤ))
    exact Subsingleton.elim _ _
  have hz : (0 : ℤ) = 1 := congrArg Multiplicative.toAdd h
  norm_num at hz

end MathlibExtTest.AlgebraicGeometry.ThetaSourceNormalizations
