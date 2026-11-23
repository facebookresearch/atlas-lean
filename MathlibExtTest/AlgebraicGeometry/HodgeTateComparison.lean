/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.HodgeTateComparison

/-!
# Tests for the Galois actions of the Hodge–Tate comparison

The completed action on `C_p` extends the action on the algebraic closure and is a group
homomorphism; the Tate scalar in Hodge degree zero is trivial, and the Hodge-side operators
form a semilinear left action.
-/

open MathlibExt.AlgebraicGeometry.HodgeTateComparison
open CategoryTheory AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- On algebraic elements the completed action is the original Galois action. -/
example (σ : Galois p) (x : PadicAlgCl p) :
    completionGaloisHom p σ (x : PadicComplex p) = ((σ x : PadicAlgCl p) : PadicComplex p) :=
  completionGalois_coe p σ x

/-- The completed action is multiplicative and unital. -/
example (σ τ : Galois p) :
    completionGaloisHom p (σ * τ) = completionGaloisHom p σ * completionGaloisHom p τ :=
  map_mul _ σ τ

example : completionGaloisHom p 1 = 1 := map_one _

/-- The Tate twist is trivial in Hodge degree zero. -/
example (σ : Galois p) : tateScalar p σ 0 = 1 := by simp [tateScalar]

/-- The Tate scalars are multiplicative in the Galois element. -/
example (σ τ : Galois p) (i : ℕ) :
    tateScalar p (σ * τ) i = tateScalar p σ i * tateScalar p τ i :=
  tateScalar_mul p σ τ i

variable (X : Over (Spec (CommRingCat.of.{0} ℚ_[p])))

/-- The Hodge-side operators form a semilinear left action. -/
example (σ τ : Galois p) (n : ℕ) (a : CompletedHodge p X n) :
    completedHodgeGalois p X (σ * τ) n a =
      completedHodgeGalois p X σ n (completedHodgeGalois p X τ n a) := by
  rw [completedHodgeGalois_mul, LinearMap.comp_apply]

example (n : ℕ) (a : CompletedHodge p X n) : completedHodgeGalois p X 1 n a = a := by
  rw [completedHodgeGalois_one, LinearMap.id_apply]

example (σ : Galois p) (n : ℕ) (c : PadicComplex p) (a : CompletedHodge p X n) :
    completedHodgeGalois p X σ n (c • a) =
      completionGalois p σ c • completedHodgeGalois p X σ n a :=
  completedHodgeGalois_smul p X σ n c a

/-- The completed étale operators are semilinear. -/
example (σ : Galois p) (n : ℕ) (c : PadicComplex p) (a : CompletedEtale p X n) :
    completedEtaleGalois p X σ n (c • a) =
      completionGalois p σ c • completedEtaleGalois p X σ n a :=
  completedEtaleGalois_smul p X σ n c a
