/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.WedgeVec

@[expose] public section

universe u

/-- `mulVec` appends a vector to a wedge. -/
example (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (a b c : M) :
    exteriorPower.mulVec R M 2 (exteriorPower.ιMulti R 2 ![a, b]) c =
      exteriorPower.ιMulti R 3 (Fin.append ![a, b] fun _ : Fin 1 => c) :=
  exteriorPower.mulVec_ιMulti R M 2 ![a, b] c

/-- `mulVec` is Mathlib's wedge product `exteriorPower.wedge R M n 1`, with the vector read in
`⋀¹ M`. -/
example (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (n : ℕ)
    (x : ⋀[R]^n M) (m : M) :
    exteriorPower.mulVec R M n x m =
      exteriorPower.wedge R M n 1 x ((exteriorPower.oneEquiv R M).symm m) :=
  rfl

/-- The wedge of two decomposable vectors appends their families. -/
example (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (a b c : M) :
    exteriorPower.wedge R M 2 1 (exteriorPower.ιMulti R 2 ![a, b]) (exteriorPower.ιMulti R 1 ![c]) =
      exteriorPower.ιMulti R 3 (Fin.append ![a, b] ![c]) :=
  exteriorPower.wedge_ιMulti_ιMulti R M ![a, b] ![c]

/-- Wedging a vector with itself gives zero. -/
example (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (a : M) :
    exteriorPower.mulVec R M 1 (exteriorPower.ιMulti R 1 ![a]) a = 0 := by
  rw [exteriorPower.mulVec_ιMulti]
  exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) (by rfl) (by decide)
