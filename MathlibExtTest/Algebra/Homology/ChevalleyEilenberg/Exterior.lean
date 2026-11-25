/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Exterior
public import Mathlib.Data.ZMod.Basic

/-!
# Clients of the canonical CE exterior boundary

The generic clients require no freeness, projectivity, or chosen differential.
A nonabelian torsion Lie algebra over the integers checks that the degree-two
boundary can be nonzero while its square vanishes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace MathlibExtTest.Algebra.Homology.ChevalleyEilenberg.Exterior

section ArbitraryLieAlgebras

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

example : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  (ChevalleyEilenberg.canonicalChainData R L).complex

example (n : ℕ) :
    (ChevalleyEilenberg.differential R L n).comp
        (ChevalleyEilenberg.differential R L (n + 1)) = 0 :=
  ChevalleyEilenberg.differential_comp_differential R L n

example (x y z : L) :
    ChevalleyEilenberg.boundary R L
        ((ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y) *
          ExteriorAlgebra.ι R z) =
      -(ExteriorAlgebra.ι R ⁅x, y⁆ * ExteriorAlgebra.ι R z) +
        ExteriorAlgebra.ι R ⁅x, z⁆ * ExteriorAlgebra.ι R y -
        ExteriorAlgebra.ι R ⁅y, z⁆ * ExteriorAlgebra.ι R x :=
  ChevalleyEilenberg.boundary_ι_mul_ι_mul_ι R L x y z

/-- error: -/
#guard_msgs (error, substring := true) in
#synth Module.Free R L

end ArbitraryLieAlgebras

section NonabelianTorsion

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev V := ZMod 4 × ZMod 4
private abbrev L := Module.End ℤ V

private def upper : L := (LinearMap.inl ℤ (ZMod 4) (ZMod 4)).comp
  (LinearMap.snd ℤ (ZMod 4) (ZMod 4))

private def lower : L := (LinearMap.inr ℤ (ZMod 4) (ZMod 4)).comp
  (LinearMap.fst ℤ (ZMod 4) (ZMod 4))

private theorem bracket_ne_zero : ⁅upper, lower⁆ ≠ 0 := by
  intro hz
  have hv := LinearMap.congr_fun hz ((1, 0) : V)
  change upper (lower (1, 0)) - lower (upper (1, 0)) = 0 at hv
  have h1 := congrArg Prod.fst hv
  simp only [upper, lower, LinearMap.comp_apply, LinearMap.inl_apply,
    LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    Prod.fst_sub, sub_zero, Prod.fst_zero] at h1
  have hne : (1 : ZMod 4) ≠ 0 := by decide
  exact hne h1

-- The negative-bracket boundary is nonzero even over a torsion ℤ-module.
example :
    ChevalleyEilenberg.boundary ℤ L
        (ExteriorAlgebra.ι ℤ upper * ExteriorAlgebra.ι ℤ lower) ≠ 0 := by
  rw [ChevalleyEilenberg.boundary_ι_mul_ι, neg_ne_zero]
  intro hz
  exact bracket_ne_zero
    ((ExteriorAlgebra.ι_eq_zero_iff (R := ℤ) (⁅upper, lower⁆ : L)).mp hz)

-- Square-zero is derived from the Lie bracket; no ChainData is supplied.
example (a : ExteriorAlgebra ℤ L) :
    ChevalleyEilenberg.boundary ℤ L (ChevalleyEilenberg.boundary ℤ L a) = 0 :=
  ChevalleyEilenberg.boundary_squared ℤ L a

end NonabelianTorsion

#print axioms ChevalleyEilenberg.boundary
#print axioms ChevalleyEilenberg.boundary_squared
#print axioms ChevalleyEilenberg.differential
#print axioms ChevalleyEilenberg.canonicalChainData
#print axioms ChevalleyEilenberg.differential_naturality

end MathlibExtTest.Algebra.Homology.ChevalleyEilenberg.Exterior
