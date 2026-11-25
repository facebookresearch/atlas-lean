/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.ExteriorPower.RankOneSplitting

/-!
# Exterior powers after adjoining a free rank-one summand

Each exterior power of `M × R` splits into the exterior power of `M` and
the exterior power one degree lower. Inclusion, projection, contraction by
the last coordinate and left exterior multiplication by its basis vector
give the two maps. The inverse identities preserve this order and its signs.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace exteriorPower

universe u v

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The original projection/contraction coordinates on an exterior power
of M × R. -/
def productOneDecompose (n : ℕ) :
    (⋀[R]^(n + 1) (M × R)) →ₗ[R] (⋀[R]^(n + 1) M) × (⋀[R]^n M) :=
  (map (n + 1) (LinearMap.fst R M R)).prod
    ((map n (LinearMap.fst R M R)).comp
      (contractLeft R (M × R) (LinearMap.snd R M R) n))

@[simp]
theorem productOneDecompose_apply (n : ℕ) (z : ⋀[R]^(n + 1) (M × R)) :
    productOneDecompose R M n z =
      (map (n + 1) (LinearMap.fst R M R) z,
        map n (LinearMap.fst R M R)
          (contractLeft R (M × R) (LinearMap.snd R M R) n z)) := rfl

/-- Assemble the original inclusion and the wedge of the last basis
vector, with that vector on the left. -/
def productOneAssemble (n : ℕ) :
    ((⋀[R]^(n + 1) M) × (⋀[R]^n M)) →ₗ[R] (⋀[R]^(n + 1) (M × R)) :=
  (map (n + 1) (LinearMap.inl R M R)).comp (LinearMap.fst R _ _) +
    (wedgeLeft R (M × R) (0, 1) n).comp
      ((map n (LinearMap.inl R M R)).comp (LinearMap.snd R _ _))

@[simp]
theorem productOneAssemble_apply (n : ℕ)
    (a : ⋀[R]^(n + 1) M) (b : ⋀[R]^n M) :
    productOneAssemble R M n (a, b) =
      map (n + 1) (LinearMap.inl R M R) a +
        wedgeLeft R (M × R) (0, 1) n (map n (LinearMap.inl R M R) b) := rfl

/-- The last-coordinate contraction is fixed by the original complement
projection in every degree. -/
theorem productOneComplement_contractLeft (n : ℕ) (z : ⋀[R]^(n + 1) (M × R)) :
    map n ((LinearMap.inl R M R).comp (LinearMap.fst R M R))
        (contractLeft R (M × R) (LinearMap.snd R M R) n z) =
      contractLeft R (M × R) (LinearMap.snd R M R) n z := by
  apply Subtype.ext
  rw [coe_map, contractLeft_apply_coe,
    ← ExteriorAlgebra.rankOneComplement_prod]
  exact ExteriorAlgebra.map_rankOneComplement_contractLeft R (M × R)
    (LinearMap.snd R M R) (0, 1) z

/-- Assembly after decomposition is the identity on the actual exterior
power, using the proved rank-one exterior identity. -/
theorem productOneAssemble_decompose (n : ℕ) (z : ⋀[R]^(n + 1) (M × R)) :
    productOneAssemble R M n (productOneDecompose R M n z) = z := by
  rw [productOneDecompose_apply, productOneAssemble_apply]
  rw [← LinearMap.comp_apply, ← map_comp,
    ← LinearMap.comp_apply (map n (LinearMap.inl R M R)), ← map_comp,
    productOneComplement_contractLeft, ← ExteriorAlgebra.rankOneComplement_prod]
  exact map_rankOneComplement_add_wedge_contract R (M × R)
    (LinearMap.snd R M R) (0, 1) n z

/-- Decomposition after assembly retains both original coordinates. -/
theorem productOneDecompose_assemble (n : ℕ)
    (a : ⋀[R]^(n + 1) M) (b : ⋀[R]^n M) :
    productOneDecompose R M n (productOneAssemble R M n (a, b)) = (a, b) := by
  rw [productOneAssemble_apply, productOneDecompose_apply]
  apply Prod.ext
  · apply Subtype.ext
    simp only [map_add, Submodule.coe_add, coe_map, wedgeLeft_apply_coe]
    rw [map_mul, ExteriorAlgebra.map_apply_ι]
    simp only [LinearMap.fst_apply, map_zero, zero_mul, add_zero]
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, LinearMap.fst_comp_inl,
      ExteriorAlgebra.map_id]
    rfl
  · apply Subtype.ext
    simp only [map_add, Submodule.coe_add, coe_map, contractLeft_apply_coe,
      wedgeLeft_apply_coe]
    rw [CliffordAlgebra.contractLeft_ι_mul]
    have ha := ExteriorAlgebra.contractLeft_map_eq_zero R (M × R)
      (LinearMap.snd R M R) (LinearMap.inl R M R) (by rfl)
      (a : ExteriorAlgebra R M)
    have hb := ExteriorAlgebra.contractLeft_map_eq_zero R (M × R)
      (LinearMap.snd R M R) (LinearMap.inl R M R) (by rfl)
      (b : ExteriorAlgebra R M)
    simp only [ha, hb, LinearMap.snd_apply, one_smul, mul_zero, sub_zero,
      map_zero, zero_add]
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, LinearMap.fst_comp_inl,
      ExteriorAlgebra.map_id]
    rfl

/-- The exterior-power splitting after adjoining a free rank-one summand, with explicit inverse maps. -/
def productOneEquiv (n : ℕ) :
    (⋀[R]^(n + 1) (M × R)) ≃ₗ[R] (⋀[R]^(n + 1) M) × (⋀[R]^n M) :=
  LinearEquiv.ofLinearMap (productOneDecompose R M n) (productOneAssemble R M n)
    (by apply LinearMap.ext; rintro ⟨a, b⟩; exact productOneDecompose_assemble R M n a b)
    (by apply LinearMap.ext; intro z; exact productOneAssemble_decompose R M n z)

end exteriorPower
