/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Quadratic coefficient certificates for literal source representative words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialP1Operator

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Addition of coefficient matrices adds their actual binary quadratic polynomials. -/
theorem representativeQuadratic_add_matrix (M N : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (t : SpinIndex) :
    monsterMonomialQuadratic (M + N) t =
      monsterMonomialQuadratic M t + monsterMonomialQuadratic N t := by
  simp [monsterMonomialQuadratic, mul_add, Finset.sum_add_distrib]

/-- The quadratic polynomial is the associated matrix expression on actual binary vectors. -/
theorem representativeQuadratic_dot (M : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (t : SpinIndex) : monsterMonomialQuadratic M t = t ⬝ᵥ (M *ᵥ t) := by
  simp only [monsterMonomialQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pulling back a quadratic sign uses the ordinary congruence of coefficient matrices. -/
theorem representativeQuadratic_pullback (P M : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (t : SpinIndex) :
    monsterMonomialQuadratic (Pᵀ * M * P) t = monsterMonomialQuadratic M (P *ᵥ t) := by
  rw [representativeQuadratic_dot, representativeQuadratic_dot,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- The value on a single binary coordinate is exactly the diagonal coefficient. -/
theorem representativeQuadratic_single (M : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (i : Fin 12) : monsterMonomialQuadratic M (Pi.single i 1) = M i i := by
  classical
  simp [monsterMonomialQuadratic, Pi.single_apply]

/-- A coefficient certificate determines the full sign on all 4096 spin coordinates.
The diagonal and symmetric coefficients suffice; no full-space enumeration is assumed. -/
theorem representativeQuadratic_coefficients (M N : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hd : ∀ i, M i i = N i i)
    (hs : ∀ i j, M i j + M j i = N i j + N j i) (t : SpinIndex) :
    monsterMonomialQuadratic M t = monsterMonomialQuadratic N t := by
  have hg (a : SpinIndex) : monsterMonomialGradient M a = monsterMonomialGradient N a := by
    ext j
    simp only [monsterMonomialGradient, hs]
  let L : SpinIndex →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun a => monsterMonomialQuadratic M a - monsterMonomialQuadratic N a
      map_add' := by
        intro a b
        rw [monsterMonomialQuadratic_add, monsterMonomialQuadratic_add, hg]
        abel
      map_smul' := by
        intro c a
        have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
        obtain rfl | rfl := hc c <;> simp [monsterMonomialQuadratic] }
  have hL : L = 0 := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro i
    simp only [L, Pi.basisFun_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.zero_apply]
    rw [representativeQuadratic_single, representativeQuadratic_single, hd, sub_self]
  have hv := LinearMap.congr_fun hL t
  exact sub_eq_zero.mp hv

/-- The value on two binary basis vectors retains the symmetric cross coefficient. -/
theorem representativeQuadratic_single_add (M : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (i j : Fin 12) :
    monsterMonomialQuadratic M (Pi.single i 1 + Pi.single j 1) =
      M i i + M j j + (M i j + M j i) := by
  rw [monsterMonomialQuadratic_add, representativeQuadratic_single,
    representativeQuadratic_single]
  congr 1
  classical
  simp [spinDot, monsterMonomialGradient, Pi.single_apply]

/-- Basis and pair values certify the full quadratic sign, using only small finite checks. -/
theorem representativeQuadratic_basis_pairs (M N : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hb : ∀ i, monsterMonomialQuadratic M (Pi.single i 1) =
      monsterMonomialQuadratic N (Pi.single i 1))
    (hp : ∀ i j, monsterMonomialQuadratic M (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic N (Pi.single i 1 + Pi.single j 1)) (t : SpinIndex) :
    monsterMonomialQuadratic M t = monsterMonomialQuadratic N t := by
  have hd (i : Fin 12) : M i i = N i i := by
    simpa only [representativeQuadratic_single] using hb i
  apply representativeQuadratic_coefficients M N hd
  intro i j
  have h := hp i j
  simp only [representativeQuadratic_single_add, hd] at h
  exact add_left_cancel h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
