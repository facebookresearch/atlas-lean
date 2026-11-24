/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.BasicLogGeometricGhosts

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.BasicLogGeometricGhosts
open MathlibExt.AlgebraicGeometry.LogCurveFamilies

namespace BasicLogGeometricGhostsTest

/-- The categorical product `ℕ²` of the node chart. -/
abbrev NatSquare : CommMonCat.{1} := prod NatMonoid NatMonoid

/-- The point `(a, b)` of `ℕ²`. -/
def pair (a b : ℕ) : NatSquare :=
  prod.lift (smoothingMap NatMonoid (ULift.up (Multiplicative.ofAdd a)))
    (smoothingMap NatMonoid (ULift.up (Multiplicative.ofAdd b)))
    (ULift.up (Multiplicative.ofAdd 1))

theorem fst_pair (a b : ℕ) :
    (prod.fst : NatSquare ⟶ NatMonoid) (pair a b) =
      ULift.up (Multiplicative.ofAdd a) := by
  change ((prod.lift (smoothingMap NatMonoid (ULift.up (Multiplicative.ofAdd a)))
      (smoothingMap NatMonoid (ULift.up (Multiplicative.ofAdd b))) ≫ prod.fst :
        NatMonoid ⟶ NatMonoid)) (ULift.up (Multiplicative.ofAdd 1)) = _
  rw [prod.lift_fst]
  apply ULift.ext
  simp [smoothingMap]

theorem snd_pair (a b : ℕ) :
    (prod.snd : NatSquare ⟶ NatMonoid) (pair a b) =
      ULift.up (Multiplicative.ofAdd b) := by
  change ((prod.lift (smoothingMap NatMonoid (ULift.up (Multiplicative.ofAdd a)))
      (smoothingMap NatMonoid (ULift.up (Multiplicative.ofAdd b))) ≫ prod.snd :
        NatMonoid ⟶ NatMonoid)) (ULift.up (Multiplicative.ofAdd 1)) = _
  rw [prod.lift_snd]
  apply ULift.ext
  simp [smoothingMap]

/-- The contact map on `ℕ²` is `(a, b) ↦ b - a`. -/
theorem branchDifference_pair (a b : ℕ) :
    branchDifference (pair a b) = ULift.up (Multiplicative.ofAdd ((b : ℤ) - a)) := by
  change natNegative ((prod.fst : NatSquare ⟶ NatMonoid) (pair a b)) *
    natPositive ((prod.snd : NatSquare ⟶ NatMonoid) (pair a b)) = _
  rw [fst_pair, snd_pair]
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  change -(a : ℤ) + b = b - a
  ring

/-- The first branch generator `(1, 0)` has contact `-1`. -/
example : branchDifference (pair 1 0) = ULift.up (Multiplicative.ofAdd (-1)) := by
  rw [branchDifference_pair]; norm_num

/-- The second branch generator `(0, 1)` has contact `+1`. -/
example : branchDifference (pair 0 1) = ULift.up (Multiplicative.ofAdd 1) := by
  rw [branchDifference_pair]; norm_num

/-- The diagonal, the direction of the smoothing parameter, has contact `0`. -/
example (a : ℕ) : branchDifference (pair a a) = 1 := by
  rw [branchDifference_pair, sub_self]; rfl

/-- The node contact map kills `Q` and is `b - a` on the `ℕ²` summand. -/
example (Q : CommMonCat.{1}) (rho : Q) :
    pushout.inl _ _ ≫ nodeDifference Q rho = CommMonCat.ofHom 1 :=
  pushout.inl_desc ..

example (Q : CommMonCat.{1}) (rho : Q) (a b : ℕ) :
    nodeDifference Q rho (pushout.inr (smoothingMap Q rho) diagonalNat (pair a b)) =
      ULift.up (Multiplicative.ofAdd ((b : ℤ) - a)) := by
  change ((pushout.inr (smoothingMap Q rho) diagonalNat ≫ nodeDifference Q rho :
      NatSquare ⟶ _)) (pair a b) = _
  rw [show pushout.inr _ _ ≫ nodeDifference Q rho = branchDifference from pushout.inr_desc ..]
  exact branchDifference_pair a b

/-- The first branch generization sends `(a, b)` to `ρ ^ a`, the second to
`ρ ^ b`; with the contact order `b - a` this fixes the branch order. -/
example (Q : CommMonCat.{1}) (rho : Q) (a b : ℕ) :
    nodeBranch1 Q rho (pushout.inr (smoothingMap Q rho) diagonalNat (pair a b)) = rho ^ a := by
  change ((pushout.inr (smoothingMap Q rho) diagonalNat ≫ nodeBranch1 Q rho :
      NatSquare ⟶ _)) (pair a b) = _
  rw [show pushout.inr _ _ ≫ nodeBranch1 Q rho = prod.fst ≫ smoothingMap Q rho
    from pushout.inr_desc ..]
  change smoothingMap Q rho ((prod.fst : NatSquare ⟶ NatMonoid) (pair a b)) = _
  rw [fst_pair]
  simp [smoothingMap]

example (Q : CommMonCat.{1}) (rho : Q) (a b : ℕ) :
    nodeBranch2 Q rho (pushout.inr (smoothingMap Q rho) diagonalNat (pair a b)) = rho ^ b := by
  change ((pushout.inr (smoothingMap Q rho) diagonalNat ≫ nodeBranch2 Q rho :
      NatSquare ⟶ _)) (pair a b) = _
  rw [show pushout.inr _ _ ≫ nodeBranch2 Q rho = prod.snd ≫ smoothingMap Q rho
    from pushout.inr_desc ..]
  change smoothingMap Q rho ((prod.snd : NatSquare ⟶ NatMonoid) (pair a b)) = _
  rw [snd_pair]
  simp [smoothingMap]

/-- Both branch generizations restrict to the identity on `Q`. -/
example (Q : CommMonCat.{1}) (rho : Q) : pushout.inl _ _ ≫ nodeBranch1 Q rho = 𝟙 Q :=
  pushout.inl_desc ..

example (Q : CommMonCat.{1}) (rho : Q) : pushout.inl _ _ ≫ nodeBranch2 Q rho = 𝟙 Q :=
  pushout.inl_desc ..

end BasicLogGeometricGhostsTest
