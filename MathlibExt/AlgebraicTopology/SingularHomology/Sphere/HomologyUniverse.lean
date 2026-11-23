/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.UnivLE
public import MathlibExt.AlgebraicTopology.SingularHomology.DiskPair
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerGrading

/-!
# Sphere and disk-pair homology across universes

This file packages the existing sphere and classical disk-pair calculations
for a topology universe `w` and an additive-group coefficient universe `u`.
The universe inequality supplies the large coproducts used by singular chains.
No new sphere or disk orientation is chosen: the diagonal coordinates are the
existing recursive sphere and disk-pair coordinates, and integer grading is
obtained through the established natural-to-integer comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicTopology

variable [UnivLE.{w, u}]

noncomputable local instance sphereHomologyUniverseAB4OfSize :
    AB4OfSize.{w} AddCommGrpCat.{u} := by
  let _ : HasFilteredColimitsOfSize.{w, w} AddCommGrpCat.{u} :=
    hasFilteredColimitsOfSize_of_univLE
  let _ : UnivLE.{u, u} := inferInstance
  let _ : AB5OfSize.{w, w} AddCommGrpCat.{u} :=
    AB5OfSize_of_univLE.{w, w, u, u} AddCommGrpCat.{u}
  let _ : HasFiniteBiproducts AddCommGrpCat.{u} :=
    Abelian.hasFiniteBiproducts
  exact AB4.of_AB5 AddCommGrpCat.{u}

/-- The accepted reduced-sphere coordinate at independent topology and
coefficient universes. -/
noncomputable def reducedSphereHomologyIsoOfUnivLE
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    reducedSingularHomology AddCommGrpCat.{u} R n
        (TopCat.sphere.{w} n) ≅ R :=
  reducedSphereHomologyIso R n

/-- Reduced sphere homology vanishes off the diagonal at independent topology
and coefficient universes.  The proof uses the existing zero-sphere,
suspension, and path-connectedness providers. -/
theorem isZero_reducedSphereHomology_of_ne_of_univLE
    (R : AddCommGrpCat.{u}) (n k : ℕ) (hkn : k ≠ n) :
    IsZero (reducedSingularHomology AddCommGrpCat.{u} R k
      (TopCat.sphere.{w} n)) := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => exact absurd rfl hkn
      | succ j =>
          have hk : Nat.succ j ≠ 0 := Nat.succ_ne_zero j
          have hOrd : IsZero
              (((singularHomologyFunctor AddCommGrpCat.{u} (Nat.succ j)).obj R).obj
                (TopCat.sphere.{w} 0)) := by
            have : TotallyDisconnectedSpace ↑(TopCat.sphere.{w} 0) :=
              inferInstance
            exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
              AddCommGrpCat.{u} (Nat.succ j) R (TopCat.sphere.{w} 0) hk
          have e :
              reducedSingularHomology AddCommGrpCat.{u} R (Nat.succ j)
                  (TopCat.sphere.{w} 0) ≅
                ((singularHomologyFunctor AddCommGrpCat.{u} (Nat.succ j)).obj R).obj
                  (TopCat.sphere.{w} 0) :=
            (reducedSingularHomologyFunctorIso AddCommGrpCat.{u} R
              (Nat.succ j) hk).app (TopCat.sphere.{w} 0)
          exact hOrd.of_iso e
  | succ n ih =>
      cases k with
      | zero =>
          have : PathConnectedSpace ↑(TopCat.sphere.{w} (Nat.succ n)) :=
            pathConnectedSpace_sphere (Nat.succ n) (Nat.succ_ne_zero n)
          exact isZero_reducedSingularHomologyZero_of_pathConnectedSpace
            AddCommGrpCat.{u} R (TopCat.sphere.{w} (Nat.succ n))
      | succ j =>
          have hjn : j ≠ n := by
            intro h
            exact hkn (congrArg Nat.succ h)
          exact (ih j hjn).of_iso
            (reducedSphereSuspensionIso
              (C := AddCommGrpCat.{u}) R n j)

/-- Ordinary sphere homology vanishes away from degree zero and the sphere
dimension at independent topology and coefficient universes. -/
theorem isZero_sphereHomology_of_ne_of_univLE
    (R : AddCommGrpCat.{u}) (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    IsZero (((singularHomologyFunctor AddCommGrpCat.{u} k).obj R).obj
      (TopCat.sphere.{w} n)) := by
  have hRed : IsZero
      (reducedSingularHomology AddCommGrpCat.{u} R k
        (TopCat.sphere.{w} n)) :=
    isZero_reducedSphereHomology_of_ne_of_univLE R n k hkn
  exact hRed.of_iso
    ((reducedSingularHomologyFunctorIso AddCommGrpCat.{u} R k hk).app
      (TopCat.sphere.{w} n)).symm

end AlgebraicTopology

namespace Topology.CWComplex

variable [UnivLE.{w, u}]

noncomputable local instance diskPairHomologyUniverseAB4OfSize :
    AB4OfSize.{w} AddCommGrpCat.{u} := by
  let _ : HasFilteredColimitsOfSize.{w, w} AddCommGrpCat.{u} :=
    hasFilteredColimitsOfSize_of_univLE
  let _ : UnivLE.{u, u} := inferInstance
  let _ : AB5OfSize.{w, w} AddCommGrpCat.{u} :=
    AB5OfSize_of_univLE.{w, w, u, u} AddCommGrpCat.{u}
  let _ : HasFiniteBiproducts AddCommGrpCat.{u} :=
    Abelian.hasFiniteBiproducts
  exact AB4.of_AB5 AddCommGrpCat.{u}

/-- The accepted natural-graded classical disk-pair coordinate at independent
topology and coefficient universes. -/
noncomputable def classicalCellDiskPairRelativeHomologyIsoOfUnivLE
    (R : AddCommGrpCat.{u}) (d : ℕ) :
    R ≅
      (AlgebraicTopology.relativeSingularHomologyFunctor
        AddCommGrpCat.{u} R d).obj (classicalCellDiskPair.{w} d) :=
  classicalCellDiskPairRelativeHomologyIso R d

/-- Relative homology of a classical disk pair vanishes away from the disk
dimension at independent topology and coefficient universes. -/
theorem isZero_relativeSingularHomology_classicalCellDiskPair_of_ne_of_univLE
    (R : AddCommGrpCat.{u}) (d k : ℕ) (hk : k ≠ d) :
    IsZero
      ((AlgebraicTopology.relativeSingularHomologyFunctor
        AddCommGrpCat.{u} R k).obj (classicalCellDiskPair.{w} d)) := by
  match d, k with
  | 0, k =>
      exact isZero_relativeSingularHomology_classicalCellDiskPair_zero_of_ne_zero
        AddCommGrpCat.{u} R k hk
  | d + 1, 0 =>
      exact AlgebraicTopology.isZero_relativeSingularHomologyZero_of_pathConnectedSpace
        AddCommGrpCat.{u} R (classicalCellDiskPair.{w} (d + 1)) inferInstance
  | d + 1, k + 1 =>
      have hkd : k ≠ d := fun h => hk (congrArg Nat.succ h)
      have hSphere : IsZero
          (AlgebraicTopology.reducedSingularHomology AddCommGrpCat.{u} R k
            (TopCat.sphere.{w} d)) :=
        AlgebraicTopology.isZero_reducedSphereHomology_of_ne_of_univLE
          R d k hkd
      have hBoundary : IsZero
          (AlgebraicTopology.reducedSingularHomology AddCommGrpCat.{u} R k
            (classicalCellDiskPair.{w} (d + 1)).snd) :=
        hSphere.of_iso
          (AlgebraicTopology.homeoReducedHomologyIso R k
            (classicalCellBoundarySphereHomeomorph.{w} d))
      exact hBoundary.of_iso
        (AlgebraicTopology.relativeSingularHomologyReducedIsoOfContractibleAmbient
          AddCommGrpCat.{u} R (classicalCellDiskPair.{w} (d + 1)) k)

/-- The accepted integer-graded classical disk-pair coordinate.  Its
normalization is exactly the natural-graded coordinate followed by the inverse
of the established natural-to-integer comparison. -/
noncomputable def classicalCellDiskPairRelativeHomologyIntIso
    (R : AddCommGrpCat.{u}) (d : ℕ) :
    R ≅
      (AlgebraicTopology.relativeSingularHomologyIntFunctor
        AddCommGrpCat.{u} R (d : ℤ)).obj
          (classicalCellDiskPair.{w} d) :=
  classicalCellDiskPairRelativeHomologyIsoOfUnivLE R d ≪≫
    ((AlgebraicTopology.relativeSingularHomologyNatToIntIso
      AddCommGrpCat.{u} R d).app (classicalCellDiskPair.{w} d)).symm

/-- The integer-graded disk coordinate returns to the accepted natural-graded
coordinate under the canonical comparison. -/
theorem classicalCellDiskPairRelativeHomologyIntIso_hom_comp_natToInt
    (R : AddCommGrpCat.{u}) (d : ℕ) :
    (classicalCellDiskPairRelativeHomologyIntIso.{w} R d).hom ≫
        (AlgebraicTopology.relativeSingularHomologyNatToIntIso
          AddCommGrpCat.{u} R d).hom.app (classicalCellDiskPair.{w} d) =
      (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{w} R d).hom := by
  simp [classicalCellDiskPairRelativeHomologyIntIso]

/-- Integer-graded relative homology of a classical disk pair vanishes away
from the disk dimension, including all negative degrees. -/
theorem isZero_relativeSingularHomologyInt_classicalCellDiskPair_of_ne_of_univLE
    (R : AddCommGrpCat.{u}) (d : ℕ) (k : ℤ) (hk : k ≠ (d : ℤ)) :
    IsZero
      ((AlgebraicTopology.relativeSingularHomologyIntFunctor
        AddCommGrpCat.{u} R k).obj (classicalCellDiskPair.{w} d)) := by
  by_cases hk0 : k < 0
  · exact AlgebraicTopology.isZero_relativeSingularHomologyIntFunctor_of_neg
      AddCommGrpCat.{u} R k hk0 (classicalCellDiskPair.{w} d)
  · have hkNonneg : 0 ≤ k := le_of_not_gt hk0
    have hkNat : k.toNat ≠ d := by
      intro h
      apply hk
      rw [← Int.toNat_of_nonneg hkNonneg, h]
    have hNat :=
      isZero_relativeSingularHomology_classicalCellDiskPair_of_ne_of_univLE.{w, u}
        R d k.toNat hkNat
    have e :=
      (AlgebraicTopology.relativeSingularHomologyNatToIntIso
        AddCommGrpCat.{u} R k.toNat).app (classicalCellDiskPair.{w} d)
    have hkCast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hkNonneg
    rw [hkCast] at e
    exact hNat.of_iso e

end Topology.CWComplex

end
