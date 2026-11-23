/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.CGWHBaseFunctoriality
public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.CGWHHomology
public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomology

/-!
# Base-map functoriality for CGWH local-coefficient homology

This file is the thin CGWH wrapper around the corresponding one-map TopCat
homology morphism and integral local-coefficient-equivalence predicate.  The
compact-probe universe does not enter the coefficient category.

Identity and composition laws, constant-coefficient naturality, ordinary
integral homology, converses, acyclicity, and plus constructions remain
outside this file.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uR uK uX

namespace CGWH

variable {R : Type uR} [CommRing R]
variable {X Y : CGWH.{uK, uX}}

/-- The local-coefficient homology map of a CGWH morphism is the map for its
underlying TopCat morphism. -/
noncomputable abbrev localCoefficientPullbackHomologyMap
    (f : X ⟶ Y) (L : CGWH.LocalSystem R Y) (n : ℕ) :
    CGWH.localCoefficientHomology (L.pullback f) n ⟶
      CGWH.localCoefficientHomology L n :=
  TopCat.localCoefficientPullbackHomologyMap
    (CGWH.cgwhToTop.map f) L n

/-- Formula identifying the CGWH base-map homology morphism with its
underlying TopCat morphism. -/
@[simp]
theorem localCoefficientPullbackHomologyMap_eq_topCat
    (f : X ⟶ Y) (L : CGWH.LocalSystem R Y) (n : ℕ) :
    localCoefficientPullbackHomologyMap f L n =
      TopCat.localCoefficientPullbackHomologyMap
        (CGWH.cgwhToTop.map f) L n :=
  rfl

/-- The CGWH integral local-coefficient-equivalence predicate is the
corresponding predicate on the underlying TopCat morphism. -/
abbrev IsLocalCoefficientHomologyEquivalence (f : X ⟶ Y) : Prop :=
  TopCat.IsLocalCoefficientHomologyEquivalence
    (CGWH.cgwhToTop.map f)

/-- Direct quantified form of the CGWH integral local-coefficient homology
equivalence predicate. -/
theorem isLocalCoefficientHomologyEquivalence_iff (f : X ⟶ Y) :
    CGWH.IsLocalCoefficientHomologyEquivalence f ↔
      ∀ (L : CGWH.LocalSystem ℤ Y) (n : ℕ),
        IsIso (CGWH.localCoefficientPullbackHomologyMap f L n) :=
  Iff.rfl

end CGWH
