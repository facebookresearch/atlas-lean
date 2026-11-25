/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGodementCoresolution
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleDerivedHomSectionsComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AcyclicResolution

/-!
# Original étale cohomology computed by the actual Godement complex

The canonical coaugmentation is a quasi-isomorphism and every actual degree
term is acyclic for positive right-derived global sections. The native
acyclic-resolution comparison therefore computes the original groups.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Global sections applied to the actual alternating Godement complex. -/
def smallEtaleGodementSectionsComplex (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    CochainComplex AddCommGrpCat.{max u w} ℕ :=
  ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (smallEtaleGodementCochainComplex.{u, w} X Q)

/-- Native right-derived global sections are the homology of the actual Godement complex. -/
def smallEtaleGodementDerivedSectionsIso (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).obj Q ≅
      (smallEtaleGodementSectionsComplex.{u, w} X Q).homology n := by
  let K := smallEtaleGodementCochainComplex.{u, w} X Q
  let ι := smallEtaleGodementCochainCoaugmentation.{u, w} X Q
  let : QuasiIso ι := smallEtaleGodementCochainCoaugmentation_quasiIso.{u, w} X Q
  exact
      (Sheaf.Γ X.smallEtaleTopology
        AddCommGrpCat.{max u w}).rightDerivedObjIsoHomologyOfAcyclicResolution
    K ι (fun q j => smallEtaleGodementCoresolutionTerm_derivedSections_succ_isZero.{u, w} X Q q j) n

/-- The original étale cohomology group is computed by the genuine Godement resolution. -/
def smallEtaleGodementCohomologyAddEquiv (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    Sheaf.H.{max u w, max u w, u, u + 1} Q n ≃+
      (smallEtaleGodementSectionsComplex.{u, w} X Q).homology n :=
  (OriginalGammaBridge.originalComparison.{u, w} X Q n).trans
    (smallEtaleGodementDerivedSectionsIso.{u, w} X Q n).addCommGroupIsoToAddEquiv

end AlgebraicGeometry.Scheme.DerivedSections
