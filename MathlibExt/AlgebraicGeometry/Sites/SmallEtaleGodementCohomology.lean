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
# Small étale cohomology from Godement sections

The Godement cochain coaugmentation resolves each common-universe abelian sheaf, and every
term is acyclic for positive right-derived global sections. Apply global sections termwise to
obtain an additive-group cochain complex.

Its degree-`n` cohomology is isomorphic to `R^nΓ` of the sheaf. Composing with the small étale
cohomology comparison gives an additive equivalence with `H^n(X,Q)` for every natural degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Global section complex of the Godement coresolution.

Apply common-universe global sections to the Godement cochain complex termwise. -/
def smallEtaleGodementSectionsComplex (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    CochainComplex AddCommGrpCat.{max u w} ℕ :=
  ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (smallEtaleGodementCochainComplex.{u, w} X Q)

/-- Godement section cohomology computes derived global sections.

For each sheaf and natural `n`, `R^nΓ(Q)` is isomorphic to degree-`n` cohomology of its
Godement section complex. -/
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

/-- Godement section cohomology computes small étale cohomology.

Compose the cohomology-to-derived section comparison with the Godement acyclic-resolution
isomorphism to identify `H^n(X,Q)` with the section-complex cohomology. -/
def smallEtaleGodementCohomologyAddEquiv (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    Sheaf.H.{max u w, max u w, u, u + 1} Q n ≃+
      (smallEtaleGodementSectionsComplex.{u, w} X Q).homology n :=
  (OriginalGammaBridge.originalComparison.{u, w} X Q n).trans
    (smallEtaleGodementDerivedSectionsIso.{u, w} X Q n).addCommGroupIsoToAddEquiv

end AlgebraicGeometry.Scheme.DerivedSections
