/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AdicDerivedContracts

@[expose] public noncomputable section

/-!
# The derived adjunction and the derived global-section comparison on the pro-étale site

For a morphism of schemes `f : Y ⟶ X` and sheaves of `R`-modules on the small pro-étale sites:

* derived inverse image `Lf^*` (computed degreewise, since inverse image is exact) is left adjoint
  to derived direct image `Rf_*`, with unit on every complex the composite of the underived unit
  and the derived units (`DerivedAdjunction`);
* derived global sections of `Rf_* K` are derived global sections of `K`, compatibly with the
  underived identification `Γ(X, f_* F) = Γ(Y, F)` (`GlobalSectionsPushforward`): direct image
  preserves injectives, being right adjoint to the exact inverse image.

The composition of derived inverse images (`DerivedPullbackPasting`) is already constructed.

References: Stacks Project, Tag 07A6 (the adjunction `Lf^* ⊣ Rf_*` for ringed topoi) and Tag 0D6E
(derived direct images compose; global sections are direct image to a point); Bhatt--Scholze,
*The pro-étale topology for schemes*, §5.
-/

namespace WantedExt.AlgebraicGeometry.AdicDerivedComparisonsWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AdicDerivedContracts

/-- The adjunction `Lf^* ⊣ Rf_*` with the expected unit. -/
public def_wanted derivedAdjunction (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) :
    DerivedAdjunction R f

/-- `RΓ(X, Rf_* -) ≅ RΓ(Y, -)`, compatible with the underived identification. -/
public def_wanted globalSectionsPushforward (R : Type) [CommRing R] {Y X : Scheme.{0}}
    (f : Y ⟶ X) : GlobalSectionsPushforward R f

end WantedExt.AlgebraicGeometry.AdicDerivedComparisonsWanted
