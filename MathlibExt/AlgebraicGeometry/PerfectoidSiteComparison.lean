/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import MathlibExt.AlgebraicGeometry.PerfectoidDiamondModels

/-!
# Canonical pro-etale/v-site comparison maps

The two sites have the same actual affine perfectoid objects and bounded
maps. The smaller cover rule gives a literal forgetful functor. Affine
and equivalence-relation comparisons are the fixed maps induced by
sheafification and coequalizer units. Their geometric invertibility is
separate from the completed definitions below.

Reference: Scholze, *Etale cohomology of diamonds*,
arXiv:1709.07343v4, Corollary 8.6, Theorem 8.7 and Proposition 11.9.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PerfectoidSiteComparison

open CategoryTheory CategoryTheory.Limits
open AffinePerfectoidVSite PerfectoidLocalModels PerfectoidDiamondModels

variable (p : ℕ) [Fact p.Prime]

theorem proEtale_le_v : proEtaleTopology p ≤ topology p := by
  apply sInf_le
  intro ι P U f _ h
  exact cover_mem p P U f h

abbrev ProEtaleSheaf := Sheaf (proEtaleTopology p) (Type 1)

/-- The identity on actual presheaves, with the coarser cover condition. -/
def forgetToProEtale : VSheaf p ⥤ ProEtaleSheaf p where
  obj F := ⟨F.obj, F.property.of_le (proEtale_le_v p)⟩
  map f := ⟨f.hom⟩

/-- The actual affine representable sheaf on the pro-etale basis. -/
def proEtaleAffineSheaf (P : Affine p) : ProEtaleSheaf p :=
  (presheafToSheaf (proEtaleTopology p) (Type 1)).obj
    (yoneda.obj P ⋙ liftTypes)

/-- The canonical comparison, normalized by the two sheafification units. -/
def affineComparison (P : Affine p) :
    proEtaleAffineSheaf p P ⟶
      (forgetToProEtale p).obj (affineSheaf p P) :=
  ((sheafificationAdjunction (proEtaleTopology p) (Type 1)).homEquiv
    (yoneda.obj P ⋙ liftTypes)
    ((forgetToProEtale p).obj (affineSheaf p P))).symm
      (toSheafify (topology p) (yoneda.obj P ⋙ liftTypes))

/-- The comparison preserves the specified affine sheafification unit. -/
theorem affineComparison_unit (P : Affine p) :
    toSheafify (proEtaleTopology p) (yoneda.obj P ⋙ liftTypes) ≫
      (affineComparison p P).hom =
        toSheafify (topology p) (yoneda.obj P ⋙ liftTypes) := by
  change toSheafify (proEtaleTopology p) _ ≫
    sheafifyLift (proEtaleTopology p) _ _ = _
  exact toSheafify_sheafifyLift _ _ _

/-- The actual pro-etale quotient of the fixed equivalence relation. -/
def proEtaleQuotient (R : Relation p) : ProEtaleSheaf p :=
  coequalizer ((forgetToProEtale p).map R.source)
    ((forgetToProEtale p).map R.target)

/-- The canonical quotient comparison, induced by the v-quotient unit. -/
def quotientComparison (R : Relation p) : proEtaleQuotient p R ⟶
    (forgetToProEtale p).obj (Relation.quotient p R) := by
  change coequalizer ((forgetToProEtale p).map R.source)
    ((forgetToProEtale p).map R.target) ⟶
      (forgetToProEtale p).obj (coequalizer R.source R.target)
  refine coequalizer.desc ((forgetToProEtale p).map
    (coequalizer.π R.source R.target)) ?_
  simpa only [Functor.map_comp] using
    congrArg ((forgetToProEtale p).map)
      (coequalizer.condition R.source R.target)

end MathlibExt.AlgebraicGeometry.PerfectoidSiteComparison
