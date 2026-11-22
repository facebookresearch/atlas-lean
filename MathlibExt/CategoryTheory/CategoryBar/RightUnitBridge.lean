/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.ElementsComparison
public import MathlibExt.CategoryTheory.CategoryBar.UnitElementsBridge

/-!
# Right-unit coefficient bridge and comparison triangle

From unit replacement `simplicialReplacement (unitCoeffL C)`, the bar route
first applies `replUnitBarSimplicialIso` to the two-sided unit bar and then
`barNerveUnitSimplicialIso` to the nerve, while the elements route first applies
`replNerveSimplicialIso` to the nerve of elements and then
`unitElementsNerveIso` to the nerve. The triangle states both composites agree.

Nonclaims: no generic coefficient iso promotion, no index-naturality square, no
comma/Grothendieck comparison, no opposite/reversal comparison, no contraction,
no homotopy, and no KQ result.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v

namespace CategoryTheory

namespace CategoryBar

/-- Right-unit coefficient isomorphism from plain to lifted unit coefficients. -/
noncomputable def replUnitIsoUnitCoeffR (C : Type u) [Category.{v} C] :
    replUnit C ≅ unitCoeffR C :=
  NatIso.ofComponents
    (fun X =>
      (Equiv.mk (fun _ => ULift.up PUnit.unit) (fun _ => PUnit.unit)
        (fun x => Subsingleton.elim _ _) (fun x => Subsingleton.elim _ _)).toIso)
    (by
      intro X Y f
      ext x
      have hSub : Subsingleton ((unitCoeffR C).obj Y) := by
        change Subsingleton (ULift.{0} PUnit)
        infer_instance
      exact @Subsingleton.elim _ hSub _ _)

/-- Data-level right-unit bridge from replacement to the two-sided unit bar. -/
noncomputable def replUnitBarDataIso (C : Type u) [Category.{v} C] :
    simplicialReplacementData (unitCoeffL C) ≅
      categoryBarData (R := unitCoeffR C) (L := unitCoeffL C) :=
  SimplicialObject.Data.isoOfIso
    (fun n =>
      Equiv.toIso
        ⟨barCoeffMap (replUnitIsoUnitCoeffR C).hom (𝟙 (unitCoeffL C)),
          barCoeffMap (replUnitIsoUnitCoeffR C).inv (𝟙 (unitCoeffL C)),
          fun x => by
            obtain ⟨F, l, r⟩ := x
            refine Sigma.ext rfl (heq_of_eq ?_)
            have hSub :
                Subsingleton
                  ((unitCoeffL C).obj F.left × (replUnit C).obj (op F.right)) := by
              change Subsingleton (ULift.{0} PUnit × PUnit)
              infer_instance
            exact @Subsingleton.elim _ hSub _ _,
          fun x => by
            obtain ⟨F, l, r⟩ := x
            refine Sigma.ext rfl (heq_of_eq ?_)
            have hSub :
                Subsingleton
                  ((unitCoeffL C).obj F.left × (unitCoeffR C).obj (op F.right)) := by
              change Subsingleton (ULift.{0} PUnit × ULift.{0} PUnit)
              infer_instance
            exact @Subsingleton.elim _ hSub _ _⟩)
    (fun {n} i => by
      ext x
      exact (barCoeffMap_δ (replUnitIsoUnitCoeffR C).hom (𝟙 (unitCoeffL C)) i x).symm)
    (fun {n} i => by
      ext x
      exact (barCoeffMap_σ (replUnitIsoUnitCoeffR C).hom (𝟙 (unitCoeffL C)) i x).symm)

/-- Simplicial-set right-unit bridge from replacement to the two-sided unit bar. -/
noncomputable def replUnitBarSimplicialIso (C : Type u) [Category.{v} C] :
    simplicialReplacement (unitCoeffL C) ≅
      categoryBar (R := unitCoeffR C) (L := unitCoeffL C) :=
  SimplicialObject.Data.toSimplicialFunctor.mapIso (replUnitBarDataIso C)

/-- The bar and elements routes from unit replacement to the nerve agree. -/
theorem replUnit_comparison_triangle (C : Type u) [Category.{v} C] :
    (replUnitBarSimplicialIso C).hom ≫ (barNerveUnitSimplicialIso C).hom =
      (replNerveSimplicialIso (unitCoeffL C)).hom ≫
        (unitElementsNerveIso C).hom := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  obtain ⟨F, l, r⟩ := x
  rfl

end CategoryBar

end CategoryTheory
