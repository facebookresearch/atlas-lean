/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ComponentUnionSubcomplex
import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategoryVertexLaws
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory

/-!
# Full original Hom subcomplexes of component equivalences

Select exactly the SAME original component-invertible Hom classes,
retaining their entire original simplices and operators. The actual
original enriched identity and composition maps land in these full
subcomplexes. Their inclusion formulas retain every original Hom map;
no Kan condition, weak outcome or global model certificate is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore

variable (C : Carrier.{u})

/-- The actual original component-invertibility predicate at the SAME original Hom endpoints. -/
def equivalentClass (x y : C) (a : SSet.π₀ (x ⟶[SSet.{u}] y)) : Prop :=
  @IsIso (ComponentCategory.objects.{u} C) inferInstance
    (ComponentCategory.objectOf.{u} C x) (ComponentCategory.objectOf.{u} C y) a

/-- The SAME whole original Hom component subcomplexes whose actual classes are invertible. -/
def homSubcomplex (x y : C) : (x ⟶[SSet.{u}] y).Subcomplex :=
  SSet.componentUnion (x ⟶[SSet.{u}] y) (equivalentClass C x y)

/-- Every full original selected Hom simplex, with its SAME original dimension and operator maps. -/
abbrev hom (x y : C) : SSet.{u} := homSubcomplex C x y

/-- The full actual original selected-Hom inclusion retains every original simplex literally. -/
abbrev inclusionHom (x y : C) : hom C x y ⟶ (x ⟶[SSet.{u}] y) := (homSubcomplex C x y).ι

/-- At degree zero the actual full original Hom selection is precisely original component invertibility. -/
theorem hom_zero_iff (x y : C) (a : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    a ∈ (homSubcomplex C x y).obj (op ⦋0⦌) ↔ IsIso (ComponentCategory.arrowOf C a) :=
  SSet.mem_componentUnion_zero (x ⟶[SSet.{u}] y) (equivalentClass C x y) a

private theorem identity_mem (q : SimplexCategoryᵒᵖ) (x : C) :
    (eId SSet.{u} x).app q PUnit.unit ∈ (homSubcomplex C x x).obj q := by
  apply (SSet.mem_componentUnion (x ⟶[SSet.{u}] x) (equivalentClass C x x) q _).mpr
  have hn := NatTrans.naturality_apply (eId SSet.{u} x) (⦋0⦌.const q.unop 0).op PUnit.unit
  have hi : IsIso (ComponentCategory.arrowOf C ((eId SSet.{u} x).app (op ⦋0⦌) PUnit.unit)) :=
    (congrArg IsIso (ComponentCategory.arrowOf_identity C x)).mpr inferInstance
  exact (congrArg (fun a => IsIso (ComponentCategory.arrowOf C a)) hn).mp hi

/-- The actual SAME original whole enriched identity lands in the full component-equivalence Hom. -/
def idMap (x : C) : 𝟙_ SSet.{u} ⟶ hom C x x where
  app q := ↾fun _ => ⟨(eId SSet.{u} x).app q PUnit.unit, identity_mem C q x⟩
  naturality q r f := by
    ext a
    apply Subtype.ext
    exact NatTrans.naturality_apply (eId SSet.{u} x) f PUnit.unit

private theorem composition_mem (q : SimplexCategoryᵒᵖ) (x y z : C)
    (a : (hom C x y).obj q) (b : (hom C y z).obj q) :
    (eComp SSet.{u} x y z).app q (a.val, b.val) ∈ (homSubcomplex C x z).obj q := by
  apply (SSet.mem_componentUnion (x ⟶[SSet.{u}] z) (equivalentClass C x z) q _).mpr
  let f := (⦋0⦌.const q.unop 0).op
  let a₀ := (x ⟶[SSet.{u}] y).map f a.val
  let b₀ := (y ⟶[SSet.{u}] z).map f b.val
  have ha : IsIso (ComponentCategory.arrowOf C a₀) :=
    (SSet.mem_componentUnion (x ⟶[SSet.{u}] y) (equivalentClass C x y) q a.val).mp a.property
  have hb : IsIso (ComponentCategory.arrowOf C b₀) :=
    (SSet.mem_componentUnion (y ⟶[SSet.{u}] z) (equivalentClass C y z) q b.val).mp b.property
  let _ := ha
  let _ := hb
  have he : IsIso (ComponentCategory.arrowOf C
      ((eComp SSet.{u} x y z).app (op ⦋0⦌) (a₀, b₀))) :=
    (congrArg IsIso (ComponentCategory.arrowOf_composition C a₀ b₀)).mp inferInstance
  have hn := congr($((eComp SSet.{u} x y z).naturality f)
    ((a.val, b.val) : ((x ⟶[SSet.{u}] y) ⊗ (y ⟶[SSet.{u}] z)).obj q))
  exact (congrArg (fun c => IsIso (ComponentCategory.arrowOf C c)) hn).mp he

/-- The SAME entire original enriched composition lands in the full actual component-equivalence Hom. -/
def compMap (x y z : C) : hom C x y ⊗ hom C y z ⟶ hom C x z where
  app q := ↾fun a => ⟨(eComp SSet.{u} x y z).app q (a.1.val, a.2.val), composition_mem C q x y z a.1 a.2⟩
  naturality q r f := by
    ext a
    apply Subtype.ext
    exact congr($((eComp SSet.{u} x y z).naturality f)
      ((a.1.val, a.2.val) : ((x ⟶[SSet.{u}] y) ⊗ (y ⟶[SSet.{u}] z)).obj q))

/-- The actual full selected identity reads back to the SAME whole original enriched identity. -/
theorem idMap_inclusion (x : C) : idMap C x ≫ inclusionHom C x x = eId SSet.{u} x := by
  ext q a
  rfl

/-- The actual full selected composition reads back to the SAME whole original composition and both complete Hom
inclusions. -/
theorem compMap_inclusion (x y z : C) : compMap C x y z ≫ inclusionHom C x z =
    (inclusionHom C x y ⊗ₘ inclusionHom C y z) ≫ eComp SSet.{u} x y z := rfl

end CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore
