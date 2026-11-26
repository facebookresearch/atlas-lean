/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleBaseChange
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Left extension of affine étale presheaves

Let f : X → Y be a morphism of schemes in universe u and put c = max(u, w).
The functor G_f : AffineEtale(Y) → Etale(X) sends an affine étale Y-scheme U
to X ×_Y U. Its values need not be affine. For an abelian-group presheaf
P on AffineEtale(Y) with coefficients in universe c, left Kan extension
along G_fᵒᵖ gives an abelian-group presheaf on Etale(X).

At V ∈ Etale(X), the extension is the colimit of P(U) over arrows
V → G_f(U), indexed by the opposite affine-comparison category.
These indexing categories are essentially small in universe c, so their
colimits exist in AddCommGrpCat c for every f, P and V.
The colimit formula specifies restriction maps and maps of presheaves;
the extension is left adjoint to precomposition by G_fᵒᵖ.

Milne, Lectures on Étale Cohomology, §8, p. 60, describes presheaf inverse
image using these comma diagrams; the affine-basis size argument uses
§7, p. 51.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- For a scheme morphism f : X → Y, the functor
G_f : AffineEtale(Y) → Etale(X) first regards an affine étale Y-scheme
U as an étale object and then takes X ×_Y U. The resulting étale X-scheme
is not required to be affine. -/
abbrev smallEtaleAffineBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.AffineEtale ⥤ X.Etale :=
  Scheme.AffineEtale.Spec Y ⋙ smallEtaleBaseChange f

/-- For a scheme Y in universe u and an independent universe w, the
category AffineEtale(Y) is essentially small in c = max(u, w):
it is equivalent to a category whose objects and morphisms lie in
that common universe. -/
theorem smallEtaleAffineCommonEssentiallySmall (Y : Scheme.{u}) :
    EssentiallySmall.{max u w} Y.AffineEtale := by
  let e := equivSmallModel.{u} Y.AffineEtale
  exact EssentiallySmall.mk'
    (e.trans
      (AsSmall.equiv : SmallModel.{u} Y.AffineEtale ≌
        AsSmall.{w} (SmallModel.{u} Y.AffineEtale)))

private instance commonAffineSmall (Y : Scheme.{u}) :
    EssentiallySmall.{max u w} Y.AffineEtale :=
  smallEtaleAffineCommonEssentiallySmall.{u, w} Y

/-- For a scheme morphism f : X → Y and V ∈ Etale(X), this is the
category of pairs (U, a), where U ∈ AffineEtale(Y) and a : V → X ×_Y U
is a morphism of étale X-schemes. A morphism is an affine étale map
U → U′ whose base change takes a to a′. -/
abbrev smallEtaleAffineStructuredComma {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) :=
  StructuredArrow V (smallEtaleAffineBaseChange f)

/-- For a scheme morphism f : X → Y and V ∈ Etale(X), this comma
category indexes presheaf extension at V. Its objects correspond to
U ∈ AffineEtale(Y) and arrows a : V → X ×_Y U. Its arrow direction
is opposite to that of the structured-arrow category of these pairs,
so an affine presheaf can be evaluated on it covariantly. -/
abbrev smallEtaleAffineComma {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) :=
  CostructuredArrow (smallEtaleAffineBaseChange f).op (op V)

/-- For schemes X, Y in universe u, a morphism f : X → Y, V ∈ Etale(X),
and an independent universe w, the category of affine comparison arrows
V → X ×_Y U is essentially small in max(u, w). No restriction on
the morphism f is imposed. -/
theorem smallEtaleAffineStructuredCommaEssentiallySmall
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) :
    EssentiallySmall.{max u w} (smallEtaleAffineStructuredComma f V) := by
  infer_instance

/-- For schemes X, Y in universe u, a morphism f : X → Y, V ∈ Etale(X),
and an independent universe w, the comma category indexing arrows
V → X ×_Y U with the presheaf arrow direction is essentially small
in max(u, w). -/
theorem smallEtaleAffineCommaEssentiallySmall
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) :
    EssentiallySmall.{max u w} (smallEtaleAffineComma f V) := by
  infer_instance

/-- Let f : X → Y be a scheme morphism, V ∈ Etale(X), and
P : AffineEtale(Y)ᵒᵖ → AddCommGrpCat max(u, w) an abelian-group presheaf.
This diagram on the affine presheaf comma category sends a comparison
arrow V → X ×_Y U to P(U), and sends a comma morphism to the corresponding
restriction map of P. -/
abbrev smallEtaleAffineCommaDiagram {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale) :=
  CostructuredArrow.proj (smallEtaleAffineBaseChange f).op (op V) ⋙ P

/-- For a scheme morphism f : X → Y with X and Y in universe u,
V ∈ Etale(X), and any universe w, AddCommGrpCat max(u, w) admits
all colimits indexed by the affine presheaf comma category at V.
The indexing category's essential smallness in max(u, w) suffices. -/
theorem smallEtaleAffineCommaHasColimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Etale) :
    HasColimitsOfShape (smallEtaleAffineComma f V) AddCommGrpCat.{max u w} := by
  let : EssentiallySmall.{max u w} (smallEtaleAffineComma f V) :=
    smallEtaleAffineCommaEssentiallySmall.{u, w} f V
  exact hasColimitsOfShape_of_essentiallySmall.{max u w} _ _

/-- For a scheme morphism f : X → Y and an abelian-group presheaf
P on AffineEtale(Y) with coefficients in c = max(u, w), a pointwise
left Kan extension along G_fᵒᵖ exists, where G_f(U) = X ×_Y U.
At V ∈ Etale(X), it is the colimit of P(U) over the affine comparison
arrows V → G_f(U). -/
theorem smallEtaleAffineHasPointwiseLeftKanExtension
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    (smallEtaleAffineBaseChange f).op.HasPointwiseLeftKanExtension P := by
  intro V
  let : HasColimitsOfShape
      (CostructuredArrow (smallEtaleAffineBaseChange f).op V)
      AddCommGrpCat.{max u w} :=
    smallEtaleAffineCommaHasColimits.{u, w} f V.unop
  infer_instance

instance smallEtaleAffineCommaColimit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etaleᵒᵖ) :
    HasColimit (CostructuredArrow.proj (smallEtaleAffineBaseChange f).op V ⋙ P) := by
  let : HasColimitsOfShape
      (CostructuredArrow (smallEtaleAffineBaseChange f).op V)
      AddCommGrpCat.{max u w} :=
    smallEtaleAffineCommaHasColimits.{u, w} f V.unop
  infer_instance

instance smallEtaleAffineLeftKanExtension
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    (smallEtaleAffineBaseChange f).op.HasLeftKanExtension P := by
  let : (smallEtaleAffineBaseChange f).op.HasPointwiseLeftKanExtension P :=
    smallEtaleAffineHasPointwiseLeftKanExtension.{u, w} f P
  exact Functor.HasLeftKanExtension.mk
    ((smallEtaleAffineBaseChange f).op.pointwiseLeftKanExtension P)
    ((smallEtaleAffineBaseChange f).op.pointwiseLeftKanExtensionUnit P)

/-- For a scheme morphism f : X → Y, this functor sends abelian-group
presheaves on AffineEtale(Y) to abelian-group presheaves on Etale(X),
with all coefficients in c = max(u, w). It is left Kan extension
along G_fᵒᵖ for G_f(U) = X ×_Y U; its value at V is the comma colimit
of P(U) over arrows V → G_f(U). -/
def smallEtaleAffinePresheafLan {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) ⥤
      (X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :=
  (smallEtaleAffineBaseChange f).op.lan (H := AddCommGrpCat.{max u w})

/-- For a scheme morphism f : X → Y and coefficients in c = max(u, w),
this is the unit η of affine presheaf left extension. For every affine
presheaf P, it is the natural map
P → (Lan_(G_fᵒᵖ) P) ∘ G_fᵒᵖ, where G_f(U) = X ×_Y U. -/
def smallEtaleAffinePresheafLanUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    𝟭 (Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) ⟶
      smallEtaleAffinePresheafLan.{u, w} f ⋙
        (Functor.whiskeringLeft Y.AffineEtaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{max u w}).obj
          (smallEtaleAffineBaseChange f).op :=
  (smallEtaleAffineBaseChange f).op.lanUnit (H := AddCommGrpCat.{max u w})

/-- For a scheme morphism f : X → Y and abelian-group coefficients
in c = max(u, w), left Kan extension along
G_fᵒᵖ : AffineEtale(Y)ᵒᵖ → Etale(X)ᵒᵖ is left adjoint to precomposition
by G_fᵒᵖ, where G_f(U) = X ×_Y U. -/
def smallEtaleAffinePresheafLanAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleAffinePresheafLan.{u, w} f ⊣
      (Functor.whiskeringLeft Y.AffineEtaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{max u w}).obj
        (smallEtaleAffineBaseChange f).op :=
  (smallEtaleAffineBaseChange f).op.lanAdjunction AddCommGrpCat.{max u w}

/-- For a scheme morphism f : X → Y, an affine abelian-group presheaf
P with coefficients in c = max(u, w), and V ∈ Etale(X), this cocone
has vertex (Lan_(G_fᵒᵖ) P)(V). Its leg at a : V → G_f(U) is the unit
P(U) → (Lan P)(G_f(U)) followed by restriction along a. -/
def smallEtaleAffinePresheafLanCocone {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale) :
    Cocone (smallEtaleAffineCommaDiagram.{u, w} f P V) :=
  (Functor.LeftExtension.mk ((smallEtaleAffinePresheafLan.{u, w} f).obj P)
    ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P)).coconeAt (op V)

/-- For a scheme morphism f : X → Y, an affine abelian-group presheaf
P with coefficients in c = max(u, w), and V ∈ Etale(X), the cocone
with vertex (Lan_(G_fᵒᵖ) P)(V) and legs given by the Kan unit followed
by restriction along V → G_f(U) is a colimit cocone. -/
def smallEtaleAffinePresheafLanIsColimit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale) :
    IsColimit (smallEtaleAffinePresheafLanCocone.{u, w} f P V) :=
  (smallEtaleAffineBaseChange f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit P (op V)

/-- For a scheme morphism f : X → Y, an affine abelian-group presheaf
P with coefficients in c = max(u, w), and V ∈ Etale(X), this is the
canonical isomorphism (Lan_(G_fᵒᵖ) P)(V) ≅ colim_(V→G_f(U)) P(U).
Here G_f(U) = X ×_Y U and the colimit uses the presheaf comma direction. -/
def smallEtaleAffinePresheafLanObjIsoColimit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale) :
    ((smallEtaleAffinePresheafLan.{u, w} f).obj P).obj (op V) ≅
      colimit (smallEtaleAffineCommaDiagram.{u, w} f P V) :=
  (smallEtaleAffineBaseChange f).op.leftKanExtensionObjIsoColimit P (op V)

/-- For a scheme morphism f : X → Y, an affine abelian-group presheaf P,
V ∈ Etale(X), and a comma object j given by a : V → G_f(U), let
χ_V : (Lan P)(V) ≅ colim P(U) be the colimit comparison, with coefficients
in c = max(u, w). The composite χ_V⁻¹ ∘ ι_j is restriction along a
after the Kan unit η_U : P(U) → (Lan P)(G_f(U)). -/
theorem smallEtaleAffinePresheafLan_ι_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale)
    (j : smallEtaleAffineComma f V) :
    colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V) j ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).inv =
      ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P).app j.left ≫
        ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map j.hom := by
  exact (smallEtaleAffineBaseChange f).op.ι_leftKanExtensionObjIsoColimit_inv P (op V) j

/-- For a scheme morphism f : X → Y, an affine abelian-group presheaf P,
V ∈ Etale(X), and a : V → G_f(U), let χ_V be the comparison from
(Lan P)(V) to its comma colimit, with coefficients in c = max(u, w).
Then χ_V ∘ restriction(a) ∘ η_U is the colimit inclusion ι_(U,a). -/
theorem smallEtaleAffinePresheafLan_ι_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale)
    (j : smallEtaleAffineComma f V) :
    ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P).app j.left ≫
        ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map j.hom ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).hom =
      colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V) j := by
  exact (smallEtaleAffineBaseChange f).op.ι_leftKanExtensionObjIsoColimit_hom P (op V) j

/-- For a scheme morphism f : X → Y, an affine abelian-group presheaf P
with coefficients in c = max(u, w), and g : V → W in Etale(X),
restriction from (Lan P)(W) to (Lan P)(V) sends the comma inclusion
indexed by a : W → G_f(U) to the inclusion indexed by a ∘ g.
The equality uses the colimit comparisons at W and V. -/
theorem smallEtaleAffinePresheafLan_restriction_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w})
    {V W : X.Etale} (g : V ⟶ W) (j : smallEtaleAffineComma f W) :
    colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P W) j ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P W).inv ≫
        ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map g.op ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).hom =
      colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V)
        ((CostructuredArrow.map g.op).obj j) := by
  have h :
      ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P).app j.left ≫
          ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map (j.hom ≫ g.op) ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).hom =
        colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V)
          ((CostructuredArrow.map g.op).obj j) :=
    smallEtaleAffinePresheafLan_ι_hom.{u, w} f P V ((CostructuredArrow.map g.op).obj j)
  rw [← Category.assoc, smallEtaleAffinePresheafLan_ι_inv.{u, w} f P W j]
  simpa only [Functor.map_comp, Category.assoc] using h

/-- For a scheme morphism f : X → Y, a morphism α : P → P′ of affine
abelian-group presheaves with coefficients in c = max(u, w), and V ∈ Etale(X),
the extension map at V sends the inclusion of P(U) indexed by
a : V → G_f(U) to the inclusion of P′(U) composed with α_U.
The equality identifies both extension values with their comma colimits. -/
theorem smallEtaleAffinePresheafLan_map_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {P P' : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}} (α : P ⟶ P')
    (V : X.Etale) (j : smallEtaleAffineComma f V) :
    colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V) j ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).inv ≫
        ((smallEtaleAffinePresheafLan.{u, w} f).map α).app (op V) ≫
        (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P' V).hom =
      α.app j.left ≫ colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P' V) j := by
  have hUnit :
      ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P).app j.left ≫
          ((smallEtaleAffinePresheafLan.{u, w} f).map α).app
            ((smallEtaleAffineBaseChange f).op.obj j.left) =
        α.app j.left ≫ ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P').app j.left :=
    (congr_app ((smallEtaleAffinePresheafLanUnit.{u, w} f).naturality α) j.left).symm
  rw [← Category.assoc, smallEtaleAffinePresheafLan_ι_inv.{u, w} f P V j]
  rw [Category.assoc,
    ((smallEtaleAffinePresheafLan.{u, w} f).map α).naturality_assoc j.hom]
  rw [← Category.assoc, hUnit]
  simpa only [Category.assoc] using congrArg (fun k => α.app j.left ≫ k)
    (smallEtaleAffinePresheafLan_ι_hom.{u, w} f P' V j)

/-- For a scheme morphism f : X → Y, an affine abelian-group presheaf
P on Y and an abelian-group presheaf Q on Etale(X), both with coefficients
in c = max(u, w), this is the natural equivalence
Hom(Lan_(G_fᵒᵖ) P, Q) ≃ Hom(P, Q ∘ G_fᵒᵖ),
where G_f(U) = X ×_Y U. -/
def smallEtaleAffinePresheafLanHomEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w})
    (Q : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    ((smallEtaleAffinePresheafLan.{u, w} f).obj P ⟶ Q) ≃
      (P ⟶ (smallEtaleAffineBaseChange f).op ⋙ Q) :=
  (smallEtaleAffinePresheafLanAdjunction.{u, w} f).homEquiv P Q

/-- For every scheme morphism f : X → Y in universe u and
c = max(u, w), the affine comma categories at all V ∈ Etale(X) are
essentially c-small and their colimits exist in AddCommGrpCat c.
The left extension of every affine abelian-group presheaf is presented
by its comma colimit cocone and is left adjoint to precomposition by G_fᵒᵖ.
The comparison sends the Kan-unit restriction at V → G_f(U) to the
corresponding colimit inclusion, restriction along g : V → W replaces
a : W → G_f(U) by a ∘ g, and a presheaf morphism acts on each inclusion
by its component at U. -/
theorem original_small_etale_affine_presheaf_left_extension
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ V : X.Etale,
      EssentiallySmall.{max u w} (smallEtaleAffineStructuredComma f V) ∧
      EssentiallySmall.{max u w} (smallEtaleAffineComma f V) ∧
      HasColimitsOfShape (smallEtaleAffineComma f V) AddCommGrpCat.{max u w}) ∧
    (∀ (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale),
      Nonempty (IsColimit (smallEtaleAffinePresheafLanCocone.{u, w} f P V))) ∧
    Nonempty (smallEtaleAffinePresheafLan.{u, w} f ⊣
      (Functor.whiskeringLeft Y.AffineEtaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{max u w}).obj
        (smallEtaleAffineBaseChange f).op) ∧
    (∀ (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (V : X.Etale)
        (j : smallEtaleAffineComma f V),
      ((smallEtaleAffinePresheafLanUnit.{u, w} f).app P).app j.left ≫
          ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map j.hom ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).hom =
        colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V) j) ∧
    (∀ (P : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w})
        (V W : X.Etale) (g : V ⟶ W) (j : smallEtaleAffineComma f W),
      colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P W) j ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P W).inv ≫
          ((smallEtaleAffinePresheafLan.{u, w} f).obj P).map g.op ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).hom =
        colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V)
          ((CostructuredArrow.map g.op).obj j)) ∧
    ∀ (P P' : Y.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (α : P ⟶ P')
      (V : X.Etale) (j : smallEtaleAffineComma f V),
      colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P V) j ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P V).inv ≫
          ((smallEtaleAffinePresheafLan.{u, w} f).map α).app (op V) ≫
          (smallEtaleAffinePresheafLanObjIsoColimit.{u, w} f P' V).hom =
        α.app j.left ≫ colimit.ι (smallEtaleAffineCommaDiagram.{u, w} f P' V) j := by
  refine ⟨?_, ?_, ⟨smallEtaleAffinePresheafLanAdjunction.{u, w} f⟩, ?_, ?_, ?_⟩
  · intro V
    exact ⟨smallEtaleAffineStructuredCommaEssentiallySmall.{u, w} f V,
      smallEtaleAffineCommaEssentiallySmall.{u, w} f V,
      smallEtaleAffineCommaHasColimits.{u, w} f V⟩
  · intro P V
    exact ⟨smallEtaleAffinePresheafLanIsColimit.{u, w} f P V⟩
  · intro P V j
    exact smallEtaleAffinePresheafLan_ι_hom.{u, w} f P V j
  · intro P V W g j
    exact smallEtaleAffinePresheafLan_restriction_ι.{u, w} f P g j
  · intro P P' α V j
    exact smallEtaleAffinePresheafLan_map_ι.{u, w} f α V j

end AlgebraicGeometry.Scheme.DerivedSections
