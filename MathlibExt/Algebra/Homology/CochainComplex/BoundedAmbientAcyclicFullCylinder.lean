/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicSubcategory
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientFullCylinder
public import MathlibExt.CategoryTheory.Waldhausen.Fibration.TrivialCofibration
public import MathlibExt.CategoryTheory.Waldhausen.CoproductExactFunctorIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Ambient weak equivalences and cylinders on acyclic bounded cochains

Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category, and F:E→A additive. A bounded integer cochain complex is F-acyclic when its image
under F has zero cohomology. The inherited ambient weak class consists of maps inducing
quasi-isomorphisms after F; every map between F-acyclic objects is therefore weak.

When F is exact, this full category has degreewise admissible-mono cofibrations and the
inherited ambient weak class. The signed bounded cylinder restricts to it. Its front i, back j
and projection p satisfy i_f≫p_f=f and j_f≫p_f=id. The joint boundary, relative corner, natural
zero-source charts and arrow-map properties give a full cylinder satisfying the Cylinder Axiom.

The source and ambient object and Hom universes uE,vE,uA,vA remain independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. A map in C is weak when the induced map of F-image cochain complexes
is a quasi-isomorphism. -/
def ambientAcyclicWeakEquivalences : MorphismProperty (AmbientAcyclic F) :=
  (ambientWeakEquivalences F).inverseImage (ambientAcyclicι F)

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Every map between objects of C induces a quasi-isomorphism of their
acyclic F-images, so every map is ambient weak. -/
theorem ambientAcyclicWeakEquivalences_all {X Y : AmbientAcyclic F} (f : X ⟶ Y) :
    ambientAcyclicWeakEquivalences F f := by
  let J := ι E ⋙ F.mapHomologicalComplex (.up ℤ)
  let _ : QuasiIso (J.map (0 : (0 : Bounded E) ⟶ X.obj)) :=
    (ambient_isWeakEquivalence_iff F _).mp
      ((ambientAcyclicObjects_iff_zeroWeak F X.obj 0).mp X.property)
  let _ : QuasiIso (J.map (0 : (0 : Bounded E) ⟶ Y.obj)) :=
    (ambient_isWeakEquivalence_iff F _).mp
      ((ambientAcyclicObjects_iff_zeroWeak F Y.obj 0).mp Y.property)
  have w : J.map (0 : (0 : Bounded E) ⟶ X.obj) ≫ J.map f.hom =
      J.map (0 : (0 : Bounded E) ⟶ Y.obj) := by rw [← J.map_comp, zero_comp]
  let _ : QuasiIso (J.map (0 : (0 : Bounded E) ⟶ X.obj) ≫ J.map f.hom) := by
    rw [w]
    infer_instance
  change QuasiIso (J.map f.hom)
  exact quasiIso_of_comp_left (J.map (0 : (0 : Bounded E) ⟶ X.obj)) (J.map f.hom)

variable [F.IsExact]

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. The F-acyclic object property agrees with the acyclic-object
property of the ambient quasi-isomorphism Waldhausen model on bounded complexes. -/
theorem ambientAcyclicObjects_eq_canonical :
    letI := ambientWaldhausenCategory F
    ambientAcyclicObjects F = WaldhausenCategoryWithoutGluing.acyclicObjects (C := Bounded E) := by
  let _ := ambientWaldhausenCategory F
  funext K
  exact propext ((ambientAcyclicObjects_iff_zeroWeak F K ((isZero_zero (Bounded E)).to_ K)).trans
    (WaldhausenCategoryWithoutGluing.acyclicObjects_iff_zero_to K ((isZero_zero (Bounded E)).to_ K)).symm)

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. This Waldhausen structure on
C has componentwise admissible-mono cofibrations, and every morphism is weak. -/
@[instance_reducible, no_expose]
def ambientAcyclicAmbientWaldhausenCategory : WaldhausenCategoryWithoutGluing (AmbientAcyclic F) :=
  { ambientAcyclicWaldhausenCategory F with
    weakEquivalences := ambientAcyclicWeakEquivalences F
    weakEquivalences_isMultiplicative := by
      dsimp only [ambientAcyclicWeakEquivalences, ambientWeakEquivalences]
      infer_instance
    weakEquivalences_respectsIso := by
      dsimp only [ambientAcyclicWeakEquivalences, ambientWeakEquivalences]
      infer_instance }

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. A map f:K→L in C is a
cofibration precisely when every component fᵣ:Kᵣ→Lᵣ is an admissible mono in E. -/
theorem ambientAcyclicAmbient_isCofibration_iff {X Y : AmbientAcyclic F} (f : X ⟶ Y) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    IsCofibration f ↔ ∀ j : ℤ, ExactCategory.IsAdmissibleMono (f.hom.hom.f j) :=
  ambientAcyclic_isCofibration_iff F f

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. A map f in C is weak
precisely when F applied to its underlying raw cochain map is a quasi-isomorphism. -/
theorem ambientAcyclicAmbient_isWeakEquivalence_iff {X Y : AmbientAcyclic F} (f : X ⟶ Y) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    IsWeakEquivalence f ↔ QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom.hom) := Iff.rfl

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Every map in C is a weak
equivalence in this inherited ambient model. -/
theorem ambientAcyclicAmbient_isWeakEquivalence_all {X Y : AmbientAcyclic F} (f : X ⟶ Y) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    IsWeakEquivalence f := ambientAcyclicWeakEquivalences_all F f

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. The full inclusion
J:C→Bounded(E) is Waldhausen exact for the inherited ambient weak class and componentwise
admissible cofibrations. -/
theorem ambientAcyclicAmbientι_isWaldhausenExact :
    @Functor.IsWaldhausenExact (AmbientAcyclic F) _ _ (ambientAcyclicAmbientWaldhausenCategory F)
      (Bounded E) _ _ (ambientWaldhausenCategory F) (ambientAcyclicι F) := by
  refine @Functor.IsWaldhausenExact.mk (AmbientAcyclic F) _ _
    (ambientAcyclicAmbientWaldhausenCategory F) (Bounded E) _ _
    (ambientWaldhausenCategory F) (ambientAcyclicι F) ?_ ?_ ?_ ?_
  · intro X hX
    exact (ambientAcyclicι F).map_isZero hX
  · intro X Y f hf
    exact (ambient_isCofibration_iff F f.hom).mpr
      ((ambientAcyclicAmbient_isCofibration_iff F f).mp hf)
  · intro X Y f hf
    exact (ambient_isWeakEquivalence_iff F f.hom).mpr
      ((ambientAcyclicAmbient_isWeakEquivalence_iff F f).mp hf)
  · intro X Y Z P i f inY inZ hi hP
    have hi₀ : ambientAcyclicCofibrations F i :=
      (ambientAcyclicAmbient_isCofibration_iff F i).mp hi
    exact (ambientAcyclicPushout_ι F (i := i) (f := f)
      (inY := inZ) (inZ := inY) hi₀ hP.flip).flip

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. For any arrow f:X→Y in C, its bounded cylinder has acyclic F-image, hence is again an
object of C. -/
theorem ambientAcyclicCylinderObject_acyclic (f : Arrow (AmbientAcyclic F)) :
    ambientAcyclicObjects F
      ((mappingCylinderFunctor E).obj ((ambientAcyclicι F).mapArrow.obj f)) := by
  let g := (ambientAcyclicι F).mapArrow.obj f
  let J := F.mapHomologicalComplex (.up ℤ)
  let _ : QuasiIso (J.map ((mappingCylinderProjection E).app g).hom) :=
    (ambient_isWeakEquivalence_iff F _).mp (ambientMappingCylinderProjection_isWeakEquivalence F g)
  intro j
  exact (exactAt_iff_of_quasiIsoAt (J.map ((mappingCylinderProjection E).app g).hom) j).mpr
    (f.right.property j)

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The cylinder of each arrow of C, with the cylinder maps of commuting squares, defines
a functor Arrow(C)→C. -/
def ambientAcyclicCylinderFunctor : Arrow (AmbientAcyclic F) ⥤ AmbientAcyclic F :=
  (ambientAcyclicObjects F).lift ((ambientAcyclicι F).mapArrow ⋙ mappingCylinderFunctor E)
    (ambientAcyclicCylinderObject_acyclic F)

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. Forgetting I(f) to Bounded(E) gives the signed bounded cylinder of J(f). -/
theorem ambientAcyclicCylinderFunctor_obj (f : Arrow (AmbientAcyclic F)) :
    ((ambientAcyclicCylinderFunctor F).obj f).obj =
      (mappingCylinderFunctor E).obj ((ambientAcyclicι F).mapArrow.obj f) := rfl

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. For a commuting square α:f→g in C, J(I(α)) is the bounded signed cylinder map of
J(α). -/
theorem ambientAcyclicCylinderFunctor_map {f g : Arrow (AmbientAcyclic F)} (α : f ⟶ g) :
    ((ambientAcyclicCylinderFunctor F).map α).hom =
      (mappingCylinderFunctor E).map ((ambientAcyclicι F).mapArrow.map α) := rfl

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The front maps i_f:X→I(f) form a natural transformation from arrow-source evaluation
to I. -/
def ambientAcyclicCylinderFront : Arrow.leftFunc ⟶ ambientAcyclicCylinderFunctor F where
  app f := ObjectProperty.homMk ((mappingCylinderFront E).app ((ambientAcyclicι F).mapArrow.obj f))
  naturality {f g} α := by
    apply ObjectProperty.hom_ext
    exact (mappingCylinderFront E).naturality ((ambientAcyclicι F).mapArrow.map α)

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The back maps j_f:Y→I(f) form a natural transformation from arrow-target evaluation
to I. -/
def ambientAcyclicCylinderBack : Arrow.rightFunc ⟶ ambientAcyclicCylinderFunctor F where
  app f := ObjectProperty.homMk ((mappingCylinderBack E).app ((ambientAcyclicι F).mapArrow.obj f))
  naturality {f g} α := by
    apply ObjectProperty.hom_ext
    exact (mappingCylinderBack E).naturality ((ambientAcyclicι F).mapArrow.map α)

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The projections p_f:I(f)→Y form a natural transformation from I to arrow-target
evaluation. -/
def ambientAcyclicCylinderProjection : ambientAcyclicCylinderFunctor F ⟶ Arrow.rightFunc where
  app f := ObjectProperty.homMk
    ((mappingCylinderProjection E).app ((ambientAcyclicι F).mapArrow.obj f))
  naturality {f g} α := by
    apply ObjectProperty.hom_ext
    exact (mappingCylinderProjection E).naturality ((ambientAcyclicι F).mapArrow.map α)

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. For every f:X→Y, i_f≫p_f=f. These equalities form the front/projection factorization
of the arrow transformation. -/
theorem ambientAcyclicCylinderFront_projection :
    ambientAcyclicCylinderFront F ≫ ambientAcyclicCylinderProjection F = Arrow.leftToRight := by
  apply NatTrans.ext
  funext f
  apply ObjectProperty.hom_ext
  exact congr_app (mappingCylinderFront_projection E) ((ambientAcyclicι F).mapArrow.obj f)

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. For every f:X→Y, j_f≫p_f=id_Y, naturally in commuting squares. -/
theorem ambientAcyclicCylinderBack_projection :
    ambientAcyclicCylinderBack F ≫ ambientAcyclicCylinderProjection F = 𝟙 Arrow.rightFunc := by
  apply NatTrans.ext
  funext f
  apply ObjectProperty.hom_ext
  exact congr_app (mappingCylinderBack_projection E) ((ambientAcyclicι F).mapArrow.obj f)

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. For each arrow f:X→Y of C, the front map i_f:X→I(f) is a cofibration. -/
theorem ambientAcyclicCylinderFront_isCofibration (f : Arrow (AmbientAcyclic F)) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    IsCofibration ((ambientAcyclicCylinderFront F).app f) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  exact (ambientAcyclicAmbient_isCofibration_iff F _).mpr
    ((ambient_isCofibration_iff F _).mp
      (ambientMappingCylinderFront_isCofibration F ((ambientAcyclicι F).mapArrow.obj f)))

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The cylinder functor and its natural front, back and projection maps define a
mapping-cylinder core, with i_f≫p_f=f and j_f≫p_f=id. -/
def ambientAcyclicMappingCylinderCore :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    WaldhausenMappingCylinderCore (AmbientAcyclic F) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  exact
    { functor := ambientAcyclicCylinderFunctor F
      front := ambientAcyclicCylinderFront F
      back := ambientAcyclicCylinderBack F
      projection := ambientAcyclicCylinderProjection F
      front_projection := ambientAcyclicCylinderFront_projection F
      back_projection := ambientAcyclicCylinderBack_projection F
      front_cofibration := ambientAcyclicCylinderFront_isCofibration F }

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. Each cylinder projection p_f is weak in the inherited ambient model, so the
restricted core satisfies the Cylinder Axiom. -/
theorem ambientAcyclicMappingCylinderCore_satisfiesCylinderAxiom :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    (ambientAcyclicMappingCylinderCore F).SatisfiesCylinderAxiom := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  intro f
  exact ambientAcyclicAmbient_isWeakEquivalence_all F _

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. Under J, the front i_f is the front map of the signed bounded cylinder of J(f). -/
theorem ambientAcyclicCylinderFront_hom (f : Arrow (AmbientAcyclic F)) :
    ((ambientAcyclicCylinderFront F).app f).hom =
      (mappingCylinderFront E).app ((ambientAcyclicι F).mapArrow.obj f) := rfl

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. Under J, the back j_f is the back map of the signed bounded cylinder of J(f). -/
theorem ambientAcyclicCylinderBack_hom (f : Arrow (AmbientAcyclic F)) :
    ((ambientAcyclicCylinderBack F).app f).hom =
      (mappingCylinderBack E).app ((ambientAcyclicι F).mapArrow.obj f) := rfl

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. Under J, the projection p_f is the projection of the signed bounded cylinder of J(f). -/
theorem ambientAcyclicCylinderProjection_hom (f : Arrow (AmbientAcyclic F)) :
    ((ambientAcyclicCylinderProjection F).app f).hom =
      (mappingCylinderProjection E).app ((ambientAcyclicι F).mapArrow.obj f) := rfl

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. If the source X of f:X→Y is zero, then I(f) is isomorphic to Y, with p_f as the
forward map and j_f as its inverse. -/
def ambientAcyclicCylinderZeroSourceIso (f : Arrow (AmbientAcyclic F)) (hX : IsZero f.left) :
    (ambientAcyclicCylinderFunctor F).obj f ≅ f.right :=
  (ambientAcyclicObjects F).isoMk (mappingCylinderZeroSourceIso E
    ((ambientAcyclicι F).mapArrow.obj f) ((ambientAcyclicι F).map_isZero hX))

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. For an arrow f:X→Y with X zero, the forward map I(f)≅Y is its cylinder projection
p_f. -/
theorem ambientAcyclicCylinderZeroSourceIso_hom (f : Arrow (AmbientAcyclic F))
    (hX : IsZero f.left) :
    (ambientAcyclicCylinderZeroSourceIso F f hX).hom = (ambientAcyclicCylinderProjection F).app f := by
  apply ObjectProperty.hom_ext
  exact mappingCylinderZeroSourceIso_hom E ((ambientAcyclicι F).mapArrow.obj f)
    ((ambientAcyclicι F).map_isZero hX)

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. For an arrow f:X→Y with X zero, the inverse of I(f)≅Y is its back inclusion j_f. -/
theorem ambientAcyclicCylinderZeroSourceIso_inv (f : Arrow (AmbientAcyclic F))
    (hX : IsZero f.left) :
    (ambientAcyclicCylinderZeroSourceIso F f hX).inv = (ambientAcyclicCylinderBack F).app f := by
  apply ObjectProperty.hom_ext
  exact mappingCylinderZeroSourceIso_inv E ((ambientAcyclicι F).mapArrow.obj f)
    ((ambientAcyclicι F).map_isZero hX)

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. Applying I to the selected zero arrow 0→Y is naturally isomorphic to Y. The
components are the zero-source cylinder charts. -/
def ambientAcyclicCylinderZeroNatIso :
    Waldhausen.zeroArrowFunctor ⋙ ambientAcyclicCylinderFunctor F ≅ 𝟭 (AmbientAcyclic F) :=
  NatIso.ofComponents
    (fun K => ambientAcyclicCylinderZeroSourceIso F (Waldhausen.zeroArrowFunctor.obj K)
      (Waldhausen.zeroArrowFunctor_source_isZero K))
    (fun {K L} f => by
      rw [ambientAcyclicCylinderZeroSourceIso_hom, ambientAcyclicCylinderZeroSourceIso_hom]
      exact (ambientAcyclicCylinderProjection F).naturality (Waldhausen.zeroArrowFunctor.map f))

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. On the selected arrow 0→Y, the forward normalization component is p_(0→Y):I(0→Y)→Y. -/
theorem ambientAcyclicCylinderZeroNatIso_hom :
    (ambientAcyclicCylinderZeroNatIso F).hom =
      Functor.whiskerLeft Waldhausen.zeroArrowFunctor (ambientAcyclicCylinderProjection F) := by
  apply NatTrans.ext
  funext K
  exact ambientAcyclicCylinderZeroSourceIso_hom F (Waldhausen.zeroArrowFunctor.obj K)
    (Waldhausen.zeroArrowFunctor_source_isZero K)

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. On the selected arrow 0→Y, the inverse normalization component is j_(0→Y):Y→I(0→Y). -/
theorem ambientAcyclicCylinderZeroNatIso_inv :
    (ambientAcyclicCylinderZeroNatIso F).inv =
      Functor.whiskerLeft Waldhausen.zeroArrowFunctor (ambientAcyclicCylinderBack F) := by
  apply NatTrans.ext
  funext K
  exact ambientAcyclicCylinderZeroSourceIso_inv F (Waldhausen.zeroArrowFunctor.obj K)
    (Waldhausen.zeroArrowFunctor_source_isZero K)

omit [F.IsExact] in
/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The natural charts I(0→Y)≅Y, with projection and back inclusion as their two maps,
provide the cylinder's zero-arrow normalization. -/
def ambientAcyclicCylinderNormalization :
    Waldhausen.CylinderNormalization (ambientAcyclicCylinderFunctor F)
      (ambientAcyclicCylinderBack F) (ambientAcyclicCylinderProjection F) where
  zeroNormalization := ambientAcyclicCylinderZeroNatIso F
  zeroNormalization_hom := ambientAcyclicCylinderZeroNatIso_hom F
  zeroNormalization_inv := ambientAcyclicCylinderZeroNatIso_inv F

attribute [local instance] Waldhausen.waldhausenHasBinaryCoproducts

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. The inclusion J:C→Bounded(E)
preserves the binary coproduct of any chosen pair X,Y in C. -/
theorem ambientAcyclicι_preservesPair (X Y : AmbientAcyclic F) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    letI := ambientWaldhausenCategory F
    PreservesColimit (pair X Y) (ambientAcyclicι F) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  let _ := ambientWaldhausenCategory F
  let J := ambientAcyclicι F
  let c : BinaryCofan X Y :=
    (Waldhausen.binaryCoproductColimitCocone (AmbientAcyclic F) (pair X Y)).cocone
  have hc : IsColimit c :=
    (Waldhausen.binaryCoproductColimitCocone (AmbientAcyclic F) (pair X Y)).isColimit
  have hcm : IsColimit (BinaryCofan.mk c.inl c.inr) :=
    IsColimit.ofIsoColimit hc (BinaryCofan.ext (Iso.refl _) (by simp) (by simp))
  have hm : IsColimit (BinaryCofan.mk (J.map c.inl) (J.map c.inr)) :=
    (ambientAcyclicAmbientι_isWaldhausenExact F).mappedCoproductCoconeIsColimit X Y
  exact preservesColimit_of_preserves_colimit_cocone hcm
    ((isColimitMapCoconeBinaryCofanEquiv J c.inl c.inr).symm hm)

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. There is a canonical
comparison isomorphism c:JX⊔JY≅J(X⊔Y) for each X,Y in C. -/
def ambientAcyclicCoproductIso (X Y : AmbientAcyclic F) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    letI := ambientWaldhausenCategory F
    X.obj ⨿ Y.obj ≅ (ambientAcyclicι F).obj (X ⨿ Y) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  let _ := ambientWaldhausenCategory F
  let _ := ambientAcyclicι_preservesPair F X Y
  exact PreservesColimitPair.iso (ambientAcyclicι F) X Y

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. The forward map
c:JX⊔JY→J(X⊔Y) is the coproduct comparison induced by J applied to the two source coproduct
injections. -/
theorem ambientAcyclicCoproductIso_hom (X Y : AmbientAcyclic F) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    letI := ambientWaldhausenCategory F
    (ambientAcyclicCoproductIso F X Y).hom = coprodComparison (ambientAcyclicι F) X Y := rfl

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. For f:X→Y, let ∂f:X⊔Y→I(f) have components i_f,j_f. The coproduct chart satisfies
c_(X,Y)≫J(∂f)=∂(Jf). -/
theorem ambientAcyclicCylinderBoundary_chart (f : Arrow (AmbientAcyclic F)) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    letI := ambientWaldhausenCategory F
    (ambientAcyclicCoproductIso F f.left f.right).hom ≫
      (ambientAcyclicι F).map (Waldhausen.cylinderBoundaryMap (ambientAcyclicCylinderFunctor F)
        (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) f) =
      Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor E)
        (mappingCylinderFront E) (mappingCylinderBack E) ((ambientAcyclicι F).mapArrow.obj f) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  let _ := ambientWaldhausenCategory F
  let J := ambientAcyclicι F
  let f₀ : Arrow (Bounded E) := Arrow.mk f.hom.hom
  let b : f.left ⨿ f.right ⟶ (ambientAcyclicCylinderFunctor F).obj f :=
    Waldhausen.cylinderBoundaryMap (ambientAcyclicCylinderFunctor F)
      (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) f
  let b₀ : f.left.obj ⨿ f.right.obj ⟶ (mappingCylinderFunctor E).obj f₀ :=
    Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor E)
      (mappingCylinderFront E) (mappingCylinderBack E) f₀
  change (ambientAcyclicCoproductIso F f.left f.right).hom ≫ J.map b = b₀
  rw [ambientAcyclicCoproductIso_hom]
  apply coprod.hom_ext
  · have h : coprod.inl ≫ (coprodComparison J f.left f.right ≫ J.map b) =
        J.map ((ambientAcyclicCylinderFront F).app f) := by
      calc
        coprod.inl ≫ (coprodComparison J f.left f.right ≫ J.map b) =
            ((coprod.inl : f.left.obj ⟶ f.left.obj ⨿ f.right.obj) ≫
              coprodComparison J f.left f.right) ≫ J.map b := (Category.assoc _ _ _).symm
        _ = J.map (coprod.inl : f.left ⟶ f.left ⨿ f.right) ≫ J.map b :=
          congrArg (fun t => t ≫ J.map b) (inl_coprodComparison J f.left f.right)
        _ = J.map ((coprod.inl : f.left ⟶ f.left ⨿ f.right) ≫ b) := (J.map_comp _ _).symm
        _ = J.map ((ambientAcyclicCylinderFront F).app f) := congrArg J.map
          (Waldhausen.cylinderBoundaryMap_inl _ _ _ f)
    exact h.trans ((ambientAcyclicCylinderFront_hom F f).trans
      (Waldhausen.cylinderBoundaryMap_inl _ _ _ f₀).symm)
  · have h : coprod.inr ≫ (coprodComparison J f.left f.right ≫ J.map b) =
        J.map ((ambientAcyclicCylinderBack F).app f) := by
      calc
        coprod.inr ≫ (coprodComparison J f.left f.right ≫ J.map b) =
            ((coprod.inr : f.right.obj ⟶ f.left.obj ⨿ f.right.obj) ≫
              coprodComparison J f.left f.right) ≫ J.map b := (Category.assoc _ _ _).symm
        _ = J.map (coprod.inr : f.right ⟶ f.left ⨿ f.right) ≫ J.map b :=
          congrArg (fun t => t ≫ J.map b) (inr_coprodComparison J f.left f.right)
        _ = J.map ((coprod.inr : f.right ⟶ f.left ⨿ f.right) ≫ b) := (J.map_comp _ _).symm
        _ = J.map ((ambientAcyclicCylinderBack F).app f) := congrArg J.map
          (Waldhausen.cylinderBoundaryMap_inr _ _ _ f)
    exact h.trans ((ambientAcyclicCylinderBack_hom F f).trans
      (Waldhausen.cylinderBoundaryMap_inr _ _ _ f₀).symm)

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. For every arrow f:X→Y, its joint boundary ∂f=[i_f,j_f]:X⊔Y→I(f) is a cofibration. -/
theorem ambientAcyclicCylinderBoundary_isCofibration (f : Arrow (AmbientAcyclic F)) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    IsCofibration (Waldhausen.cylinderBoundaryMap (ambientAcyclicCylinderFunctor F)
      (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) f) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  let _ := ambientWaldhausenCategory F
  let b := Waldhausen.cylinderBoundaryMap (ambientAcyclicCylinderFunctor F)
    (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) f
  let e := ambientAcyclicCoproductIso F f.left f.right
  have hb : IsCofibration (e.hom ≫ b.hom) := by
    have hChart := ambientAcyclicCylinderBoundary_chart F f
    exact hChart.symm ▸
      ambientMappingCylinderBoundary_isCofibration F ((ambientAcyclicι F).mapArrow.obj f)
  have hcomp : IsCofibration (e.inv ≫ (e.hom ≫ b.hom)) :=
    WaldhausenCategoryWithoutGluing.cofibrations.comp_mem _ _
      (WaldhausenCategoryWithoutGluing.cofibrations.of_isIso e.inv) hb
  have hBounded : IsCofibration b.hom := by
    simpa only [Iso.inv_hom_id_assoc] using hcomp
  exact (ambientAcyclicAmbient_isCofibration_iff F b).mpr
    ((ambient_isCofibration_iff F b.hom).mp hBounded)

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. If both components of a commuting square α:f→g are cofibrations, then I(α):I(f)→I(g)
is a cofibration. -/
theorem ambientAcyclicCylinder_map_isCofibration {f g : Arrow (AmbientAcyclic F)} (α : f ⟶ g) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    Waldhausen.arrowCofibrations (AmbientAcyclic F) α →
      IsCofibration ((ambientAcyclicCylinderFunctor F).map α) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  let _ := ambientWaldhausenCategory F
  intro hα
  have hα₀ : Waldhausen.arrowCofibrations (Bounded E) ((ambientAcyclicι F).mapArrow.map α) :=
    ⟨(ambient_isCofibration_iff F α.left.hom).mpr
        ((ambientAcyclicAmbient_isCofibration_iff F α.left).mp hα.1),
      (ambient_isCofibration_iff F α.right.hom).mpr
        ((ambientAcyclicAmbient_isCofibration_iff F α.right).mp hα.2)⟩
  exact (ambientAcyclicAmbient_isCofibration_iff F _).mpr
    ((ambient_isCofibration_iff F _).mp
      (ambientMappingCylinder_map_isCofibration F ((ambientAcyclicι F).mapArrow.map α) hα₀))

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. If both components of a commuting square α:f→g are weak equivalences, then
I(α):I(f)→I(g) is weak. -/
theorem ambientAcyclicCylinder_map_isWeakEquivalence {f g : Arrow (AmbientAcyclic F)} (α : f ⟶ g) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    Waldhausen.arrowWeakEquivalences (AmbientAcyclic F) α →
      IsWeakEquivalence ((ambientAcyclicCylinderFunctor F).map α) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  intro _
  exact ambientAcyclicAmbient_isWeakEquivalence_all F _

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. For a square α:f→g, form the chosen pushout I(f)⊔_(X⊔Y)(X'⊔Y'). The inclusion J sends
this square to a pushout of bounded complexes after the canonical coproduct charts on X⊔Y and
X'⊔Y'. -/
theorem ambientAcyclicCylinderCorner_mappedPushout {f g : Arrow (AmbientAcyclic F)} (α : f ⟶ g) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    letI := ambientWaldhausenCategory F
    let hBoundary := ambientAcyclicCylinderBoundary_isCofibration F
    letI := Waldhausen.cylinderCorner_hasPushout (ambientAcyclicCylinderFunctor F)
      (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) hBoundary α
    let bf := Waldhausen.cylinderBoundaryMap (ambientAcyclicCylinderFunctor F)
      (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) f
    let u := coprod.map α.left α.right
    IsPushout
      (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor E)
        (mappingCylinderFront E) (mappingCylinderBack E) ((ambientAcyclicι F).mapArrow.obj f))
      (coprod.map α.left.hom α.right.hom)
      ((ambientAcyclicι F).map (pushout.inl bf u))
      ((ambientAcyclicCoproductIso F g.left g.right).hom ≫
        (ambientAcyclicι F).map (pushout.inr bf u)) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  let _ := ambientWaldhausenCategory F
  let J := ambientAcyclicι F
  let hBoundary := ambientAcyclicCylinderBoundary_isCofibration F
  let _ := Waldhausen.cylinderCorner_hasPushout (ambientAcyclicCylinderFunctor F)
    (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) hBoundary α
  let bf := Waldhausen.cylinderBoundaryMap (ambientAcyclicCylinderFunctor F)
    (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) f
  let u := coprod.map α.left α.right
  have hi : ambientAcyclicCofibrations F bf :=
    (ambientAcyclicAmbient_isCofibration_iff F bf).mp (hBoundary f)
  have hP : IsPushout (J.map bf) (J.map u) (J.map (pushout.inl bf u))
      (J.map (pushout.inr bf u)) := ambientAcyclicPushout_ι F hi (IsPushout.of_hasPushout bf u)
  let ef := ambientAcyclicCoproductIso F f.left f.right
  let eg := ambientAcyclicCoproductIso F g.left g.right
  apply hP.of_iso' ef (Iso.refl _) eg (Iso.refl _)
  · exact (ambientAcyclicCylinderBoundary_chart F f).trans (Category.comp_id _).symm
  · change ef.hom ≫ J.map (coprod.map α.left α.right) =
      coprod.map α.left.hom α.right.hom ≫ eg.hom
    rw [ambientAcyclicCoproductIso_hom, ambientAcyclicCoproductIso_hom]
    exact coprodComparison_natural J α.left α.right
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. If both components of α:f→g are cofibrations, the induced corner map
I(f)⊔_(X⊔Y)(X'⊔Y')→I(g) is a cofibration. -/
theorem ambientAcyclicCylinderCorner_isCofibration :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    ∀ {f g : Arrow (AmbientAcyclic F)} (α : f ⟶ g),
      Waldhausen.arrowCofibrations (AmbientAcyclic F) α →
      letI := Waldhausen.cylinderCorner_hasPushout (ambientAcyclicCylinderFunctor F)
        (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F)
        (ambientAcyclicCylinderBoundary_isCofibration F) α
      IsCofibration (Waldhausen.cylinderCornerMap (ambientAcyclicCylinderFunctor F)
        (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F)
        (ambientAcyclicCylinderBoundary_isCofibration F) α) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  let _ := ambientWaldhausenCategory F
  intro f g α hα
  let J := ambientAcyclicι F
  let a := J.mapArrow.map α
  let f₀ := J.mapArrow.obj f
  let g₀ := J.mapArrow.obj g
  let hBoundary := ambientAcyclicCylinderBoundary_isCofibration F
  let hBoundary₀ := ambientMappingCylinderBoundary_isCofibration F
  let _ := Waldhausen.cylinderCorner_hasPushout (ambientAcyclicCylinderFunctor F)
    (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) hBoundary α
  let _ := Waldhausen.cylinderCorner_hasPushout (mappingCylinderFunctor E)
    (mappingCylinderFront E) (mappingCylinderBack E) hBoundary₀ a
  let bf := Waldhausen.cylinderBoundaryMap (ambientAcyclicCylinderFunctor F)
    (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) f
  let bg := Waldhausen.cylinderBoundaryMap (ambientAcyclicCylinderFunctor F)
    (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) g
  let bf₀ := Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor E)
    (mappingCylinderFront E) (mappingCylinderBack E) f₀
  let bg₀ := Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor E)
    (mappingCylinderFront E) (mappingCylinderBack E) g₀
  let u := coprod.map α.left α.right
  let u₀ := coprod.map a.left a.right
  let d := Waldhausen.cylinderCornerMap (ambientAcyclicCylinderFunctor F)
    (ambientAcyclicCylinderFront F) (ambientAcyclicCylinderBack F) hBoundary α
  let d₀ := Waldhausen.cylinderCornerMap (mappingCylinderFunctor E)
    (mappingCylinderFront E) (mappingCylinderBack E) hBoundary₀ a
  let eg := ambientAcyclicCoproductIso F g.left g.right
  have hP : IsPushout bf₀ u₀ (J.map (pushout.inl bf u))
      (eg.hom ≫ J.map (pushout.inr bf u)) := ambientAcyclicCylinderCorner_mappedPushout F α
  let e := hP.isoPushout
  have hOld : J.map (pushout.inl bf u) ≫ J.map d = (mappingCylinderFunctor E).map a := by
    have h := congrArg J.map
      (Waldhausen.cylinderCornerMap_inl _ _ _ hBoundary α)
    have hComp : J.map (pushout.inl bf u) ≫ J.map d =
        J.map ((ambientAcyclicCylinderFunctor F).map α) := (J.map_comp _ _).symm.trans h
    exact hComp.trans (ambientAcyclicCylinderFunctor_map F α)
  have hNew : (eg.hom ≫ J.map (pushout.inr bf u)) ≫ J.map d = bg₀ := by
    have h := congrArg J.map
      (Waldhausen.cylinderCornerMap_inr _ _ _ hBoundary α)
    have hComp : J.map (pushout.inr bf u) ≫ J.map d = J.map bg :=
      (J.map_comp _ _).symm.trans h
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => eg.hom ≫ t) hComp).trans (ambientAcyclicCylinderBoundary_chart F g))
  have hChart : J.map d = e.hom ≫ d₀ := by
    apply hP.hom_ext
    · have hFace : J.map (pushout.inl bf u) ≫ (e.hom ≫ d₀) =
          (mappingCylinderFunctor E).map a := by
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ d₀) hP.inl_isoPushout_hom).trans
            (Waldhausen.cylinderCornerMap_inl _ _ _ hBoundary₀ a))
      exact hOld.trans hFace.symm
    · have hFace : (eg.hom ≫ J.map (pushout.inr bf u)) ≫ (e.hom ≫ d₀) = bg₀ := by
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ d₀) hP.inr_isoPushout_hom).trans
            (Waldhausen.cylinderCornerMap_inr _ _ _ hBoundary₀ a))
      exact hNew.trans hFace.symm
  have hα₀ : Waldhausen.arrowCofibrations (Bounded E) a :=
    ⟨(ambient_isCofibration_iff F α.left.hom).mpr
        ((ambientAcyclicAmbient_isCofibration_iff F α.left).mp hα.1),
      (ambient_isCofibration_iff F α.right.hom).mpr
        ((ambientAcyclicAmbient_isCofibration_iff F α.right).mp hα.2)⟩
  have hd₀ : IsCofibration d₀ := ambientMappingCylinderCorner_isCofibration F a hα₀
  have hComp : IsCofibration (e.hom ≫ d₀) :=
    WaldhausenCategoryWithoutGluing.cofibrations.comp_mem _ _
      (WaldhausenCategoryWithoutGluing.cofibrations.of_isIso e.hom) hd₀
  have hd : IsCofibration (J.map d) := hChart.symm ▸ hComp
  exact (ambientAcyclicAmbient_isCofibration_iff F d).mpr
    ((ambient_isCofibration_iff F (J.map d)).mp hd)

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The restricted cylinder preserves arrow cofibrations and weak maps, has cofibration
joint boundaries and relative corners for arrow cofibrations, and has the specified zero-arrow
normalization. These maps define a full cylinder on C. -/
def ambientAcyclicFullCylinder :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    Waldhausen.FullCylinder (AmbientAcyclic F) := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  exact
    { toWaldhausenMappingCylinderCore := ambientAcyclicMappingCylinderCore F
      normalization := ambientAcyclicCylinderNormalization F
      boundary_cofibration := ambientAcyclicCylinderBoundary_isCofibration F
      map_weakEquivalence := ambientAcyclicCylinder_map_isWeakEquivalence F
      map_cofibration := ambientAcyclicCylinder_map_isCofibration F
      corner_cofibration := ambientAcyclicCylinderCorner_isCofibration F }

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The full cylinder satisfies the Cylinder Axiom because each projection p_f:I(f)→Y is
a weak equivalence. -/
theorem ambientAcyclicFullCylinder_satisfiesCylinderAxiom :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    (ambientAcyclicFullCylinder F).SatisfiesCylinderAxiom := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  intro f
  exact ambientAcyclicAmbient_isWeakEquivalence_all F _

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The functor of the full-cylinder structure is the restricted signed cylinder
I:Arrow(C)→C. -/
theorem ambientAcyclicFullCylinder_functor :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    (ambientAcyclicFullCylinder F).functor = ambientAcyclicCylinderFunctor F := rfl

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The relative corner map restricts on the old cylinder I(f) to I(α):I(f)→I(g), for
every commuting square α:f→g. -/
theorem ambientAcyclicFullCylinderCorner_inl {f g : Arrow (AmbientAcyclic F)} (α : f ⟶ g) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    let T := ambientAcyclicFullCylinder F
    letI := Waldhausen.cylinderCorner_hasPushout T.functor T.front T.back
      T.boundary_cofibration α
    pushout.inl (Waldhausen.cylinderBoundaryMap T.functor T.front T.back f)
        (coprod.map α.left α.right) ≫
      Waldhausen.cylinderCornerMap T.functor T.front T.back T.boundary_cofibration α =
        T.functor.map α := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  exact Waldhausen.cylinderCornerMap_inl _ _ _ (ambientAcyclicFullCylinder F).boundary_cofibration α

/-- Let E be a preadditive exact category with a zero object and binary biproducts, A an abelian
category and F:E→A additive. Let C be the full category of bounded integer cochain complexes
whose F-images are acyclic. Assume F is exact, and use degreewise admissible-mono cofibrations
and inherited F-image quasi-isomorphisms as the Waldhausen classes. Write I for the signed
cylinder restricted to C, with front i, back j and projection p, and J:C→Bounded(E) for the
inclusion. The relative corner map restricts on the new boundary X'⊔Y' to ∂g:X'⊔Y'→I(g), for
every commuting square α:f→g. -/
theorem ambientAcyclicFullCylinderCorner_inr {f g : Arrow (AmbientAcyclic F)} (α : f ⟶ g) :
    letI := ambientAcyclicAmbientWaldhausenCategory F
    let T := ambientAcyclicFullCylinder F
    letI := Waldhausen.cylinderCorner_hasPushout T.functor T.front T.back
      T.boundary_cofibration α
    pushout.inr (Waldhausen.cylinderBoundaryMap T.functor T.front T.back f)
        (coprod.map α.left α.right) ≫
      Waldhausen.cylinderCornerMap T.functor T.front T.back T.boundary_cofibration α =
        Waldhausen.cylinderBoundaryMap T.functor T.front T.back g := by
  let _ := ambientAcyclicAmbientWaldhausenCategory F
  exact Waldhausen.cylinderCornerMap_inr _ _ _ (ambientAcyclicFullCylinder F).boundary_cofibration α

end CochainComplex.Bounded

end
