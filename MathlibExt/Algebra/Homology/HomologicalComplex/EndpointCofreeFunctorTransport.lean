/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

public import MathlibExt.Algebra.Homology.HomologicalComplex.EndpointCofree
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Additive functors and endpoint cofree complexes

An additive functor F between abelian categories carries the endpoint cofree
complex on a family I to the endpoint cofree complex on the family F(I).
The comparison is induced by the images of the first coefficient projections.
It is an isomorphism because F preserves binary biproducts and zero objects.
No exactness assumption on F is needed.

The comparison is natural in the coefficient family and commutes with the
cofree unit and counit. At an index without an outgoing edge, it uses the
canonical isomorphism F(0) ≅ 0 for the optional second coefficient.
The complex shape and the object and morphism universes of both categories
are independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Classical ZeroObject

namespace HomologicalComplex

universe u₁ u₂ v₁ v₂ w

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] {ι : Type w} (c : ComplexShape ι)

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- Applying an additive functor to the optional next coefficient gives the
optional next coefficient of the image family, using F(0) ≅ 0 at an endpoint. -/
def endpointCofreeNextTermFunctorIso (I : GradedObject ι C) (i : ι) :
    F.obj (endpointCofreeNextTerm (c := c) I i) ≅
      endpointCofreeNextTerm (c := c) (fun j => F.obj (I j)) i :=
  if hi : c.Rel i (c.next i) then
    F.mapIso (endpointCofreeNextTermIso I hi) ≪≫
      (endpointCofreeNextTermIso (fun j => F.obj (I j)) hi).symm
  else
    F.mapIso (eqToIso (endpointCofreeNextTerm_of_no_next I i hi)) ≪≫
      F.mapZeroObject ≪≫
        (eqToIso (endpointCofreeNextTerm_of_no_next (fun j => F.obj (I j)) i hi)).symm

/-- Along an outgoing edge, the optional-coefficient comparison commutes with
the two canonical identifications of that coefficient with the target term. -/
@[reassoc (attr := simp)]
theorem endpointCofreeNextTermFunctorIso_hom_next (I : GradedObject ι C)
    {i j : ι} (hij : c.Rel i j) :
    (endpointCofreeNextTermFunctorIso F c I i).hom ≫
        (endpointCofreeNextTermIso (fun j => F.obj (I j)) hij).hom =
      F.map ((endpointCofreeNextTermIso I hij).hom) := by
  obtain rfl := c.next_eq' hij
  simp only [endpointCofreeNextTermFunctorIso, dif_pos hij, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.mapIso]

/-- In each degree, preservation of the binary biproduct and the optional next
coefficient gives the comparison between the image cofree term and the cofree
term of the image family. -/
def endpointCofreeFunctorTransportDegreeIso (I : GradedObject ι C) (i : ι) :
    F.obj ((endpointCofree (c := c) I).X i) ≅
      (endpointCofree (c := c) (fun j => F.obj (I j))).X i :=
  F.mapBiprod (I i) (endpointCofreeNextTerm (c := c) I i) ≪≫
    biprod.mapIso (Iso.refl _) (endpointCofreeNextTermFunctorIso F c I i)

/-- The degreewise comparison followed by the first projection is the image
under F of the original first projection. -/
@[reassoc (attr := simp)]
theorem endpointCofreeFunctorTransportDegreeIso_fst (I : GradedObject ι C) (i : ι) :
    (endpointCofreeFunctorTransportDegreeIso F c I i).hom ≫
        endpointCofreeProjection (c := c) (fun j => F.obj (I j)) i =
      F.map (endpointCofreeProjection (c := c) I i) := by
  simp only [endpointCofreeFunctorTransportDegreeIso, Iso.trans_hom, biprod.mapIso,
    Iso.refl_hom, endpointCofreeProjection, Category.assoc, biprod.map_fst,
    Category.comp_id, Functor.mapBiprod_hom, biprod.lift_fst]

/-- The second coefficient of the degreewise comparison is the image of the
old second projection followed by the optional-coefficient comparison. -/
@[reassoc]
theorem endpointCofreeFunctorTransportDegreeIso_snd (I : GradedObject ι C) (i : ι) :
    (endpointCofreeFunctorTransportDegreeIso F c I i).hom ≫
        endpointCofreeSecondProjection (c := c) (fun j => F.obj (I j)) i =
      F.map (endpointCofreeSecondProjection (c := c) I i) ≫
        (endpointCofreeNextTermFunctorIso F c I i).hom := by
  simp only [endpointCofreeFunctorTransportDegreeIso, Iso.trans_hom, biprod.mapIso,
    Iso.refl_hom, endpointCofreeSecondProjection, Category.assoc, biprod.map_snd,
    Functor.mapBiprod_hom, biprod.lift_snd_assoc]

/-- The complex comparison into the cofree image family is the existing cofree
map with first coefficients F applied to the original first projections. -/
def endpointCofreeFunctorTransportHom (I : GradedObject ι C) :
    (F.mapHomologicalComplex c).obj ((endpointCofreeFunctor C c).obj I) ⟶
      (endpointCofreeFunctor D c).obj ((Functor.pi (fun _ : ι => F)).obj I) :=
  endpointCofreeHom
    ((F.mapHomologicalComplex c).obj (endpointCofree (c := c) I))
    (fun j => F.obj (I j))
    (fun i => F.map (endpointCofreeProjection (c := c) I i))

/-- The first coefficient of the complex comparison is the image under F of
the original first projection. -/
@[reassoc (attr := simp)]
theorem endpointCofreeFunctorTransportHom_fst (I : GradedObject ι C) (i : ι) :
    (endpointCofreeFunctorTransportHom F c I).f i ≫
        endpointCofreeProjection (c := c) (fun j => F.obj (I j)) i =
      F.map (endpointCofreeProjection (c := c) I i) :=
  endpointCofreeHom_fst _ _ _ i

/-- The complex comparison has the degreewise biproduct comparison as each of
its components, including at endpoints. -/
theorem endpointCofreeFunctorTransportHom_f (I : GradedObject ι C) (i : ι) :
    (endpointCofreeFunctorTransportHom F c I).f i =
      (endpointCofreeFunctorTransportDegreeIso F c I i).hom := by
  apply biprod.hom_ext
  · change (endpointCofreeFunctorTransportHom F c I).f i ≫
        endpointCofreeProjection (c := c) (fun j => F.obj (I j)) i =
      (endpointCofreeFunctorTransportDegreeIso F c I i).hom ≫
        endpointCofreeProjection (c := c) (fun j => F.obj (I j)) i
    exact (endpointCofreeFunctorTransportHom_fst F c I i).trans
      (endpointCofreeFunctorTransportDegreeIso_fst F c I i).symm
  · change (endpointCofreeFunctorTransportHom F c I).f i ≫
        endpointCofreeSecondProjection (c := c) (fun j => F.obj (I j)) i =
      (endpointCofreeFunctorTransportDegreeIso F c I i).hom ≫
        endpointCofreeSecondProjection (c := c) (fun j => F.obj (I j)) i
    by_cases hi : c.Rel i (c.next i)
    · apply (cancel_mono
        (endpointCofreeNextTermIso (fun j => F.obj (I j)) hi).hom).1
      calc
        _ = F.map ((endpointCofree (c := c) I).d i (c.next i)) ≫
            F.map (endpointCofreeProjection (c := c) I (c.next i)) :=
          endpointCofreeHom_snd_of_rel
            ((F.mapHomologicalComplex c).obj (endpointCofree (c := c) I))
            (fun j => F.obj (I j))
            (fun j => F.map (endpointCofreeProjection (c := c) I j)) hi
        _ = F.map ((endpointCofree (c := c) I).d i (c.next i) ≫
            endpointCofreeProjection (c := c) I (c.next i)) :=
          (F.map_comp _ _).symm
        _ = F.map (endpointCofreeSecondProjection (c := c) I i) ≫
            F.map ((endpointCofreeNextTermIso I hi).hom) := by
          rw [endpointCofree_d I hi]
          simp only [Category.assoc, endpointCofreeInclusion_projection,
            Category.comp_id, Functor.map_comp]
        _ = (F.map (endpointCofreeSecondProjection (c := c) I i) ≫
            (endpointCofreeNextTermFunctorIso F c I i).hom) ≫
              (endpointCofreeNextTermIso (fun j => F.obj (I j)) hi).hom :=
          (congrArg (F.map (endpointCofreeSecondProjection (c := c) I i) ≫ ·)
            (endpointCofreeNextTermFunctorIso_hom_next F c I hi).symm).trans
              (Category.assoc _ _ _).symm
        _ = _ := congrArg
          (· ≫ (endpointCofreeNextTermIso (fun j => F.obj (I j)) hi).hom)
          (endpointCofreeFunctorTransportDegreeIso_snd F c I i).symm
    · exact (endpointCofreeNextTerm_isZero (fun j => F.obj (I j)) i hi).eq_of_tgt _ _

/-- Every component of the cofree transport comparison is an isomorphism, so
the comparison is an isomorphism of complexes. -/
instance endpointCofreeFunctorTransportHom_isIso (I : GradedObject ι C) :
    IsIso (endpointCofreeFunctorTransportHom F c I) := by
  letI : ∀ i, IsIso ((endpointCofreeFunctorTransportHom F c I).f i) := fun i => by
    rw [endpointCofreeFunctorTransportHom_f]
    infer_instance
  exact Hom.isIso_of_components _

/-- Applying F degreewise to the cofree complex is naturally isomorphic to
forming the cofree complex after applying F to every coefficient object. -/
def endpointCofreeFunctorTransportIso :
    endpointCofreeFunctor C c ⋙ F.mapHomologicalComplex c ≅
      (Functor.pi (fun _ : ι => F) : GradedObject ι C ⥤ GradedObject ι D) ⋙
        endpointCofreeFunctor D c :=
  NatIso.ofComponents
    (fun I => asIso (endpointCofreeFunctorTransportHom F c I))
    (fun {I J} a => by
      apply endpointCofree_hom_ext (fun j => F.obj (J j))
      intro i
      change (F.map ((endpointCofreeMap (c := c) a).f i) ≫
          (endpointCofreeFunctorTransportHom F c J).f i) ≫
            endpointCofreeProjection (c := c) (fun j => F.obj (J j)) i =
        ((endpointCofreeFunctorTransportHom F c I).f i ≫
          (endpointCofreeMap (c := c) (fun j => F.map (a j))).f i) ≫
            endpointCofreeProjection (c := c) (fun j => F.obj (J j)) i
      calc
        _ = F.map ((endpointCofreeMap (c := c) a).f i) ≫
            F.map (endpointCofreeProjection (c := c) J i) :=
          (Category.assoc _ _ _).trans (congrArg
            (F.map ((endpointCofreeMap (c := c) a).f i) ≫ ·)
            (endpointCofreeFunctorTransportHom_fst F c J i))
        _ = F.map ((endpointCofreeMap (c := c) a).f i ≫
            endpointCofreeProjection (c := c) J i) := (F.map_comp _ _).symm
        _ = F.map (endpointCofreeProjection (c := c) I i ≫ a i) :=
          congrArg F.map (endpointCofreeMap_fst (c := c) a i)
        _ = F.map (endpointCofreeProjection (c := c) I i) ≫ F.map (a i) :=
          F.map_comp _ _
        _ = ((endpointCofreeFunctorTransportHom F c I).f i ≫
            endpointCofreeProjection (c := c) (fun j => F.obj (I j)) i) ≫
              F.map (a i) := congrArg (· ≫ F.map (a i))
          (endpointCofreeFunctorTransportHom_fst F c I i).symm
        _ = (endpointCofreeFunctorTransportHom F c I).f i ≫
            (endpointCofreeProjection (c := c) (fun j => F.obj (I j)) i ≫
              F.map (a i)) := Category.assoc _ _ _
        _ = _ := (congrArg ((endpointCofreeFunctorTransportHom F c I).f i ≫ ·)
          (endpointCofreeMap_fst (c := c) (fun j => F.map (a j)) i).symm).trans
            (Category.assoc _ _ _).symm)

/-- The natural comparison has the canonical transported first projection in
every degree. -/
@[reassoc (attr := simp)]
theorem endpointCofreeFunctorTransportIso_fst (I : GradedObject ι C) (i : ι) :
    ((endpointCofreeFunctorTransportIso F c).hom.app I).f i ≫
        endpointCofreeProjection (c := c) (fun j => F.obj (I j)) i =
      F.map (endpointCofreeProjection (c := c) I i) :=
  endpointCofreeFunctorTransportHom_fst F c I i

/-- Applying F to the cofree unit and then the comparison gives the cofree unit
of the degreewise image complex. -/
theorem endpointCofreeFunctorTransportIso_unit (K : HomologicalComplex C c) :
    (F.mapHomologicalComplex c).map ((endpointCofreeUnit C c).app K) ≫
        (endpointCofreeFunctorTransportIso F c).hom.app ((forget C c).obj K) =
      (endpointCofreeUnit D c).app ((F.mapHomologicalComplex c).obj K) := by
  apply endpointCofree_hom_ext (fun i => F.obj (K.X i))
  intro i
  change (F.map (((endpointCofreeUnit C c).app K).f i) ≫
      ((endpointCofreeFunctorTransportIso F c).hom.app K.X).f i) ≫
        endpointCofreeProjection (c := c) (fun j => F.obj (K.X j)) i = _
  calc
    _ = F.map (((endpointCofreeUnit C c).app K).f i) ≫
        F.map (endpointCofreeProjection (c := c) K.X i) :=
      (Category.assoc _ _ _).trans (congrArg
        (F.map (((endpointCofreeUnit C c).app K).f i) ≫ ·)
        (endpointCofreeFunctorTransportIso_fst F c K.X i))
    _ = F.map (((endpointCofreeUnit C c).app K).f i ≫
        endpointCofreeProjection (c := c) K.X i) := (F.map_comp _ _).symm
    _ = F.map (𝟙 (K.X i)) := congrArg F.map (endpointCofreeUnit_fst C c K i)
    _ = 𝟙 (F.obj (K.X i)) := F.map_id _
    _ = _ := (endpointCofreeUnit_fst D c ((F.mapHomologicalComplex c).obj K) i).symm

/-- The transported cofree comparison commutes degreewise with the canonical
counits on the original and image coefficient families. -/
@[reassoc]
theorem endpointCofreeFunctorTransportIso_counit (I : GradedObject ι C) (i : ι) :
    ((endpointCofreeFunctorTransportIso F c).hom.app I).f i ≫
        ((endpointCofreeCounit D c).app ((Functor.pi (fun _ : ι => F)).obj I)) i =
      F.map (((endpointCofreeCounit C c).app I) i) := by
  rw [endpointCofreeCounit_app, endpointCofreeCounit_app]
  change ((endpointCofreeFunctorTransportIso F c).hom.app I).f i ≫
      endpointCofreeProjection (c := c) (fun j => F.obj (I j)) i =
    F.map (endpointCofreeProjection (c := c) I i)
  exact endpointCofreeFunctorTransportIso_fst F c I i

end HomologicalComplex
