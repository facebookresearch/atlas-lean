/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingFunctorTransport

/-!
# Isomorphism and functor coherence of actual splitting data

The raw transport laws use zero morphisms, arbitrary shapes and independent
category/index universes. The existing identity/composition functor laws are
reused. Only compatibility with the square-zero normalization uses preadditivity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v w uD vD uE vE

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι} {K L : HomologicalComplex C c}

/-- Actual inverse components retain the native equality maps when their indices are rewritten. -/
lemma hom_XIsoOfEq (s : Splitting K) {i i' j j' : ι} (hi : i = i') (hj : j = j') :
    s.hom i j = (K.XIsoOfEq hi).hom ≫ s.hom i' j' ≫ (K.XIsoOfEq hj).inv := by
  subst i' j'
  simp only [XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id]

/-- The existing reflexive inverse construction commutes with actual complex isomorphisms. -/
lemma ofIso_reflexive (s : Splitting K) (e : K ≅ L) :
    (s.ofIso e).reflexive = s.reflexive.ofIso e := by
  ext i j
  have hi : e.hom.f i ≫ e.inv.f i = 𝟙 (K.X i) := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f : K ⟶ K => f.f i) e.hom_inv_id
  have hi' {Y : C} (f : K.X i ⟶ Y) : e.hom.f i ≫ e.inv.f i ≫ f = f := by
    rw [← Category.assoc, hi, Category.id_comp]
  simp only [reflexive_hom, ofIso_hom, Category.assoc]
  rw [e.hom.comm_assoc j i, hi']

variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]

/-- Componentwise functor transport commutes with the actual mapped complex isomorphism. -/
lemma map_ofIso (s : Splitting K) (e : K ≅ L) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] :
    (s.ofIso e).map F =
      (s.map F).ofIso ((F.mapHomologicalComplex c).mapIso e) := by
  ext i j
  change F.map (e.inv.f i ≫ s.hom i j ≫ e.hom.f j) =
    F.map (e.inv.f i) ≫ F.map (s.hom i j) ≫ F.map (e.hom.f j)
  simp only [Functor.map_comp]

/-- A native natural isomorphism of base functors gives the same actual inverse family. -/
lemma map_natIso (s : Splitting K) {F G : C ⥤ D}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (e : F ≅ G) :
    (s.map F).ofIso ((NatIso.mapHomologicalComplex e c).app K) = s.map G := by
  ext i j
  change e.inv.app (K.X i) ≫ F.map (s.hom i j) ≫ e.hom.app (K.X j) =
    G.map (s.hom i j)
  rw [e.hom.naturality (s.hom i j), ← Category.assoc,
    e.inv_hom_id_app, Category.id_comp]

variable {E : Type uE} [Category.{vE} E] [HasZeroMorphisms E]

/-- Successive transports agree through the native comparison for an isomorphic composite. -/
lemma map_comp_iso (s : Splitting K) (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (e : F ⋙ G ≅ H) :
    ((s.map F).map G).ofIso ((Functor.mapHomologicalComplexCompIso e c).app K) =
      s.map H := by
  change (s.map (F ⋙ G)).ofIso ((NatIso.mapHomologicalComplex e c).app K) = s.map H
  exact s.map_natIso e

end HomologicalComplex.Splitting

namespace HomologicalComplex.Splitting

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K L : HomologicalComplex C c}

/-- The actual square-zero normalization commutes with isomorphism conjugation. -/
lemma ofIso_normalize (s : Splitting K) (e : K ≅ L) :
    (s.ofIso e).normalize = s.normalize.ofIso e := by
  have hi (i : ι) : e.hom.f i ≫ e.inv.f i = 𝟙 (K.X i) := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f : K ⟶ K => f.f i) e.hom_inv_id
  have ha (i : ι) :
      (𝟙 (L.X i) - L.d i (c.next i) ≫ e.inv.f (c.next i) ≫
          s.reflexive.hom (c.next i) i ≫ e.hom.f i) ≫ e.inv.f i =
        e.inv.f i ≫
          (𝟙 (K.X i) - K.d i (c.next i) ≫ s.reflexive.hom (c.next i) i) := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub,
      Category.id_comp, Category.comp_id, Category.assoc]
    rw [← e.inv.comm_assoc i (c.next i), hi i, Category.comp_id]
  ext i j
  simp only [normalize_hom, ofIso_reflexive, ofIso_hom, Category.assoc]
  calc
    _ = ((𝟙 (L.X i) - L.d i (c.next i) ≫ e.inv.f (c.next i) ≫
          s.reflexive.hom (c.next i) i ≫ e.hom.f i) ≫ e.inv.f i) ≫
            s.reflexive.hom i j ≫ e.hom.f j := by
      simp only [Category.assoc]
    _ = e.inv.f i ≫
        (𝟙 (K.X i) - K.d i (c.next i) ≫ s.reflexive.hom (c.next i) i) ≫
          s.reflexive.hom i j ≫ e.hom.f j := by
      rw [ha]
      simp only [Category.assoc]

end HomologicalComplex.Splitting
