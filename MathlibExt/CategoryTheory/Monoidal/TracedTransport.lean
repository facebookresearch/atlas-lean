/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.TracedFunctor

/-!
# Transport of symmetric traces

A fully faithful strong symmetric monoidal functor into a traced category
induces a unique trace on its source that the functor preserves. Neither category
is required to be rigid. The construction pulls back the target trace using
fullness; faithfulness proves the axioms and uniqueness. Identity and composition
laws make the transport independent of a choice of intermediate category.

Source: Joyal, Street and Verity, Traced monoidal categories (1996),
Proposition 2.4, https://doi.org/10.1017/S0305004100074338,
specialized from balanced to symmetric monoidal categories.
-/

@[expose] public section

namespace CategoryTheory.SymmetricTrace

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonoidalCategory

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Changing the feedback object by an isomorphism does not change the trace. -/
theorem trace_conjugate (T : SymmetricTrace C) {X Y U V : C} (i : U ≅ V)
    (f : X ⊗ V ⟶ Y ⊗ V) :
    T.trace (X ◁ i.hom ≫ f ≫ Y ◁ i.inv) = T.trace f := by
  have h := T.dinaturality (X ◁ i.hom ≫ f) i.inv
  simpa only [id_tensorHom, Category.assoc, ← whiskerLeft_comp_assoc,
    Iso.inv_hom_id, whiskerLeft_id, Category.id_comp] using h

universe v' u'
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [SymmetricCategory D]

omit [SymmetricCategory C] in
private theorem map_naturality (S : SymmetricTrace D) (F : C ⥤ D) [F.Monoidal] [F.Full] [F.Faithful]
    {X X' Y Y' U : C} (f : X ⊗ U ⟶ Y ⊗ U) (g : X' ⟶ X) (h : Y ⟶ Y') :
    F.preimage (S.trace (μ F X' U ≫ F.map ((g ⊗ₘ 𝟙 U) ≫ f ≫ (h ⊗ₘ 𝟙 U)) ≫
      δ F Y' U)) = g ≫ F.preimage (S.trace (μ F X U ≫ F.map f ≫ δ F Y U)) ≫ h := by
  apply F.map_injective
  simp only [Functor.map_preimage, Functor.map_comp]
  simpa only [Functor.map_comp, Functor.Monoidal.map_tensor, Functor.map_id,
    Category.assoc, Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ,
    Category.comp_id] using
    S.naturality (μ F X U ≫ F.map f ≫ δ F Y U) (F.map g) (F.map h)

omit [SymmetricCategory C] in
private theorem map_dinaturality (S : SymmetricTrace D) (F : C ⥤ D) [F.Monoidal]
    {X Y U V : C} (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U) :
    S.trace (μ F X U ≫ F.map (f ≫ (𝟙 Y ⊗ₘ g)) ≫ δ F Y U) =
      S.trace (μ F X V ≫ F.map ((𝟙 X ⊗ₘ g) ≫ f) ≫ δ F Y V) := by
  simpa only [Functor.map_comp, Functor.Monoidal.map_tensor, Functor.map_id,
    Category.assoc, Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ,
    Category.comp_id] using
    S.dinaturality (μ F X U ≫ F.map f ≫ δ F Y V) (F.map g)

private theorem map_yanking (S : SymmetricTrace D) (F : C ⥤ D) [F.Braided] (X : C) :
    S.trace (μ F X X ≫ F.map (β_ X X).hom ≫ δ F X X) = F.map (𝟙 X) := by
  simpa only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ_assoc,
    Functor.Monoidal.μ_δ, Category.comp_id, Functor.map_id] using S.yanking (F.obj X)

omit [SymmetricCategory C] in
private theorem map_superposing (S : SymmetricTrace D) (F : C ⥤ D) [F.Monoidal]
    {X Y U W Z : C} (f : X ⊗ U ⟶ Y ⊗ U) (g : W ⟶ Z) :
    S.trace (μ F (W ⊗ X) U ≫ F.map ((α_ W X U).hom ≫ (g ⊗ₘ f) ≫
      (α_ Z Y U).inv) ≫ δ F (Z ⊗ Y) U) =
      Functor.OplaxMonoidal.δ F W X ≫ (F.map g ⊗ₘ
        S.trace (μ F X U ≫ F.map f ≫ δ F Y U)) ≫ μ F Z Y := by
  rw [← S.superposing (μ F X U ≫ F.map f ≫ δ F Y U) (F.map g),
    ← S.naturality _ (δ F W X) (μ F Z Y)]
  congr 1
  simp only [Functor.map_comp, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_associator_inv, Functor.Monoidal.map_tensor,
    Category.assoc, Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ,
    Category.comp_id]
  simp only [tensorHom_def, whiskerLeft_comp, Category.assoc,
    whiskerLeft_id, Category.comp_id]
  simp only [whisker_exchange_assoc]

omit [SymmetricCategory C] in
private theorem map_unit (S : SymmetricTrace D) (F : C ⥤ D) [F.Monoidal]
    {X Y : C} (f : X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C) :
    S.trace (μ F X (𝟙_ C) ≫ F.map f ≫ δ F Y (𝟙_ C)) =
      F.map ((ρ_ X).inv ≫ f ≫ (ρ_ Y).hom) := by
  rw [← trace_conjugate S (Functor.Monoidal.εIso F), S.vanishing_unit]
  simp only [Functor.Monoidal.εIso_hom, Functor.Monoidal.εIso_inv,
    Functor.map_comp, Functor.Monoidal.map_rightUnitor_inv,
    Functor.Monoidal.map_rightUnitor, Category.assoc]

omit [SymmetricCategory C] in
private theorem map_tensor (S : SymmetricTrace D) (F : C ⥤ D) [F.Monoidal]
    {X Y U V : C} (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)) :
    S.trace (μ F X (U ⊗ V) ≫ F.map f ≫ δ F Y (U ⊗ V)) =
      S.trace (μ F X U ≫ S.trace (μ F (X ⊗ U) V ≫
        F.map ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv) ≫ δ F (Y ⊗ U) V) ≫ δ F Y U) := by
  rw [← trace_conjugate S (Functor.Monoidal.μIso F U V), S.vanishing_tensor,
    ← S.naturality _ (μ F X U) (δ F Y U)]
  congr 1
  congr 1
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
    Functor.map_comp, Functor.Monoidal.map_associator, Functor.Monoidal.map_associator_inv,
    Category.assoc, Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ,
    tensorHom_id, Functor.Monoidal.whiskerRight_μ_δ_assoc,
    Functor.Monoidal.whiskerRight_μ_δ, Category.comp_id]

/-- A symmetric trace is determined by its operation on morphisms. -/
@[ext] theorem ext {T R : SymmetricTrace C}
    (h : ∀ {X Y U : C} (f : X ⊗ U ⟶ Y ⊗ U), T.trace f = R.trace f) : T = R := by
  cases T
  cases R
  congr
  funext X Y U f
  exact h f

private theorem trace_eq_of_preserves (T R : SymmetricTrace C) (S : SymmetricTrace D) (F : C ⥤ D)
    [F.Monoidal] [F.Faithful] (hT : T.Preserves S F) (hR : R.Preserves S F)
    {X Y U : C} (f : X ⊗ U ⟶ Y ⊗ U) : T.trace f = R.trace f := by
  apply F.map_injective
  exact (hT f).trans (hR f).symm


/-- Pull back a symmetric trace along a fully faithful strong symmetric monoidal functor. -/
noncomputable def ofFullyFaithful (S : SymmetricTrace D) (F : C ⥤ D)
    [F.Braided] [F.Full] [F.Faithful] : SymmetricTrace C where
  trace {X Y U} f := F.preimage (S.trace (μ F X U ≫ F.map f ≫ δ F Y U))
  naturality f g h := by exact map_naturality S F f g h
  dinaturality f g := by
    apply F.map_injective
    simpa only [Functor.map_preimage] using map_dinaturality S F f g
  vanishing_unit f := by
    apply F.map_injective
    simpa only [Functor.map_preimage] using map_unit S F f
  vanishing_tensor f := by
    apply F.map_injective
    simpa only [Functor.map_preimage] using map_tensor S F f
  superposing f g := by
    apply F.map_injective
    simpa only [Functor.Monoidal.map_tensor, Functor.map_preimage] using
      map_superposing S F f g
  yanking X := by
    apply F.map_injective
    simpa only [Functor.map_preimage] using map_yanking S F X

/-- The functor preserves the trace transported along it. -/
theorem preserves_ofFullyFaithful (S : SymmetricTrace D) (F : C ⥤ D)
    [F.Braided] [F.Full] [F.Faithful] : (ofFullyFaithful S F).Preserves S F := by
  intro X Y U f
  exact F.map_preimage _

/-- For a fully faithful braided strong monoidal functor `F : C ⥤ D` and a fixed trace `S` on
`D`, the transported trace `ofFullyFaithful S F` is the only trace `T` on `C` that `F` carries
to `S`, that is, with `T.Preserves S F`. -/
theorem ofFullyFaithful_unique (S : SymmetricTrace D) (F : C ⥤ D)
    [F.Braided] [F.Full] [F.Faithful] (T : SymmetricTrace C) (h : T.Preserves S F) :
    T = ofFullyFaithful S F := by
  apply ext
  intro X Y U f
  exact trace_eq_of_preserves T _ S F h (preserves_ofFullyFaithful S F) f

/-- Transport along the identity functor leaves a trace unchanged. -/
@[simp] theorem ofFullyFaithful_id (T : SymmetricTrace C) :
    T.ofFullyFaithful (𝟭 C) = T :=
  (T.ofFullyFaithful_unique (𝟭 C) T T.preserves_id).symm

universe v'' u''
variable {E : Type u''} [Category.{v''} E] [MonoidalCategory E] [SymmetricCategory E]

/-- For fully faithful braided strong monoidal functors `F : C ⥤ D` and `G : D ⥤ E` and a fixed
trace `S` on `E`, transporting `S` along `G` and then along `F` agrees with transporting it
along `F ⋙ G`. -/
@[simp] theorem ofFullyFaithful_comp (S : SymmetricTrace E) (F : C ⥤ D) (G : D ⥤ E)
    [F.Braided] [G.Braided] [F.Full] [F.Faithful] [G.Full] [G.Faithful] :
    (S.ofFullyFaithful G).ofFullyFaithful F = S.ofFullyFaithful (F ⋙ G) :=
  S.ofFullyFaithful_unique (F ⋙ G) _
    (Preserves.comp ((S.ofFullyFaithful G).preserves_ofFullyFaithful F)
      (S.preserves_ofFullyFaithful G))

/-- For a fully faithful braided strong monoidal functor `F : C ⥤ D` between right rigid
categories, transporting the canonical trace `symmetricTraceOfRigid D` along `F` gives the
canonical trace `symmetricTraceOfRigid C`. -/
theorem ofFullyFaithful_rigid [RightRigidCategory C] [RightRigidCategory D]
    (F : C ⥤ D) [F.Braided] [F.Full] [F.Faithful] :
    (symmetricTraceOfRigid D).ofFullyFaithful F = symmetricTraceOfRigid C :=
  ((symmetricTraceOfRigid D).ofFullyFaithful_unique F _ (preserves_of_rigid F)).symm

end CategoryTheory.SymmetricTrace
