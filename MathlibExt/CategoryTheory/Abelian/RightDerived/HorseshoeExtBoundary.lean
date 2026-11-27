/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import MathlibExt.Algebra.Homology.HomComplex.CocycleBoundary
public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitBoundary
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeExtendedDiagram

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C} {hS : S.ShortExact}

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`, with resolutions
`I₁,I₂,I₃` and chosen row splittings. In each nonnegative degree `q`, the section of the integer
zero-extended row is the original section `I₃^q → I₂^q` transported
by the extension coordinate isomorphisms. -/
theorem HorseshoeData.extendedSplitting_section (H : HorseshoeData S hS) (q : ℕ) :
    (H.extendedSplitting q).s =
      (H.res₃.cochainComplexXIso q q rfl).hom ≫ (H.split q).s ≫
        (H.res₂.cochainComplexXIso q q rfl).inv := by
  dsimp only [HorseshoeData.extendedSplitting, HomologicalComplex.extendDiagramSplitting]
  split
  · rename_i h
    have hc : Classical.choose h = q := by
      have he := Classical.choose_spec h
      change ((Classical.choose h : ℕ) : ℤ) = (q : ℤ) at he
      exact_mod_cast he
    have hn (k : ℕ) (hk : k = q)
        (he : ComplexShape.embeddingUpNat.f k = (q : ℤ)) :
        ((H.split k).ofIso
          (HomologicalComplex.extendDiagramEvalIso H.diagram ComplexShape.embeddingUpNat k q he).symm).s =
        (H.res₃.cochainComplexXIso q q rfl).hom ≫ (H.split q).s ≫
          (H.res₂.cochainComplexXIso q q rfl).inv := by
      subst k
      rfl
    exact hn (Classical.choose h) hc (Classical.choose_spec h)
  · rename_i h
    exact False.elim (h ⟨q, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`, with resolutions
`I₁,I₂,I₃` and chosen row splittings. In each nonnegative degree `q`, the retraction of the integer
zero-extended row is the original retraction `I₂^q → I₁^q` transported
by the extension coordinate isomorphisms. -/
theorem HorseshoeData.extendedSplitting_retraction (H : HorseshoeData S hS) (q : ℕ) :
    (H.extendedSplitting q).r =
      (H.res₂.cochainComplexXIso q q rfl).hom ≫ (H.split q).r ≫
        (H.res₁.cochainComplexXIso q q rfl).inv := by
  dsimp only [HorseshoeData.extendedSplitting, HomologicalComplex.extendDiagramSplitting]
  split
  · rename_i h
    have hc : Classical.choose h = q := by
      have he := Classical.choose_spec h
      change ((Classical.choose h : ℕ) : ℤ) = (q : ℤ) at he
      exact_mod_cast he
    have hn (k : ℕ) (hk : k = q)
        (he : ComplexShape.embeddingUpNat.f k = (q : ℤ)) :
        ((H.split k).ofIso
          (HomologicalComplex.extendDiagramEvalIso H.diagram ComplexShape.embeddingUpNat k q he).symm).r =
        (H.res₂.cochainComplexXIso q q rfl).hom ≫ (H.split q).r ≫
          (H.res₁.cochainComplexXIso q q rfl).inv := by
      subst k
      rfl
    exact hn (Classical.choose h) hc (Classical.choose_spec h)
  · rename_i h
    exact False.elim (h ⟨q, rfl⟩)

end CategoryTheory.Functor.RightDerived

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C} {hS : S.ShortExact}

/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`, with resolutions
`I₁,I₂,I₃` and chosen row splittings. For `f : Z → I₃^q`, the connecting representative
`Z → I₁^(q+1)` is `f ≫ s_q ≫ d_I₂^q ≫ r_(q+1)`, using the section
in degree `q` and retraction in degree `q+1`. -/
def HorseshoeData.originalConnectingRepresentative (H : HorseshoeData S hS)
    {Z : C} (q : ℕ) (f : Z ⟶ H.res₃.cocomplex.X q) :
    Z ⟶ H.res₁.cocomplex.X (q + 1) :=
  f ≫ (H.split q).s ≫ H.res₂.cocomplex.d q (q + 1) ≫ (H.split (q + 1)).r

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`, with resolutions
`I₁,I₂,I₃` and chosen row splittings. For `f : Z → I₃^q`, the split-boundary representative in the
integer zero-extended diagram is the original representative
`f ≫ s_q ≫ d_I₂^q ≫ r_(q+1)` transported to the extended `I₁^(q+1)`. -/
theorem HorseshoeData.extendedConnectingRepresentative_eq (H : HorseshoeData S hS)
    {Z : C} (q : ℕ) (f : Z ⟶ H.res₃.cocomplex.X q) :
    HomologicalComplex.SplitBoundary.representative H.extendedDiagram H.extendedSplitting
      q (q + 1) (f ≫ (H.res₃.cochainComplexXIso q q rfl).inv) =
    H.originalConnectingRepresentative q f ≫
      (H.res₁.cochainComplexXIso (q + 1) (q + 1) (by simp)).inv := by
  dsimp only [HomologicalComplex.SplitBoundary.representative,
    HomologicalComplex.SplitBoundary.cycleLift, HorseshoeData.originalConnectingRepresentative]
  change ((f ≫ (H.res₃.cochainComplexXIso q q rfl).inv) ≫
      (H.extendedSplitting q).s) ≫ H.res₂.cochainComplex.d q (q + 1) ≫
      (H.extendedSplitting (q + 1)).r = _
  have hs := H.extendedSplitting_section q
  have hr : (H.extendedSplitting ((q : ℤ) + 1)).r =
      (H.res₂.cochainComplexXIso ((q : ℤ) + 1) (q + 1) (by simp)).hom ≫
        (H.split (q + 1)).r ≫
        (H.res₁.cochainComplexXIso ((q : ℤ) + 1) (q + 1) (by simp)).inv := by
    have ht (i : ℤ) (hi : i = ((q + 1 : ℕ) : ℤ)) :
        (H.extendedSplitting i).r =
          (H.res₂.cochainComplexXIso i (q + 1) (by simp [hi])).hom ≫
          (H.split (q + 1)).r ≫
          (H.res₁.cochainComplexXIso i (q + 1) (by simp [hi])).inv := by
      subst i
      exact H.extendedSplitting_retraction (q + 1)
    exact ht ((q : ℤ) + 1) (by simp)
  have hd := H.res₂.cochainComplex_d q (q + 1) q (q + 1) rfl (by simp)
  rw [hs, hr, hd]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end CategoryTheory.Functor.RightDerived

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C} {hS : S.ShortExact}

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`, with resolutions
`I₁,I₂,I₃` and chosen row splittings. If `f : Z → I₃^q` is a cocycle, so `f ≫ d_I₃^q=0`, its
connecting representative `f ≫ s_q ≫ d_I₂^q ≫ r_(q+1)` is a cocycle
in `I₁^(q+1)`, including when `q=0`. -/
theorem HorseshoeData.originalConnectingRepresentative_cycle (H : HorseshoeData S hS)
    {Z : C} (q : ℕ) (f : Z ⟶ H.res₃.cocomplex.X q)
    (hf : f ≫ H.res₃.cocomplex.d q (q + 1) = 0) :
    H.originalConnectingRepresentative q f ≫ H.res₁.cocomplex.d (q + 1) (q + 2) = 0 := by
  have h := HomologicalComplex.SplitBoundary.representative_cycle H.diagram H.split
    q (q + 1) (q + 2) f hf
  dsimp only [HomologicalComplex.SplitBoundary.representative,
    HomologicalComplex.SplitBoundary.cycleLift, HorseshoeData.originalConnectingRepresentative, HorseshoeData.diagram] at h ⊢
  simpa only [Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`, with resolutions
`I₁,I₂,I₃` and chosen row splittings. If `f : Z → I₃^q` is a cocycle, its image under the extension
coordinate identification is a cocycle in the integer zero-extended
resolution of `X₃`. -/
theorem HorseshoeData.originalCycle_extended (H : HorseshoeData S hS)
    {Z : C} (q : ℕ) (f : Z ⟶ H.res₃.cocomplex.X q)
    (hf : f ≫ H.res₃.cocomplex.d q (q + 1) = 0) :
    (f ≫ (H.res₃.cochainComplexXIso q q rfl).inv) ≫
      H.res₃.cochainComplex.d q (q + 1) = 0 := by
  rw [H.res₃.cochainComplex_d q (q + 1) q (q + 1) rfl (by simp)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp]

end CategoryTheory.Functor.RightDerived

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.InjectiveResolution
open CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C] [HasDerivedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C` be abelian, with a derived category and Ext at its hom-set
universe, and let `R` be an injective resolution of `Y`. For a cocycle
`f : X → R^q`, the Ext class in `Ext^q(X,Y)` has derived morphism
obtained from the shifted map of its zero-extended cocycle followed
by the inverse coaugmentation of `R`, shifted by `q`. -/
theorem extMk_hom_original_cocycle {X Y : C} (R : InjectiveResolution Y)
    (q : ℕ) (f : X ⟶ R.cocomplex.X q)
    (hf : f ≫ R.cocomplex.d q (q + 1) = 0) :
    (R.extMk f (q + 1) rfl hf).hom =
      Cocycle.mappedShiftedHom DerivedCategory.Q
        (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso q q rfl).inv)
          (zero_add _) (q + 1) (by simp)
          (by
            rw [R.cochainComplex_d (q : ℤ) ((q : ℤ) + 1) q (q + 1) rfl (by simp)]
            simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp])) ≫
      (CategoryTheory.inv (DerivedCategory.Q.map R.ι'))⟦(q : ℤ)⟧' := by
  rw [R.extMk_hom]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp]
  dsimp only [ShiftedHom.map, Cocycle.mappedShiftedHom]
  simp only [Nat.cast_add, Nat.cast_one]
  have hi : CategoryTheory.inv (DerivedCategory.Q.map R.ι') ≫
      𝟙 ((DerivedCategory.singleFunctor C 0).obj Y) =
      CategoryTheory.inv (DerivedCategory.Q.map R.ι') := by
    exact Category.comp_id _
  exact congrArg (fun t =>
    (DerivedCategory.Q.map (Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso q q rfl).inv)
        (zero_add _) ((q : ℤ) + 1) rfl (by
          rw [R.cochainComplex_d q ((q : ℤ) + 1) q (q + 1) rfl (by simp)]
          simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp]))) ≫
      (DerivedCategory.Q.commShiftIso (q : ℤ)).hom.app R.cochainComplex) ≫
        (shiftFunctor (DerivedCategory C) (q : ℤ)).map t) hi

end CategoryTheory.InjectiveResolution

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
universe u v
namespace CategoryTheory.Functor.RightDerived
open CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasExt.{v} C] [HasDerivedCategory C]
variable {S : ShortComplex C} {hS : S.ShortExact}

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`, with resolutions
`I₁,I₂,I₃` and chosen row splittings. Suppose `C` has a derived category and Ext at its hom-set
universe. For a cocycle `f : Z → I₃^q`, composing its class in
`Ext^q(Z,X₃)` with the extension class of `S` equals the class in
`Ext^(q+1)(Z,X₁)` represented by `f ≫ s_q ≫ d_I₂^q ≫ r_(q+1)`. -/
theorem HorseshoeData.extMk_original_boundary (H : HorseshoeData S hS)
    {Z : C} (q : ℕ) (f : Z ⟶ H.res₃.cocomplex.X q)
    (hf : f ≫ H.res₃.cocomplex.d q (q + 1) = 0) :
    (H.res₃.extMk f (q + 1) rfl hf).comp hS.extClass rfl =
      H.res₁.extMk (H.originalConnectingRepresentative q f) (q + 2)
        (by omega) (H.originalConnectingRepresentative_cycle q f hf) := by
  have h := HomologicalComplex.SplitBoundary.derived_SES_original_cocycle_boundary
    H.extendedDiagram H.extended_shortExact H.extendedSplitting q
    (f ≫ (H.res₃.cochainComplexXIso q q rfl).inv) (H.originalCycle_extended q f hf)
  have hc := H.extendedConnectingRepresentative_eq q f
  have ha := H.original_extClass_boundary
  have hb := H.original_extClass_normalized
  ext
  rw [Abelian.Ext.comp_hom, H.res₃.extMk_hom_original_cocycle,
    H.res₁.extMk_hom_original_cocycle]
  dsimp only [ShiftedHom.comp]
  have ht := CategoryTheory.triangle_boundary_transport
    (asIso (DerivedCategory.Q.map H.res₃.ι'))
    (asIso (DerivedCategory.Q.map H.res₁.ι'))
    hS.extClass.hom (DerivedCategory.triangleOfSESδ H.extended_shortExact) ha (q : ℤ)
    (Cocycle.mappedShiftedHom DerivedCategory.Q
      (Cocycle.fromSingleMk (f ≫ (H.res₃.cochainComplexXIso q q rfl).inv)
        (zero_add _) ((q : ℤ) + 1) rfl (H.originalCycle_extended q f hf)))
  have hh := h
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply] at hh
  dsimp only [DerivedCategory.triangleOfSES, Triangle.mk_mor₃] at hh
  dsimp only [asIso, Triangle.mk_obj₁] at ht hh
  have hh' := congrArg (fun t => t ≫
    (CategoryTheory.inv (DerivedCategory.Q.map H.res₁.ι'))⟦(q : ℤ) + 1⟧') hh
  refine ht.trans (hh'.trans ?_)
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  apply congrArg (Cocycle.mappedShiftedHom DerivedCategory.Q)
  apply Cocycle.ext
  dsimp only [HomologicalComplex.SplitBoundary.representativeCocycle, Cocycle.fromSingleMk,
    Cocycle.mk_coe]
  have hcc := congrArg (fun t => Cochain.fromSingleMk (p := (0 : ℤ)) t
    (zero_add ((q : ℤ) + 1))) hc
  change Cochain.fromSingleMk
      (HomologicalComplex.SplitBoundary.representative H.extendedDiagram H.extendedSplitting
        (q : ℤ) ((q : ℤ) + 1) (f ≫ (H.res₃.cochainComplexXIso q q rfl).inv))
      (zero_add ((q : ℤ) + 1)) =
    Cochain.fromSingleMk
      (H.originalConnectingRepresentative q f ≫
        (H.res₁.cochainComplexXIso ((q : ℤ) + 1) (q + 1) (by simp)).inv)
      (zero_add ((q : ℤ) + 1))
  exact hcc

end CategoryTheory.Functor.RightDerived

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v u' v'
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {S : ShortComplex C} {hS : S.ShortExact}

/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`, with resolutions
`I₁,I₂,I₃` and chosen row splittings. For additive `F : C → D` into an abelian category, applying
`F` to the section and retraction in degree `q` gives a splitting
of the mapped resolution row `F(I₁^q) → F(I₂^q) → F(I₃^q)`. -/
def HorseshoeData.mappedSplitting (H : HorseshoeData S hS) (F : C ⥤ D) [F.Additive]
    (q : ℕ) :
    ((H.mapped F).map (HomologicalComplex.eval D (.up ℕ) q)).Splitting :=
  (H.split q).map F

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `H` be compatible injective
horseshoe data for short exact `S : X₁ → X₂ → X₃`, with resolutions
`I₁,I₂,I₃` and chosen row splittings. Let `D` be abelian and `F : C → D` additive. On the cycles
of `F(I₃)` in degree `q`, quotient to homology followed by the mapped
cohomology boundary equals the class of the split connecting
representative obtained by section, middle differential, and retraction
in the mapped diagram. -/
theorem HorseshoeData.mapped_delta_cycles (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (q : ℕ) :
    (H.mapped F).X₃.homologyπ q ≫ (H.mapped_shortExact F).δ q (q + 1) rfl =
      (H.mapped F).X₁.liftCycles
        (HomologicalComplex.splitConnectingRepresentative (H.mapped F) (H.mappedSplitting F)
          q ((H.mapped F).X₃.iCycles q))
        (q + 2) (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl))
        (HomologicalComplex.splitConnectingRepresentative_cycle (H.mapped F)
          (H.mappedSplitting F) q ((H.mapped F).X₃.iCycles q)
          ((H.mapped F).X₃.iCycles_d q (q + 1))) ≫ (H.mapped F).X₁.homologyπ (q + 1) :=
  HomologicalComplex.splitDiagram_delta_cycles (H.mapped F) (H.mappedSplitting F) q

end CategoryTheory.Functor.RightDerived

end
