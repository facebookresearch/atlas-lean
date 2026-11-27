/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import MathlibExt.Algebra.Homology.HomComplex.HomologyRepresentatives

/-!
# Mapping-cone boundaries and connecting morphisms

For a short exact sequence of integer cochain complexes, the boundary
of the canonical cone triangle agrees on homology with the connecting
morphism after the canonical cone-to-quotient map and shift identification.

Degreewise split sequences remain short exact under additive functors.
Their cone-boundary formula is compatible with the functor and its shift
comparison. Extension by zero also retains the evaluated splitting data.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe u v
namespace CochainComplex.mappingCone
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Let C be an abelian category and S=(A→B→D) a short exact sequence of integer cochain
complexes, with first map f. Let p:Cone(f)→D be the canonical map and b:Cone(f)→A⟦1⟧ the third
arrow of its cone triangle. For q∈ℤ and the standard shift isomorphism η:H^q(A⟦1⟧)≅H^{q+1}(A),
H^q(b)≫η.hom = H^q(p)≫δ_S, where δ_S:H^q(D)→H^{q+1}(A) is the sequence's connecting morphism.
-/
theorem native_boundary_of_shortExact
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (q : ℤ) :
    HomologicalComplex.homologyMap (triangle S.f).mor₃ q ≫
        (CochainComplex.ShiftSequence.shiftIso C 1 q (q + 1)
          (by omega)).hom.app S.X₁ =
      HomologicalComplex.homologyMap (descShortComplex S) q ≫
        hS.δ q (q + 1) rfl := by
  have h := homologySequenceδ_triangleh hS q (q + 1) rfl
  change (HomotopyCategory.homologyFunctor C (.up ℤ) 0).homologySequenceδ
      ((HomotopyCategory.quotient C (.up ℤ)).mapTriangle.obj (triangle S.f))
      q (q + 1) rfl = _ at h
  rw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj] at h
  apply (cancel_epi ((HomotopyCategory.homologyFunctorFactors C (.up ℤ) q).hom.app _)).mp
  apply (cancel_mono ((HomotopyCategory.homologyFunctorFactors C (.up ℤ) (q + 1)).inv.app _)).mp
  simp only [Functor.shiftMap, CochainComplex.homologyFunctor_shift, Category.assoc] at h
  change (HomotopyCategory.homologyFunctorFactors C (.up ℤ) q).hom.app (mappingCone S.f) ≫
      HomologicalComplex.homologyMap (triangle S.f).mor₃ q ≫
      (CochainComplex.ShiftSequence.shiftIso C 1 q (q + 1) (by omega)).hom.app S.X₁ ≫
      (HomotopyCategory.homologyFunctorFactors C (.up ℤ) (q + 1)).inv.app S.X₁ =
    (HomotopyCategory.homologyFunctorFactors C (.up ℤ) q).hom.app (mappingCone S.f) ≫
      HomologicalComplex.homologyMap (descShortComplex S) q ≫
      hS.δ q (q + 1) rfl ≫
      (HomotopyCategory.homologyFunctorFactors C (.up ℤ) (q + 1)).inv.app S.X₁ at h
  dsimp only [triangle] at h ⊢
  simp only [Category.assoc]
  exact h

end CochainComplex.mappingCone

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe u v u' v'
namespace CochainComplex.mappingCone
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/--
Let C,D be abelian categories and F:C⥤D an additive functor. Let S=(A→B→E) be a short complex
of integer cochain complexes, with a splitting of its evaluation at every integer degree.
Applying F termwise gives a short exact sequence of cochain complexes in D. Degreewise
splitting is sufficient; preservation of arbitrary exact sequences by F is not assumed.
-/
theorem degreewiseSplit_map_shortExact (F : C ⥤ D) [F.Additive]
    (S : ShortComplex (CochainComplex C ℤ))
    (s : ∀ n : ℤ, (S.map (HomologicalComplex.eval C (.up ℤ) n)).Splitting) :
    (S.map (F.mapHomologicalComplex (.up ℤ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have h := ((s n).map F).shortExact
  simp only [← ShortComplex.map_comp] at h ⊢
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Let C,D be abelian categories and F:C⥤D an additive functor. Let S=(A→B→E) be a short complex
of integer cochain complexes, with a splitting of its evaluation at every integer degree. For
the canonical cone maps b:Cone(S.f)→A⟦1⟧ and p:Cone(S.f)→E, apply F and identify F(A⟦1⟧) with
F(A)⟦1⟧. In every degree q, the induced boundary H^q(F(b)) followed by the shift
identification equals H^q(F(p)) followed by the connecting map of F(S).
-/
theorem mapped_native_boundary (F : C ⥤ D) [F.Additive]
    (S : ShortComplex (CochainComplex C ℤ))
    (s : ∀ n : ℤ, (S.map (HomologicalComplex.eval C (.up ℤ) n)).Splitting)
    (q : ℤ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map (triangle S.f).mor₃ ≫
          ((F.mapHomologicalComplex (.up ℤ)).commShiftIso 1).hom.app S.X₁) q ≫
      (CochainComplex.ShiftSequence.shiftIso D 1 q (q + 1) (by omega)).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj S.X₁) =
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map (descShortComplex S)) q ≫
      (degreewiseSplit_map_shortExact F S s).δ q (q + 1) rfl := by
  have hm := congrArg (fun f => HomologicalComplex.homologyMap f q) (map_δ S.f F)
  simp only [HomologicalComplex.homologyMap_comp] at hm
  rw [HomologicalComplex.homologyMap_comp, hm, Category.assoc]
  have hb := native_boundary_of_shortExact (degreewiseSplit_map_shortExact F S s) q
  have hd := congrArg (fun f => HomologicalComplex.homologyMap f q)
    (mapHomologicalComplexIso_hom_descShortComplex F S)
  simp only [HomologicalComplex.homologyMap_comp] at hd
  exact (congrArg (fun f => HomologicalComplex.homologyMap
    (mapHomologicalComplexIso S.f F).hom q ≫ f) hb).trans
      (((Category.assoc _ _ _).symm).trans
        (congrArg (fun f => f ≫ (degreewiseSplit_map_shortExact F S s).δ q (q + 1) rfl) hd))

end CochainComplex.mappingCone

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v
namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

set_option backward.isDefEq.respectTransparency false in
/--
Let C be an abelian category, S a short complex of c-complexes, and e:c→c' a shape embedding.
At i'=e(i), extending all three complexes by zero and evaluating at i' gives a short complex
canonically isomorphic to evaluation of S at i, through the three original
extension-coordinate isomorphisms.
-/
def extendDiagramEvalIso (S : ShortComplex (HomologicalComplex C c))
    (e : c.Embedding c') (i : ι) (i' : ι') (h : e.f i = i') :
    ((S.map (e.extendFunctor C)).map (eval C c' i')) ≅ S.map (eval C c i) := by
  refine ShortComplex.isoMk (extendXIso S.X₁ e h) (extendXIso S.X₂ e h)
    (extendXIso S.X₃ e h) ?_ ?_
  · symm
    change (extendMap S.f e).f i' ≫ (extendXIso S.X₂ e h).hom =
      (extendXIso S.X₁ e h).hom ≫ S.f.f i
    rw [extendMap_f _ e h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · symm
    change (extendMap S.g e).f i' ≫ (extendXIso S.X₃ e h).hom =
      (extendXIso S.X₂ e h).hom ≫ S.g.f i
    rw [extendMap_f _ e h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
Let C be an abelian category and S a short complex of c-complexes with a splitting at every
evaluated degree i. For a shape embedding e:c→c', its extension by zero has a splitting at
every degree i': at i'=e(i) transport the original splitting, and outside the image all three
objects are zero.
-/
def extendDiagramSplitting (S : ShortComplex (HomologicalComplex C c))
    (s : ∀ i : ι, (S.map (eval C c i)).Splitting) (e : c.Embedding c') (i' : ι') :
    ((S.map (e.extendFunctor C)).map (eval C c' i')).Splitting := by
  classical
  by_cases h : ∃ i : ι, e.f i = i'
  · exact (s (Classical.choose h)).ofIso
      (extendDiagramEvalIso S e (Classical.choose h) i' (Classical.choose_spec h)).symm
  · exact ShortComplex.Splitting.ofIsZero
      ((S.map (e.extendFunctor C)).map (eval C c' i'))
      (S.X₁.isZero_extend_X e i' (fun i hi => h ⟨i, hi⟩))
      (S.X₂.isZero_extend_X e i' (fun i hi => h ⟨i, hi⟩))
      (S.X₃.isZero_extend_X e i' (fun i hi => h ⟨i, hi⟩))

end HomologicalComplex

end
