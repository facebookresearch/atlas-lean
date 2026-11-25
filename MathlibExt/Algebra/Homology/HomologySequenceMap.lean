/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module
public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.Algebra.Homology.ShortComplex.MapHomologyOpcycles
public import MathlibExt.Algebra.Homology.ShortComplex.SnakeLemmaFunctor
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
@[expose] public section
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {ι : Type*} {c : ComplexShape ι}
private noncomputable def mapOpcyclesFunctorIso (i : ι) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    F.mapHomologicalComplex c ⋙ opcyclesFunctor D c i ≅
      opcyclesFunctor C c i ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc i).mapOpcyclesIso F)
    (fun f => ShortComplex.mapOpcyclesIso_hom_naturality
      ((shortComplexFunctor C c i).map f) F)
private noncomputable def mapCyclesFunctorIso (i : ι) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    F.mapHomologicalComplex c ⋙ cyclesFunctor D c i ≅
      cyclesFunctor C c i ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc i).mapCyclesIso F)
    (fun f => ShortComplex.mapCyclesIso_hom_naturality
      ((shortComplexFunctor C c i).map f) F)
end HomologicalComplex
namespace CategoryTheory
namespace ShortComplex
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (T : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable {ι : Type*} {c : ComplexShape ι}
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma mapCyclesIso_hom_homologyπ :
    (T.mapCyclesIso F).hom ≫ F.map T.homologyπ =
      (T.map F).homologyπ ≫ (T.mapHomologyIso F).hom := by
  rw [T.homologyData.left.mapHomologyIso_eq F]
  rw [T.homologyData.left.mapCyclesIso_eq F]
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [Category.assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  rw [cancel_epi]
  rw [ShortComplex.LeftHomologyData.map_π]
  rw [← F.map_comp, ← F.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma map_homological_toCycles_mapCyclesIso_hom
    (K : HomologicalComplex C c) (i j : ι) :
    ((F.mapHomologicalComplex c).obj K).toCycles i j ≫
      ((K.sc j).mapCyclesIso F).hom = F.map (K.toCycles i j) := by
  have hC : ((K.sc j).mapCyclesIso F).hom ≫ F.map (K.iCycles j) =
      ((F.mapHomologicalComplex c).obj K).iCycles j := by
    exact ShortComplex.mapCyclesIso_hom_iCycles (S := K.sc j) F
  rw [← cancel_mono (F.map (K.iCycles j))]
  rw [Category.assoc, hC]
  rw [← F.map_comp, K.toCycles_i,
    ((F.mapHomologicalComplex c).obj K).toCycles_i]
  rfl
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma mapOpcyclesToCycles (K : HomologicalComplex C c) (i j : ι) :
    ((K.sc i).mapOpcyclesIso F).hom ≫ F.map (K.opcyclesToCycles i j) =
      ((F.mapHomologicalComplex c).obj K).opcyclesToCycles i j ≫
        ((K.sc j).mapCyclesIso F).hom := by
  rw [← cancel_epi (((K.sc i).map F).pOpcycles)]
  rw [← Category.assoc, pOpcycles_comp_mapOpcyclesIso_hom]
  rw [← F.map_comp]
  change F.map (K.pOpcycles i ≫ K.opcyclesToCycles i j) = _
  rw [K.pOpcycles_opcyclesToCycles]
  rw [show ((K.sc i).map F).pOpcycles =
    ((F.mapHomologicalComplex c).obj K).pOpcycles i from rfl]
  rw [← Category.assoc,
    ((F.mapHomologicalComplex c).obj K).pOpcycles_opcyclesToCycles]
  rw [map_homological_toCycles_mapCyclesIso_hom]
namespace ShortExact
theorem mapHomologyFunctorIso_hom_δ
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
    (hSF : (S.map (F.mapHomologicalComplex c)).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    (HomologicalComplex.mapHomologyFunctorIso (c := c) i F).hom.app S.X₃ ≫
        F.map (hS.δ i j hij) =
      hSF.δ i j hij ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := c) j F).hom.app S.X₁ := by
  let src := HomologicalComplex.HomologySequence.snakeInput hS i j hij
  let tgt := HomologicalComplex.HomologySequence.snakeInput hSF i j hij
  let eHi := HomologicalComplex.mapHomologyFunctorIso (c := c) i F
  let eOi := HomologicalComplex.mapOpcyclesFunctorIso (c := c) i F
  let eCj := HomologicalComplex.mapCyclesFunctorIso (c := c) j F
  let eHj := HomologicalComplex.mapHomologyFunctorIso (c := c) j F
  let φ : tgt ⟶ src.mapExactFunctor F :=
    { f₀ := S.mapNatTrans eHi.hom
      f₁ := S.mapNatTrans eOi.hom
      f₂ := S.mapNatTrans eCj.hom
      f₃ := S.mapNatTrans eHj.hom
      comm₀₁ := by
        apply ShortComplex.hom_ext
        all_goals
          dsimp [src, tgt, eHi, eOi,
            HomologicalComplex.mapHomologyFunctorIso,
            HomologicalComplex.mapOpcyclesFunctorIso,
            HomologicalComplex.HomologySequence.snakeInput,
            ShortComplex.SnakeInput.mapExactFunctor]
        all_goals
          apply mapHomologyIso_hom_comp_homologyι
      comm₁₂ := by
        apply ShortComplex.hom_ext
        all_goals
          dsimp [src, tgt, eOi, eCj,
            HomologicalComplex.mapOpcyclesFunctorIso,
            HomologicalComplex.mapCyclesFunctorIso,
            HomologicalComplex.HomologySequence.snakeInput,
            ShortComplex.SnakeInput.mapExactFunctor]
        all_goals
          apply mapOpcyclesToCycles
      comm₂₃ := by
        apply ShortComplex.hom_ext
        all_goals
          dsimp [src, tgt, eCj, eHj,
            HomologicalComplex.mapCyclesFunctorIso,
            HomologicalComplex.mapHomologyFunctorIso,
            HomologicalComplex.HomologySequence.snakeInput,
            ShortComplex.SnakeInput.mapExactFunctor]
        all_goals
          apply mapCyclesIso_hom_homologyπ }
  have hn := ShortComplex.SnakeInput.naturality_δ φ
  dsimp [src, tgt, eHi, eHj] at hn ⊢
  rw [ShortComplex.SnakeInput.mapExactFunctor_δ] at hn
  exact hn.symm

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian and `F : C → D` preserve zero morphisms,
finite limits and finite colimits. For a short exact sequence `S`
of complexes of shape `c`, with its mapped sequence also short exact,
and `c.Rel i j`, the inverse homology comparisons satisfy
`e_i⁻¹ ≫ δ_(F(S)) = F(δ_S) ≫ e_j⁻¹` at the third and first objects. -/
theorem mapHomologyFunctorIso_inv_δ
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
    (hSF : (S.map (F.mapHomologicalComplex c)).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    (HomologicalComplex.mapHomologyFunctorIso (c := c) i F).inv.app S.X₃ ≫
        hSF.δ i j hij =
      F.map (hS.δ i j hij) ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := c) j F).inv.app S.X₁ := by
  let eSource := (HomologicalComplex.mapHomologyFunctorIso (c := c) i F).app S.X₃
  let eTarget := (HomologicalComplex.mapHomologyFunctorIso (c := c) j F).app S.X₁
  have h := mapHomologyFunctorIso_hom_δ F hS hSF i j hij
  change eSource.hom ≫ F.map (hS.δ i j hij) =
    hSF.δ i j hij ≫ eTarget.hom at h
  change eSource.inv ≫ hSF.δ i j hij =
    F.map (hS.δ i j hij) ≫ eTarget.inv
  apply (cancel_epi eSource.hom).mp
  calc
    eSource.hom ≫ (eSource.inv ≫ hSF.δ i j hij) =
        hSF.δ i j hij := by
      rw [Iso.hom_inv_id_assoc]
    _ = (hSF.δ i j hij ≫ eTarget.hom) ≫ eTarget.inv := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (eSource.hom ≫ F.map (hS.δ i j hij)) ≫ eTarget.inv := by
      rw [h]
    _ = eSource.hom ≫
        (F.map (hS.δ i j hij) ≫ eTarget.inv) := by
      rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian and `F : C → D` preserve zero morphisms,
finite limits and finite colimits. Let `S` be short exact in complexes
of shape `c`, its mapped sequence short exact, and `φ : F(S) → T`
a map to another short exact sequence. For `c.Rel i j`, the inverse
homology comparisons followed by `H_i(φ₃)` and `H_j(φ₁)` give a
commuting square with `F(δ_S)` and `δ_T`. -/
theorem mapHomologyFunctorIso_inv_comp_δ_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S : ShortComplex (HomologicalComplex C c)}
    {T : ShortComplex (HomologicalComplex D c)}
    (hS : S.ShortExact)
    (hSF : (S.map (F.mapHomologicalComplex c)).ShortExact)
    (hT : T.ShortExact)
    (φ : S.map (F.mapHomologicalComplex c) ⟶ T)
    (i j : ι) (hij : c.Rel i j) :
    ((HomologicalComplex.mapHomologyFunctorIso (c := c) i F).inv.app S.X₃ ≫
        HomologicalComplex.homologyMap φ.τ₃ i) ≫
      hT.δ i j hij =
    F.map (hS.δ i j hij) ≫
      ((HomologicalComplex.mapHomologyFunctorIso (c := c) j F).inv.app S.X₁ ≫
        HomologicalComplex.homologyMap φ.τ₁ j) := by
  have hMap := mapHomologyFunctorIso_inv_δ F hS hSF i j hij
  have hNat := HomologicalComplex.HomologySequence.δ_naturality
    φ hSF hT i j hij
  simp only [Category.assoc]
  rw [← hNat, ← Category.assoc, hMap]
  simp only [Category.assoc]

/-- In an abelian category `C`, let `e : S ≅ T` be an isomorphism
of short exact sequences of complexes of shape `c`. For `c.Rel i j`,
the boundaries satisfy `δ_S = H_i(e₃) ≫ δ_T ≫ H_j(e₁⁻¹)`. -/
theorem δ_eq_comp_of_iso
    {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S T : ShortComplex (HomologicalComplex C c)}
    (e : S ≅ T) (hS : S.ShortExact) (hT : T.ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    hS.δ i j hij =
      HomologicalComplex.homologyMap e.hom.τ₃ i ≫ hT.δ i j hij ≫
        HomologicalComplex.homologyMap e.inv.τ₁ j := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    e.hom hS hT i j hij
  rw [← Category.assoc, ← h, Category.assoc,
    ← HomologicalComplex.homologyMap_comp]
  have he : e.hom.τ₁ ≫ e.inv.τ₁ = 𝟙 _ :=
    congrArg (fun f : S ⟶ S => f.τ₁) e.hom_inv_id
  rw [he, HomologicalComplex.homologyMap_id, Category.comp_id]

/-- In an abelian category `C`, let `e : S ≅ T` be an isomorphism
of short exact sequences of complexes of shape `c`. For `c.Rel i j`,
the inverse conjugation formula is
`δ_T = H_i(e₃⁻¹) ≫ δ_S ≫ H_j(e₁)`. -/
theorem δ_eq_comp_of_iso_inv
    {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S T : ShortComplex (HomologicalComplex C c)}
    (e : S ≅ T) (hS : S.ShortExact) (hT : T.ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    hT.δ i j hij =
      HomologicalComplex.homologyMap e.inv.τ₃ i ≫ hS.δ i j hij ≫
        HomologicalComplex.homologyMap e.hom.τ₁ j := by
  simpa using δ_eq_comp_of_iso e.symm hT hS i j hij
end ShortExact
end ShortComplex
end CategoryTheory
