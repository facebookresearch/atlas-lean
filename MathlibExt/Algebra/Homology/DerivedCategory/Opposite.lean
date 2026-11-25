/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.Opposite
public import MathlibExt.Algebra.Homology.ChainToCochainHomology
public import Mathlib.CategoryTheory.Localization.Equivalence
public import Mathlib.CategoryTheory.Localization.Opposite

/-!
# The actual opposite equivalence of derived categories and reflected bounds

The native cochain opposite/degree-reflection equivalence preserves
quasi-isomorphisms by the existing homology-op and reindexing comparisons.
Native localization lifts its forward and inverse functors. The original
cochain equivalence unit and counit give both localization round trips.

The same actual reflected complexes exchange strict upper and lower
bounds. Native strictly bounded representatives then prove the exact
IsLE/IsGE correspondence on derived objects. No desired equivalence,
resolution, comparison, or bound certificate is caller input.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

namespace DerivedCategory.OppositeTransport

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The original native cochain opposite and degree-reflection equivalence. -/
abbrev cochainEquivalence : (CochainComplex C ℤ)ᵒᵖ ≌ CochainComplex Cᵒᵖ ℤ :=
  CochainComplex.opEquivalence C

/-- Homology of the actual reflected complex is the original opposite homology in degree -n. -/
def cochainHomologyIso (K : CochainComplex C ℤ) (n : ℤ) :
    ((cochainEquivalence C).functor.obj (op K)).homology n ≅ op (K.homology (-n)) :=
  HomologicalComplex.chainToCochainHomologyIso K.op n ≪≫ K.homologyOp (-n)

/-- Native homology-op and degree reflection preserve precisely the original quasi-isomorphisms. -/
theorem cochain_map_quasiIso_iff {X Y : (CochainComplex C ℤ)ᵒᵖ} (f : X ⟶ Y) :
    QuasiIso ((cochainEquivalence C).functor.map f) ↔ QuasiIso f.unop :=
  (HomologicalComplex.quasiIso_cochainComplexEquivalence_map_iff
    ((HomologicalComplex.opFunctor C (ComplexShape.up ℤ)).map f)).trans
      (HomologicalComplex.quasiIso_opFunctor_map_iff f.unop)

/-- The native inverse reflection preserves quasi-isomorphisms by its original counit round trip. -/
theorem cochain_inverse_map_quasiIso {X Y : CochainComplex Cᵒᵖ ℤ} (f : X ⟶ Y)
    (hf : QuasiIso f) : QuasiIso (((cochainEquivalence C).inverse.map f).unop) := by
  let E := cochainEquivalence C
  let _ : QuasiIso f := hf
  have h : QuasiIso (E.functor.map (E.inverse.map f)) := by
    apply (quasiIso_iff_comp_right _ (E.counitIso.hom.app Y)).1
    have hNat : E.functor.map (E.inverse.map f) ≫ E.counitIso.hom.app Y =
        E.counitIso.hom.app X ≫ f := by
      simpa only [Functor.comp_map, Functor.id_map] using E.counitIso.hom.naturality f
    rw [hNat]
    infer_instance
  exact (cochain_map_quasiIso_iff C (E.inverse.map f)).1 h

private theorem strictGE_reflection (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    CochainComplex.IsStrictlyGE ((cochainEquivalence C).functor.obj (op K)) (-n) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  change IsZero (op (K.X (-i)))
  have hlt : i < -n := by simpa using hi
  have hn : n < -i := by simpa only [neg_neg] using (neg_lt_neg hlt)
  exact (K.isZero_of_isStrictlyLE n (-i) hn).op

private theorem strictLE_inverse (K : CochainComplex Cᵒᵖ ℤ) (n : ℤ) [K.IsStrictlyGE (-n)] :
    CochainComplex.IsStrictlyLE (unop ((cochainEquivalence C).inverse.obj K)) n := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  change IsZero (unop (K.X (-i)))
  have hlt : n < i := by simpa using hi
  exact (K.isZero_of_isStrictlyGE (-n) (-i) (neg_lt_neg hlt)).unop

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} Cᵒᵖ]

omit [HasDerivedCategory.{w} C] in
/-- The actual reflected cochain functor is inverted by native derived localization. -/
theorem forwardInverts :
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op.IsInvertedBy
      ((cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ)) := by
  intro X Y f hf
  let _ : QuasiIso ((cochainEquivalence C).functor.map f) := (cochain_map_quasiIso_iff C f).2 hf
  change IsIso (DerivedCategory.Q.map ((cochainEquivalence C).functor.map f))
  infer_instance

omit [HasDerivedCategory.{w'} Cᵒᵖ] in
/-- The original inverse cochain functor is inverted by native opposite derived localization. -/
theorem inverseInverts :
    (HomologicalComplex.quasiIso Cᵒᵖ (ComplexShape.up ℤ)).IsInvertedBy
      ((cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C)))) := by
  intro X Y f hf
  let _ : QuasiIso (((cochainEquivalence C).inverse.map f).unop) :=
    cochain_inverse_map_quasiIso C f hf
  change IsIso ((DerivedCategory.Q.map (((cochainEquivalence C).inverse.map f).unop)).op)
  infer_instance

/-- Native localization of the actual forward cochain reflection. -/
def forward : (DerivedCategory C)ᵒᵖ ⥤ DerivedCategory Cᵒᵖ :=
  Localization.lift ((cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ))
    (forwardInverts C) (Functor.op (DerivedCategory.Q (C := C)))

/-- Native localization of the actual inverse cochain reflection. -/
def backward : DerivedCategory Cᵒᵖ ⥤ (DerivedCategory C)ᵒᵖ :=
  Localization.lift ((cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C))))
    (inverseInverts C) (DerivedCategory.Q (C := Cᵒᵖ))

/-- The forward localization comparison retains the actual cochain reflection. -/
def forwardFac : (Functor.op (DerivedCategory.Q (C := C))) ⋙ forward C ≅
    (cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ) :=
  Localization.fac ((cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ))
    (forwardInverts C) (Functor.op (DerivedCategory.Q (C := C)))

/-- The inverse localization comparison retains the actual inverse cochain reflection. -/
def backwardFac : DerivedCategory.Q (C := Cᵒᵖ) ⋙ backward C ≅
    (cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C))) :=
  Localization.fac ((cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C))))
    (inverseInverts C) (DerivedCategory.Q (C := Cᵒᵖ))

/-- The same actual forward localization comes with its native lifting comparison. -/
instance forward_lifting :
    Localization.Lifting (Functor.op (DerivedCategory.Q (C := C)))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
      ((cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ)) (forward C) :=
  ⟨forwardFac C⟩

/-- The same actual inverse localization comes with its native lifting comparison. -/
instance backward_lifting :
    Localization.Lifting (DerivedCategory.Q (C := Cᵒᵖ))
      (HomologicalComplex.quasiIso Cᵒᵖ (ComplexShape.up ℤ))
      ((cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C)))) (backward C) :=
  ⟨backwardFac C⟩

/-- The actual derived-category opposite equivalence, with both native reflection round trips earned. -/
def equivalence : (DerivedCategory C)ᵒᵖ ≌ DerivedCategory Cᵒᵖ := by
  let α : ((cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ)) ⋙ backward C ≅
      (Functor.op (DerivedCategory.Q (C := C))) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (cochainEquivalence C).functor (backwardFac C) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (cochainEquivalence C).unitIso.symm
        (Functor.op (DerivedCategory.Q (C := C))) ≪≫ Functor.leftUnitor _
  let β : ((cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C)))) ⋙ forward C ≅
      DerivedCategory.Q (C := Cᵒᵖ) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (cochainEquivalence C).inverse (forwardFac C) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (cochainEquivalence C).counitIso
        (DerivedCategory.Q (C := Cᵒᵖ)) ≪≫ Functor.leftUnitor _
  exact Localization.equivalence
    (Functor.op (DerivedCategory.Q (C := C))) (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
    (DerivedCategory.Q (C := Cᵒᵖ)) (HomologicalComplex.quasiIso Cᵒᵖ (ComplexShape.up ℤ))
    ((cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ)) (forward C)
    ((cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C)))) (backward C) α β

/-- Native localization retains precisely the original forward functor. -/
theorem equivalence_functor_eq : (equivalence C).functor = forward C := rfl

/-- Native localization retains precisely the original inverse functor. -/
theorem equivalence_inverse_eq : (equivalence C).inverse = backward C := rfl

/-- The actual reflected derived object. -/
abbrev reflect (X : DerivedCategory C) : DerivedCategory Cᵒᵖ :=
  (equivalence C).functor.obj (op X)

/-- A native lower cohomological bound becomes the corresponding original upper bound under the inverse. -/
theorem inverse_isLE_of_isGE (Y : DerivedCategory Cᵒᵖ) (n : ℤ) (hY : Y.IsGE (-n)) :
    (unop ((equivalence C).inverse.obj Y)).IsLE n := by
  let _ : Y.IsGE (-n) := hY
  obtain ⟨K, hK, ⟨eK⟩⟩ := Y.exists_iso_Q_obj_of_isGE (-n)
  let _ : K.IsStrictlyGE (-n) := hK
  let _ : CochainComplex.IsStrictlyLE (unop ((cochainEquivalence C).inverse.obj K)) n :=
    strictLE_inverse C K n
  let e : (equivalence C).inverse.obj Y ≅
      op (DerivedCategory.Q.obj (unop ((cochainEquivalence C).inverse.obj K))) :=
    by
      rw [equivalence_inverse_eq]
      refine (backward C).mapIso eK ≪≫ ?_
      simpa only [Functor.comp_obj, Functor.op_obj] using (backwardFac C).app K
  exact DerivedCategory.TStructure.t.isLE_of_iso e.unop n

/-- Native cohomological upper bounds correspond exactly to reflected lower bounds. -/
theorem isLE_iff_reflect_isGE (X : DerivedCategory C) (n : ℤ) :
    X.IsLE n ↔ (reflect C X).IsGE (-n) := by
  constructor
  · intro hX
    let _ : X.IsLE n := hX
    obtain ⟨K, hK, ⟨eK⟩⟩ := X.exists_iso_Q_obj_of_isLE n
    let _ : K.IsStrictlyLE n := hK
    let _ : CochainComplex.IsStrictlyGE ((cochainEquivalence C).functor.obj (op K)) (-n) :=
      strictGE_reflection C K n
    let e : reflect C X ≅ DerivedCategory.Q.obj ((cochainEquivalence C).functor.obj (op K)) :=
      by
        change (equivalence C).functor.obj (op X) ≅ _
        rw [equivalence_functor_eq]
        refine ((forward C).mapIso eK.op).symm ≪≫ ?_
        simpa only [Functor.comp_obj, Functor.op_obj] using (forwardFac C).app (op K)
    exact DerivedCategory.TStructure.t.isGE_of_iso e.symm (-n)
  · intro hX
    let _ := inverse_isLE_of_isGE C (reflect C X) n hX
    let e : X ≅ unop ((equivalence C).inverse.obj (reflect C X)) :=
      ((equivalence C).unitIso.app (op X)).unop.symm
    exact DerivedCategory.TStructure.t.isLE_of_iso e.symm n

end DerivedCategory.OppositeTransport

end
