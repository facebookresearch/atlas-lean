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
# Opposite derived categories and cohomological bound reflection

Let C be abelian. Degree-negating cochain reflection gives
Cochain(C,ℤ)ᵒᵖ ≃ Cochain(Cᵒᵖ,ℤ), with degree-n homology
canonically op(H^{−n}(K)). It preserves quasi-isomorphisms in both
directions.

For independently chosen derived categories, localization gives
D(C)ᵒᵖ ≃ D(Cᵒᵖ). The forward and inverse localization comparisons
retain the reflected cochain representatives. A derived object has
cohomology vanishing above n exactly when its reflection has
cohomology vanishing below −n.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

namespace DerivedCategory.OppositeTransport

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Let C be abelian and R_op the contravariant cochain reflection from
integer-indexed C-complexes to Cᵒᵖ-complexes, with term op(K^{−n})
in degree n.

The equivalence Cochain(C,ℤ)ᵒᵖ ≃ Cochain(Cᵒᵖ,ℤ) given by passage to the opposite category and
negation of the degree index. -/
abbrev cochainEquivalence : (CochainComplex C ℤ)ᵒᵖ ≌ CochainComplex Cᵒᵖ ℤ :=
  CochainComplex.opEquivalence C

/-- Let C be abelian and R_op the contravariant cochain reflection from
integer-indexed C-complexes to Cᵒᵖ-complexes, with term op(K^{−n})
in degree n.

For any K and n∈ℤ, the canonical isomorphism H^n(R_op(K)) ≅ op(H^{−n}(K)). -/
def cochainHomologyIso (K : CochainComplex C ℤ) (n : ℤ) :
    ((cochainEquivalence C).functor.obj (op K)).homology n ≅ op (K.homology (-n)) :=
  HomologicalComplex.chainToCochainHomologyIso K.op n ≪≫ K.homologyOp (-n)

/-- Let C be abelian and R_op the contravariant cochain reflection from
integer-indexed C-complexes to Cᵒᵖ-complexes, with term op(K^{−n})
in degree n.

A cochain map f is a quasi-isomorphism if and only if its reflected opposite map R_op(f) is a
quasi-isomorphism. -/
theorem cochain_map_quasiIso_iff {X Y : (CochainComplex C ℤ)ᵒᵖ} (f : X ⟶ Y) :
    QuasiIso ((cochainEquivalence C).functor.map f) ↔ QuasiIso f.unop :=
  (HomologicalComplex.quasiIso_cochainComplexEquivalence_map_iff
    ((HomologicalComplex.opFunctor C (ComplexShape.up ℤ)).map f)).trans
      (HomologicalComplex.quasiIso_opFunctor_map_iff f.unop)

/-- Let C be abelian and R_op the contravariant cochain reflection from
integer-indexed C-complexes to Cᵒᵖ-complexes, with term op(K^{−n})
in degree n.

If a map of Cᵒᵖ-cochain complexes is a quasi-isomorphism, its inverse-reflected map of C-cochain
complexes is a quasi-isomorphism. -/
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
/-- Let C be abelian and R_op the contravariant cochain reflection from
integer-indexed C-complexes to Cᵒᵖ-complexes, with term op(K^{−n})
in degree n.

With a chosen derived category of Cᵒᵖ, its localization sends reflected quasi-isomorphisms of
C-complexes to isomorphisms. -/
theorem forwardInverts :
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op.IsInvertedBy
      ((cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ)) := by
  intro X Y f hf
  let _ : QuasiIso ((cochainEquivalence C).functor.map f) := (cochain_map_quasiIso_iff C f).2 hf
  change IsIso (DerivedCategory.Q.map ((cochainEquivalence C).functor.map f))
  infer_instance

omit [HasDerivedCategory.{w'} Cᵒᵖ] in
/-- Let C be abelian and R_op the contravariant cochain reflection from
integer-indexed C-complexes to Cᵒᵖ-complexes, with term op(K^{−n})
in degree n.

With a chosen derived category of C, opposite localization sends the inverse reflections of
quasi-isomorphisms of Cᵒᵖ-complexes to isomorphisms. -/
theorem inverseInverts :
    (HomologicalComplex.quasiIso Cᵒᵖ (ComplexShape.up ℤ)).IsInvertedBy
      ((cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C)))) := by
  intro X Y f hf
  let _ : QuasiIso (((cochainEquivalence C).inverse.map f).unop) :=
    cochain_inverse_map_quasiIso C f hf
  change IsIso ((DerivedCategory.Q.map (((cochainEquivalence C).inverse.map f).unop)).op)
  infer_instance

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

The forward functor Φ:D(C)ᵒᵖ → D(Cᵒᵖ) obtained by localizing R_op. -/
def forward : (DerivedCategory C)ᵒᵖ ⥤ DerivedCategory Cᵒᵖ :=
  Localization.lift ((cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ))
    (forwardInverts C) (Functor.op (DerivedCategory.Q (C := C)))

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

The backward functor Ψ:D(Cᵒᵖ) → D(C)ᵒᵖ obtained by localizing inverse cochain reflection. -/
def backward : DerivedCategory Cᵒᵖ ⥤ (DerivedCategory C)ᵒᵖ :=
  Localization.lift ((cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C))))
    (inverseInverts C) (DerivedCategory.Q (C := Cᵒᵖ))

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

The natural comparison Φ(Q_C(K)ᵒᵖ) ≅ Q_{Cᵒᵖ}(R_op(K)) identifies forward derived reflection with
localization of the reflected representative. -/
def forwardFac : (Functor.op (DerivedCategory.Q (C := C))) ⋙ forward C ≅
    (cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ) :=
  Localization.fac ((cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ))
    (forwardInverts C) (Functor.op (DerivedCategory.Q (C := C)))

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

The natural comparison for Ψ identifies Ψ(Q_{Cᵒᵖ}(L)) with the opposite localization of the
inverse-reflected C-complex. -/
def backwardFac : DerivedCategory.Q (C := Cᵒᵖ) ⋙ backward C ≅
    (cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C))) :=
  Localization.fac ((cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C))))
    (inverseInverts C) (DerivedCategory.Q (C := Cᵒᵖ))

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

The forward functor Φ, together with Φ∘Q_Cᵒᵖ ≅ Q_{Cᵒᵖ}∘R_op, is the localization lift of cochain
reflection. -/
instance forward_lifting :
    Localization.Lifting (Functor.op (DerivedCategory.Q (C := C)))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
      ((cochainEquivalence C).functor ⋙ DerivedCategory.Q (C := Cᵒᵖ)) (forward C) :=
  ⟨forwardFac C⟩

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

The backward functor Ψ, with its comparison on localized representatives, is the localization lift
of inverse cochain reflection. -/
instance backward_lifting :
    Localization.Lifting (DerivedCategory.Q (C := Cᵒᵖ))
      (HomologicalComplex.quasiIso Cᵒᵖ (ComplexShape.up ℤ))
      ((cochainEquivalence C).inverse ⋙ (Functor.op (DerivedCategory.Q (C := C)))) (backward C) :=
  ⟨backwardFac C⟩

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

The equivalence D(C)ᵒᵖ ≃ D(Cᵒᵖ), with forward and inverse functors the two localization lifts of
cochain reflection. -/
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

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

The forward functor of the derived opposite equivalence is Φ, the localized cochain-reflection
functor. -/
theorem equivalence_functor_eq : (equivalence C).functor = forward C := rfl

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

The inverse functor of the derived opposite equivalence is Ψ, the localized inverse-reflection
functor. -/
theorem equivalence_inverse_eq : (equivalence C).inverse = backward C := rfl

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

For X in D(C), its reflected object in D(Cᵒᵖ) is the forward equivalence applied to op(X). -/
abbrev reflect (X : DerivedCategory C) : DerivedCategory Cᵒᵖ :=
  (equivalence C).functor.obj (op X)

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

If Y in D(Cᵒᵖ) has cohomology zero below −n, its inverse-reflected object in D(C) has cohomology
zero above n. -/
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

/-- Let C be abelian with chosen derived categories D(C) and D(Cᵒᵖ).
Their category object, morphism and derived-category universes are
independent. Write R_op for degree-negating cochain reflection.

For X in D(C) and n∈ℤ, H^k(X)=0 for k>n if and only if H^k(reflect(X))=0 for k<−n. -/
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
