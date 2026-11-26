/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import MathlibExt.Algebra.Homology.HomotopyCofiberMappingCone
public import MathlibExt.Algebra.Homology.HomotopyCofiberReindex
public import MathlibExt.Algebra.Homology.ChainToCochainHomology
import MathlibExt.Algebra.Homology.ShortComplex.MiddleQuasiIso

/-!
# Homotopy cofibers of short exact sequences of complexes

In an abelian category, the canonical descendant from the homotopy
cofiber of the first map of a short exact sequence of integer complexes
to its third complex is a quasi-isomorphism. The integer cochain case
is compared with the mapping-cone sequence, and degree-negation
reindexing gives the integer chain case.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency.types false in
theorem quasiIso_map
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂)
    (ha : QuasiIso a) (hb : QuasiIso b) :
    QuasiIso (map φ₁ φ₂ a b comm) := by
  let tm := (CategoryTheory.Pretriangulated.rotate (CochainComplex C ℤ)).map
    (triangleMap φ₁ φ₂ a b comm)
  let f : triangleRotateShortComplex φ₁ ⟶ triangleRotateShortComplex φ₂ :=
    { τ₁ := b
      τ₂ := map φ₁ φ₂ a b comm
      τ₃ := tm.hom₃
      comm₁₂ := tm.comm₁.symm
      comm₂₃ := tm.comm₂.symm }
  have hS₁ : (triangleRotateShortComplex φ₁).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n ↦ (triangleRotateShortComplexSplitting φ₁ n).shortExact)
  have hS₂ : (triangleRotateShortComplex φ₂).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n ↦ (triangleRotateShortComplexSplitting φ₂ n).shortExact)
  have h₁ : QuasiIso f.τ₁ := by
    dsimp [f]
    exact hb
  have h₃ : QuasiIso f.τ₃ := by
    change QuasiIso (a⟦(1 : ℤ)⟧')
    exact (CochainComplex.quasiIso_shift_iff a 1).2 ha
  exact HomologicalComplex.HomologySequence.quasiIso_τ₂ f hS₁ hS₂ h₁ h₃

end CochainComplex.mappingCone

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem quasiIso_mapArrowHom_up
    {F G F' G' : CochainComplex C ℤ}
    {φ : F ⟶ G} {ψ : F' ⟶ G'}
    (a : Arrow.mk φ ⟶ Arrow.mk ψ)
    (ha : QuasiIso a.left) (hb : QuasiIso a.right) :
    QuasiIso (mapArrowHom φ ψ (fun j ↦ ⟨j - 1, by simp⟩) a) := by
  rw [mapArrowHom_eq_mappingCone_map (fun j ↦ ⟨j - 1, by simp⟩) a]
  exact CochainComplex.mappingCone.quasiIso_map
    φ ψ a.left a.right a.w.symm ha hb

set_option backward.isDefEq.respectTransparency.types false in
theorem quasiIso_mapArrowHom
    {F G F' G' : ChainComplex C ℤ}
    {φ : F ⟶ G} {ψ : F' ⟶ G'}
    (a : Arrow.mk φ ⟶ Arrow.mk ψ)
    (ha : QuasiIso a.left) (hb : QuasiIso a.right) :
    QuasiIso (mapArrowHom φ ψ (fun j ↦ ⟨j + 1, by simp⟩) a) := by
  rw [← HomologicalComplex.quasiIso_cochainComplexEquivalence_map_iff]
  let E := (ChainComplex.cochainComplexEquivalence C).functor
  let ae := E.mapArrow.map a
  have hae_left : QuasiIso ae.left := by
    change QuasiIso (E.map a.left)
    exact (HomologicalComplex.quasiIso_cochainComplexEquivalence_map_iff a.left).2 ha
  have hae_right : QuasiIso ae.right := by
    change QuasiIso (E.map a.right)
    exact (HomologicalComplex.quasiIso_cochainComplexEquivalence_map_iff a.right).2 hb
  have hcone : QuasiIso
      (mapArrowHom (E.mapArrow.obj (Arrow.mk φ)).hom
        (E.mapArrow.obj (Arrow.mk ψ)).hom
        (fun j ↦ ⟨j - 1, by simp⟩) ae) := by
    exact quasiIso_mapArrowHom_up ae hae_left hae_right
  let e := chainToCochainNatIso (C := C)
  let f := E.map (mapArrowHom φ ψ (fun j ↦ ⟨j + 1, by simp⟩) a)
  rw [← quasiIso_iff_comp_right f (e.app (Arrow.mk ψ)).hom]
  have hn :
      f ≫ (e.app (Arrow.mk ψ)).hom =
        (e.app (Arrow.mk φ)).hom ≫
          mapArrowHom (E.mapArrow.obj (Arrow.mk φ)).hom
            (E.mapArrow.obj (Arrow.mk ψ)).hom
            (fun j ↦ ⟨j - 1, by simp⟩) ae := by
    simpa [f, E, ae] using e.hom.naturality a
  rw [hn]
  exact quasiIso_comp
    (hφ := (inferInstance : QuasiIso ((e.app (Arrow.mk φ)).hom)))
    (hφ' := hcone)
    (e.app (Arrow.mk φ)).hom
    (mapArrowHom (E.mapArrow.obj (Arrow.mk φ)).hom
      (E.mapArrow.obj (Arrow.mk ψ)).hom
      (fun j ↦ ⟨j - 1, by simp⟩) ae)

private lemma descShortComplex_eq_mappingCone_descShortComplex
    (S : ShortComplex (CochainComplex C ℤ)) :
    HomologicalComplex.homotopyCofiber.descShortComplex S =
      CochainComplex.mappingCone.descShortComplex S := by
  ext i
  dsimp only [HomologicalComplex.homotopyCofiber.descShortComplex]
  unfold CochainComplex.mappingCone.descShortComplex
  rw [HomologicalComplex.homotopyCofiber.desc_f S.f S.g (Homotopy.ofEq S.zero)
    i (i + 1) (by simp)]
  rw [CochainComplex.mappingCone.desc_f S.f 0 S.g _ i (i + 1) (by simp)]
  simp only [homotopyCofiber_X, Homotopy.ofEq_hom, Pi.zero_apply, comp_zero,
    zero_add, Int.reduceNeg, CochainComplex.HomComplex.Cochain.zero_v]
  erw [CochainComplex.HomComplex.Cochain.ofHoms_v]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem quasiIso_descShortComplex
    (S : ShortComplex (ChainComplex C ℤ)) (hS : S.ShortExact) :
    QuasiIso (HomologicalComplex.homotopyCofiber.descShortComplex S) := by
  rw [← HomologicalComplex.quasiIso_cochainComplexEquivalence_map_iff]
  rw [← chainToCochainNatIso_hom_descShortComplex S]
  have hS' :
      (S.map (ChainComplex.cochainComplexEquivalence C).functor).ShortExact :=
    hS.map_of_exact (ChainComplex.cochainComplexEquivalence C).functor
  apply (_root_.quasiIso_iff_comp_left
    ((chainToCochainNatIso (C := C)).app (Arrow.mk S.f)).hom
    (HomologicalComplex.homotopyCofiber.descShortComplex
      (S.map (ChainComplex.cochainComplexEquivalence C).functor))).2
  rw [descShortComplex_eq_mappingCone_descShortComplex]
  exact CochainComplex.mappingCone.quasiIso_descShortComplex hS'

end HomologicalComplex.homotopyCofiber

-- Author: @toskua
namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an abelian category `C`, let `S : K → L → M` be a short
exact sequence of integer cochain complexes. The canonical descendant
`homotopyCofiber(S.f) → M` is a quasi-isomorphism. -/
theorem quasiIso_descShortComplex_up
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact) :
    QuasiIso (HomologicalComplex.homotopyCofiber.descShortComplex S) := by
  rw [descShortComplex_eq_mappingCone_descShortComplex S]
  exact CochainComplex.mappingCone.quasiIso_descShortComplex hS

end HomologicalComplex.homotopyCofiber
