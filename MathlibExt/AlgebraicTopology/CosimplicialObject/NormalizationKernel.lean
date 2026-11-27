/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.CosimplicialObject.Normalization
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Codegeneracy kernels and normalized cochains

The normalized cochain inclusion identifies its source with the common kernel
of the codegeneracy maps. A cochain annihilated by every codegeneracy has a
unique lift through this inclusion. The normalization projection supplies the
lift, and the projection-inclusion identity proves uniqueness.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicTopology

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The degree carrier of the alternating-coface comparison. -/
def alternatingCofaceObjIso (X : CosimplicialObject A) (n : ℕ) :
    ((alternatingCofaceMapComplex A).obj X).X n ≅ X.obj (SimplexCategory.mk n) :=
  Iso.refl _

/-- The forward map of the degreewise alternating-coface comparison is the identity. -/
@[simp]
theorem alternatingCofaceObjIso_hom (X : CosimplicialObject A) (n : ℕ) :
    (alternatingCofaceObjIso X n).hom = 𝟙 _ := rfl

/-- The cochain projection is the dual normalized Moore inclusion. -/
theorem normalizedCofaceMapProjection_f (X : CosimplicialObject A) (n : ℕ) :
    ((normalizedCofaceMapProjection A).app X).f n =
      ((inclusionOfMooreComplexMap
        ((cosimplicialSimplicialEquiv A).functor.obj (op X))).f n).unop :=
  normalizedCofaceMapProjection_app_f A X n

/-- The cochain inclusion is the dual Dold--Kan projection. -/
theorem inclusionOfNormalizedCofaceMapComplex_f (X : CosimplicialObject A) (n : ℕ) :
    ((inclusionOfNormalizedCofaceMapComplex A).app X).f n =
      ((DoldKan.PInftyToNormalizedMooreComplex
        ((cosimplicialSimplicialEquiv A).functor.obj (op X))).f n).unop :=
  inclusionOfNormalizedCofaceMapComplex_app_f A X n

/-- In each degree the normalized inclusion is split by the projection. -/
theorem inclusionOfNormalizedCofaceMapComplex_f_comp_projection
    (X : CosimplicialObject A) (n : ℕ) :
    ((inclusionOfNormalizedCofaceMapComplex A).app X).f n ≫
        ((normalizedCofaceMapProjection A).app X).f n = 𝟙 _ := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
    congrArg (fun f => f.f n) (normalizedCoface_inclusion_projection_app A X)

/-- The full-degree projector is the dual Dold--Kan projector. -/
theorem normalizedCofaceMapProjection_f_comp_inclusion
    (X : CosimplicialObject A) (n : ℕ) :
    ((normalizedCofaceMapProjection A).app X).f n ≫
        ((inclusionOfNormalizedCofaceMapComplex A).app X).f n =
      ((DoldKan.PInfty
        (X := (cosimplicialSimplicialEquiv A).functor.obj (op X))).f n).unop := by
  let S : SimplicialObject Aᵒᵖ := (cosimplicialSimplicialEquiv A).functor.obj (op X)
  let K : ChainComplex Aᵒᵖ ℕ := (alternatingFaceMapComplex Aᵒᵖ).obj S
  let N : ChainComplex Aᵒᵖ ℕ := (normalizedMooreComplex Aᵒᵖ).obj S
  let i : N ⟶ K := inclusionOfMooreComplexMap S
  let p : K ⟶ N := DoldKan.PInftyToNormalizedMooreComplex S
  let P : K ⟶ K := DoldKan.PInfty (X := S)
  let T : A := ((alternatingCofaceMapComplex A).obj X).X n
  let TN : A := ((normalizedCofaceMapComplex A).obj X).X n
  let iU : T ⟶ TN := (i.f n).unop
  let pU : TN ⟶ T := (p.f n).unop
  let PU : T ⟶ T := (P.f n).unop
  have hi : ((normalizedCofaceMapProjection A).app X).f n = iU :=
    normalizedCofaceMapProjection_f X n
  have hp : ((inclusionOfNormalizedCofaceMapComplex A).app X).f n = pU :=
    inclusionOfNormalizedCofaceMapComplex_f X n
  have hWhole : p ≫ i = P :=
    DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap S
  have hNative : p.f n ≫ i.f n = P.f n := by
    change (p ≫ i).f n = P.f n
    exact HomologicalComplex.congr_hom hWhole n
  have hUnop : iU ≫ pU = PU := by
    exact (CategoryTheory.unop_comp (f := p.f n) (g := i.f n)).symm.trans
      (congrArg (fun f : K.X n ⟶ K.X n => f.unop) hNative)
  calc
    _ = iU ≫ ((inclusionOfNormalizedCofaceMapComplex A).app X).f n :=
      congrArg (fun f : T ⟶ TN =>
        f ≫ ((inclusionOfNormalizedCofaceMapComplex A).app X).f n) hi
    _ = iU ≫ pU := congrArg (fun f : TN ⟶ T => iU ≫ f) hp
    _ = PU := hUnop

/-- The normalized inclusion is annihilated by every codegeneracy. -/
theorem inclusionOfNormalizedCofaceMapComplex_f_comp_σ
    (X : CosimplicialObject A) (n : ℕ) (i : Fin (n + 1)) :
    ((inclusionOfNormalizedCofaceMapComplex A).app X).f (n + 1) ≫
      (alternatingCofaceObjIso X (n + 1)).hom ≫ X.σ i = 0 := by
  have hCoordinate : (alternatingCofaceObjIso X (n + 1)).hom ≫ X.σ i = X.σ i := by
    change 𝟙 (X.obj (SimplexCategory.mk (n + 1))) ≫ X.σ i = X.σ i
    exact Category.id_comp _
  calc
    _ = ((inclusionOfNormalizedCofaceMapComplex A).app X).f (n + 1) ≫ X.σ i :=
      congrArg (fun f => ((inclusionOfNormalizedCofaceMapComplex A).app X).f (n + 1) ≫ f)
        hCoordinate
    _ = 0 := inclusionOfNormalizedCofaceMapComplex_codegeneracy A X n i

/-- A map annihilating all codegeneracies factors through the normalization. -/
theorem comp_normalizedCofaceMapProjection_f_comp_inclusion
    (X : CosimplicialObject A) (n : ℕ) {T : A}
    (g : T ⟶ ((alternatingCofaceMapComplex A).obj X).X (n + 1))
    (hg : ∀ i : Fin (n + 1), g ≫ (alternatingCofaceObjIso X (n + 1)).hom ≫
      X.σ i = 0) :
    g ≫ ((normalizedCofaceMapProjection A).app X).f (n + 1) ≫
        ((inclusionOfNormalizedCofaceMapComplex A).app X).f (n + 1) = g := by
  let S := (cosimplicialSimplicialEquiv A).functor.obj (op X)
  let fN : S.obj (op (SimplexCategory.mk (n + 1))) ⟶ op T := g.op
  have hSσ (i : Fin (n + 1)) : (S.σ i).unop = X.σ i := by
    dsimp [S, cosimplicialSimplicialEquiv, Functor.opUnopEquiv, Functor.opHom,
      SimplicialObject.σ, CosimplicialObject.σ]
  have hv : DoldKan.DegeneraciesVanish (X := S) fN := by
    rw [DoldKan.degeneraciesVanish_succ_iff]
    intro i
    have hDegree : (alternatingCofaceObjIso X (n + 1)).hom ≫ X.σ i = X.σ i :=
      (congrArg (fun k ↦ k ≫ X.σ i)
        (alternatingCofaceObjIso_hom X (n + 1))).trans (Category.id_comp _)
    have hCodegeneracy : g ≫ X.σ i = 0 :=
      (congrArg (fun k ↦ g ≫ k) hDegree).symm.trans (hg i)
    have hNative : g ≫ (S.σ i).unop = 0 :=
      (congrArg (fun k ↦ g ≫ k) (hSσ i)).trans hCodegeneracy
    apply Quiver.Hom.unop_inj
    change g ≫ (S.σ i).unop = 0
    exact hNative
  have hQ : ((DoldKan.QInfty (X := S)).f (n + 1)) ≫ fN = 0 :=
    (DoldKan.degeneraciesVanish_iff_QInfty_f_comp (X := S) fN).mp hv
  have hSum := congrArg (fun t ↦ t ≫ fN)
    (DoldKan.PInfty_f_add_QInfty_f (X := S) (n + 1))
  have hP : ((DoldKan.PInfty (X := S)).f (n + 1)) ≫ fN = fN := by
    calc
      ((DoldKan.PInfty (X := S)).f (n + 1)) ≫ fN =
          ((DoldKan.PInfty (X := S)).f (n + 1)) ≫ fN + 0 := (add_zero _).symm
      _ = ((DoldKan.PInfty (X := S)).f (n + 1)) ≫ fN +
          ((DoldKan.QInfty (X := S)).f (n + 1)) ≫ fN := congrArg _ hQ.symm
      _ = (((DoldKan.PInfty (X := S)).f (n + 1)) +
          ((DoldKan.QInfty (X := S)).f (n + 1))) ≫ fN :=
        (Preadditive.add_comp _ _ _ _ _ _).symm
      _ = 𝟙 _ ≫ fN := hSum
      _ = fN := Category.id_comp _
  have hPUnop : g ≫ ((DoldKan.PInfty (X := S)).f (n + 1)).unop = g := by
    apply Quiver.Hom.op_inj
    change (DoldKan.PInfty (X := S)).f (n + 1) ≫ g.op = g.op
    simpa only [fN] using hP
  exact (congrArg (fun k ↦ g ≫ k)
    (normalizedCofaceMapProjection_f_comp_inclusion X (n + 1))).trans hPUnop

/-- The map collecting all codegeneracies out of degree n+1. -/
def codegeneracyProduct (X : CosimplicialObject A) (n : ℕ) :
    ((alternatingCofaceMapComplex A).obj X).X (n + 1) ⟶
      ∏ᶜ (fun _ : Fin (n + 1) ↦ X.obj (SimplexCategory.mk n)) :=
  (alternatingCofaceObjIso X (n + 1)).hom ≫ Pi.lift (fun i ↦ X.σ i)

/-- The normalized inclusion is a kernel fork for the joint codegeneracy map. -/
theorem inclusionOfNormalizedCofaceMapComplex_f_comp_codegeneracyProduct
    (X : CosimplicialObject A) (n : ℕ) :
    ((inclusionOfNormalizedCofaceMapComplex A).app X).f (n + 1) ≫
      codegeneracyProduct X n = 0 := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, codegeneracyProduct, Category.assoc, Pi.lift_comp_π,
    inclusionOfNormalizedCofaceMapComplex_f_comp_σ, zero_comp]

/-- The normalization is the universal kernel of the codegeneracies. -/
def normalizationKernelIsLimit (X : CosimplicialObject A) (n : ℕ) :
    IsLimit (KernelFork.ofι
      (((inclusionOfNormalizedCofaceMapComplex A).app X).f (n + 1))
      (inclusionOfNormalizedCofaceMapComplex_f_comp_codegeneracyProduct X n)) := by
  refine KernelFork.IsLimit.ofι _ _
    (fun {T} g _ ↦ g ≫ ((normalizedCofaceMapProjection A).app X).f (n + 1)) ?_ ?_
  · intro T g hg
    rw [Category.assoc]
    apply comp_normalizedCofaceMapProjection_f_comp_inclusion
    intro i
    let π := Pi.π (fun _ : Fin (n + 1) ↦ X.obj (SimplexCategory.mk n)) i
    have h := congrArg (fun t ↦ t ≫ π) hg
    calc
      g ≫ (alternatingCofaceObjIso X (n + 1)).hom ≫ X.σ i =
          g ≫ (codegeneracyProduct X n ≫ π) := by
        rw [codegeneracyProduct, Category.assoc, Pi.lift_comp_π]
      _ = (g ≫ codegeneracyProduct X n) ≫ π := (Category.assoc _ _ _).symm
      _ = 0 ≫ π := h
      _ = 0 := zero_comp
  · intro T g hg m hm
    have hm' := congrArg
      (fun k ↦ k ≫ ((normalizedCofaceMapProjection A).app X).f (n + 1)) hm
    calc
      m = m ≫ ((inclusionOfNormalizedCofaceMapComplex A).app X).f (n + 1) ≫
          ((normalizedCofaceMapProjection A).app X).f (n + 1) := by
        rw [inclusionOfNormalizedCofaceMapComplex_f_comp_projection, Category.comp_id]
      _ = (m ≫ ((inclusionOfNormalizedCofaceMapComplex A).app X).f (n + 1)) ≫
          ((normalizedCofaceMapProjection A).app X).f (n + 1) :=
        (Category.assoc _ _ _).symm
      _ = g ≫ ((normalizedCofaceMapProjection A).app X).f (n + 1) := hm'

end AlgebraicTopology

end
